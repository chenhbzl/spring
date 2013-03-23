/* This file is part of the Spring engine (GPL v2 or later), see LICENSE.html */

#include <cassert>

#include "lib/gml/gmlmut.h"
#include "lib/gml/gml_base.h"
#include "UnitHandler.h"
#include "Unit.h"
#include "UnitDefHandler.h"
#include "CommandAI/BuilderCAI.h"
#include "Sim/Misc/AirBaseHandler.h"
#include "Sim/Misc/TeamHandler.h"
#include "Sim/MoveTypes/MoveType.h"
#include "Sim/Path/IPathManager.h"
#include "System/Config/ConfigHandler.h"
#include "System/EventHandler.h"
#include "System/EventBatchHandler.h"
#include "System/Log/ILog.h"
#include "System/Platform/SimThreadPool.h"
#include "System/TimeProfiler.h"
#include "System/myMath.h"
#include "System/Sync/SyncTracer.h"
#include "System/creg/STL_Deque.h"
#include "System/creg/STL_List.h"
#include "System/creg/STL_Set.h"

#if defined(DEBUG) && defined(HEADLESS) // assume validation test
CONFIG(int, SimThreadCount).defaultValue(3).safemodeValue(3).minimumValue(3).maximumValue(3);
#else
CONFIG(int, SimThreadCount).defaultValue(0).safemodeValue(1).minimumValue(0).maximumValue(GML_MAX_NUM_THREADS);
#endif

//////////////////////////////////////////////////////////////////////
// Construction/Destruction
//////////////////////////////////////////////////////////////////////

CUnitHandler* unitHandler = NULL;
static void UpdateMoveTypeThreadFuncStatic(bool threaded) { unitHandler->UpdateMoveTypeThreadFunc(threaded); }
static void SlowUpdateMoveTypeInitThreadFuncStatic(bool threaded) { unitHandler->SlowUpdateMoveTypeInitThreadFunc(threaded); }
static void SlowUpdateMoveTypeThreadFuncStatic(bool threaded) { unitHandler->SlowUpdateMoveTypeThreadFunc(threaded); }
static void DelayedSlowUpdateMoveTypeThreadFuncStatic(bool threaded) { unitHandler->DelayedSlowUpdateMoveTypeThreadFunc(threaded); }

CR_BIND(CUnitHandler, );
CR_REG_METADATA(CUnitHandler, (
	CR_MEMBER(units),
	CR_MEMBER(unitsByDefs),
	CR_MEMBER(activeUnits),
	CR_MEMBER(builderCAIs),
	CR_MEMBER(idPool),
	CR_MEMBER(unitsToBeRemoved),
	CR_MEMBER(maxUnits),
	CR_MEMBER(maxUnitRadius),
	CR_POSTLOAD(PostLoad)
));



void CUnitHandler::PostLoad()
{
	// reset any synced stuff that is not saved
	activeSlowUpdateUnit = activeUnits.end();
}


CUnitHandler::CUnitHandler()
:
	maxUnits(0),
	maxUnitRadius(0.0f)
{
	// set the global (runtime-constant) unit-limit as the sum
	// of  all team unit-limits, which is *always* <= MAX_UNITS
	// (note that this also counts the Gaia team)
	//
	// teams can not be created at runtime, but they can die and
	// in that case the per-team limit is recalculated for every
	// other team in the respective allyteam
	for (unsigned int n = 0; n < teamHandler->ActiveTeams(); n++) {
		maxUnits += teamHandler->Team(n)->GetMaxUnits();
	}

	units.resize(maxUnits, NULL);
	unitsByDefs.resize(teamHandler->ActiveTeams(), std::vector<CUnitSet>(unitDefHandler->unitDefs.size()));

	// id's are used as indices, so they must lie in [0, units.size() - 1]
	// (furthermore all id's are treated equally, none have special status)
	idPool.Expand(0, units.size());

	activeSlowUpdateUnit = activeUnits.end();
	airBaseHandler = new CAirBaseHandler();
	simThreadPool = new CSimThreadPool();
}


CUnitHandler::~CUnitHandler()
{
	delete simThreadPool;
	for (std::list<CUnit*>::iterator usi = activeUnits.begin(); usi != activeUnits.end(); ++usi) {
		// ~CUnit dereferences featureHandler which is destroyed already
		(*usi)->delayedWreckLevel = -1;
		delete (*usi);
	}

	delete airBaseHandler;
}

void CUnitHandler::InsertActiveUnit(CUnit* unit)
{
	std::list<CUnit*>::iterator ui = activeUnits.begin();

	if (ui != activeUnits.end()) {
		// randomize this to make the slow-update order random (good if one
		// builds say many buildings at once and then many mobile ones etc)
		const unsigned int insertionPos = gs->randFloat() * activeUnits.size();

		for (unsigned int n = 0; n < insertionPos; ++n) {
			++ui;
		}
	}

	idPool.AssignID(unit);

	assert(unit->id < units.size());
	assert(units[unit->id] == NULL);

	activeUnits.insert(ui, unit);
	units[unit->id] = unit;
}


bool CUnitHandler::AddUnit(CUnit* unit)
{
	// LoadUnit should make sure this is true
	assert(CanAddUnit(unit->id));

	InsertActiveUnit(unit);

	teamHandler->Team(unit->team)->AddUnit(unit, CTeam::AddBuilt);
	unitsByDefs[unit->team][unit->unitDef->id].insert(unit);

	maxUnitRadius = std::max(unit->radius, maxUnitRadius);
	return true;
}

void CUnitHandler::DeleteUnit(CUnit* unit)
{
	unitsToBeRemoved.push_back(unit);
	(eventBatchHandler->GetUnitCreatedDestroyedBatch()).dequeue_synced(unit);
}


void CUnitHandler::DeleteUnitNow(CUnit* delUnit)
{
	delUnit->ExecuteDelayOps();
	int delTeam = 0;
	int delType = 0;

	std::list<CUnit*>::iterator usi;

	for (usi = activeUnits.begin(); usi != activeUnits.end(); ++usi) {
		if (*usi == delUnit) {
			if (activeSlowUpdateUnit != activeUnits.end() && *usi == *activeSlowUpdateUnit) {
				++activeSlowUpdateUnit;
			}
			delTeam = delUnit->team;
			delType = delUnit->unitDef->id;

			GML_STDMUTEX_LOCK(dque); // DeleteUnitNow

			teamHandler->Team(delTeam)->RemoveUnit(delUnit, CTeam::RemoveDied);

			activeUnits.erase(usi);
			unitsByDefs[delTeam][delType].erase(delUnit);
			idPool.FreeID(delUnit->id, true);

			units[delUnit->id] = NULL;

			CSolidObject::SetDeletingRefID(delUnit->id);
			delete delUnit;
			CSolidObject::SetDeletingRefID(-1);

			break;
		}
	}

#ifdef _DEBUG
	for (usi = activeUnits.begin(); usi != activeUnits.end(); /* no post-op */) {
		if (*usi == delUnit) {
			LOG_L(L_ERROR, "Duplicated unit found in active units on erase");
			usi = activeUnits.erase(usi);
		} else {
			++usi;
		}
	}
#endif
}

void CUnitHandler::Update()
{
	static int nBlockOps = 0;
	{
		GML_STDMUTEX_LOCK(runit); // Update

		IPathManager::ScopedDisableThreading sdt;
		{
			SCOPED_TIMER("Unit::MoveType::Update");

			for (int i = 0; i < nBlockOps; ++i) {
				int id = blockOps[i];
				(id > 0) ? units[id - 1]->Block() : units[-id - 1]->UnBlock();
			}
			if (modInfo.multiThreadSim)
				pathManager->MergePathCaches();
			CSolidObject::UpdateStableData();
		}

		if (!unitsToBeRemoved.empty()) {
			GML_RECMUTEX_LOCK(obj); // Update

			while (!unitsToBeRemoved.empty()) {
				eventHandler.DeleteSyncedObjects(); // the unit destructor may invoke eventHandler, so we need to call these for every unit to clear invaild references from the batching systems

				GML_RECMUTEX_LOCK(unit); // Update

				eventHandler.DeleteSyncedUnits();

				GML_RECMUTEX_LOCK(proj); // Update - projectile drawing may access owner() and lead to crash
				GML_RECMUTEX_LOCK(sel);  // Update - unit is removed from selectedUnits in ~CObject, which is too late.
				GML_RECMUTEX_LOCK(quad); // Update - make sure unit does not get partially deleted before before being removed from the quadfield

				CUnit* delUnit = unitsToBeRemoved.back();
				unitsToBeRemoved.pop_back();

				DeleteUnitNow(delUnit);
			}
		}

		eventHandler.UpdateUnits();
	}

	GML::UpdateTicks();

	#define VECTOR_SANITY_CHECK(v)                              \
		assert(!math::isnan(v.x) && !math::isinf(v.x)); \
		assert(!math::isnan(v.y) && !math::isinf(v.y)); \
		assert(!math::isnan(v.z) && !math::isinf(v.z));
	#define MAPPOS_SANITY_CHECK(unit)                          \
		if (unit->unitDef->IsGroundUnit()) {                   \
			assert(unit->pos.x >= -(float3::maxxpos * 16.0f)); \
			assert(unit->pos.x <=  (float3::maxxpos * 16.0f)); \
			assert(unit->pos.z >= -(float3::maxzpos * 16.0f)); \
			assert(unit->pos.z <=  (float3::maxzpos * 16.0f)); \
		}
	#define UNIT_SANITY_CHECK(unit)                 \
		VECTOR_SANITY_CHECK(unit->pos);             \
		VECTOR_SANITY_CHECK(unit->midPos);          \
		VECTOR_SANITY_CHECK(unit->relMidPos);       \
		VECTOR_SANITY_CHECK(unit->speed);           \
		VECTOR_SANITY_CHECK(unit->deathSpeed);      \
		VECTOR_SANITY_CHECK(unit->residualImpulse); \
		VECTOR_SANITY_CHECK(unit->rightdir);        \
		VECTOR_SANITY_CHECK(unit->updir);           \
		VECTOR_SANITY_CHECK(unit->frontdir);        \
		MAPPOS_SANITY_CHECK(unit);

	{
		SCOPED_TIMER("Unit::MoveType::Update");

		Threading::SetMultiThreadedSim(modInfo.multiThreadSim);
		Threading::SetThreadedPath(modInfo.asyncPathFinder);
		if (Threading::threadedPath)
			pathManager->Update(1);
		simThreadPool->Execute(&UpdateMoveTypeThreadFuncStatic);
		Threading::SetMultiThreadedSim(false);

		if (modInfo.asyncPathFinder) {
			nBlockOps = 0;
			// threaded pathing can run also during ExecuteDelayOps, since Block/UnBlock is further delayed
			for (std::list<CUnit*>::iterator i = activeUnits.begin(); i != activeUnits.end(); ++i) {
				CUnit* u = *i;
				if (!u->delayOps.empty()) {
					int block = u->ExecuteDelayOps(); // can generate new delay ops, but it will execute these also
					if (block) {
						blockOps[nBlockOps++] = block ? u->id + 1 : -(u->id + 1);
					}
				}
			}
		}
	}

	{
		SCOPED_TIMER("Unit::Update");
		std::list<CUnit*>::iterator usi;
		for (usi = activeUnits.begin(); usi != activeUnits.end(); ++usi) {
			CUnit* unit = *usi;

			UNIT_SANITY_CHECK(unit);

			if (unit->deathScriptFinished) {
				// there are many ways to fiddle with "deathScriptFinished", so a unit may
				// arrive here without having been properly killed (and isDead still false),
				// which can result in MT deadlocking -- FIXME verify this
				// (KU returns early if isDead)
				unit->KillUnit(NULL, false, true);

				DeleteUnit(unit);
			} else {
				unit->Update();
			}

			UNIT_SANITY_CHECK(unit);
		}
	}


	{
		SCOPED_TIMER("Unit::MoveType::SlowUpdate");

		Threading::SetMultiThreadedSim(modInfo.multiThreadSim);
		simThreadPool->Execute(&SlowUpdateMoveTypeThreadFuncStatic, &SlowUpdateMoveTypeInitThreadFuncStatic);

		Threading::SetMultiThreadedSim(false);
		simThreadPool->Execute(&DelayedSlowUpdateMoveTypeThreadFuncStatic);
	}

	{
		SCOPED_TIMER("Unit::SlowUpdate");

		// reset the iterator every <UNIT_SLOWUPDATE_RATE> frames
		if ((gs->frameNum & (UNIT_SLOWUPDATE_RATE - 1)) == 0) {
			activeSlowUpdateUnit = activeUnits.begin();
		}

		// stagger the SlowUpdate's
		int n = (activeUnits.size() / UNIT_SLOWUPDATE_RATE) + 1;

		for (; activeSlowUpdateUnit != activeUnits.end() && n != 0; ++activeSlowUpdateUnit) {
			CUnit* unit = *activeSlowUpdateUnit;

			UNIT_SANITY_CHECK(unit);
			unit->SlowUpdate();
			UNIT_SANITY_CHECK(unit);

			n--;
		}
	}
}


inline void UpdateMoveType(CUnit *unit) {
	Threading::SetThreadCurrentObjectID(unit->id);
	UNIT_SANITY_CHECK(unit);

	if (unit->moveType->Update())
		unit->QueMove();
	if (!unit->pos.IsInBounds() && (unit->speed.SqLength() > (MAX_UNIT_SPEED * MAX_UNIT_SPEED))) {
		// this unit is not coming back, kill it now without any death
		// sequence (so deathScriptFinished becomes true immediately)
		unit->QueKillUnit(false);
	}

	UNIT_SANITY_CHECK(unit);
	GML::GetTicks(unit->lastUnitUpdate);
}


void CUnitHandler::UpdateMoveTypeThreadFunc(bool threaded) {
	std::list<CUnit*>::iterator usi = activeUnits.begin();
	if (!threaded) {
		for (; usi != activeUnits.end(); ++usi)
			UpdateMoveType(*usi);
		return;
	}
	// (threaded)
	int curPos = 0;
	const int countEnd = activeUnits.size();
	while (true) {
		int nextPos = simThreadPool->NextIter();
		if (nextPos >= countEnd) break;
		while(curPos < nextPos) { ++usi; ++curPos; }
		UpdateMoveType(*usi);
	}
}

void CUnitHandler::SlowUpdateMoveTypeInitThreadFunc(bool threaded) {
	if (!modInfo.multiThreadSim)
		return; // not needed for singlethreaded sim
	// (threaded or not)
	memset(CUnit::updateOps, 0, sizeof(CUnit::updateOps));
}

void CUnitHandler::SlowUpdateMoveTypeThreadFunc(bool threaded) {
	std::list<CUnit*>::iterator sui = ((gs->frameNum & (UNIT_SLOWUPDATE_RATE - 1)) == 0) ? activeUnits.begin() : activeSlowUpdateUnit;
	int curPos = 0;
	const int countEnd = (activeUnits.size() / UNIT_SLOWUPDATE_RATE) + 1;
	if (!threaded) {
		for (; sui != activeUnits.end() && curPos < countEnd; ++sui, ++curPos) {
			CUnit *unit = *sui;
			Threading::SetThreadCurrentObjectID(unit->id);
			unit->moveType->SlowUpdate();
		}
		return;
	}
	// (threaded)
	while (true) {
		int nextPos = simThreadPool->NextIter();
		if (nextPos >= countEnd) break;
		while(curPos < nextPos && sui != activeUnits.end()) { ++sui; ++curPos; }
		if (sui == activeUnits.end()) break;
		CUnit *unit = *sui;
		Threading::SetThreadCurrentObjectID(unit->id);
		unit->moveType->SlowUpdate();
	}
}

inline void CUnitHandler::DelayedSlowUpdateMoveTypePart(int pos) {
	Threading::SetThreadCurrentObjectID(pos);
	switch(pos) {
		case 0:
			for (int i = 0; i < MAX_UNITS; ++i) {
				if (CUnit::updateOps[i] & CUnit::UPDATE_LOS) {
					units[i]->QueUpdateLOS(false);
				}
			}
			break;
		case 1:
			for (int i = 0; i < MAX_UNITS; ++i) {
				if (CUnit::updateOps[i] & CUnit::UPDATE_RADAR) {
					units[i]->QueUpdateRadar(false);
				}
			}
			break;
		case 2:
			for (int i = 0; i < MAX_UNITS; ++i) {
				if (CUnit::updateOps[i] & CUnit::UPDATE_QUAD) {
					units[i]->QueUpdateQuad(false);
				}
			}
			break;
		case 3:
			for (int i = 0; i < MAX_UNITS; ++i) {
				if (CUnit::updateOps[i] & CUnit::FIND_PAD) {
					units[i]->QueFindPad(false);
				}
			}
			break;
		default:
			LOG_L(L_ERROR, "Invalid slow update type");
	}
}

void CUnitHandler::DelayedSlowUpdateMoveTypeThreadFunc(bool threaded) {
	if (!modInfo.multiThreadSim)
		return; // not needed for singlethreaded sim
	// (threaded)
	const int countEnd = 4;
	if (!threaded) {
		for (int pos = 0; pos < countEnd; ++pos)
			DelayedSlowUpdateMoveTypePart(pos);
		return;
	}
	while (true) {
		int nextPos = simThreadPool->NextIter();
		if (nextPos >= countEnd) break;
		DelayedSlowUpdateMoveTypePart(nextPos);
	}
}



void CUnitHandler::AddBuilderCAI(CBuilderCAI* b)
{
	GML_STDMUTEX_LOCK(cai); // AddBuilderCAI

	// called from CBuilderCAI --> owner is already valid
	builderCAIs[b->owner->id] = b;
}

void CUnitHandler::RemoveBuilderCAI(CBuilderCAI* b)
{
	GML_STDMUTEX_LOCK(cai); // RemoveBuilderCAI

	// called from ~CUnit --> owner is still valid
	assert(b->owner != NULL);
	builderCAIs.erase(b->owner->id);
}



bool CUnitHandler::CanBuildUnit(const UnitDef* unitdef, int team) const
{
	if (teamHandler->Team(team)->AtUnitLimit()) {
		return false;
	}
	if (unitsByDefs[team][unitdef->id].size() >= unitdef->maxThisUnit) {
		return false;
	}

	return true;
}
