/* This file is part of the Spring engine (GPL v2 or later), see LICENSE.html */

#include "IPathManager.h"
#include "Default/PathManager.h"
#include "QTPFS/PathManager.hpp"
#include "Game/GlobalUnsynced.h"
#include "Sim/Misc/ModInfo.h"
#include "System/Config/ConfigHandler.h"
#include "System/Log/ILog.h"
#include "System/Platform/CrashHandler.h"
#include "System/TimeProfiler.h"

IPathManager* pathManager = NULL;
boost::thread* IPathManager::pathBatchThread = NULL;

IPathManager* IPathManager::GetInstance(unsigned int type, bool async) {
	static IPathManager* pm = NULL;

	if (pm == NULL) {
		const char* fmtStr = "[IPathManager::GetInstance] using %s path-manager in %s mode";
		const char* typeStr = "";

		switch (type) {
			case PFS_TYPE_DEFAULT: { typeStr = "DEFAULT"; pm = new       CPathManager(); } break;
			case PFS_TYPE_QTPFS:   { typeStr = "QTPFS";   pm = new QTPFS::PathManager(); } break;
		}
		if (async)
			pathBatchThread = new boost::thread(boost::bind<void, IPathManager, IPathManager*>(&IPathManager::AsynchronousThread, pm));

		LOG(fmtStr, typeStr, async ? "asynchronous" : "synchronous");
	}

	return pm;
}

IPathManager::IPathManager() : pathRequestID(0), wait(false), stopThread(false) {
}


int IPathManager::GetPathID(int cid) {
	std::map<int, unsigned int>::iterator it = newPathCache.find(cid);
	if (it != newPathCache.end())
		return it->second;

	PathData* p = GetPathDataRaw(cid);
	return (p == NULL) ? -1 : p->pathID;
}

#define NOTIFY_PATH_THREAD(stm) \
	bool waited; \
	{ \
		boost::mutex::scoped_lock preqLock(preqMutex); \
		stm \
		if ((waited = wait)) \
			wait = false;\
	} \
	if (waited) \
		cond.notify_one();

void IPathManager::Update(MT_WRAP int unused) {
	if (unused) {
		NOTIFY_PATH_THREAD(
			pathOps.push_back(PathOpData());
		)
		return;
	}
	ScopedDisableThreading sdt;
	Update(ST_CALL unused);
}

bool IPathManager::PathUpdated(MT_WRAP unsigned int pathID) {
	if (!Threading::threadedPath) {
		if (!modInfo.asyncPathFinder)
			return PathUpdated(ST_CALL pathID);
		PathData* p = GetPathData(pathID);
		return (p != NULL && p->pathID >= 0) ? PathUpdated(ST_CALL p->pathID) : false;
	}
	PathData* p;
	NOTIFY_PATH_THREAD(
		p = GetNewPathData(pathID);
		pathOps.push_back(PathOpData(PATH_UPDATED, pathID));
	)
	return (p != NULL && p->pathID >= 0) ? p->updated : false;
}


void IPathManager::UpdatePath(MT_WRAP const CSolidObject* owner, unsigned int pathID) {
	if (!Threading::threadedPath) {
		if (!modInfo.asyncPathFinder)
			return UpdatePath(ST_CALL owner, pathID);
		PathData* p = GetPathData(pathID);
		if (p != NULL && p->pathID >= 0)
			UpdatePath(ST_CALL owner, p->pathID);
		return;
	}
	NOTIFY_PATH_THREAD(
		pathOps.push_back(PathOpData(UPDATE_PATH, owner, pathID));
	)
}


bool IPathManager::IsFailPath(unsigned int pathID) {
	if (!modInfo.asyncPathFinder)
		return false;
	boost::mutex::scoped_lock preqLock(preqMutex);

	PathData* p = GetNewPathData(pathID);
	return (p == NULL) || (p->pathID == 0);
}


void IPathManager::DeletePath(MT_WRAP unsigned int pathID) {
	if (!Threading::threadedPath) {
		if (!modInfo.asyncPathFinder)
			return DeletePath(ST_CALL pathID);
		PathData* p = GetPathData(pathID);
		if (p != NULL && p->pathID >= 0)
			DeletePath(ST_CALL p->pathID);
		pathInfos.erase(pathID);
		return;
	}
	PathData* p;
	NOTIFY_PATH_THREAD(
		p = GetNewPathData(pathID);
		pathOps.push_back(PathOpData(DELETE_PATH, pathID));
	)
	if (p) {
		p->deleted = true;
	}
}


float3 IPathManager::NextWayPoint(
	MT_WRAP
	const CSolidObject* owner,
	unsigned int pathID,
	unsigned int numRetries,
	float3 callerPos,
	float radius,
	bool synced
	) {
		bool curwp = (owner != NULL) && (owner->pos == callerPos);
		if (!Threading::threadedPath) {
			if (!modInfo.asyncPathFinder)
				return NextWayPoint(ST_CALL owner, pathID, numRetries, callerPos, radius, synced);
			PathData* p = GetPathData(pathID);
			if (p == NULL || p->pathID < 0)
				return callerPos;
			float3& wp = curwp ? p->curWayPoint : p->nextWayPoint;
			wp = NextWayPoint(ST_CALL owner, p->pathID, numRetries, callerPos, radius, synced);
			return wp;
		}
		PathData* p;
		NOTIFY_PATH_THREAD(
			p = GetNewPathData(pathID);
			pathOps.push_back(PathOpData(curwp ? CUR_WAYPOINT : NEXT_WAYPOINT, owner, pathID, numRetries, callerPos, radius, synced));
		)
		if (p == NULL || p->pathID < 0)
			return callerPos;
		return curwp ? p->curWayPoint : p->nextWayPoint;
}


void IPathManager::GetPathWayPoints(
	MT_WRAP
	unsigned int pathID,
	std::vector<float3>& points,
	std::vector<int>& starts
	) {
		if (!modInfo.asyncPathFinder)
			return GetPathWayPoints(ST_CALL pathID, points, starts);
		ScopedDisableThreading sdt;
		PathData* p = GetPathData(pathID);
		if (p == NULL || p->pathID < 0)
			return;
		return GetPathWayPoints(ST_CALL p->pathID, points, starts);
}


unsigned int IPathManager::RequestPath(
	MT_WRAP
	CSolidObject* caller,
	const MoveDef* moveDef,
	const float3& startPos,
	const float3& goalPos,
	float goalRadius,
	bool synced
	) {
		if (!Threading::threadedPath) {
			if (!modInfo.asyncPathFinder)
				return RequestPath(ST_CALL caller, moveDef, startPos, goalPos, goalRadius, synced);
			unsigned int cid;
			do { cid = ++pathRequestID; } while ((cid == 0) || (pathInfos.find(cid) != pathInfos.end()));
			pathInfos[cid] = PathData(RequestPath(ST_CALL caller, moveDef, startPos, goalPos, goalRadius, synced), startPos);
			return cid;
		}
		unsigned int cid;
		NOTIFY_PATH_THREAD(
			do { cid = ++pathRequestID; } while ((cid == 0) || (pathInfos.find(cid) != pathInfos.end()));
			newPathInfos[cid] = PathData(-1, startPos);
			pathOps.push_back(PathOpData(REQUEST_PATH, caller, cid, moveDef, startPos, goalPos, goalRadius, synced));
		)
		return cid;
}


void IPathManager::AsynchronousThread() {
	streflop::streflop_init<streflop::Simple>();
	GML::ThreadNumber(GML_MAX_NUM_THREADS);
	Threading::SetThreadCurrentObjectID(-1);
	Threading::SetAffinityHelper("Path", configHandler->GetUnsigned("SetCoreAffinityPath"));

	while(true) {
		std::vector<PathOpData> pops;
		{
			boost::mutex::scoped_lock preqLock(preqMutex);
			if (stopThread)
				return;
			if (pathOps.empty()) {
				if (wait)
					cond.notify_one();
				wait = true;
				cond.wait(preqLock);
			}
			pathOps.swap(pops);
		}

		SCOPED_TIMER("IPathManager::AsynchronousThread");

		for (std::vector<PathOpData>::iterator i = pops.begin(); i != pops.end(); ++i) {
			PathOpData &cid = *i;
			unsigned int pid;
#if defined(USE_DESYNC_DETECTOR) && defined(MT_DESYNC_DETECTION)
			if (cid.ownerid >= 0)
				Threading::SetThreadCurrentObjectID(cid.ownerid + MAX_UNITS);
#endif
			switch(cid.type) {
				case REQUEST_PATH:
					pid = RequestPath(ST_CALL const_cast<CSolidObject*>(cid.owner), cid.moveDef, cid.startPos, cid.goalPos, cid.goalRadius, cid.synced);
					newPathCache[cid.pathID] = pid;
					pathUpdates[cid.pathID].push_back(PathUpdateData(REQUEST_PATH, pid));
					break;
				case CUR_WAYPOINT:
					pid = GetPathID(cid.pathID);
					if (pid >= 0)
						pathUpdates[cid.pathID].push_back(PathUpdateData(CUR_WAYPOINT, NextWayPoint(ST_CALL cid.owner, pid, cid.numRetries, cid.startPos, cid.minDistance, cid.synced)));
					break;
				case NEXT_WAYPOINT:
					pid = GetPathID(cid.pathID);
					if (pid >= 0)
						pathUpdates[cid.pathID].push_back(PathUpdateData(NEXT_WAYPOINT, NextWayPoint(ST_CALL cid.owner, pid, cid.numRetries, cid.startPos, cid.minDistance, cid.synced)));
					break;
				case UPDATE_PATH:
					pid = GetPathID(cid.pathID);
					if (pid >= 0)
						UpdatePath(ST_CALL cid.owner, pid);
					break;
				case PATH_UPDATED:
					pid = GetPathID(cid.pathID);
					if (pid >= 0)
						pathUpdates[cid.pathID].push_back(PathUpdateData(PATH_UPDATED, PathUpdated(ST_CALL pid)));
					break;
					/*			case TERRAIN_CHANGE:
					TerrainChange(ST_CALL cid.cx1, cid.cz1, cid.cx2, cid.cz2);
					break;*/
				case DELETE_PATH:
					pid = GetPathID(cid.pathID);
					if (pid >= 0) {
						DeletePath(ST_CALL pid);
						pathUpdates[cid.pathID].push_back(PathUpdateData(DELETE_PATH));
					}
					newPathCache.erase(cid.pathID);
					break;
				case PATH_NONE:
					Update(ST_CALL 0);
					break;
				default:
					LOG_L(L_ERROR,"Invalid path request %d", cid.type);
			}
#if defined(USE_DESYNC_DETECTOR) && defined(MT_DESYNC_DETECTION)
			if (cid.ownerid >= 0)
				Threading::SetThreadCurrentObjectID(-1);
#endif
		}
	}
}


void IPathManager::SynchronizeThread() {
	ASSERT_SINGLETHREADED_SIM();
	if (pathBatchThread == NULL)
		return;

	SCOPED_TIMER("IPathManager::SynchronizeThread"); // lots of waiting here means the asynchronous mechanism is ineffient

	boost::mutex::scoped_lock preqLock(preqMutex);
	if (!wait) {
		wait = true;
		cond.wait(preqLock);
	}
	for (std::map<unsigned int, PathData>::iterator i = newPathInfos.begin(); i != newPathInfos.end(); ++i) {
		pathInfos[i->first] = i->second;
	}
	newPathInfos.clear();

	for (std::map<unsigned int, std::vector<PathUpdateData> >::iterator i  = pathUpdates.begin(); i != pathUpdates.end(); ++i) {
		for (std::vector<PathUpdateData>::iterator v  = i->second.begin(); v != i->second.end(); ++v) {
			PathUpdateData &u = *v;
			switch(u.type) {
				case REQUEST_PATH:
					pathInfos[i->first].pathID = u.pathID;
					break;
				case CUR_WAYPOINT:
					pathInfos[i->first].curWayPoint = u.wayPoint;
					break;
				case NEXT_WAYPOINT:
					pathInfos[i->first].nextWayPoint = u.wayPoint;
					break;
				case PATH_UPDATED:
					pathInfos[i->first].updated = u.updated;
					break;
				case DELETE_PATH:
					pathInfos.erase(i->first);
					break;
				default:
					LOG_L(L_ERROR,"Invalid path update %d", u.type);
			}
		}
	}

	newPathCache.clear();
	pathUpdates.clear();
}
