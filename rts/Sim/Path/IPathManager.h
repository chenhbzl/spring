/* This file is part of the Spring engine (GPL v2 or later), see LICENSE.html */

#ifndef I_PATH_MANAGER_H
#define I_PATH_MANAGER_H

#include <boost/cstdint.hpp> /* Replace with <stdint.h> if appropriate */

#include "PFSTypes.h"
#include "System/Vec2.h"
#include "System/float3.h"
#include "System/Platform/Threading.h"
#include <boost/thread/mutex.hpp>
#include <boost/thread/condition.hpp>
#include "System/Sync/DesyncDetector.h"
#include "System/TimeProfiler.h"

#if defined(USE_DESYNC_DETECTOR) && defined(MT_DESYNC_DETECTION)
#include "Sim/Objects/SolidObject.h"
#define OWNERID(x) , ownerid(x)
#else
#define OWNERID(x)
#endif

enum ThreadParam { THREAD_DUMMY };

#if THREADED_PATH
#define ST_FUNC ThreadParam dummy,
#define ST_CALL THREAD_DUMMY,
#define MT_WRAP
#else
#define ST_FUNC
#define ST_CALL
#define MT_WRAP ThreadParam dummy,
#endif

struct MoveDef;
class CSolidObject;

class IPathManager {
public:
	static IPathManager* GetInstance(unsigned int type, bool async);

	IPathManager();

	// MSVC8 for some reason does not compile unless this is in the header
	virtual ~IPathManager() {
		if (pathBatchThread != NULL) {
			{
				boost::mutex::scoped_lock preqLock(preqMutex);
				stopThread = true;
				if (wait) {
					wait = false;
					cond.notify_one();
				}
			}
			pathBatchThread->join();
			pathBatchThread = NULL;
		}
	}

	virtual void MergePathCaches() = 0;

	virtual unsigned int GetPathFinderType() const = 0;
	virtual boost::uint32_t GetPathCheckSum() const { return 0; }

	enum PathRequestType { PATH_NONE, REQUEST_PATH, NEXT_WAYPOINT, DELETE_PATH, UPDATE_PATH, TERRAIN_CHANGE, PATH_UPDATED };

#if DEBUG_THREADED_PATH
	struct ScopedDisableThreadingDummy {};
	#define ScopedDisableThreading ScopedDisableThreadingReal
#endif
	struct ScopedDisableThreading {
#if THREADED_PATH
		bool oldThreading;
		ScopedDisableThreading(bool sync = true) : oldThreading(Threading::threadedPath) { ASSERT_SINGLETHREADED_SIM(); extern IPathManager* pathManager; if (sync) pathManager->SynchronizeThread(); Threading::threadedPath = false; }
		~ScopedDisableThreading() { Threading::threadedPath = oldThreading; }
#else
		ScopedDisableThreading(bool sync = true) {}
#endif
	};
#if DEBUG_THREADED_PATH
#undef ScopedDisableThreading
#define ScopedDisableThreading ScopedDisableThreadingDummy sdtdummy ## __LINE__; char str ## __LINE__[40], sdtdata ## __LINE__[sizeof(ScopedTimer)]; sprintf(str ## __LINE__, "ScopedDisableThreading @ %d", __LINE__); new (sdtdata ## __LINE__) ScopedTimer(str ## __LINE__); IPathManager::ScopedDisableThreadingReal sdt ## __LINE__; ((ScopedTimer *)sdtdata ## __LINE__)->~ScopedTimer(); IPathManager::ScopedDisableThreadingDummy 
#endif

	/**
	 * returns if a path was changed after RequestPath returned its pathID
	 * this can happen eg. if a PathManager reacts to TerrainChange events
	 * (by re-requesting affected paths without changing their ID's)
	 */

	virtual bool PathUpdated(ST_FUNC unsigned int pathID) { return false; }
	bool PathUpdated(MT_WRAP unsigned int pathID);

	virtual void Update(ST_FUNC int unused = 0) {}
	void Update(MT_WRAP int unused = 0);

	struct PathData {
		PathData() : pathID(-1), nextWayPoint(ZeroVector), updated(false), deleted(false) {}
		PathData(int pID, const float3& nwp) : pathID(pID), nextWayPoint(nwp), updated(false), deleted(false) {}
		int pathID;
		float3 nextWayPoint;
		bool updated;
		bool deleted;
	};

	PathData* GetPathDataRaw(int cid) {
		std::map<unsigned int, PathData>::iterator pit = pathInfos.find(cid);
		return (pit == pathInfos.end()) ? NULL : &(pit->second);
	}

	PathData* GetPathData(int cid) {
		PathData* p = GetPathDataRaw(cid);
		return ((p == NULL) || p->deleted) ? NULL : p;
	}

	PathData* GetNewPathData(int cid) {
		PathData* p = GetPathData(cid);
		if (p != NULL) return p;
		std::map<unsigned int, PathData>::iterator pit = newPathInfos.find(cid);
		return ((pit == newPathInfos.end()) || pit->second.deleted) ? NULL : &(pit->second);
	}

	bool IsFailPath(unsigned int pathID);

	struct PathOpData {
		PathOpData() : type(PATH_NONE), owner(NULL), pathID(-1), moveDef(NULL), startPos(ZeroVector), goalPos(ZeroVector), minDistance(0.0f), synced(false), numRetries(0) OWNERID(-1) {}
		PathOpData(PathRequestType tp, const CSolidObject* own, unsigned int pID, const MoveDef* md, const float3& sp, const float3& gp, float gr, bool sync):
		type(tp), owner(own), pathID(pID), moveDef(md), startPos(sp), goalPos(gp), goalRadius(gr), synced(sync), numRetries(0) OWNERID(own?own->id:-1) {}
		PathOpData(PathRequestType tp, const CSolidObject* own, unsigned int pID):
		type(tp), owner(own), pathID(pID), moveDef(NULL), startPos(ZeroVector), goalPos(ZeroVector), minDistance(0.0f), synced(false), numRetries(0) OWNERID(own?own->id:-1) {}
		PathOpData(PathRequestType tp, unsigned int pID):
		type(tp), owner(NULL), pathID(pID), moveDef(NULL), startPos(ZeroVector), goalPos(ZeroVector), minDistance(0.0f), synced(false), numRetries(0) OWNERID(-1) {}
		PathOpData(PathRequestType tp, const CSolidObject* own, unsigned int pID, int nRet, const float3& callPos, float minDist, bool sync):
		type(tp), owner(own), pathID(pID), moveDef(NULL), startPos(callPos), goalPos(ZeroVector), minDistance(minDist), synced(sync), numRetries(nRet) OWNERID(own?own->id:-1) {}
		PathOpData(PathRequestType tp, unsigned int x1, unsigned int z1, unsigned int x2, unsigned int z2):
		type(tp), cx1(x1), cz1(z1), moveDef(NULL), startPos(ZeroVector), goalPos(ZeroVector), cx2(x2), synced(false), cz2(z2) OWNERID(-1) {}

		PathRequestType type;
		union {
			const CSolidObject* owner;
			int cx1;
		};
		union {	int pathID, cz1; };
		const MoveDef* moveDef;
		float3 startPos, goalPos;
		union {
			float goalRadius, minDistance;
			int cx2;
		};
		bool synced;
		union { int numRetries, cz2; };
#if defined(USE_DESYNC_DETECTOR) && defined(MT_DESYNC_DETECTION)
		int ownerid;
#endif
	};

	struct PathUpdateData {
		PathUpdateData() : type(PATH_NONE), pathID(0), wayPoint(ZeroVector) {}
		PathUpdateData(PathRequestType t) : type(t), pathID(0), wayPoint(ZeroVector) {}
		PathUpdateData(PathRequestType t, unsigned int pID) : type(t), pathID(pID), wayPoint(ZeroVector) {}
		PathUpdateData(PathRequestType t, const float3& wP) : type(t), pathID(0), wayPoint(wP) {}
		PathUpdateData(PathRequestType t, const bool u) : type(t), updated(u), wayPoint(ZeroVector) {}
		PathRequestType type;
		union {
			unsigned int pathID;
			bool updated;
		};
		float3 wayPoint;
	};

	std::map<unsigned int, PathData> pathInfos;
	std::map<unsigned int, PathData> newPathInfos;
	std::vector<PathOpData> pathOps;
	std::map<unsigned int, std::vector<PathUpdateData> > pathUpdates;
	std::map<int, unsigned int> newPathCache;
	static boost::thread *pathBatchThread;

	virtual void UpdateFull(ST_FUNC int unused = 0) {}
	void UpdateFull(MT_WRAP int unused = 0) {
		ScopedDisableThreading sdt;
		return UpdateFull(ST_CALL unused);
	}

	virtual void UpdatePath(ST_FUNC const CSolidObject* owner, unsigned int pathID) {}
	void UpdatePath(MT_WRAP const CSolidObject* owner, unsigned int pathID);

	/**
	 * When a path is no longer used, call this function to release it from
	 * memory.
	 * @param pathID
	 *     The path-id returned by RequestPath.
	 */
	virtual void DeletePath(ST_FUNC unsigned int pathID) {}
	void DeletePath(MT_WRAP unsigned int pathID);

	/**
	 * Returns the next waypoint of the path.
	 *
	 * @param pathID
	 *     The path-id returned by RequestPath.
	 * @param callerPos
	 *     The current position of the user of the path.
	 *     This extra information is needed to keep the path connected to its
	 *     user.
	 * @param minDistance
	 *     Could be used to set a minimum required distance between callerPos
	 *     and the returned waypoint.
	 * @param numRetries
	 *     Dont set this, used internally
	 * @param owner
	 *     The unit the path is used for, or NULL.
	 * @param synced
	 *     Whether this evaluation has to run synced or unsynced.
	 *     If false, this call may not change any state of the path manager
	 *     that could alter paths requested in the future.
	 *     example: if (synced == false) turn of heat-mapping
	 * @return
	 *     the next waypoint of the path, or (-1,-1,-1) in case no new
	 *     waypoint could be found.
	 */
	virtual float3 NextWayPoint(
		ST_FUNC
		const CSolidObject* owner,
		unsigned int pathID,
		unsigned int numRetries,
		float3 callerPos,
		float radius,
		bool synced
	) { return ZeroVector; }
	float3 NextWayPoint(
		MT_WRAP
		const CSolidObject* owner,
		unsigned int pathID,
		unsigned int numRetries,
		float3 callerPos,
		float radius,
		bool synced
	);

	/**
	 * Returns all waypoints of a path. Different segments of a path might
	 * have different resolutions, or each segment might be represented at
	 * multiple different resolution levels. In the former case, a subset
	 * of waypoints (those belonging to i-th resolution path SEGMENTS) are
	 * stored between points[starts[i]] and points[starts[i + 1]], while in
	 * the latter case ALL waypoints (of the i-th resolution PATH) are stored
	 * between points[starts[i]] and points[starts[i + 1]]
	 *
	 * @param pathID
	 *     The path-id returned by RequestPath.
	 * @param points
	 *     The list of waypoints.
	 * @param starts
	 *     The list of starting indices for the different resolutions
	 */
	virtual void GetPathWayPoints(
		ST_FUNC
		unsigned int pathID,
		std::vector<float3>& points,
		std::vector<int>& starts
	) const {}
	void GetPathWayPoints(
		MT_WRAP
		unsigned int pathID,
		std::vector<float3>& points,
		std::vector<int>& starts
	);


	/**
	 * Generate a path from startPos to the target defined by
	 * (goalPos, goalRadius).
	 * If no complete path from startPos to goalPos could be found,
	 * then a path getting as "close" as possible to target is generated.
	 *
	 * @param moveDef
	 *     Defines the move details of the unit to use the path.
	 * @param startPos
	 *     The starting location of the requested path.
	 * @param goalPos
	 *     The center of the path goal area.
	 * @param goalRadius
	 *     Use goalRadius to define a goal area within any square that could
	 *     be accepted as path goal.
	 *     If a singular goal position is wanted, use goalRadius = 0.
	 * @param caller
	 *     The unit or feature the path will be used for.
	 * @param synced
	 *     Whether this evaluation has to run synced or unsynced.
	 *     If false, this call may not change any state of the path manager
	 *     that could alter paths requested in the future.
	 *     example: if (synced == false) turn off heat-mapping
	 * @return
	 *     a path-id >= 1 on success, 0 on failure
	 *     Failure means, no path getting "closer" to goalPos then startPos
	 *     could be found
	 */
	virtual unsigned int RequestPath(
		ST_FUNC
		CSolidObject* caller,
		const MoveDef* moveDef,
		const float3& startPos,
		const float3& goalPos,
		float goalRadius,
		bool synced
	) { return 0; }
	unsigned int RequestPath(
		MT_WRAP
		CSolidObject* caller,
		const MoveDef* moveDef,
		const float3& startPos,
		const float3& goalPos,
		float goalRadius,
		bool synced
	);

	int GetPathID(int cid);

	void AsynchronousThread();

	void SynchronizeThread();

	/**
	 * Whenever there are any changes in the terrain
	 * (examples: explosions, new buildings, etc.)
	 * this function will be called.
	 * @param x1
	 *     First corners X-axis value, defining the rectangular area
	 *     affected by the changes.
	 * @param z1
	 *     First corners Z-axis value, defining the rectangular area
	 *     affected by the changes.
	 * @param x2
	 *     Second corners X-axis value, defining the rectangular area
	 *     affected by the changes.
	 * @param z2
	 *     Second corners Z-axis value, defining the rectangular area
	 *     affected by the changes.
	 * @param type see @TerrainChangeTypes
	 */
	virtual void TerrainChange(ST_FUNC unsigned int x1, unsigned int z1, unsigned int x2, unsigned int z2, unsigned int type) {}
	void TerrainChange(MT_WRAP unsigned int x1, unsigned int z1, unsigned int x2, unsigned int z2, unsigned int type) {
		ScopedDisableThreading sdt;
		TerrainChange(ST_CALL x1, z1 ,x2, z2, type);
	}

	virtual bool SetNodeExtraCosts(ST_FUNC const float* costs, unsigned int sizex, unsigned int sizez, bool synced) { return false; }
	bool SetNodeExtraCosts(MT_WRAP const float* costs, unsigned int sizex, unsigned int sizez, bool synced) {
		ScopedDisableThreading sdt;
		return SetNodeExtraCosts(ST_CALL costs, sizex, sizez, synced);
	}

	virtual bool SetNodeExtraCost(ST_FUNC unsigned int x, unsigned int z, float cost, bool synced) { return false; }
	bool SetNodeExtraCost(MT_WRAP unsigned int x, unsigned int z, float cost, bool synced) {
		ScopedDisableThreading sdt;
		return SetNodeExtraCost(ST_CALL x, z, cost, synced);
	}

	virtual float GetNodeExtraCost(ST_FUNC unsigned int x, unsigned int z, bool synced) const { return 0.0f; }
	float GetNodeExtraCost(MT_WRAP unsigned int x, unsigned int z, bool synced) {
		ScopedDisableThreading sdt;
		return GetNodeExtraCost(ST_CALL x, z, synced);
	}

	virtual const float* GetNodeExtraCosts(ST_FUNC bool synced) const { return NULL; }
	const float* GetNodeExtraCosts(MT_WRAP bool synced) {
		ScopedDisableThreading sdt;
		return GetNodeExtraCosts(ST_CALL synced);
	}

	unsigned int pathRequestID;
	boost::mutex preqMutex;
	bool wait;
	boost::condition_variable cond;
	volatile bool stopThread;

	virtual int2 GetNumQueuedUpdates(ST_FUNC int unused = 0) const { return (int2(0, 0)); }
	int2 GetNumQueuedUpdates(MT_WRAP int unused = 0) const {
//		ScopedDisableThreading sdt;
		return GetNumQueuedUpdates(ST_CALL unused);
	}
};

extern IPathManager* pathManager;

#endif
