/* This file is part of the Spring engine (GPL v2 or later), see LICENSE.html */

#ifndef SIMTHREADPOOL_H
#define SIMTHREADPOOL_H
#include "System/Platform/Threading.h"
#include <boost/thread/barrier.hpp>
#include "lib/gml/gmlcnt.h"

class CSimThreadPool {
public:
	CSimThreadPool();
	virtual ~CSimThreadPool();
	void Execute(void (* tf)(bool) = NULL, void (* itf)(bool) = NULL, int i = 0);
	long NextIter() { return ++atomicCount; }

private:
	volatile bool stopThread;
	gmlCount atomicCount;
	boost::barrier* simBarrier;
	void (* volatile InitThreadFunc)(bool);
	void (* volatile ThreadFunc)(bool);
	int simNumExtraThreads;
	boost::thread* simThreads[GML_MAX_NUM_THREADS];
};

extern CSimThreadPool* simThreadPool;

#endif // SIMTHREADPOOL_H
