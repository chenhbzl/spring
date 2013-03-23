/* This file is part of the Spring engine (GPL v2 or later), see LICENSE.html */

#include "SimThreadPool.h"
#include "System/Config/ConfigHandler.h"
#include "System/Log/ILog.h"
#include "Sim/Misc/ModInfo.h"
#include "lib/streflop/streflop_cond.h"

CSimThreadPool* simThreadPool = NULL;

CSimThreadPool::CSimThreadPool() :
	stopThread(false),
	atomicCount(-1),
	simBarrier(NULL),
	InitThreadFunc(NULL),
	ThreadFunc(NULL),
	simNumExtraThreads(0)
{
	memset(simThreads, 0, sizeof(simThreads));
	int numThreads = std::max(0, configHandler->GetInt("SimThreadCount"));
	if (numThreads == 0) {
		int lcpu = Threading::GetAvailableCores();
		int pcpu = Threading::GetPhysicalCores();
		// deduct all logical cores dedicated to the rendering/sim main threads
		numThreads = std::max((int)GML::NumMainSimThreads(), lcpu - GML::NumMainThreads() * (int)(lcpu / pcpu) + GML::NumMainSimThreads()); // add the main sim thread
		if (pcpu >= 6)
			numThreads -= (int)(lcpu / pcpu);
	}
	simNumExtraThreads = (!modInfo.multiThreadSim) ? 0 : std::max(0, numThreads - GML::NumMainSimThreads());
	Threading::SimThreadCount(simNumExtraThreads + GML::NumMainSimThreads() + (modInfo.asyncPathFinder ? 1 : 0));
	if (simNumExtraThreads > 0)
		LOG("[Threading] Simulation multithreading is enabled with %d threads", simNumExtraThreads + GML::NumMainSimThreads());
	else
		LOG("[Threading] Simulation multithreading is disabled");
	simBarrier = new boost::barrier(simNumExtraThreads + 1);
	for (unsigned int i = 1; i <= simNumExtraThreads; i++) {
		simThreads[i] = new boost::thread(boost::bind(&CSimThreadPool::Execute, this, (void(*)(bool))NULL, (void(*)(bool))NULL, i));
	}
}

void CSimThreadPool::Execute(void (* tf)(bool), void (* itf)(bool), int i) {
	if (!modInfo.multiThreadSim) {
		(*ThreadFunc)(false);
		return;
	}
	if (simNumExtraThreads > 0) {
		if (i == 0) {
			InitThreadFunc = itf;
			ThreadFunc = tf;
		} else {
			streflop::streflop_init<streflop::Simple>();
			GML::ThreadNumber(GML_MAX_NUM_THREADS + i);
			char threadName[32];
			sprintf(threadName,"SimMT%d", i);
			Threading::SetAffinityHelper(threadName, configHandler->GetUnsigned("SetCoreAffinitySimMT"));
		}
		do {
			if (i == 0) {
				atomicCount %= -1;
				if (InitThreadFunc != NULL)
					(*InitThreadFunc)(true);
			}
			simBarrier->wait();
			if (stopThread)
				break;
			Threading::SetThreadCurrentObjectID(-1);
			(*ThreadFunc)(true);
			Threading::SetThreadCurrentObjectID(-1);
			simBarrier->wait();
		} while (i > 0);
	}
	else {
		if (itf != NULL)
			(*itf)(false);
		Threading::SetThreadCurrentObjectID(-1);
		(*tf)(false);
		Threading::SetThreadCurrentObjectID(-1);
	}
}

CSimThreadPool::~CSimThreadPool() {
	stopThread = true;
	simBarrier->wait();
	for (unsigned int i = 1; i <= simNumExtraThreads; i++) {
		simThreads[i]->join();
		delete simThreads[i];
	}
	delete simBarrier;
}
