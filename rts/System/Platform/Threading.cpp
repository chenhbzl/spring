/* This file is part of the Spring engine (GPL v2 or later), see LICENSE.html */

#include "lib/gml/gml_base.h"
#include "lib/gml/gmlmut.h"
#include "Threading.h"
#include "Game/GameController.h"
#include "System/bitops.h"
#include "System/OpenMP_cond.h"
#include "System/Config/ConfigHandler.h"
#include "System/Log/ILog.h"
#include "System/Platform/CrashHandler.h"
#include "System/Sync/FPUCheck.h"

#include <boost/version.hpp>
#include <boost/thread.hpp>
#include <boost/cstdint.hpp>
#if defined(__APPLE__)
#elif defined(WIN32)
	#include <windows.h>
#else
	#if defined(__USE_GNU)
		#include <sys/prctl.h>
	#endif
	#include <sched.h>
#endif

extern void streflop_init_omp();

namespace Threading {
	unsigned simThreadCount = GML::NumMainSimThreads();

	static Error* threadError = NULL;
	static bool haveMainThreadID = false;
	static boost::thread::id mainThreadID;
	static NativeThreadId nativeMainThreadID;
#ifdef USE_GML
	static int const noThreadID = -1;
	static int simThreadID      = noThreadID;
	static int batchThreadID    = noThreadID;
#else
	static boost::thread::id noThreadID;
	static boost::thread::id simThreadID;
	static boost::thread::id batchThreadID;
#endif	

#if MULTITHREADED_SIM
	bool multiThreadedSim = false;
	int threadCurrentUnitIDs[2 * GML_MAX_NUM_THREADS + 10];
#endif
#if THREADED_PATH
	bool threadedPath = false;
#endif

void MultiThreadSimErrorFunc() { LOG_L(L_ERROR, "Non-threadsafe sim code reached from multithreaded context"); CrashHandler::OutputStacktrace(); }
void NonThreadedPathErrorFunc() { LOG_L(L_ERROR, "Non-threadsafe path code reached from threaded context"); CrashHandler::OutputStacktrace(); }
void ThreadNotUnitOwnerErrorFunc() { LOG_L(L_ERROR, "Illegal attempt to modify a unit not owned by the current thread"); CrashHandler::OutputStacktrace(); }

#if defined(__APPLE__)
#elif defined(WIN32)
	static DWORD cpusSystem = 0;
#else
	static cpu_set_t cpusSystem;
#endif

	void DetectCores()
	{
		static bool inited = false;
		if (inited)
			return;
		
	#if defined(__APPLE__)
		// no-op

	#elif defined(WIN32)
		// Get the available cores
		DWORD curMask;
		GetProcessAffinityMask(GetCurrentProcess(), &curMask, &cpusSystem);

	#else
		// Get the available cores
		CPU_ZERO(&cpusSystem);
		sched_getaffinity(0, sizeof(cpu_set_t), &cpusSystem);
	#endif

		inited = true;
	}


	boost::uint32_t SetAffinity(boost::uint32_t cores_bitmask, bool hard)
	{
		if (cores_bitmask == 0) {
			return ~0;
		}

	#if defined(__APPLE__)
		// no-op

	#elif defined(WIN32)
		// Create mask
		DWORD_PTR cpusWanted = (cores_bitmask & cpusSystem);

		// Set the affinity
		HANDLE thread = GetCurrentThread();
		DWORD_PTR result = 0;
		if (hard) {
			result = SetThreadAffinityMask(thread, cpusWanted);
		} else {
			result = SetThreadIdealProcessor(thread, (DWORD)cpusWanted);
		}

		// Return final mask
		return (result > 0) ? (boost::uint32_t)cpusWanted : 0;
	#else
		// Create mask
		cpu_set_t cpusWanted; CPU_ZERO(&cpusWanted);
		int numCpus = std::min(CPU_COUNT(&cpusSystem), 32); // w/o the min(.., 32) `(1 << n)` could overflow!
		for (int n = numCpus - 1; n >= 0; --n) {
			if ((cores_bitmask & (1 << n)) != 0) {
				CPU_SET(n, &cpusWanted);
			}
		}
		CPU_AND(&cpusWanted, &cpusWanted, &cpusSystem);

		// Set the affinity
		int result = sched_setaffinity(0, sizeof(cpu_set_t), &cpusWanted);

		// Return final mask
		uint32_t finalMask = 0;
		for (int n = numCpus - 1; n >= 0; --n) {
			if (CPU_ISSET(n, &cpusWanted)) {
				finalMask |= (1 << n);
			}
		}
		return (result == 0) ? finalMask : 0;
	#endif
	}

	void SetAffinityHelper(const char *threadName, boost::uint32_t affinity) {
		if (affinity == 0)
			affinity = GetDefaultAffinity(threadName);
		const boost::uint32_t cpuMask  = Threading::SetAffinity(affinity);
		if (cpuMask == ~0) {
			LOG("[Threading] %s thread CPU affinity not set", threadName);
		}
		else if (cpuMask != affinity) {
			LOG("[Threading] %s thread CPU affinity mask set: %d (config is %d)", threadName, cpuMask, affinity);
		}
		else if (cpuMask == 0) {
			LOG_L(L_ERROR, "[Threading] %s thread CPU affinity mask failed: %d", threadName, affinity);
		}
		else {
			LOG("[Threading] %s thread CPU affinity mask set: %d", threadName, cpuMask);
		}
	}

	unsigned GetAvailableCores()
	{
		// auto-detect number of system threads
	#if (BOOST_VERSION >= 103500)
		return boost::thread::hardware_concurrency();
	#elif defined(USE_GML)
		return gmlCPUCount();
	#else
		return 1;
	#endif
	}


	boost::uint32_t GetAvailableCoresMask()
	{
		boost::uint32_t systemCores = 0;
	#if defined(__APPLE__)
		// no-op
		systemCores = ~0;

	#elif defined(WIN32)
		// Create mask
		systemCores = cpusSystem;

	#else
		// Create mask
		int numCpus = std::min(CPU_COUNT(&cpusSystem), 32); // w/o the min(.., 32) `(1 << n)` could overflow!
		for (int n = numCpus - 1; n >= 0; --n) {
			if (CPU_ISSET(n, &cpusSystem)) {
				systemCores |= (1 << n);
			}
		}
	#endif

		return systemCores;
	}


	bool OMPInited = false;

	#ifdef _OPENMP
	static boost::uint32_t GetOpenMPCpuCore(int index, boost::uint32_t availCores, boost::uint32_t avoidCores)
	{
		boost::uint32_t ompCore = 1;

		// find an unused core
		{
			while ((ompCore) && !(ompCore & availCores))
				ompCore <<= 1;
			int n = index;
			// select n'th bit in availCores
			while (n--)
				do ompCore <<= 1; while ((ompCore) && !(ompCore & availCores));
		}

		// select one of the mainthread cores if none found
		if (ompCore == 0) {
			/*int cntBits =*/ count_bits_set(avoidCores);
			ompCore = 1;
			while ((ompCore) && !(ompCore & avoidCores))
				ompCore <<= 1;
			int n = index;
			// select n'th bit in avoidCores
			while (n--)
				do ompCore <<= 1; while ((ompCore) && !(ompCore & avoidCores));
		}

		// fallback use all
		if (ompCore == 0) {
			ompCore = ~0;
		}

		return ompCore;
	}
	#endif

	static void streflop_omp() {
	#ifdef STREFLOP_SSE
		::streflop_init_omp();
	#endif
	}

	void InitOMP(bool useOMP) {
		if (OMPInited) {
			LOG_L(L_ERROR, "InitOMP: OMP already initialized!");
			return;
		}
		OMPInited = true;
	#ifdef _OPENMP
		if (useOMP) {
			boost::uint32_t systemCores   = Threading::GetAvailableCoresMask();
			boost::uint32_t mainAffinity  = systemCores & configHandler->GetUnsigned("SetCoreAffinity");
			boost::uint32_t ompAvailCores = systemCores & ~mainAffinity;

			// For latency reasons our openmp threads yield rarely and so eat a lot cputime with idleing.
			// So it's better we always leave 1 core free for our other threads, drivers & OS
			if (omp_get_max_threads() > 2)
				omp_set_num_threads(omp_get_max_threads() - 1); 

			streflop_omp();

			// omp threads
			boost::uint32_t ompCores = 0;
			Threading::OMPCheck();
			#pragma omp parallel reduction(|:ompCores)
			{
				int i = omp_get_thread_num();
				if (i != 0) { // 0 is the source thread
					Threading::SetThreadName(IntToString(i, "omp%i"));
					//boost::uint32_t ompCore = 1 << i;
					boost::uint32_t ompCore = GetOpenMPCpuCore(i - 1, ompAvailCores, mainAffinity);
					Threading::SetAffinity(ompCore);
					ompCores |= ompCore;
				}
			}

			// mainthread
			boost::uint32_t nonOmpCores = ~ompCores;
			if (mainAffinity == 0) mainAffinity = systemCores;
			Threading::SetAffinityHelper("Main", mainAffinity & nonOmpCores);
		} else
#endif
		{
			Threading::SetAffinityHelper("Main", configHandler->GetUnsigned("SetCoreAffinity"));
		}
	}

	void OMPError() {
		LOG_L(L_ERROR, "OMPCheck: Attempt to use OMP before initialization");
		CrashHandler::OutputStacktrace();
	}

	void SetThreadScheduler()
	{
	#if defined(__APPLE__)
		// no-op

	#elif defined(WIN32)
		//TODO add MMCSS (http://msdn.microsoft.com/en-us/library/ms684247.aspx)
		//Note: only available with mingw64!!!

	#else
		if (!GML::Enabled()) { // with GML mainthread yields a lot, so SCHED_BATCH with its longer wakup times is counter-productive then
			if (GetAvailableCores() > 1) {
				// Change os scheduler for this process.
				// This way the kernel knows that we are a CPU-intensive task
				// and won't randomly move us across the cores and tries
				// to maximize the runtime (_slower_ wakeups, less yields)
				//Note:
				// It _may_ be possible that this has negative impact in case
				// threads are waiting for mutexes (-> less yields).
				int policy;
				struct sched_param param;
				pthread_getschedparam(Threading::GetCurrentThread(), &policy, &param);
				pthread_setschedparam(Threading::GetCurrentThread(), SCHED_BATCH, &param);
			}
		}
	#endif
	}

	unsigned GetPhysicalCores() {
		unsigned regs[4];
		memset(regs, 0, sizeof(regs));
		regs[0] = 0;
		proc::ExecCPUID(&regs[0], &regs[1], &regs[2], &regs[3]);
		char vendor[12];
		((unsigned *)vendor)[0] = regs[1];
		((unsigned *)vendor)[1] = regs[3];
		((unsigned *)vendor)[2] = regs[2];
		std::string cpuVendor = std::string(vendor, 12);

		unsigned threads = boost::thread::hardware_concurrency();
		if (threads > 1 && cpuVendor == "GenuineIntel") {
			memset(regs, 0, sizeof(regs));
			regs[0] = 1;
			proc::ExecCPUID(&regs[0], &regs[1], &regs[2], &regs[3]);
			if ((regs[3] >> 28) & 1) {
				// this is not entirely correct, HT can be disabled in BIOS or
				// there could be more than 2 logical cores per physical core
				return threads / 2;
			}
		}
		return threads;
	}

	unsigned GetDefaultAffinity(const char *threadName) {
		if ((!GML::SimEnabled() && configHandler->GetInt("SetCoreAffinityAuto") <= 0) ||
			// affinity is really important with the large number of threads MT uses, so enable by default
			(GML::SimEnabled() && configHandler->GetInt("SetCoreAffinityAuto") < 0) ||
			configHandler->GetUnsigned("SetCoreAffinity") > 1 ||
			configHandler->GetUnsigned("SetCoreAffinitySim") != 0 ||
			configHandler->GetUnsigned("SetCoreAffinitySimMT") != 0 ||
			configHandler->GetUnsigned("SetCoreAffinityRenderMT") != 0 ||
			configHandler->GetUnsigned("SetCoreAffinityPath") != 0)
			return 0;
		unsigned lcpu = GetAvailableCores();
		unsigned pcpu = GetPhysicalCores();
		unsigned cpuq = std::max((unsigned)1, (pcpu > 0) ? lcpu / pcpu : 1);
		if (lcpu <= 1)
			return 0;
		unsigned allmask = 0;
		for (int i = 0; i < lcpu; ++i)
			allmask |= (1 << i);
		unsigned main = 0;
		bool simcore = (pcpu >= 2);
		bool pathcore = (pcpu >= 6);
		unsigned sim = simcore ? cpuq : 1;
		unsigned path = pathcore ? (2 * cpuq) : sim;
		unsigned mainmask = 1 << main;
		unsigned simmask = 1 << sim;
		unsigned pathmask = 1 << path;
		if (main / cpuq != sim / cpuq) {
			for (int i = 1; i < cpuq; ++i) {
				mainmask |= (1 << (main + i));
				simmask |= (1 << (sim + i));
				pathmask |= (1 << (path + i));
			}
		}
#ifdef HEADLESS
		allmask &= GML::SimEnabled() ? ~(simmask | pathmask) : ~mainmask;
#else
		allmask &= GML::SimEnabled() ? ~(mainmask | simmask | pathmask) : ~mainmask;
#endif

		if (StringCaseCmp(threadName, "Main"))
			return (1 << main);
		else if (StringCaseCmp(threadName, "Sim"))
			return (1 << sim);
		else if (StringCaseCmp(threadName, "SimMT", 5))
			return allmask;
		else if (StringCaseCmp(threadName, "RenderMT", 8))
			return allmask;
		else if (StringCaseCmp(threadName, "Path"))
			return pathcore ? (1 << path) : allmask;
		else
			LOG_L(L_ERROR, "GetDefaultAffinity: Unknown thread name %s", threadName);
		return 0;
	}

	NativeThreadHandle GetCurrentThread()
	{
	#ifdef WIN32
		// we need to use this cause GetCurrentThread() just returns a pseudo handle,
		// which returns in all threads the current active one, so we need to translate it
		// with DuplicateHandle to an absolute handle valid in our watchdog thread
		NativeThreadHandle hThread;
		::DuplicateHandle(::GetCurrentProcess(), ::GetCurrentThread(), ::GetCurrentProcess(), &hThread, 0, TRUE, DUPLICATE_SAME_ACCESS);
		return hThread;
	#else
		return pthread_self();
	#endif
	}


	NativeThreadId GetCurrentThreadId()
	{
	#ifdef WIN32
		return ::GetCurrentThreadId();
	#else
		return pthread_self();
	#endif
	}



	void SetMainThread()
	{
		if (!haveMainThreadID) {
			haveMainThreadID = true;
			mainThreadID = boost::this_thread::get_id();
			nativeMainThreadID = Threading::GetCurrentThreadId();
		}
	}

	bool IsMainThread()
	{
		return (boost::this_thread::get_id() == Threading::mainThreadID);
	}

	bool IsMainThread(NativeThreadId threadID)
	{
		return NativeThreadIdsEqual(threadID, Threading::nativeMainThreadID);
	}



	void SetSimThread(bool set) {
	#ifdef USE_GML // GML::ThreadNumber() is likely to be much faster than boost::this_thread::get_id()
		batchThreadID = simThreadID = set ? GML::ThreadNumber() : noThreadID;
	#else
		batchThreadID = simThreadID = set ? boost::this_thread::get_id() : noThreadID;
	#endif
	}
	bool IsSimThread() {
	#ifdef USE_GML
		return GML::ThreadNumber() == simThreadID;
	#else
		return boost::this_thread::get_id() == simThreadID;
	#endif
	}

	bool UpdateGameController(CGameController* ac) {
		GML_MSTMUTEX_LOCK(sim, 1); // UpdateGameController

		SetSimThread(true);
		bool ret = ac->Update();
		SetSimThread(false);
		return ret;
	}

	void SetBatchThread(bool set) {
	#ifdef USE_GML // GML::ThreadNumber() is likely to be much faster than boost::this_thread::get_id()
		batchThreadID = set ? GML::ThreadNumber() : noThreadID;
	#else
		batchThreadID = set ? boost::this_thread::get_id() : noThreadID;
	#endif
	}
	bool IsBatchThread() {
	#ifdef USE_GML
		return GML::ThreadNumber() == batchThreadID;
	#else
		return boost::this_thread::get_id() == batchThreadID;
	#endif
	}


	void SetThreadName(std::string newname)
	{
	#if defined(__USE_GNU) && !defined(WIN32)
		//alternative: pthread_setname_np(pthread_self(), newname.c_str());
		prctl(PR_SET_NAME, newname.c_str(), 0, 0, 0);
	#endif
	}


	void SetThreadError(const Error& err)
	{
		threadError = new Error(err); //FIXME memory leak!
	}

	Error* GetThreadError()
	{
		return threadError;
	}
};
