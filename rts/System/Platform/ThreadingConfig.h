/* This file is part of the Spring engine (GPL v2 or later), see LICENSE.html */

#ifndef THREADINGCONFIG_H
#define THREADINGCONFIG_H

#define MULTITHREADED_SIM 1 // more than one sim thread, very dangerous sync wise but with enormous performance potential
#define THREADED_PATH (1 || MULTITHREADED_SIM) // separate path manager thread running in asynchronous mode, offering a nice speedup
#define STABLE_UPDATE (MULTITHREADED_SIM || THREADED_PATH) // both these require stable data to avoid desyncs


namespace Threading {

#if MULTITHREADED_SIM
	extern bool multiThreadedSim;
#else
	const bool multiThreadedSim = 0; // speedup
#endif
#if THREADED_PATH
	extern bool threadedPath;
#else
	const bool threadedPath = 0; // speedup
#endif

}

#endif // THREADINGCONFIG_H