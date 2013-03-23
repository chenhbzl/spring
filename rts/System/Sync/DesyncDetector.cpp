/* This file is part of the Spring engine (GPL v2 or later), see LICENSE.html */

#include "DesyncDetector.h"
#include "System/Platform/Threading.h"

#ifdef USE_DESYNC_DETECTOR

namespace DesyncDetector {
#if defined(MT_DESYNC_DETECTION) && !defined(DEBUG_MULTITHREADED_SIM)
#error "MT_DESYNC_DETECTION requires DEBUG_MULTITHREADED_SIM"
#endif
	// Instructions: To start a new debugging session, first define USE_DESYNC_DETECTOR and compile.
	// Delete this sync data file if it already exists (you may want to set an absolute path here):
	char* syncDataFileName = "sync.txt";
	// Directory for per-object-id sync files (if MT_DESYNC_DETECTION)
	// Delete these files if they already exist (you may want to set an absolute path here):
	char* desyncFileDir = "sync";
	// Play a multiplayer game etc, and when it detects a desync let it run for a few more seconds
	// and then close spring. You will find that a new sync data file has been generated.
	// Take the demo from the desynced game and run it again. The game will hang when a desync
	// is detected, and you can then attach the debugger. If it did not desync, try to run with the
	// same demo again. Multithreading is unpredictable so it may very well need a few tries.
	char* desyncErrorFileName = "desync_err.txt";
	// The desync error file will contain a comparison of the input datas (and sizes) that
	// generated different checksums in CSyncChecker::Sync.

	int desyncFilePos[MAX_DESYNC_IDS] = {0};
	FILE* desyncFiles[MAX_DESYNC_IDS] = {NULL};
	FILE* desyncReadFile = fopen(syncDataFileName, "rb");
	FILE* desyncWriteFile = (desyncReadFile == NULL) ? fopen(syncDataFileName, "wb") : NULL;
	unsigned g_checksums[MAX_DESYNC_IDS] = { 0xfade1eaf };
	bool desyncDetectorActive = false;

	int GetThreadObjectID() { return Threading::GetThreadCurrentObjectID(); }
	bool IsPathThread() { return GML::ThreadNumber() == GML_MAX_NUM_THREADS; }
	bool GetMultiThreadSim() {
#ifdef MT_DESYNC_DETECTION
		return (!IsPathThread() && Threading::multiThreadedSim) || (IsPathThread() && GetThreadObjectID() >= 0);
#else
		return Threading::multiThreadedSim;
#endif
	}

	struct AutoCloseFiles {
		~AutoCloseFiles() {
			if (desyncReadFile != NULL)
				fclose(desyncReadFile);
			if (desyncWriteFile != NULL)
				fclose(desyncWriteFile);
		}
	};

	AutoCloseFiles acf;

	int dummyDesyncVar = 0;
	void DesyncTriggerFunc() {
		while(1) {
			++dummyDesyncVar; // put a breakpoint here
		}
	}
}

#endif