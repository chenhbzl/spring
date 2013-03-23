/* This file is part of the Spring engine (GPL v2 or later), see LICENSE.html */

#ifndef DESYNCDETECTOR_H
#define DESYNCDETECTOR_H

#include "Sim/Misc/GlobalConstants.h"
#include <stdio.h>

//#define USE_DESYNC_DETECTOR
//#define MT_DESYNC_DETECTION // detects desync per object ID

// This is an ultra-lightweight desync detector, that detects the first call to
// CSyncChecker::Sync that generates a different checksum compared to a previous run.
// It is particularly useful for finding desyncs caused by multithreaded simulation

namespace DesyncDetector {
#ifdef USE_DESYNC_DETECTOR
#ifndef USE_GML
#error "Desync detector requires GML"
#endif
	const int MAX_DESYNC_IDS = 2 * MAX_UNITS;
	extern bool desyncDetectorActive;
	extern void DesyncTriggerFunc();
	extern FILE* desyncWriteFile;
	extern FILE* desyncReadFile;
	extern FILE* desyncFiles[MAX_DESYNC_IDS];
	extern char* desyncFileDir;
	extern char* desyncErrorFileName;
	extern int desyncFilePos[MAX_DESYNC_IDS];
	extern unsigned g_checksums[MAX_DESYNC_IDS];

	int GetThreadObjectID();
	bool GetMultiThreadSim();
	bool IsPathThread();
	inline bool Synced() {
#ifdef MT_DESYNC_DETECTION
		return !IsPathThread() || GetThreadObjectID() >= 0;
#else
		return !GetMultiThreadSim();
#endif
	}
	inline void NewFrame() {
#ifdef MT_DESYNC_DETECTION
		for (int i = 0; i < MAX_DESYNC_IDS; ++i) {
			g_checksums[i] = 0xfade1eaf;
		}
#endif
	}

	inline unsigned int& GetChecksum(unsigned int& checksum) {
#ifdef MT_DESYNC_DETECTION
		if (GetMultiThreadSim()) {
			int oid = GetThreadObjectID();
			while (oid < 0); // error! (infinite loop)
			return g_checksums[oid];
		}
#endif
		return checksum;
	}

	inline void StartPlaying() { desyncDetectorActive = true; }

	inline FILE *GetDesyncReadFile(bool close) {
		if (!GetMultiThreadSim())
			return desyncReadFile;
		int oid = GetThreadObjectID();
		FILE *desyncReadFileX = desyncFiles[oid];
		if (close) {
			if (desyncReadFileX != NULL) {
				desyncFilePos[oid] = ftell(desyncReadFileX);
				fclose(desyncReadFileX);
				desyncFiles[oid] = NULL;
			}
			return NULL;
		}
		if (desyncReadFileX != NULL)
			return desyncReadFileX;
		char dfName[20];
		sprintf(dfName, "%s\\%d.txt", desyncFileDir, oid);
		desyncReadFileX = fopen(dfName, "rb");
		if (desyncReadFileX == NULL || fseek(desyncReadFileX, desyncFilePos[oid], SEEK_SET) != 0)
			DesyncTriggerFunc();
		desyncFiles[oid] = desyncReadFileX;
		return desyncReadFileX;
	}
	inline FILE *GetDesyncWriteFile(bool close) {
		if (!GetMultiThreadSim())
			return desyncWriteFile;
		int oid = GetThreadObjectID();
		FILE *desyncWriteFileX = desyncFiles[oid];
		if (close) {
			if (desyncWriteFileX != NULL) {
				fclose(desyncWriteFileX);
				desyncFiles[oid] = NULL;
			}
			return NULL;
		}
		if (desyncWriteFileX != NULL)
			return desyncWriteFileX;
		char dfName[20];
		sprintf(dfName, "%s\\%d.txt", desyncFileDir, oid);
		desyncWriteFileX = fopen(dfName, "ab");
		if (desyncWriteFileX == NULL)
			DesyncTriggerFunc();
		desyncFiles[oid] = desyncWriteFileX;
		return desyncWriteFileX;
	}
	inline void Sync(const void* p, unsigned size, unsigned int checkSum) {
		if(desyncDetectorActive) {
			if (desyncReadFile != NULL) {
				FILE *desyncReadFile = GetDesyncReadFile(false);
				int sz, chk;
				if(fread(&sz, sizeof(sz), 1, desyncReadFile) && fread(&chk, sizeof(chk), 1, desyncReadFile)) {
					if (checkSum != chk) {
						FILE *desyncErrorFile = fopen(desyncErrorFileName,"wb");
						if (desyncErrorFile != NULL) {
							fprintf(desyncErrorFile, "THIS GAME size: %d   checksum: %d\r\nData: ", size, checkSum);
							for(int i = 0; i < size; ++i)
								fprintf(desyncErrorFile, "0x%x ", (unsigned int)((unsigned char *)p)[i]);
							fprintf(desyncErrorFile, "\r\n\r\nSYNC FILE size: %d   checksum: %d\r\nData: ", sz, chk);
							for(int i = 0; i < sz; ++i)
								fprintf(desyncErrorFile, "0x%x ", (unsigned int)fgetc(desyncReadFile));
							fclose(desyncErrorFile);
						}
						DesyncTriggerFunc();
					}
					else {
						for(int i = 0; i < sz; ++i) {
							fgetc(desyncReadFile);
						}
					}
				} else {
					DesyncTriggerFunc();
				}
			} else if(desyncWriteFile != NULL) {
				FILE *desyncWriteFile = GetDesyncWriteFile(false);
				fwrite(&size, sizeof(size), 1, desyncWriteFile);
				fwrite(&checkSum, sizeof(checkSum), 1, desyncWriteFile);
				for(int i = 0; i<size; ++i) {
					fputc(((char *)p)[i], desyncWriteFile);
				}
			}
		}
	}
	inline void Close() {
		if(desyncDetectorActive) {
			if (desyncReadFile != NULL) {
				GetDesyncReadFile(true);
			} else if(desyncWriteFile != NULL) {
				GetDesyncWriteFile(true);
			}
		}
	}

#else
	inline void StartPlaying() {}
	inline void Sync(const void* p, unsigned size, unsigned int checkSum) {}
	inline void NewFrame() {}
	inline void Close() {}
#endif
}

#endif // DESYNCDETECTOR_H
