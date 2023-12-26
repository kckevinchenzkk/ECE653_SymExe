//
// Copyright(C) 1993-1996 Id Software, Inc.
// Copyright(C) 2005-2014 Simon Howard
//
// This program is free software; you can redistribute it and/or
// modify it under the terms of the GNU General Public License
// as published by the Free Software Foundation; either version 2
// of the License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// DESCRIPTION:
//	DOOM main program (D_DoomMain) and game loop (D_DoomLoop),
//	plus functions to determine game mode (shareware, registered),
//	parse command line parameters, configure game parameters (turbo),
//	and call the startup functions.
//
#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "config.h"
#include "deh_main.h"
#include "doomdef.h"
#include "doomstat.h"

#include "dstrings.h"
#include "sounds.h"

#include "d_iwad.h"

#include "s_sound.h"
#include "v_diskicon.h"
#include "v_video.h"
#include "w_main.h"
#include "w_wad.h"
#include "z_zone.h"

#include "f_finale.h"
#include "f_wipe.h"

#include "m_argv.h"
#include "m_config.h"
#include "m_controls.h"
#include "m_menu.h"
#include "m_misc.h"
#include "p_saveg.h"

#include "i_endoom.h"
#include "i_input.h"
#include "i_joystick.h"
#include "i_system.h"
#include "i_timer.h"
#include "i_video.h"

#include "g_game.h"

#include "am_map.h"
#include "hu_stuff.h"
#include "net_client.h"
#include "net_dedicated.h"
#include "net_query.h"
#include "st_stuff.h"
#include "wi_stuff.h"

#include "p_setup.h"
#include "r_local.h"
#include "statdump.h"

#include "d_main.h"
#include <errno.h>
#include <stdlib.h>
#include <err.h>
#include <unistd.h>

#include <setjmp.h>

#include <stdbool.h>
#include "d_loop.h"
#include "i_glob.h"
#include "am_map.h"
#include "r_main.h"
#include "r_sky.h"
#include "z_zone.h"
#include "p_spec.h"
/** jmp environment */
extern jmp_buf g_jmp_buf;

void I_Grace_Quit(void);
void D_IdentifyVersion(void);
void D_BindVariables(void);
void PrintDehackedBanners();

// should be defined during compilation
#ifndef FREEDOM_WAD
#define FREEDOM_WAD "freedom.wad"
#endif


char *iwadfile;
//
// D_DoomMain
//int main() {
//    const char *filename1 = "doom.wad";
//    bool isIWAD1 = D_IsIWADName(filename1);

    // Rest of your code
    // ...

//    return 0;
//}


static boolean D_AddFile(char *filename) {
  printf(" adding %s\n", filename);
//  W_ReleaseLumpNum(100000000);
//  W_ReadLump(1, NULL);
  wad_file_t *handle;
//  filename = "~freedoom2.wad";
  handle = W_AddFile(filename);
//  W_NumLumps();
  //  W_CacheLumpNum(100000000,1);
 // W_GetNumForName("ddd");
//  int i;
//  i = W_NumLumps();
//  W_LumpLength(1000000000);
 // W_IsIWADLump(NULL); 
  return handle != NULL;
}

//adding coverage


bool flag = false;
int flags = 0;
int count = 0;
bool isIWAD1 = false;
static char *result;
// D_DoomMain
const char *dirToCheck = "./SEED/";
const char *iwadToFind = "doom.wad";
const char *glob = "1";
//net_connect_data_t *my_connect_data;
//bool net_initialized;
//net_connect_data_t my_connect_data_instance = { 0 };
bool net_initialized = false;
// Definition of the initialization function
void initializeIsIWAD1(void) {
	char *filename1 = "~";
//	glob_t result;
//	flag = D_AddFile(filename1);	
	isIWAD1 = D_IsIWADName(filename1);
//    result = CheckDirectoryHasIWAD(dirToCheck, iwadToFind);
//	net_initialized = D_InitNetGame(my_connect_data);
//	handle1 = W_AddFile(filename1); 
//	NetUpdate();
//	TryRunTics();
	DEH_AutoLoadPatches(dirToCheck);
	flags = DEH_LoadFile(filename1);
	I_ShutdownJoystick();
        I_UpdateJoystick();
	I_UpdateSound();
        I_InitTimer();
	
	count = I_GetTime ();
        count = I_GetTimeMS ();
        I_Sleep(0);
        I_WaitVBL(0);
	I_DisplayFPSDots(flag);
	I_ShutdownGraphics();
	I_StartFrame();
	I_GetEvent();
	I_StartTic();
	I_UpdateNoBlit();
	I_FinishUpdate();
	count = I_GetPaletteIndex(0,0,0);
	I_InitWindowTitle();
	I_InitWindowIcon();
	count = SlopeDiv(1, 1);
	V_DrawDiskIcon();
	V_RestoreDiskBackground();
	AM_Ticker ();
	AM_Drawer ();
	
	R_SetViewSize(1,1);
	R_ClearSprites();
	R_ClearSprites ();
//	ST_Ticker ();
//	ST_refreshBackground();
	//count = Z_FreeMemory ();
	//	R_Init ();
	//count = W_NumLumps ();
	//column_t* column;
	//R_DrawMaskedColumn (column);
	//	R_InitTextureMapping ();
//	R_ExecuteSetViewSize ();
	//	UpdateMouseButtonState(1, true);
//	glob_t *I_StartMultiGlob(dirToCheck, flags,glob, &result);
}







static void LoadIwadDeh(void) {
  // The Freedoom IWADs have DEHACKED lumps that must be loaded.
  if (gamevariant == freedoom || gamevariant == freedm) {
    // Old versions of Freedoom (before 2014-09) did not have technically
    // valid DEHACKED lumps, so ignore errors and just continue if this
    // is an old IWAD.
    DEH_LoadLumpByName("DEHACKED", false, true);
  }
}

static void InitGameVersion(void) {
  gameversion = exe_doom_1_9;
  gamemission = doom2;
}

// global pointer to current fuzz data
extern const uint8_t *g_fuzz_data;
extern size_t g_fuzz_size;

/** Entry point for the fuzzer */
int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  // set longjmp. Execution goes here if the main program is about to exit
  // we trap this and return from the function instead
  initializeIsIWAD1();
  if (setjmp(g_jmp_buf)) {
    return 0;
  }  
  // -- make fuzz data globally accessible
  g_fuzz_data = data;
  g_fuzz_size = size;

  // prepare command line arguments (these might affect coverage)
  char *args[] = {"doom_fuzz",
                  // -- main WAD file. Additional WAD files are added later
                  "-iwad", FREEDOM_WAD,
                  // disable gui and music
                  "-nogui", "-nosound", "-nosfx", "-nomusic", "-nomusicpacks",
                  NULL};

  // Start initializing Doom subsystem
  myargc = (sizeof(args) / sizeof(args[0])) - 1;
  myargv = args;
  int numiwadlumps;

  DEH_printf("Z_Init: Init zone memory allocation daemon. \n");
  Z_Init();

  // Auto-detect the configuration dir.
  M_SetConfigDir(NULL);

  // init subsystems
  DEH_printf("V_Init: allocate screens.\n");
  V_Init();

  // Load configuration files before initialising other subsystems.
  DEH_printf("M_LoadDefaults: Load system defaults.\n");
  M_SetConfigFilenames("default.cfg", PROGRAM_PREFIX "doom.cfg");
  D_BindVariables();
  M_LoadDefaults();

  // Save configuration at exit.
  I_AtExit(M_SaveDefaults, false);

  // Find main IWAD file and load it.
  iwadfile = D_FindIWAD(IWAD_MASK_DOOM, &gamemission);

  modifiedgame = false;

  DEH_printf("W_Init: Init WADfiles.\n");
  D_AddFile(iwadfile);
  numiwadlumps = numlumps;
  W_CheckCorrectIWAD(doom);

  // Now that we've loaded the IWAD, we can figure out what gamemission
  // we're playing and which version of Vanilla Doom we need to emulate.
  D_IdentifyVersion();
  InitGameVersion();

  // Check which IWAD variant we are using.

  gamevariant = freedoom;
  //!
  // @category mod
  //
  // Disable automatic loading of Dehacked patches for certain
  // IWAD files.
  //
  if (!M_ParmExists("-nodeh")) {
    // Some IWADs have dehacked patches that need to be loaded for
    // them to be played properly.
    LoadIwadDeh();
  }

  DEH_ParseCommandLine();

  modifiedgame = true;

  // generate wad file from random data provided by libFuzzer
  // We have modified DooM so that any file with 'fuzz' in its name
  // is loaded from the global fuzz data g_fuzz_data
  char *filename = "fuzz.wad";

  DEH_printf("Fuzzing with file: %s\n", filename);
  if (!W_AddFile(filename)) {
    return 0;
  }

  // Generate the WAD hash table.  Speed things up a bit.
  W_GenerateHashTable();

  savegamedir = M_GetSaveGameDir(D_SaveGameIWADName(gamemission, gamevariant));

  // Check for -file in shareware
  if (modifiedgame && (gamevariant != freedoom)) {
    // These are the lumps that will be checked in IWAD,
    // if any one is not present, execution will be aborted.
    char name[23][8] = {"e2m1",   "e2m2",   "e2m3",    "e2m4",   "e2m5",
                        "e2m6",   "e2m7",   "e2m8",    "e2m9",   "e3m1",
                        "e3m3",   "e3m3",   "e3m4",    "e3m5",   "e3m6",
                        "e3m7",   "e3m8",   "e3m9",    "dphoof", "bfgga0",
                        "heada1", "cybra1", "spida1d1"};
    int i;

    // Check for fake IWAD with right name,
    // but w/o all the lumps of the registered version.
    if (gamemode == registered)
      for (i = 0; i < 23; i++)
        if (W_CheckNumForName(name[i]) < 0)
          I_Error(DEH_String("\nThis is not the registered version."));
  }

  if (W_CheckNumForName("SS_START") >= 0 || W_CheckNumForName("FF_END") >= 0) {
    I_PrintDivider();
    printf(" WARNING: The loaded WAD file contains modified sprites or\n"
           " floor textures.  You may want to use the '-merge' command\n"
           " line option instead of '-file'.\n");
  }

  I_PrintStartupBanner("Freedoom: Phase2");
  PrintDehackedBanners();

  DEH_printf("I_Init: Setting up machine state.\n");
  I_CheckIsScreensaver();
  I_InitTimer();
  I_InitJoystick();
  I_InitSound(true);
  I_InitMusic();

  timelimit = 0;

  DEH_printf("M_Init: Init miscellaneous info.\n");
  M_Init();

  DEH_printf("R_Init: Init DOOM refresh daemon - ");
  R_Init();

  DEH_printf("\nP_Init: Init Playloop state.\n");
  P_Init();

  DEH_printf("S_Init: Setting up sound.\n");
  S_Init(sfxVolume * 8, musicVolume * 8);

  G_InitNew(sk_medium, 1, 1);
  DEH_printf("Setup level completed\n");

  // we are done with fuzzing, gracefully exit for next run
  I_Grace_Quit();

  return 0;
}
