/*
 * init.c
 */

/*
 *  Copyright (C) 1997, 1998 Olivetti & Oracle Research Laboratory
 *
 *  This is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; either version 2 of the License, or
 *  (at your option) any later version.
 *
 *  This software is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this software; if not, write to the Free Software
 *  Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307,
 *  USA.
 */

/*

Copyright (c) 1993  X Consortium

Permission is hereby granted, free of charge, to any person obtaining
a copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be included
in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
IN NO EVENT SHALL THE X CONSORTIUM BE LIABLE FOR ANY CLAIM, DAMAGES OR
OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE,
ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
OTHER DEALINGS IN THE SOFTWARE.

Except as contained in this notice, the name of the X Consortium shall
not be used in advertising or otherwise to promote the sale, use or
other dealings in this Software without prior written authorization
from the X Consortium.

*/

/* Use ``#define CORBA'' to enable CORBA control interface */

#include <stdio.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <netdb.h>
#include "X11/X.h"
#define NEED_EVENTS
#include "X11/Xproto.h"
#include "X11/Xos.h"
#include "scrnintstr.h"
#include "servermd.h"
#define PSZ 8
#include "cfb.h"
#include "mibstore.h"
#include "colormapst.h"
#include "gcstruct.h"
#include "input.h"
#include "mipointer.h"
#include "dixstruct.h"
#include <errno.h>
#include <sys/param.h>
#include "dix.h"
#include "rfb.h"

#ifdef CORBA
#include <vncserverctrl.h>
#endif

#define RFB_DEFAULT_WIDTH  640
#define RFB_DEFAULT_HEIGHT 480
#define RFB_DEFAULT_DEPTH  8
#define RFB_DEFAULT_WHITEPIXEL 0
#define RFB_DEFAULT_BLACKPIXEL 1

rfbScreenInfo rfbScreen;
int rfbGCIndex;

static Bool initOutputCalled = FALSE;
static Bool noCursor = FALSE;
char *desktopName = "x11";


static long alwaysCheckForInput[2] = { 0, 1 };
static long *mieqCheckForInput[2];

static char primaryOrder[4] = "";
static int redBits, greenBits, blueBits;


static Bool rfbScreenInit _((int index, ScreenPtr pScreen, int argc,
			     char **argv));
static int rfbKeybdProc _((DeviceIntPtr pDevice, int onoff));
static int rfbMouseProc _((DeviceIntPtr pDevice, int onoff));

static Bool rfbAlwaysTrue();
static char *rfbAllocateFramebufferMemory _((rfbScreenInfoPtr prfb));
static Bool rfbCursorOffScreen _((ScreenPtr *ppScreen, int *x, int *y));
static void rfbCrossScreen _((ScreenPtr pScreen, Bool entering));
static void rfbClientStateChange _((CallbackListPtr *, pointer myData,
				    pointer client));

static miPointerScreenFuncRec rfbPointerCursorFuncs = {
    rfbCursorOffScreen,
    rfbCrossScreen,
    miPointerWarpCursor
};


/*
 * ddxProcessArgument is our first entry point and will be called at the
 * very start for each argument.  It is not called again on server reset.
 */

int
ddxProcessArgument (argc, argv, i)
    int argc;
    char *argv[];
    int i;
{
    static Bool firstTime = TRUE;

    if (firstTime)
    {
	rfbScreen.width  = RFB_DEFAULT_WIDTH;
	rfbScreen.height = RFB_DEFAULT_HEIGHT;
	rfbScreen.depth  = RFB_DEFAULT_DEPTH;
	rfbScreen.blackPixel = RFB_DEFAULT_BLACKPIXEL;
	rfbScreen.whitePixel = RFB_DEFAULT_WHITEPIXEL;
	rfbScreen.pfbMemory = NULL;
        firstTime = FALSE;
    }

    if (strcmp (argv[i], "-geometry") == 0)	/* -geometry WxH */
    {
	if (i + 1 >= argc) UseMsg();
	if (sscanf(argv[i+1],"%dx%d",
		   &rfbScreen.width,&rfbScreen.height) != 2) {
	    ErrorF("Invalid geometry %s\n", argv[i+1]);
	    UseMsg();
	}
#ifdef CORBA
	screenWidth= rfbScreen.width;
	screenHeight= rfbScreen.height;
#endif
	return 2;
    }

    if (strcmp (argv[i], "-depth") == 0)	/* -depth D */
    {
	if (i + 1 >= argc) UseMsg();
	rfbScreen.depth = atoi(argv[i+1]);
#ifdef CORBA
	screenDepth= rfbScreen.depth;
#endif
	return 2;
    }

    if (strcmp (argv[i], "-pixelformat") == 0) {
	if (i + 1 >= argc) UseMsg();
	if (sscanf(argv[i+1], "%3s%1d%1d%1d", primaryOrder,
		   &redBits, &greenBits, &blueBits) < 4) {
	    ErrorF("Invalid pixel format %s\n", argv[i+1]);
	    UseMsg();
	}

	if (strcasecmp(primaryOrder, "bgr") == 0) {
	    int tmp = redBits;
	    redBits = blueBits;
	    blueBits = tmp;
	} else if (strcasecmp(primaryOrder, "rgb") != 0) {
	    ErrorF("Invalid pixel format %s\n", argv[i+1]);
	    UseMsg();
	}

	return 2;
    }

    if (strcmp (argv[i], "-blackpixel") == 0) {	/* -blackpixel n */
	if (i + 1 >= argc) UseMsg();
	rfbScreen.blackPixel = atoi(argv[i+1]);
	return 2;
    }

    if (strcmp (argv[i], "-whitepixel") == 0) {	/* -whitepixel n */
	if (i + 1 >= argc) UseMsg();
	rfbScreen.whitePixel = atoi(argv[i+1]);
	return 2;
    }

    if (strcmp(argv[i], "-udpinputport") == 0) { /* -udpinputport port */
	if (i + 1 >= argc) UseMsg();
	udpPort = atoi(argv[i+1]);
	return 2;
    }

    if (strcmp(argv[i], "-rfbport") == 0) {	/* -rfbport port */
	if (i + 1 >= argc) UseMsg();
	rfbPort = atoi(argv[i+1]);
	return 2;
    }

    if (strcmp(argv[i], "-rfbwait") == 0) {	/* -rfbwait ms */
	if (i + 1 >= argc) UseMsg();
	rfbMaxClientWait = atoi(argv[i+1]);
	return 2;
    }

    if (strcmp(argv[i], "-nocursor") == 0) {
	noCursor = TRUE;
	return 1;
    }

    if (strcmp(argv[i], "-rfbauth") == 0) {	/* -rfbauth passwd-file */
	if (i + 1 >= argc) UseMsg();
	rfbAuthPasswdFile = argv[i+1];
	return 2;
    }

    if (strcmp(argv[i], "-httpd") == 0) {
	if (i + 1 >= argc) UseMsg();
	httpDir = argv[i+1];
	return 2;
    }

    if (strcmp(argv[i], "-httpport") == 0) {
	if (i + 1 >= argc) UseMsg();
	httpPort = atoi(argv[i+1]);
	return 2;
    }

    if (strcmp(argv[i], "-desktop") == 0) {	/* -desktop desktop-name */
	if (i + 1 >= argc) UseMsg();
	desktopName = argv[i+1];
	
	if (strcmp(desktopName, "default")==0) {
	  ErrorF("Cannot create a desktop called ``%s''.\n", desktopName);
	  exit(1);
	}

	return 2;
    }

    return 0;
}


/*
 * InitOutput is called every time the server resets.  It should call
 * AddScreen for each screen (but we only ever have one), and in turn this
 * will call rfbScreenInit.
 */

void
InitOutput(screenInfo, argc, argv)
    ScreenInfo *screenInfo;
    int argc;
    char **argv;
{
    initOutputCalled = TRUE;

    rfbInitSockets();
    httpInitSockets();

#ifdef CORBA
    initialiseCORBA(argc, argv, desktopName);
#endif

    /* initialize pixmap formats */

    screenInfo->imageByteOrder = IMAGE_BYTE_ORDER;
    screenInfo->bitmapScanlineUnit = BITMAP_SCANLINE_UNIT;
    screenInfo->bitmapScanlinePad = BITMAP_SCANLINE_PAD;
    screenInfo->bitmapBitOrder = BITMAP_BIT_ORDER;
    screenInfo->numPixmapFormats = 2;

    screenInfo->formats[0].depth = 1;
    screenInfo->formats[0].bitsPerPixel = 1;
    screenInfo->formats[0].scanlinePad = BITMAP_SCANLINE_PAD;

    screenInfo->formats[1].depth = rfbScreen.depth;
    screenInfo->formats[1].bitsPerPixel = rfbBitsPerPixel(rfbScreen.depth);
    screenInfo->formats[1].scanlinePad = BITMAP_SCANLINE_PAD;

    rfbGCIndex = AllocateGCPrivateIndex();
    if (rfbGCIndex < 0) {
	FatalError("InitOutput: AllocateGCPrivateIndex failed\n");
    }

    if (!AddCallback(&ClientStateCallback, rfbClientStateChange, NULL)) {
	fprintf(stderr,"InitOutput: AddCallback failed\n");
	return;
    }

    /* initialize screen */

    if (AddScreen(rfbScreenInit, argc, argv) == -1) {
	FatalError("Couldn't add screen");
    }
}


static Bool
rfbScreenInit(index, pScreen, argc, argv)
    int index;
    ScreenPtr pScreen;
    int argc;
    char ** argv;
{
    rfbScreenInfoPtr prfb = &rfbScreen;
    int dpix = 100, dpiy = 100;
    int ret;
    char *pbits;
    VisualPtr vis;

    prfb->paddedWidthInBytes = PixmapBytePad(prfb->width, prfb->depth);
    prfb->bitsPerPixel = rfbBitsPerPixel(prfb->depth);
    pbits = rfbAllocateFramebufferMemory(prfb);
    if (!pbits) return FALSE;

    if (prfb->bitsPerPixel > 1) {
	extern int defaultColorVisualClass;
	if (defaultColorVisualClass != -1) {
	    cfbSetVisualTypes(prfb->depth, (1 << defaultColorVisualClass), 8);
	} else {
	    cfbSetVisualTypes(prfb->depth, (1 << TrueColor), 8);
	}
    }

    switch (prfb->bitsPerPixel)
    {
    case 1:
	ret = mfbScreenInit(pScreen, pbits, prfb->width, prfb->height,
			    dpix, dpiy, prfb->paddedWidthInBytes * 8);
	break;
    case 8:
	ret = cfbScreenInit(pScreen, pbits, prfb->width, prfb->height,
			    dpix, dpiy, prfb->paddedWidthInBytes);
	break;
    case 16:
	ret = cfb16ScreenInit(pScreen, pbits, prfb->width, prfb->height,
			      dpix, dpiy, prfb->paddedWidthInBytes / 2);
	break;
    case 32:
	ret = cfb32ScreenInit(pScreen, pbits, prfb->width, prfb->height,
			      dpix, dpiy, prfb->paddedWidthInBytes / 4);
	break;
    default:
	return FALSE;
    }

    if (!ret) return FALSE;

    if (!AllocateGCPrivate(pScreen, rfbGCIndex, sizeof(rfbGCRec))) {
	FatalError("rfbScreenInit: AllocateGCPrivate failed\n");
    }

    prfb->cursorIsDrawn = FALSE;
    prfb->dontSendFramebufferUpdate = FALSE;

    prfb->CloseScreen = pScreen->CloseScreen;
    prfb->CreateGC = pScreen->CreateGC;
    prfb->PaintWindowBackground = pScreen->PaintWindowBackground;
    prfb->PaintWindowBorder = pScreen->PaintWindowBorder;
    prfb->CopyWindow = pScreen->CopyWindow;
    prfb->ClearToBackground = pScreen->ClearToBackground;
    prfb->RestoreAreas = pScreen->RestoreAreas;

    pScreen->CloseScreen = rfbCloseScreen;
    pScreen->CreateGC = rfbCreateGC;
    pScreen->PaintWindowBackground = rfbPaintWindowBackground;
    pScreen->PaintWindowBorder = rfbPaintWindowBorder;
    pScreen->CopyWindow = rfbCopyWindow;
    pScreen->ClearToBackground = rfbClearToBackground;
    pScreen->RestoreAreas = rfbRestoreAreas;

    pScreen->InstallColormap = rfbInstallColormap;
    pScreen->UninstallColormap = rfbUninstallColormap;
    pScreen->ListInstalledColormaps = rfbListInstalledColormaps;
    pScreen->StoreColors = rfbStoreColors;

    pScreen->SaveScreen = rfbAlwaysTrue;

    rfbDCInitialize(pScreen, &rfbPointerCursorFuncs);

    if (noCursor) {
	pScreen->DisplayCursor = rfbAlwaysTrue;
	prfb->cursorIsDrawn = TRUE;
    }

    pScreen->blackPixel = prfb->blackPixel;
    pScreen->whitePixel = prfb->whitePixel;

    for (vis = pScreen->visuals; vis->vid != pScreen->rootVisual; vis++)
	;

    if (!vis) {
	fprintf(stderr,"rfbScreenInit: couldn't find root visual\n");
	exit(1);
    }

    if (strcasecmp(primaryOrder, "rgb") == 0) {
	vis->offsetBlue = 0;
	vis->blueMask = (1 << blueBits) - 1;
	vis->offsetGreen = blueBits;
	vis->greenMask = ((1 << greenBits) - 1) << vis->offsetGreen;
	vis->offsetRed = vis->offsetGreen + greenBits;
	vis->redMask = ((1 << redBits) - 1) << vis->offsetRed;
    } else if (strcasecmp(primaryOrder, "bgr") == 0) {
	fprintf(stderr,"BGR format %d %d %d\n", blueBits, greenBits, redBits);
	vis->offsetRed = 0;
	vis->redMask = (1 << redBits) - 1;
	vis->offsetGreen = redBits;
	vis->greenMask = ((1 << greenBits) - 1) << vis->offsetGreen;
	vis->offsetBlue = vis->offsetGreen + greenBits;
	vis->blueMask = ((1 << blueBits) - 1) << vis->offsetBlue;
    }

    rfbServerFormat.bitsPerPixel = prfb->bitsPerPixel;
    rfbServerFormat.depth = prfb->depth;
    rfbServerFormat.bigEndian = !(*(char *)&rfbEndianTest);
    rfbServerFormat.trueColour = (vis->class == TrueColor);
    if (rfbServerFormat.trueColour) {
	rfbServerFormat.redMax = vis->redMask >> vis->offsetRed;
	rfbServerFormat.greenMax = vis->greenMask >> vis->offsetGreen;
	rfbServerFormat.blueMax = vis->blueMask >> vis->offsetBlue;
	rfbServerFormat.redShift = vis->offsetRed;
	rfbServerFormat.greenShift = vis->offsetGreen;
	rfbServerFormat.blueShift = vis->offsetBlue;
    } else {
	rfbServerFormat.redMax
	    = rfbServerFormat.greenMax = rfbServerFormat.blueMax = 0;
	rfbServerFormat.redShift
	    = rfbServerFormat.greenShift = rfbServerFormat.blueShift = 0;
    }

    if (prfb->bitsPerPixel == 1)
    {
	ret = mfbCreateDefColormap(pScreen);
    }
    else
    {
	ret = cfbCreateDefColormap(pScreen);
    }

    return ret;

} /* end rfbScreenInit */



/*
 * InitInput is also called every time the server resets.  It is called after
 * InitOutput so we can assume that rfbInitSockets has already been called.
 */

void
InitInput(argc, argv)
    int argc;
    char *argv[];
{
    DevicePtr p, k;
    k = AddInputDevice(rfbKeybdProc, TRUE);
    p = AddInputDevice(rfbMouseProc, TRUE);
    RegisterKeyboardDevice(k);
    RegisterPointerDevice(p);
    miRegisterPointerDevice(screenInfo.screens[0], p);
    (void)mieqInit (k, p);
    mieqCheckForInput[0] = checkForInput[0];
    mieqCheckForInput[1] = checkForInput[1];
    SetInputCheck(&alwaysCheckForInput[0], &alwaysCheckForInput[1]);
}


static int
rfbKeybdProc(pDevice, onoff)
    DeviceIntPtr pDevice;
    int onoff;
{
    KeySymsRec		keySyms;
    CARD8 		modMap[MAP_LENGTH];
    DevicePtr pDev = (DevicePtr)pDevice;

    switch (onoff)
    {
    case DEVICE_INIT: 
	KbdDeviceInit(pDevice, &keySyms, modMap);
	InitKeyboardDeviceStruct(pDev, &keySyms, modMap,
				 (BellProcPtr)rfbSendBell,
				 (KbdCtrlProcPtr)NoopDDA);
	    break;
    case DEVICE_ON: 
	pDev->on = TRUE;
	KbdDeviceOn();
	break;
    case DEVICE_OFF: 
	pDev->on = FALSE;
	KbdDeviceOff();
	break;
    case DEVICE_CLOSE:
	if (pDev->on)
	    KbdDeviceOff();
	break;
    }
    return Success;
}

static int
rfbMouseProc(pDevice, onoff)
    DeviceIntPtr pDevice;
    int onoff;
{
    BYTE map[4];
    DevicePtr pDev = (DevicePtr)pDevice;

    switch (onoff)
    {
    case DEVICE_INIT:
	PtrDeviceInit();
	map[1] = 1;
	map[2] = 2;
	map[3] = 3;
	InitPointerDeviceStruct(pDev, map, 3, miPointerGetMotionEvents,
				PtrDeviceControl,
				miPointerGetMotionBufferSize());
	break;

    case DEVICE_ON:
	pDev->on = TRUE;
	PtrDeviceOn(pDevice);
        break;

    case DEVICE_OFF:
	pDev->on = FALSE;
	PtrDeviceOff();
	break;

    case DEVICE_CLOSE:
	if (pDev->on)
	    PtrDeviceOff();
	break;
    }
    return Success;
}


Bool
LegalModifier(key, pDev)
    unsigned int key;
    DevicePtr	pDev;
{
    return TRUE;
}


void
ProcessInputEvents()
{
    rfbCheckFds();
    httpCheckFds();
#ifdef CORBA
    corbaCheckFds();
#endif
    if (*mieqCheckForInput[0] != *mieqCheckForInput[1]) {
	mieqProcessInputEvents();
	miPointerUpdate();
    }
}


int
rfbBitsPerPixel(depth)
    int depth;
{
    if (depth == 1) return 1;
    else if (depth <= 8) return 8;
    else if (depth <= 16) return 16;
    else return 32;
}


static Bool
rfbAlwaysTrue()
{
    return TRUE;
}


static char *
rfbAllocateFramebufferMemory(prfb)
    rfbScreenInfoPtr prfb;
{
    if (prfb->pfbMemory) return prfb->pfbMemory; /* already done */

    prfb->sizeInBytes = (prfb->paddedWidthInBytes * prfb->height);

    prfb->pfbMemory = (char *)Xalloc(prfb->sizeInBytes);

    return prfb->pfbMemory;
}


static Bool
rfbCursorOffScreen (ppScreen, x, y)
    ScreenPtr   *ppScreen;
    int         *x, *y;
{
    return FALSE;
}

static void
rfbCrossScreen (pScreen, entering)
    ScreenPtr   pScreen;
    Bool        entering;
{
}

static void
rfbClientStateChange(cbl, myData, clt)
    CallbackListPtr *cbl;
    pointer myData;
    pointer clt;
{
    dispatchException &= ~DE_RESET;	/* hack - force server not to reset */
}

void
ddxGiveUp()
{
    Xfree(rfbScreen.pfbMemory);
    if (initOutputCalled) {
	char unixSocketName[32];
	sprintf(unixSocketName,"/tmp/.X11-unix/X%s",display);
	unlink(unixSocketName);
#ifdef CORBA
	shutdownCORBA();
#endif
    }
}

void
AbortDDX()
{
    ddxGiveUp();
}

void
OsVendorInit()
{
}

void
ddxUseMsg()
{
    ErrorF("-geometry WxH          set framebuffer width & height\n");
    ErrorF("-depth D		   set framebuffer depth\n");
    ErrorF("-pixelformat format    set pixel format (BGRnnn or RGBnnn)\n");
    ErrorF("-udpinputport port     UDP port for keyboard/pointer data\n");
    ErrorF("-rfbport port          TCP port for RFB protocol\n");
    ErrorF("-rfbwait time          max time in ms to wait for RFB client\n");
    ErrorF("-nocursor              don't put up a cursor\n");
    ErrorF("-rfbauth passwd-file   use authentication on RFB protocol\n");
    ErrorF("-httpd dir             serve files via HTTP from here\n");
    ErrorF("-httpport port         port for HTTP\n");
#ifdef CORBA
    ErrorF("-desktop name          VNC desktop name (default x11)\n");
#endif
    exit(1);
}