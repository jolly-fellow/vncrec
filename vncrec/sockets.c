/*
 *  Copyright (C) 1999 AT&T Laboratories Cambridge.  All Rights Reserved.
 *  Copyright (C) 2001 Yoshiki Hayashi <yoshiki@xemacs.org>
 *  Copyright (C) 2006 Karel Kulhavy <clock (at) twibright (dot) com>
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
 * sockets.c - functions to deal with sockets.
 * Karel Kulhavy changed the XPM output to yuv4mpeg2 so it can be used easily
 * to encode Theora (with the example libtheora encoder), Xvid and wmv (with
 * transcode). Now it encodes at 85% video playback speed on Pentium M 1.5GHz
 * which is way faster than the original XPM output.
 */

#include <unistd.h>
#include <sys/socket.h>
#include <sys/wait.h>
#include <errno.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <arpa/inet.h>
#include <netdb.h>
#include <fcntl.h>
#include <assert.h>
#include <vncviewer.h>

void PrintInHex(char *buf, int len);

Bool errorMessageOnReadFailure = True;

#define BUF_SIZE 8192
static char buf[BUF_SIZE];
static char *bufoutptr = buf;
static int buffered = 0;
Bool vncLogTimeStamp = False;

static char *data_buffer; // buffer which contains data chunk without header
static size_t data_pos; // current reading|writing position
const uint64_t MAGIC_NUMBER = 0xAAAAAAAAAAAAAAAA; //1010101010101010101010101010101010101010101010101010101010101010

typedef struct DataHeader {
    uint64_t magic_num;	
    size_t data_size;
	struct timeval timestamp;	
    uint64_t crc64;	
} DataHeader;

static DataHeader data_header; // header of current data chunk

/* Shifts to obtain the red, green, and blue value
 * from a long loaded from the memory. These are initialized once before the
 * first snapshot is taken. */
unsigned red_shift, green_shift, blue_shift;

/*
 * ReadFromRFBServer is called whenever we want to read some data from the RFB
 * server.  It is non-trivial for two reasons:
 *
 * 1. For efficiency it performs some intelligent buffering, avoiding invoking
 *    the read() system call too often.  For small chunks of data, it simply
 *    copies the data out of an internal buffer.  For large amounts of data it
 *    reads directly into the buffer provided by the caller.
 *
 * 2. Whenever read() would block, it invokes the Xt event dispatching
 *    mechanism to process X events.  In fact, this is the only place these
 *    events are processed, as there is no XtAppMainLoop in the program.
 */

static Bool rfbsockReady = False;
static void
rfbsockReadyCallback(XtPointer clientData, int *fd, XtInputId *id)
{
  rfbsockReady = True;
  XtRemoveInput(*id);
}

static void
ProcessXtEvents()
{
  rfbsockReady = False;
  XtAppAddInput(appContext, rfbsock, (XtPointer)XtInputReadMask,
		rfbsockReadyCallback, NULL);
  while (!rfbsockReady) {
    XtAppProcessEvent(appContext, XtIMAll);
  }
}

void my_fwrite(const void *ptr, size_t size, size_t nmemb, FILE *stream)
{
	if (fwrite(ptr, size, nmemb, stream)
		!=nmemb){
		fprintf(stderr,"vncrec: Error occured writing %u bytes"
			"into a file stream: ", (unsigned)(size*nmemb));
		perror(NULL);
		exit(1);
	}
}

static void
writeLogHeader (void)
{
  struct timeval tv;
  static unsigned int frame = 0;

  if (vncLogTimeStamp)
    {
      long tell = ftell(vncLog);
      unsigned int wframe = Swap32IfLE(frame);

      my_fwrite (&wframe, sizeof(wframe), 1, vncLog);

      gettimeofday (&tv, NULL);

      if (appData.debugFrames) {
          fprintf(stderr, "write frame %u at time %.3f @ offset %ld\n",
                  frame, tv.tv_sec + tv.tv_usec / 1e6, tell);
      }

      tv.tv_sec = Swap32IfLE (tv.tv_sec);
      tv.tv_usec = Swap32IfLE (tv.tv_usec);
      my_fwrite (&tv, sizeof (struct timeval), 1, vncLog);

      frame++;
    }
}

static struct timeval
timeval_subtract (struct timeval x,
		  struct timeval y)
{
  struct timeval result;

  result.tv_sec = x.tv_sec - y.tv_sec;
  result.tv_usec = x.tv_usec - y.tv_usec;
  if (result.tv_usec < 0)
    {
      result.tv_sec--;
      result.tv_usec += 1000000;
    }
  assert (result.tv_usec >= 0);
  return result;
}

void scanline(unsigned char *r, unsigned char *g, unsigned char *b, unsigned
		char *src, unsigned cycles)
{
	unsigned long v; /* This will probably work only on 32-bit
			    architecture */

	for (;cycles;cycles--){
		v=*(unsigned long *)(void *)src;

		*r++=v>>red_shift;
		*g++=v>>green_shift;
		*b++=v>>blue_shift;

		src+=4;
	}
}

/* Use on variable names only */
#define CLIP(x) if (x<0) x=0; else if (x>255) x=255;

/* Converts RGB to the "yuv" that is in yuv4mpeg.
 * It looks like the unspecified "yuv" that is in yuv4mpeg2 is actually
 * Y'CbCr, with all 3 components full range 0-255 as in JPEG. If
 * the reduced range (16-240 etc.) is used here, the result looks washed out. */
void rgb2yuv(unsigned char *d, unsigned plane)
{
	unsigned char *r, *g, *b;
	int y,u,v;

	r=d;
	g=r+plane;
	b=g+plane;
	for (;plane;plane--){
		y=((77**r+150**g+29**b+0x80)>>8);
		u=0x80+((-43**r-85**g+128**b+0x7f)>>8);
		v=0x80+((128**r-107**g-21**b+0x7f)>>8);
		CLIP(y);
		CLIP(u);
		CLIP(v);
		*r++=y;
		*g++=u;
		*b++=v;
	}
}

/* Writes a frame of yuv4mpeg file to the stdout. Repeats writing
 * the identical frame "times" times. */
void dump_image(XImage *i, unsigned times)
{
    unsigned char frame_header[]="FRAME\n";

    unsigned w=si.framebufferWidth; /* Image size */
    unsigned h=si.framebufferHeight;
    unsigned char *d; /* R'G'B' / Y'CbCr data buffer */
    unsigned x, y; /* Counters */
    unsigned char *rptr, *gptr, *bptr; /* R'/Cr, green/get, B'/Cb pointer */
    unsigned char *wptr; /* Write ptr for moving the chroma samples
                            together */

    /* Test that the image has 32-bit pixels */
    if (i->bitmap_unit!=32) {
        fprintf(stderr,"Sorry, only >= 8 bits per channel colour "
                "is supported. bitmap_unit=%u\n",
                i->bitmap_unit);
        exit(1);
    }

    /* Allocate a R'G'B' buffer (' values mean gamma-corrected so the
     * numbers are linear to the electrical video signal. RGB would mean
     * linear photometric space */
    d = malloc(w*h*3);

    if (!appData.writeYUV)
    {
        // output frame as RGB8 data

        /* Read the data in from the image into the RGB buffer */
        rptr = i->data;
        wptr = d;

        for (y=0; y<h; y++){
            for (x=0; x<w; ++x){
                int v;

                v = *(unsigned long *)(void *)rptr;
                rptr += 4;

                *wptr++ = v >> red_shift;
                *wptr++ = v >> green_shift;
                *wptr++ = v >> blue_shift;
            }
        }

        /* Write out the frame, "times" times. */
        for (;times;times--){
            my_fwrite(d, w*h*3, 1, stdout);
        }
    }
    else
    {
        // output frame as YUV4MPEG data (as in vncrec-twibright)

	/* Read the data in from the image into the RGB buffer */
	for (y=0; y<h; y++){
            rptr=d+y*w;
            gptr=rptr+w*h;
            bptr=gptr+w*h;
            scanline(rptr, gptr, bptr, i->data+i->bytes_per_line*y, w);
	}

	/* Convert the R'G'B' buffer into an Y'CbCr buffer */
	rgb2yuv(d, w*h);

	/* Decimate the chroma down to 4:2:0. This is mathematically incorrect,
	 * but it's the customary way how to do it in TV technology. To be
	 * mathematically correct, the decimation would have to take place in
	 * linear photometric space. This way it generates the usual
	 * chroma-bleeding artifacts on the edges in the colour monoscope */
	for (y=0;y<h-1;y+=2){
            bptr=d+(h+y)*w;
            rptr=bptr+h*w;
            for (x=0;x<w-1;x+=2, bptr+=2, rptr+=2){
                bptr[0]=(bptr[0]+bptr[1]+bptr[w]+bptr[w+1])>>2;
                rptr[0]=(rptr[0]+rptr[1]+rptr[w]+rptr[w+1])>>2;
            }
	}

	/* Shuffle the chroma so the data can be written out at once. */
	bptr=d+w*h; /* Cb */
	rptr=bptr+w*h; /* Cr */
	wptr=bptr;
	for (y=0;y<h-1;y+=2){
            gptr=bptr+y*w; /* gptr now doesn't mean green pointer,
                              but get pointer. */
            for (x=0;x<w-1;x+=2, gptr+=2)
                *wptr++=*gptr; /* Only subsampling, now the
                                  decimation has already been
                                  done. */
	}
	for (y=0;y<h-1;y+=2){
            gptr=rptr+y*w;
            for (x=0;x<w-1;x+=2, gptr+=2)
                *wptr++=*gptr;
	}
	/* Now the data to be written begin at d and are wptr-d long. */

	/* Write out the frame, "times" times. */
	for (;times;times--){
            my_fwrite(frame_header, sizeof(frame_header)-1, 1, stdout);
            my_fwrite(d, wptr-d, 1, stdout);
	}
    }

    /* Throw away the formerly R'G'B', now Y'CbCr buffer */
    free(d);
}

/* Returns MSBFirst for big endian and LSBFirst for little */
int test_endian(void)
{
	long a=1;

	*((unsigned char *)(void *)&a)=0;
	return a?MSBFirst:LSBFirst;
}

unsigned mask2shift(unsigned long in)
{
	unsigned shift=0;

	if (!in) return 0;

	while(!(in&1)){
		in>>=1;
		shift++;
	}
	return shift;
}

/* Sets the red_shift, green_shift and blue_shift variables. */
void examine_layout(void)
{
	XWindowAttributes attr;
	Window rootwin;
	int dummy_i;
	unsigned dummy_u;

	XGetGeometry(dpy, desktopWin, &rootwin,
		&dummy_i, &dummy_i, &dummy_u, &dummy_u, &dummy_u, &dummy_u);
	XGetWindowAttributes(dpy, rootwin, &attr);
	fprintf(stderr,"red_mask=%lx, green_mask=%lx, blue_mask=%lx, "
			"CPU endian=%u, dpy endian=%u\n",
			attr.visual->red_mask,
			attr.visual->green_mask,
			attr.visual->blue_mask,
			test_endian(),
			ImageByteOrder(dpy));
	red_shift=mask2shift(attr.visual->red_mask);
	green_shift=mask2shift(attr.visual->green_mask);
	blue_shift=mask2shift(attr.visual->blue_mask);
	if (test_endian()!=ImageByteOrder(dpy)){
		red_shift=24-red_shift;
		green_shift=24-green_shift;
		blue_shift=24-blue_shift;
	}
	fprintf(stderr,"Image dump color channel shifts: R=%u, G=%u, B=%u\n",
			red_shift, green_shift, blue_shift);
}

void print_movie_frames_up_to_time(struct timeval tv) {
    static double framerate;
    static double start_time = 0;
    double now = tv.tv_sec + tv.tv_usec / 1e6;
    static unsigned last_frame = 0, this_frame = 0;
    static unsigned times;
    XImage *image;

    if (start_time == 0) {  // one-time initialization
        framerate = getenv("VNCREC_MOVIE_FRAMERATE") ? atoi(getenv("VNCREC_MOVIE_FRAMERATE")) : 25;

        if (appData.ffInfo) {
            if (appData.writeYUV) {
                fprintf(stderr,
                        "Error: -ffinfo and -writeYUV are mutually exclusive, "
                        "use -f yuv4mpegpipe.\n");
            }
            else {
                printf("-pixel_format rgb24 -video_size %ux%u -framerate %u\n",
                       si.framebufferWidth,
                       si.framebufferHeight,
                       (unsigned)framerate);
            }
            exit(0);
        }

        if (appData.writeYUV) {
            printf("YUV4MPEG2 W%u H%u F%u:1 Ip A0:0\n",
                   si.framebufferWidth,
                   si.framebufferHeight,
                   (unsigned)framerate);
        }
        else {
            fprintf(stderr,"RGB8 W%u H%u F%u:1 Ip A0:0\n",
                    si.framebufferWidth,
                    si.framebufferHeight,
                    (unsigned)framerate);
        }

        examine_layout(); /* Figure out red_shift, green_shift, blue_shift */

        start_time = now;
    }

    this_frame = (unsigned)((now - start_time) * framerate);
    assert(this_frame >= last_frame);

    if (this_frame == last_frame) return; /* not time for the next frame yet. */

    times = this_frame - last_frame;
    last_frame = this_frame;

    image = XGetImage(dpy, desktopWin,0, 0, si.framebufferWidth,
                      si.framebufferHeight, 0xffffffff,
                      ZPixmap);
    assert(image);

    if (0) {
        if (times == 1) {
            fprintf(stderr,"Dumping frame for time %.2f sec - %.6f.\n",
                    times / framerate, now);
        }
        else {
            fprintf(stderr,"Dumping %u frames for time %.2f sec - %.6f.\n",
                    times, times / framerate, now);
        }
    }

    /* Print the frame(s) */
    dump_image(image, times);

    XDestroyImage(image);
}



    static const uint64_t crc64_tab[256] = {
            UINT64_C(0x0000000000000000), UINT64_C(0x7ad870c830358979),
            UINT64_C(0xf5b0e190606b12f2), UINT64_C(0x8f689158505e9b8b),
            UINT64_C(0xc038e5739841b68f), UINT64_C(0xbae095bba8743ff6),
            UINT64_C(0x358804e3f82aa47d), UINT64_C(0x4f50742bc81f2d04),
            UINT64_C(0xab28ecb46814fe75), UINT64_C(0xd1f09c7c5821770c),
            UINT64_C(0x5e980d24087fec87), UINT64_C(0x24407dec384a65fe),
            UINT64_C(0x6b1009c7f05548fa), UINT64_C(0x11c8790fc060c183),
            UINT64_C(0x9ea0e857903e5a08), UINT64_C(0xe478989fa00bd371),
            UINT64_C(0x7d08ff3b88be6f81), UINT64_C(0x07d08ff3b88be6f8),
            UINT64_C(0x88b81eabe8d57d73), UINT64_C(0xf2606e63d8e0f40a),
            UINT64_C(0xbd301a4810ffd90e), UINT64_C(0xc7e86a8020ca5077),
            UINT64_C(0x4880fbd87094cbfc), UINT64_C(0x32588b1040a14285),
            UINT64_C(0xd620138fe0aa91f4), UINT64_C(0xacf86347d09f188d),
            UINT64_C(0x2390f21f80c18306), UINT64_C(0x594882d7b0f40a7f),
            UINT64_C(0x1618f6fc78eb277b), UINT64_C(0x6cc0863448deae02),
            UINT64_C(0xe3a8176c18803589), UINT64_C(0x997067a428b5bcf0),
            UINT64_C(0xfa11fe77117cdf02), UINT64_C(0x80c98ebf2149567b),
            UINT64_C(0x0fa11fe77117cdf0), UINT64_C(0x75796f2f41224489),
            UINT64_C(0x3a291b04893d698d), UINT64_C(0x40f16bccb908e0f4),
            UINT64_C(0xcf99fa94e9567b7f), UINT64_C(0xb5418a5cd963f206),
            UINT64_C(0x513912c379682177), UINT64_C(0x2be1620b495da80e),
            UINT64_C(0xa489f35319033385), UINT64_C(0xde51839b2936bafc),
            UINT64_C(0x9101f7b0e12997f8), UINT64_C(0xebd98778d11c1e81),
            UINT64_C(0x64b116208142850a), UINT64_C(0x1e6966e8b1770c73),
            UINT64_C(0x8719014c99c2b083), UINT64_C(0xfdc17184a9f739fa),
            UINT64_C(0x72a9e0dcf9a9a271), UINT64_C(0x08719014c99c2b08),
            UINT64_C(0x4721e43f0183060c), UINT64_C(0x3df994f731b68f75),
            UINT64_C(0xb29105af61e814fe), UINT64_C(0xc849756751dd9d87),
            UINT64_C(0x2c31edf8f1d64ef6), UINT64_C(0x56e99d30c1e3c78f),
            UINT64_C(0xd9810c6891bd5c04), UINT64_C(0xa3597ca0a188d57d),
            UINT64_C(0xec09088b6997f879), UINT64_C(0x96d1784359a27100),
            UINT64_C(0x19b9e91b09fcea8b), UINT64_C(0x636199d339c963f2),
            UINT64_C(0xdf7adabd7a6e2d6f), UINT64_C(0xa5a2aa754a5ba416),
            UINT64_C(0x2aca3b2d1a053f9d), UINT64_C(0x50124be52a30b6e4),
            UINT64_C(0x1f423fcee22f9be0), UINT64_C(0x659a4f06d21a1299),
            UINT64_C(0xeaf2de5e82448912), UINT64_C(0x902aae96b271006b),
            UINT64_C(0x74523609127ad31a), UINT64_C(0x0e8a46c1224f5a63),
            UINT64_C(0x81e2d7997211c1e8), UINT64_C(0xfb3aa75142244891),
            UINT64_C(0xb46ad37a8a3b6595), UINT64_C(0xceb2a3b2ba0eecec),
            UINT64_C(0x41da32eaea507767), UINT64_C(0x3b024222da65fe1e),
            UINT64_C(0xa2722586f2d042ee), UINT64_C(0xd8aa554ec2e5cb97),
            UINT64_C(0x57c2c41692bb501c), UINT64_C(0x2d1ab4dea28ed965),
            UINT64_C(0x624ac0f56a91f461), UINT64_C(0x1892b03d5aa47d18),
            UINT64_C(0x97fa21650afae693), UINT64_C(0xed2251ad3acf6fea),
            UINT64_C(0x095ac9329ac4bc9b), UINT64_C(0x7382b9faaaf135e2),
            UINT64_C(0xfcea28a2faafae69), UINT64_C(0x8632586aca9a2710),
            UINT64_C(0xc9622c4102850a14), UINT64_C(0xb3ba5c8932b0836d),
            UINT64_C(0x3cd2cdd162ee18e6), UINT64_C(0x460abd1952db919f),
            UINT64_C(0x256b24ca6b12f26d), UINT64_C(0x5fb354025b277b14),
            UINT64_C(0xd0dbc55a0b79e09f), UINT64_C(0xaa03b5923b4c69e6),
            UINT64_C(0xe553c1b9f35344e2), UINT64_C(0x9f8bb171c366cd9b),
            UINT64_C(0x10e3202993385610), UINT64_C(0x6a3b50e1a30ddf69),
            UINT64_C(0x8e43c87e03060c18), UINT64_C(0xf49bb8b633338561),
            UINT64_C(0x7bf329ee636d1eea), UINT64_C(0x012b592653589793),
            UINT64_C(0x4e7b2d0d9b47ba97), UINT64_C(0x34a35dc5ab7233ee),
            UINT64_C(0xbbcbcc9dfb2ca865), UINT64_C(0xc113bc55cb19211c),
            UINT64_C(0x5863dbf1e3ac9dec), UINT64_C(0x22bbab39d3991495),
            UINT64_C(0xadd33a6183c78f1e), UINT64_C(0xd70b4aa9b3f20667),
            UINT64_C(0x985b3e827bed2b63), UINT64_C(0xe2834e4a4bd8a21a),
            UINT64_C(0x6debdf121b863991), UINT64_C(0x1733afda2bb3b0e8),
            UINT64_C(0xf34b37458bb86399), UINT64_C(0x8993478dbb8deae0),
            UINT64_C(0x06fbd6d5ebd3716b), UINT64_C(0x7c23a61ddbe6f812),
            UINT64_C(0x3373d23613f9d516), UINT64_C(0x49aba2fe23cc5c6f),
            UINT64_C(0xc6c333a67392c7e4), UINT64_C(0xbc1b436e43a74e9d),
            UINT64_C(0x95ac9329ac4bc9b5), UINT64_C(0xef74e3e19c7e40cc),
            UINT64_C(0x601c72b9cc20db47), UINT64_C(0x1ac40271fc15523e),
            UINT64_C(0x5594765a340a7f3a), UINT64_C(0x2f4c0692043ff643),
            UINT64_C(0xa02497ca54616dc8), UINT64_C(0xdafce7026454e4b1),
            UINT64_C(0x3e847f9dc45f37c0), UINT64_C(0x445c0f55f46abeb9),
            UINT64_C(0xcb349e0da4342532), UINT64_C(0xb1eceec59401ac4b),
            UINT64_C(0xfebc9aee5c1e814f), UINT64_C(0x8464ea266c2b0836),
            UINT64_C(0x0b0c7b7e3c7593bd), UINT64_C(0x71d40bb60c401ac4),
            UINT64_C(0xe8a46c1224f5a634), UINT64_C(0x927c1cda14c02f4d),
            UINT64_C(0x1d148d82449eb4c6), UINT64_C(0x67ccfd4a74ab3dbf),
            UINT64_C(0x289c8961bcb410bb), UINT64_C(0x5244f9a98c8199c2),
            UINT64_C(0xdd2c68f1dcdf0249), UINT64_C(0xa7f41839ecea8b30),
            UINT64_C(0x438c80a64ce15841), UINT64_C(0x3954f06e7cd4d138),
            UINT64_C(0xb63c61362c8a4ab3), UINT64_C(0xcce411fe1cbfc3ca),
            UINT64_C(0x83b465d5d4a0eece), UINT64_C(0xf96c151de49567b7),
            UINT64_C(0x76048445b4cbfc3c), UINT64_C(0x0cdcf48d84fe7545),
            UINT64_C(0x6fbd6d5ebd3716b7), UINT64_C(0x15651d968d029fce),
            UINT64_C(0x9a0d8ccedd5c0445), UINT64_C(0xe0d5fc06ed698d3c),
            UINT64_C(0xaf85882d2576a038), UINT64_C(0xd55df8e515432941),
            UINT64_C(0x5a3569bd451db2ca), UINT64_C(0x20ed197575283bb3),
            UINT64_C(0xc49581ead523e8c2), UINT64_C(0xbe4df122e51661bb),
            UINT64_C(0x3125607ab548fa30), UINT64_C(0x4bfd10b2857d7349),
            UINT64_C(0x04ad64994d625e4d), UINT64_C(0x7e7514517d57d734),
            UINT64_C(0xf11d85092d094cbf), UINT64_C(0x8bc5f5c11d3cc5c6),
            UINT64_C(0x12b5926535897936), UINT64_C(0x686de2ad05bcf04f),
            UINT64_C(0xe70573f555e26bc4), UINT64_C(0x9ddd033d65d7e2bd),
            UINT64_C(0xd28d7716adc8cfb9), UINT64_C(0xa85507de9dfd46c0),
            UINT64_C(0x273d9686cda3dd4b), UINT64_C(0x5de5e64efd965432),
            UINT64_C(0xb99d7ed15d9d8743), UINT64_C(0xc3450e196da80e3a),
            UINT64_C(0x4c2d9f413df695b1), UINT64_C(0x36f5ef890dc31cc8),
            UINT64_C(0x79a59ba2c5dc31cc), UINT64_C(0x037deb6af5e9b8b5),
            UINT64_C(0x8c157a32a5b7233e), UINT64_C(0xf6cd0afa9582aa47),
            UINT64_C(0x4ad64994d625e4da), UINT64_C(0x300e395ce6106da3),
            UINT64_C(0xbf66a804b64ef628), UINT64_C(0xc5bed8cc867b7f51),
            UINT64_C(0x8aeeace74e645255), UINT64_C(0xf036dc2f7e51db2c),
            UINT64_C(0x7f5e4d772e0f40a7), UINT64_C(0x05863dbf1e3ac9de),
            UINT64_C(0xe1fea520be311aaf), UINT64_C(0x9b26d5e88e0493d6),
            UINT64_C(0x144e44b0de5a085d), UINT64_C(0x6e963478ee6f8124),
            UINT64_C(0x21c640532670ac20), UINT64_C(0x5b1e309b16452559),
            UINT64_C(0xd476a1c3461bbed2), UINT64_C(0xaeaed10b762e37ab),
            UINT64_C(0x37deb6af5e9b8b5b), UINT64_C(0x4d06c6676eae0222),
            UINT64_C(0xc26e573f3ef099a9), UINT64_C(0xb8b627f70ec510d0),
            UINT64_C(0xf7e653dcc6da3dd4), UINT64_C(0x8d3e2314f6efb4ad),
            UINT64_C(0x0256b24ca6b12f26), UINT64_C(0x788ec2849684a65f),
            UINT64_C(0x9cf65a1b368f752e), UINT64_C(0xe62e2ad306bafc57),
            UINT64_C(0x6946bb8b56e467dc), UINT64_C(0x139ecb4366d1eea5),
            UINT64_C(0x5ccebf68aecec3a1), UINT64_C(0x2616cfa09efb4ad8),
            UINT64_C(0xa97e5ef8cea5d153), UINT64_C(0xd3a62e30fe90582a),
            UINT64_C(0xb0c7b7e3c7593bd8), UINT64_C(0xca1fc72bf76cb2a1),
            UINT64_C(0x45775673a732292a), UINT64_C(0x3faf26bb9707a053),
            UINT64_C(0x70ff52905f188d57), UINT64_C(0x0a2722586f2d042e),
            UINT64_C(0x854fb3003f739fa5), UINT64_C(0xff97c3c80f4616dc),
            UINT64_C(0x1bef5b57af4dc5ad), UINT64_C(0x61372b9f9f784cd4),
            UINT64_C(0xee5fbac7cf26d75f), UINT64_C(0x9487ca0fff135e26),
            UINT64_C(0xdbd7be24370c7322), UINT64_C(0xa10fceec0739fa5b),
            UINT64_C(0x2e675fb4576761d0), UINT64_C(0x54bf2f7c6752e8a9),
            UINT64_C(0xcdcf48d84fe75459), UINT64_C(0xb71738107fd2dd20),
            UINT64_C(0x387fa9482f8c46ab), UINT64_C(0x42a7d9801fb9cfd2),
            UINT64_C(0x0df7adabd7a6e2d6), UINT64_C(0x772fdd63e7936baf),
            UINT64_C(0xf8474c3bb7cdf024), UINT64_C(0x829f3cf387f8795d),
            UINT64_C(0x66e7a46c27f3aa2c), UINT64_C(0x1c3fd4a417c62355),
            UINT64_C(0x935745fc4798b8de), UINT64_C(0xe98f353477ad31a7),
            UINT64_C(0xa6df411fbfb21ca3), UINT64_C(0xdc0731d78f8795da),
            UINT64_C(0x536fa08fdfd90e51), UINT64_C(0x29b7d047efec8728),
    };

    uint64_t crc64(uint64_t crc, const unsigned char *s, uint64_t l) {
        uint64_t j;

        for (j = 0; j < l; j++) {
            uint8_t byte = s[j];
            crc = crc64_tab[(uint8_t)crc ^ byte] ^ (crc >> 8);
        }
        return crc;
    }

char * ReadDataChunk(DataHeader *header) {

	uint64_t crc = 0;
	static unsigned int frame_counter = 0;
	fprintf(stderr, "read frame [%u]\n", ++frame_counter);
    // reading of the header

	int i = fread (header, sizeof(DataHeader), 1, vncLog);

	if (i < 1) { 
		fprintf(stderr, "Problem with reading of data chunk header\n");
		return NULL; 
	}

	if (header->magic_num != MAGIC_NUMBER)  { 
		fprintf(stderr, "magic number is wrong\n");
		return NULL; 
	}

	// reading of the data part
	char *data = (char*) malloc(header->data_size);

	i = fread (data, header->data_size, 1, vncLog);

	if (i < 1) { 
		fprintf(stderr, "Problem with reading of data part of the chunk\n");
		return NULL; 
	}

	crc = crc64(0, data, header->data_size);

	if (crc != header->crc64) { 
		fprintf(stderr, "CRC of the data chunk is wrong. It seems the data is corrupted.\n");
		return NULL; 
	}

	return data;
}



Bool ReadFromBuffer(char *out, size_t n) {
// n          is number of bytes to read
// buf_size  is size of the data buffer
// data_pos   is current position since we do reading
// n_rest     is unread part of the buffer
// n_read     is already read part of the buffer

    size_t buf_size = data_header.data_size;
    int n_rest = data_header.data_size - data_pos;
    int n_read = data_pos;

    // if buffer is empty read it
    if(0 == buf_size) {
        data_buffer = ReadDataChunk(&data_header);
        if(data_buffer == NULL) {
            return False;
        }
        memcpy(out, data_buffer, n);
        data_pos = n;
        return True;
    }
    // if we reached end of the buffer but need to read more
    if(data_pos == buf_size) {
        free(data_buffer);
        data_buffer = ReadDataChunk(&data_header);
        if(data_buffer == NULL) {
            return False;
        }
        memcpy(out, data_buffer, n);
        data_pos = n;
        return True;
    }
    // if we have partially read buffer but need to read less than rest number of bytes
    if(n_rest >= n) {
        memcpy(out, data_buffer+data_pos, n);
        data_pos += n;
        return True;
    }
    // if we have partially read buffer but need to read more than rest number of bytes
    if(n_rest < n) {
        // read unread part till end of the buffer
        memcpy(out, data_buffer+data_pos, n_rest);
        free(data_buffer);
        // read new chunk of data
        data_buffer = ReadDataChunk(&data_header);        
        data_pos = 0;
        if (data_buffer == NULL) { return False; }
        memcpy(out+n_rest, data_buffer, n-n_rest);
        data_pos = n-n_rest;
        return True;
    }
    return False;
}

Bool
ReadFromRFBServer(char *out, unsigned int n) {
	if (appData.play || appData.movie) {
        if (vncLogTimeStamp) {

            // This looks like the best way to adjust time at the moment.
            static struct timeval prev;

            if (!appData.movie && prev.tv_sec) { // print the movie frames as fast as possible
                struct timeval diff = timeval_subtract(data_header.timestamp, prev);
                sleep (diff.tv_sec);
                usleep (diff.tv_usec);
            }
            prev = data_header.timestamp;

            if (appData.debugFrames) {
                  fprintf(stderr, "read frame at time %.3f\n", data_header.timestamp.tv_sec + data_header.timestamp.tv_usec / 1e6);
            }

            if(appData.movie) {
                print_movie_frames_up_to_time(data_header.timestamp);
            }
        }
        return ReadFromBuffer(out, n);

/*
		int i;
		char buf[1];

		if (vncLogTimeStamp) {
			long tell = ftell(vncLog);

			static unsigned long rframe_curr = 0; // frame counter for verification
			unsigned int rframe;

			static struct timeval prev;
			struct timeval tv;

			i = fread (&rframe, sizeof (rframe), 1, vncLog);

			if (i < 1) { return False; }

			rframe = Swap32IfLE(rframe);

			if (rframe != rframe_curr) {
				fprintf(stderr, "current frame %u read frame %u at time %.3f @ offset %ld\n",
                      rframe_curr, rframe, tv.tv_sec + tv.tv_usec / 1e6, tell);
				fprintf(stderr, "Frame number does not match! File desynced or corrupt!.\n");
				abort();
			}

			++rframe_curr;

			i = fread (&tv, sizeof (struct timeval), 1, vncLog);

			if (i < 1) { return False; }

			tv.tv_sec = Swap32IfLE (tv.tv_sec);
			tv.tv_usec = Swap32IfLE (tv.tv_usec);

			// This looks like the best way to adjust time at the moment. 
			if (!appData.movie && prev.tv_sec) { // print the movie frames as fast as possible	  
				struct timeval diff = timeval_subtract (tv, prev);
				sleep (diff.tv_sec);
				usleep (diff.tv_usec);
			}
			prev = tv;

			if (appData.debugFrames) {
    	          fprintf(stderr, "read frame %u at time %.3f @ offset %ld\n",
    	                  rframe, tv.tv_sec + tv.tv_usec / 1e6, tell);
			}
			if(appData.movie) { print_movie_frames_up_to_time(tv); }
		}

		i = fread (out, 1, n, vncLog);		
		if (i < 0) {
			return False;
		}
		else {
			return True;
		}
*/
	}

	if (n <= buffered) {
		memcpy(out, bufoutptr, n);
	    if (appData.record) {
			writeLogHeader (); /* writes the timestamp */
			fwrite (bufoutptr, 1, n, vncLog);
    	}
	    bufoutptr += n;
    	buffered -= n;
	    return True;
	}

	memcpy(out, bufoutptr, buffered);
	if (appData.record) {
		writeLogHeader (); /* Writes the timestamp */
		fwrite (bufoutptr, 1, buffered, vncLog);
	}

	out += buffered;
	n -= buffered;

	bufoutptr = buf;
	buffered = 0;

	if (n <= BUF_SIZE) {

		while (buffered < n) {
			int i = read(rfbsock, buf + buffered, BUF_SIZE - buffered);
			if (i <= 0) {
				if (i < 0) {
					if (errno == EWOULDBLOCK || errno == EAGAIN) {
						ProcessXtEvents();
						i = 0;
					} 
					else {
						fprintf(stderr,"%s",programName);
						perror(": read");
						return False;
					}
				} 
				else {
					if (errorMessageOnReadFailure) {
						fprintf(stderr,"%s: VNC server closed connection\n",programName);
					}
					return False;
				}
			}
			buffered += i;
		}

		memcpy(out, bufoutptr, n);
		if (appData.record) {
			fwrite (bufoutptr, 1, n, vncLog);
		}
		bufoutptr += n;
		buffered -= n;
		return True;

		} 
		else {
			while (n > 0) {
			int i = read(rfbsock, out, n);
			if (i <= 0) {
				if (i < 0) {
					if (errno == EWOULDBLOCK || errno == EAGAIN) {
						ProcessXtEvents();
						i = 0;
					} 
					else {
						fprintf(stderr,"%s",programName);
						perror(": read");
						return False;
					}
				} 
				else {
					if (errorMessageOnReadFailure) {
						fprintf(stderr,"%s: VNC server closed connection\n",programName);
					}
					return False;
				}
			}
			else {
				if (appData.record) {
					fwrite (out, 1, i, vncLog);
				}
			}
			out += i;
			n -= i;
		}

		return True;
	}
}


/*
 * Write an exact number of bytes, and don't return until you've sent them.
 */

Bool
WriteExact(int sock, char *buf, int n)
{
  fd_set fds;
  int i = 0;
  int j;

  if (appData.play || appData.movie)
    return True;

  while (i < n) {
    j = write(sock, buf + i, (n - i));
    if (j <= 0) {
      if (j < 0) {
	if (errno == EWOULDBLOCK || errno == EAGAIN) {
	  FD_ZERO(&fds);
	  FD_SET(rfbsock,&fds);

	  if (select(rfbsock+1, NULL, &fds, NULL, NULL) <= 0) {
	    fprintf(stderr,"%s",programName);
	    perror(": select");
	    return False;
	  }
	  j = 0;
	} else {
	  fprintf(stderr,"%s",programName);
	  perror(": write");
	  return False;
	}
      } else {
	fprintf(stderr,"%s: write failed\n",programName);
	return False;
      }
    }
    i += j;
  }
  return True;
}


/*
 * ConnectToTcpAddr connects to the given TCP port.
 */

int
ConnectToTcpAddr(unsigned int host, int port)
{
  int sock;
  struct sockaddr_in addr;
  int one = 1;

  addr.sin_family = AF_INET;
  addr.sin_port = htons(port);
  addr.sin_addr.s_addr = host;

  sock = socket(AF_INET, SOCK_STREAM, 0);
  if (sock < 0) {
    fprintf(stderr,"%s",programName);
    perror(": ConnectToTcpAddr: socket");
    return -1;
  }

  if (connect(sock, (struct sockaddr *)&addr, sizeof(addr)) < 0) {
    fprintf(stderr,"%s",programName);
    perror(": ConnectToTcpAddr: connect");
    close(sock);
    return -1;
  }

  if (setsockopt(sock, IPPROTO_TCP, TCP_NODELAY,
		 (char *)&one, sizeof(one)) < 0) {
    fprintf(stderr,"%s",programName);
    perror(": ConnectToTcpAddr: setsockopt");
    close(sock);
    return -1;
  }

  return sock;
}



/*
 * FindFreeTcpPort tries to find unused TCP port in the range
 * (TUNNEL_PORT_OFFSET, TUNNEL_PORT_OFFSET + 99]. Returns 0 on failure.
 */

int
FindFreeTcpPort(void)
{
  int sock, port;
  struct sockaddr_in addr;

  addr.sin_family = AF_INET;
  addr.sin_addr.s_addr = INADDR_ANY;

  sock = socket(AF_INET, SOCK_STREAM, 0);
  if (sock < 0) {
    fprintf(stderr,"%s",programName);
    perror(": FindFreeTcpPort: socket");
    return 0;
  }

  for (port = TUNNEL_PORT_OFFSET + 99; port > TUNNEL_PORT_OFFSET; port--) {
    addr.sin_port = htons((unsigned short)port);
    if (bind(sock, (struct sockaddr *)&addr, sizeof(addr)) == 0) {
      close(sock);
      return port;
    }
  }

  close(sock);
  return 0;
}


/*
 * ListenAtTcpPort starts listening at the given TCP port.
 */

int
ListenAtTcpPort(int port)
{
  int sock;
  struct sockaddr_in addr;
  int one = 1;

  addr.sin_family = AF_INET;
  addr.sin_port = htons(port);
  addr.sin_addr.s_addr = INADDR_ANY;

  sock = socket(AF_INET, SOCK_STREAM, 0);
  if (sock < 0) {
    fprintf(stderr,"%s",programName);
    perror(": ListenAtTcpPort: socket");
    return -1;
  }

  if (setsockopt(sock, SOL_SOCKET, SO_REUSEADDR,
		 (const char *)&one, sizeof(one)) < 0) {
    fprintf(stderr,"%s",programName);
    perror(": ListenAtTcpPort: setsockopt");
    close(sock);
    return -1;
  }

  if (bind(sock, (struct sockaddr *)&addr, sizeof(addr)) < 0) {
    fprintf(stderr,"%s",programName);
    perror(": ListenAtTcpPort: bind");
    close(sock);
    return -1;
  }

  if (listen(sock, 5) < 0) {
    fprintf(stderr,"%s",programName);
    perror(": ListenAtTcpPort: listen");
    close(sock);
    return -1;
  }

  return sock;
}


/*
 * AcceptTcpConnection accepts a TCP connection.
 */

int
AcceptTcpConnection(int listenSock)
{
  int sock;
  struct sockaddr_in addr;
  int addrlen = sizeof(addr);
  int one = 1;

  sock = accept(listenSock, (struct sockaddr *) &addr, &addrlen);
  if (sock < 0) {
    fprintf(stderr,"%s",programName);
    perror(": AcceptTcpConnection: accept");
    return -1;
  }

  if (setsockopt(sock, IPPROTO_TCP, TCP_NODELAY,
		 (char *)&one, sizeof(one)) < 0) {
    fprintf(stderr,"%s",programName);
    perror(": AcceptTcpConnection: setsockopt");
    close(sock);
    return -1;
  }

  return sock;
}


/*
 * SetNonBlocking sets a socket into non-blocking mode.
 */

Bool
SetNonBlocking(int sock)
{
  if (fcntl(sock, F_SETFL, O_NONBLOCK) < 0) {
    fprintf(stderr,"%s",programName);
    perror(": AcceptTcpConnection: fcntl");
    return False;
  }
  return True;
}


/*
 * StringToIPAddr - convert a host string to an IP address.
 */

Bool
StringToIPAddr(const char *str, unsigned int *addr)
{
  struct hostent *hp;

  if (strcmp(str,"") == 0) {
    *addr = 0; /* local */
    return True;
  }

  *addr = inet_addr(str);

  if (*addr != -1)
    return True;

  hp = gethostbyname(str);

  if (hp) {
    *addr = *(unsigned int *)hp->h_addr;
    return True;
  }

  return False;
}


/*
 * Test if the other end of a socket is on the same machine.
 */

Bool
SameMachine(int sock)
{
  struct sockaddr_in peeraddr, myaddr;
  int addrlen = sizeof(struct sockaddr_in);

  if (appData.play || appData.record || appData.movie)
    return False;

  getpeername(sock, (struct sockaddr *)&peeraddr, &addrlen);
  getsockname(sock, (struct sockaddr *)&myaddr, &addrlen);

  return (peeraddr.sin_addr.s_addr == myaddr.sin_addr.s_addr);
}


/*
 * Print out the contents of a packet for debugging.
 */

void
PrintInHex(char *buf, int len)
{
  int i, j;
  char c, str[17];

  str[16] = 0;

  fprintf(stderr,"ReadExact: ");

  for (i = 0; i < len; i++)
    {
      if ((i % 16 == 0) && (i != 0)) {
	fprintf(stderr,"           ");
      }
      c = buf[i];
      str[i % 16] = (((c > 31) && (c < 127)) ? c : '.');
      fprintf(stderr,"%02x ",(unsigned char)c);
      if ((i % 4) == 3)
	fprintf(stderr," ");
      if ((i % 16) == 15)
	{
	  fprintf(stderr,"%s\n",str);
	}
    }
  if ((i % 16) != 0)
    {
      for (j = i % 16; j < 16; j++)
	{
	  fprintf(stderr,"   ");
	  if ((j % 4) == 3) fprintf(stderr," ");
	}
      str[i % 16] = 0;
      fprintf(stderr,"%s\n",str);
    }

  fflush(stderr);
}
