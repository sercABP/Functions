/******************************************************************************
* FILE: condvar.c
* DESCRIPTION:
*   Example code for using Pthreads condition variables.  The main thread
*   creates three threads.  Two of those threads increment a "count" variable,
*   while the third thread watches the value of "count".  When "count"
*   reaches a predefined limit, the waiting thread is signaled by one of the
*   incrementing threads. The waiting thread "awakens" and then modifies
*   count. The program continues until the incrementing threads reach
*   TCOUNT. The main program prints the final value of count.
* SOURCE: Adapted from example code in "Pthreads Programming", B. Nichols
*   et al. O'Reilly and Associates.
* LAST REVISED: 10/14/10  Blaise Barney
* FURTHER MODIFIED June 2016 William Valliant for ABP project and multithreading multiple programs
* 6/23/2016 added GNC code that Shruthi was working on HI SHRUTHI!
* variable t changed to tt in order to keep from running into a double definition of t (for GNC)
*
* superseedes autorun and will replace it when done copying over the pozyx localization stuff
* 8/8/2016 CLEANING THIS UP AND MAKING SURE THAT YOU WILL HAVE ALL OF YOUR SERIAL STREAMS WORKING AT THE SAME TIME IN THEIR OWN ENVIRONMENTS
* 8/8/2016 IMPORTING NS_DIAGNOSTIC_FOR_ALL_STARS_9.C -WV V BASIC_FUNCTION_PROGRAM 0.002.C
* 8/22/2016 Starting over, deleting everything and starting with just creating threads, V0.003 WV
* v.003 is the skeleton used for the basic functions of the ABP WV
* V.004 is where I start putting in RTC, RTC_ALARM_CLOCKS
* modified working on alarmclock to ensure that I can flag events as they come due
* added global function called setalarmfor that puts a time from now and a position in the timetime buffer to go off
* V.005 is start of bringing NS_diagnostic_all stars 20.c into this function and seperating the serial portion from the analysis portion
* 8/24/2016 begin import of NS and figuring out how to split up the program V.006
*got the NS utility function imported into the real time environment and am ready to test performance of clock at work tomorrow v.008
* 8/25/2016 v.009 removing unused variables or demoting them from globals (that came in from NS diagnostic v20)
*v.009 commented out abounch of stuff using #defines
*8/30/2016 v.010 Working on getting the ADC functionality added WV
* V 0.011 Need to add an flag for the ADC thread and others to use to tell the ADC
* also looking at queue and sorting for RTC -WV
* V 0.012 Now looking into bringing in the RCS functions -wv
* V 0.013 imported the RCS valve portion, now looking on how to incorporate this with the event scheduler and valve commands -wv
*V 0.014 cleaned up the thread creat environment so that you are not just using the thread[0]
* V 0.015 looking on how to incorporate RCS with an event scheduler and valve commands probably will add another thread called SCHEDULER -WV
*V 0.016 avoided working on the SCHEDULER and decided to work next on the IMU
*V 1.000 meshed pozyx initialize and pozyx get data threads into the basic functions thread. the functions were taken from gyro_gnc.c - 6/14/2017
*V 1.002 meshed more functions that are necessary to run pozyx initialization
    eg. set_interface_attribs, and timer(), kalman_filter, and all gnc functions and nav functions. 6/14/2017
*V 1.004 code compiles with new threads eg. pozyx, IMU, and GNC threads. in order for code to compile matrix operations in GNC thread needed to be
    moved above their implementations. 6/14/2017
******************************************************************************/

/**************************************************FLAG and INTERRUPT Keys along with other helpfull information
 * RTC starts up and populates billytime[] sets flag[0] to let alarmclock to check the fresh clock reading
 * alarm_clock starts up and checks to see if any alarms have been set sets flag[0] to let RTC
 * FLAGS[] 0 is fresh reading from RTC query in RTC thread [1] is check RCS pressure [2] is check fuel tank for low pressure [3] is data added to the schedule
 * FLAGS[] more information on what the positions do and what kind of values are used for them
 * 0 if 1, the RTC just got queried and has populated billytime[] 0 if alarmclock thred has already checked the allarms buffer with whatever it got and is now waiting on a new reading from RTC
 * 1 if 1, there is a request for a pressure reading through the ADC connected to the low pressure manifold that is hooked up to the RCS
 * 2 if 1, there is a request for a pressure reading through the ADC connected to the fuel tank (values from high pressure side are pegged until the paintball tank is almost out of air)
 * 3 if 1, there is at least one open valve on the RCS system
 * 4 if 1, there has been another event scheduled and you need to run some kind of event sorter to ensure that the scheduled event gets queued up correctly
 *
 * FLAGS (NS_POINTER + 0) is average flag (NS_POINTER + 1) is fresh data has been coppied into the DIGEST_NS buffer from the FIFO_NS buffer
 * FLAGS[(NS_POINTER plus #) is [0] is averageFLAG [1] is reportendFLAG [2] is transferFLAG [3] crc flag [4] minimum threshold flag for intensities from stars [5] fresh averaged or rolling averaged data for star alanysis flag
 *	FLAGS[(NS_POINTER plus #) [6] data is now fresh for NS_DATA thread  [7] split between angles flag from the corrected angle data indicating that the heading is either near 0 deg or there is a problem with star perception
 * MORE INFO ON HOW the NS_POINTER flags work and what kind of values may be in them:
 * NS_POINTER + 0 if 1 there is a fresh reading from the report end parser, the parser has already coppied what was read and put it into the DIGEST_NS[] buffer for the rolling average function to use
 * NS_POINTER + 1 if 1 there is fresh data
 * NS_POINTER + 2	if 1 there is fresh data
 * NS_POINTER + 3 if 0 there is a problem with the crc otherwise the value of this flag will be the most current CRC check
 * NS_POINTER + 4 1 if you have at least one bat minimum threshold check or 0 if you are good for min threshold on all four stars
 * NS_POINTER + 5 1 for fresh averaged data 0 for waiting on new data (this comes from rolling average once it has a full history and a fresh rolled average to report)
 * NS_POINTER + 6 1 if you have your current iteration location and heading 0 if NS_data thread is waiting on new data
 * NS_POINTER + 7 1 if there was a problem with some of the stars relative corrected angles 0 if your in normal operation
 *
 *  INTERRUPTS[] 0 is master kill signal----------------------------------
 * 0 : if master kill signal is == 1 then break out of your infinite loop and close your thread after safteying anything needed
 * 1: indicates that the alarm_clock thread just found an event  that came due and the value will go from idle 0 to i which is a number representing the timetime[] event number that just went off
 * 2: if 1, the low fuel light has just turned on for your vehicle indicating that you should begin RTB (return to base) procedures
 *
 * TIMETIME_MASKS[MAXBUFF] is used to let the alarm_clock thread know if it should be checking within the scheduled event list for a time comparison value is 1 if there is no need to check times against RTC
 *
 * */

//include libraries here
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <wiringPi.h> //used for adc's, digital pins for RCS
#include <wiringSerial.h>//used for uart communications for NS,
#include <errno.h>
#include <fcntl.h>
#include <string.h>
#include <termios.h>
#include <unistd.h>
#include <time.h>
#include <unistd.h>


//Switches to change outputs to the monitor or whatnot------------------------------------------------------------------------------------------------------------------------
#define print_threads //comment this out if you don't need to see how your threads are starting and stopping
#define show_killtime //define show_rtc //shows every query to the RTC
#define KILLTIME 30 //how many seconds to kill the whole program for test running to see if the RTC portion of the code is working
//#define show_raw_ns //prints out the received buffer of the NS system
//#define report_constelation_geometry //prints out the dimensions of the square discribed by the stars on the roof
//#define report_raws_from_stars
//#define report_raw_polars //used to look at the polar vector information from the stars as seen by the sensor after figuring out the heading angle in order to despin the constelation
//#define report_agreeing_corrected_relative_angles
//#define report_found_splits_between_angle_agreement
#define show_pressures


//---------------settings that affect sensor thresholds------------------------------------------------------------------------------------------------------------------------
#define THREADS 12         //EDIT - JA changed this number from 10 to 12 to include the GNC THREAD, Pozyx_Serial, IMU_Serial
#define MININTENSITY 3100 //this is the star intensity minimum that if a value comes in under it, that batch of data gets erased and you wait for a fresh reading
#define NUMAVERAGE 4 //number of samples to average before spitting out a value MAXIMUM value is 254/2 (just say 75 to keep the buffer from constantly having to be coppied in rolling_average())

//all of your pointers for the various buffers
#define NS_POINTER 30 //pointer for the flags buffer so that you can copy the code into here and stack all of the various flags[] into one heap
#define IMU_POINTER 30 // added 3/3/2017 by JA. this pointer is for the flags buffer in order to copy the data into here and stack the various flags[] into one heap

//put your definitions here-------------------------------------------------------------------------------------------------------------------------------------------------------------------
#define MAX_BUFFER 255 //value for my arrays maximum size
#define _POSIX_C_SOURCE 200809L //need this def for the RTC clock to work
#define RTC_QUERY_TICK_WAIT_TIME 300 //this is a usleep(###) value at the end  of the infinite for loop grabbing the RTC and putting it into billytime[0](sec) and billytime[1] (milli)
#define KILL_RTC_QUERY_TICK_WAIT_TIME 300 //this is a usleep(###) value at the end  of the infinite for loop grabbing the RTC and putting it into billytime[0](sec) and billytime[1] (milli)
#define MINIMUM_SOLENOID_LATENCY 10000 //should be 10 ms and this us used in a usleep(10000) command in ADC loop
#define RAD_to_DEG 57.29577951
#define MIN_FUEL 500 //minimum fuel level which will lead to a low fuel light turing on
#define PORT_ADC1   0   // ADC.AIN0 0 to 200 psi pressure transducer 1015 if not connected
#define PORT_ADC2   1   // ADC.AIN1 0 to 500 psi pressure transducer 1015 if not connected
#define ADC1_TO_PSI	4.6 //ballpark conversion of analog value to psi this is the manifold for the RCS system on the low side
#define ADC2_TO_PSI	1.5 //ballpark conversion of analog value to psi this is the high side of the system and should be pegged until the air tank is almost exhausted
#define Y_final 2.15
#define X_final 1.42
#define pi 22/7
#define t 0.1

#define ON 1
#define OFF 0
//define the pin numbers on the ODROID GPIO that get used for running the valve relay signals
#define T1 0
#define T2 2
#define T3 3
#define T4 4
#define T5 5
#define T6 6
#define T7 26
#define T8 27


#define SAFETYOFF VALVECOMMANDBUFFER[0] = 1;
#define SAFETYON VALVECOMMANDBUFFER[0] = 0;
//#define FWD 2,5
#define FWD_ON VALVECOMMANDBUFFER[2] = VALVECOMMANDBUFFER[5] = 1;
#define FWD_OFF VALVECOMMANDBUFFER[2] = VALVECOMMANDBUFFER[5] = 0;
//#define REV 1,6
#define REV_ON VALVECOMMANDBUFFER[1] = VALVECOMMANDBUFFER[6] = 1;
#define REV_OFF VALVECOMMANDBUFFER[1] = VALVECOMMANDBUFFER[6] = 0;
//#define SLEFT 8,3
#define SLEFT_ON VALVECOMMANDBUFFER[8] = VALVECOMMANDBUFFER[3] = 1;
#define SLEFT_OFF VALVECOMMANDBUFFER[8] = VALVECOMMANDBUFFER[3] = 0;
//#define SRIGHT 7,4
#define SRIGHT_ON VALVECOMMANDBUFFER[7] = VALVECOMMANDBUFFER[4] = 1;
#define SRIGHT_OFF VALVECOMMANDBUFFER[7] = VALVECOMMANDBUFFER[4] = 0;
//#define RLEFT 2,6 //or 4,8 works
#define RLEFT_ON VALVECOMMANDBUFFER[2] = VALVECOMMANDBUFFER[6] = 1;
#define RLEFT_OFF VALVECOMMANDBUFFER[2] = VALVECOMMANDBUFFER[6] = 0;

//#define RRIGHT 1,5 // or 3,7 works
#define RRIGHT_ON VALVECOMMANDBUFFER[1] = VALVECOMMANDBUFFER[5] = 1;
#define RRIGHT_OFF VALVECOMMANDBUFFER[1] = VALVECOMMANDBUFFER[5] = 0;




//put your global chars here------------------------------------------------------------------------------------------------------------------------------------------------------------------
char sendbuff_NS [MAX_BUFFER]={0};
char rcvbuff_NS[MAX_BUFFER] = {0};
char FIFO_NS [MAX_BUFFER]={0}; //buffer for the loop part of decoding

char DIGEST_NS [MAX_BUFFER]={0};
//put your global ints here-------------------------------------------------------------------------------------------------------------------------------------------------------------------
extern unsigned int sleep(); // needed to call this out for some reason to make it work...
int usleep(); // needed to call this out for some reason to make it work...
int FLAGS[MAX_BUFFER] = {0}; //[0] is for RTC to pass to RTC_KILL [1] NS initialization [2-9] Open [10] averageFLAG [11] reportendFLAG [12] transferFLAG [20 - 26] Kill autopilots set by killRTC
int INTERUPTS[MAX_BUFFER] = {0}; //[0] is to kill the infinite for loop in the RTC [1] is to kill the Serial stream from NS and shut it down [2] is open
int TIMETIME_MASKS [MAX_BUFFER] = {1};//mask for alarmclock query started with all queries masked
int TIMETIME_FLAGS [MAX_BUFFER] = {0};//makes sure that there are no initial alarmclocks going off these switch to 1 when due

//int     count = 0;//I think this was for threading


int averaged_x[MAX_BUFFER] = {0};// globals for outputing the averaged data from rolling average ()
int	averaged_y[MAX_BUFFER] = {0};
int	averaged_intens[MAX_BUFFER] = {0};



signed short numberx [20] = {0};
signed short numbery [20] = {0};
//signed short xposition;//variables for DIGEST_NS_3() including sensor position and theta;
//signed short yposition;
signed long intens[20] = {0};

int FIFO_NSpointer = 0; // FIFO_NSpointer for where to put stuff in the FIFO_NS in the loop part of decoding

int current_centerpoint_x;//populated by star_analysis after averaging all the x positions in order to get the center of the observed stars
int current_centerpoint_y;//populated by star_analysis after averaging all the x positions in order to get the center of the observed stars
int displaced_centerpoint_x;// after subtracting the current_centerpoint found from the center of the table
int displaced_centerpoint_y;


static int adcValue1 = 0;//variables for the ADCs
static int adcValue2 = 0;

int VALVECOMMANDBUFFER[9] = {0}; //buffer that is used by SERVICEVALVECOMMANDBUFFER() in order to know if a valve needs to be turned on or off
//VALVECOMMANDBUFFER [1] through [8] used for valves T1 through T8		VALVECOMMANDBUFFER[0] is used as a safety and the SERVICEVALVECOMMANDS won't work if it is == 0
int VALVEFLAGBUFFER[9] = {0}; // buffer that is used to know if a valve is currently turned on or off in SERVICEVALVECOMMANDS
//a valveflagbuffer value of 1 indicates that the valve is currently firing and this information is used by the USER_INPUTS thread setcommand() to toggle the calles using the above defined valvecommands



int toavgx[MAX_BUFFER] = {0};  //ACTIVELY USED FOR AVERAGE_1
int toavgy[MAX_BUFFER] = {0};
int toavgintens[MAX_BUFFER] = {0};

int numtimesglobalcounter = 0; //initialized counter for my averaging of x y and theta rev 1
int DIGEST_NSsize = 0;


//put your global floats here-------------------------------------------------------------------------------------------------------------------------------------------------------------------

float TIMETIME[MAX_BUFFER] = {0}; //used to store the RTC query in the KILL_RTC() for comparison to current RTC value in billytime[0]
//TIMETIME [0] is the time in seconds.milliseconds TIMETIME[1] is the time in seconds and [2] is the time in milliseconds [20-26 are kill times for rcs autopilot]
float billytime[3] = {0}; //have a global for time slots [second], [millisecond] count this is used by runclock which populates it with gettime.c
//billytime is populated by an RTC query in RTC_STUFF and is structured like TIMETIME[]
float global_heading_NS = 0.00; //heading data from the NS after being analyzed
float global_x_NS[18] ={0};//global position fix data from NS after being analyzed value of interest is 18 after the star analysis program populates it look for a FLAGS[NS_pointer +6] to pop from 0 to 1 for fresh readings
float global_y_NS[18] ={0};

float Pozyx[4];
float PV[3];
float theta_bias=0;
float ax_bias=0, ay_bias=0, gyro_bias=0;//used to adjust values before placing them in the IMU array
float IMU[3];//the x, y, and theta values respectively are stored in this array
float IMU_control[2];
float Epoch=0;
float phi=0;        //used in the kalman filter function in GNC thread



pthread_mutex_t count_mutex;							//this is the lock for count_mutex
pthread_cond_t count_threshold_cv;

//any global functions that you will be calling-------------------------------------------------------------------------------------------------------------------------------------------------------------------
int SET_ALARM_FOR(int timetime_position, float time_to_go_off)//just used to put an event in the TIMETIME[] buffer as well as set the query mask for it for the alarm_clock thread
{
	//turn off query mask
	TIMETIME_MASKS[timetime_position] = 0; //no longer query for the event until another alarm is set for it
	//mark current time plus alarm time by putting alarm time into TIMETIME[timetime_position]
	TIMETIME[timetime_position] = ((billytime[0]) + (time_to_go_off));//copy the real time clock at start of this thread sec


	return 0;
}



//begin of your threads-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
void *BLANK_THREAD(void *id) 								//blank thread to copy from (don't forget that whatever you make you have to call in main() under the p_thread_create portion AND ++ #define THREADS)
{

  int my_id = (int)id;
#ifdef print_threads
printf("%d\t Started \n",my_id);
#endif
    sleep(1);
#ifdef print_threads
printf("\n%d\t Ended \n",my_id);
#endif

  pthread_exit(NULL);
}


void *RTC(void *id) 								//Basic RTC query that happens every 300 useconds
{

  int my_id = (int)id;
#ifdef print_threads
printf("%d\t Started \n",my_id);
#endif


// THREAD STUFF______________________END

//RTC STUFF_________________________________initializations____________


	struct timespec spec;

//RTC STUFF_________________________________initializations____________END
					//unlock the mutex count_mutex
   //RTC STUFF_________________sub-routines__________________


int gettime ()
{


	//this function is used to query the RTC and then put the info into a global array called billytime.
	//extern int billytime[];



	clock_gettime(CLOCK_MONOTONIC, &spec);

    billytime[1] = spec.tv_sec;							//I think they are using tv_sec
    billytime[2] = (round(spec.tv_nsec / 1.0e6)); // Convert nanoseconds to milliseconds    // I think they are using tv_nsec
		//if (pacemakercheck ==1) {TIMETIME[2] = billytime[2];} //for troubleshooting to see if the sampling rate is fast enough to catch every millisecond query other part of this is in KILL_RTC
	billytime[0] = billytime[1] + ((billytime[2])/1000);


	#ifdef show_rtc

	printf("\n%d \t got billytime \n	TOTAL %f	SECOND %f  MS %f\n", my_id, billytime[0], billytime[1], billytime[2]);
	#endif





    return 0;
}



for(;;)
{
	usleep(RTC_QUERY_TICK_WAIT_TIME);

	gettime();

		if (INTERUPTS[0] == 1)
		{
		printf("\nRTC_STUFF(): thread %d \n", my_id);
		printf("\n\nBROKE with RTC of %f \n\n", billytime[0]);
		break;
		}
	FLAGS[0] = 1; //set clock ready to be compared flag


}

//end of thread exit strategy stuff_______________________________________

// THREAD STUFF______________________END

//RTC STUFF_________________________________initializations____________



//RTC STUFF_________________________________initializations____________END
					//unlock the mutex count_mutex



#ifdef print_threads
printf("\n%d\t Ended \n",my_id);
#endif

  pthread_exit(NULL);
}

void *RTC_ALARM_CLOCKS(void *id) 								//alarm_clock looks at timestamps in TIMETIME[] compared to Billytime[] for expirity if so pops a flag and re-masks task time stamp query
{

  int my_id = (int)id;
  int i;//counter for billytime
#ifdef print_threads
 printf("%d\t Started \n",my_id);
 #endif

if (FLAGS[0] == 0)//wait a tick for the RTC to get going
{usleep (KILL_RTC_QUERY_TICK_WAIT_TIME*5);}

  TIMETIME[0] = ((billytime[0]) + (KILLTIME));//This is the alarm clock for killing the whole program and when it comes due, INTERRUPTS[0] gets set to 0 indicating that all threads exit
  printf("\n\nINITIAL TIME WAS        %f\n", billytime[0]);
  printf("\n\nKILL TIME programed WAS %f\n", TIMETIME[0]);

  void put_all_masks()//for whatever reason, when I initialized the array TIMETIME_MASKS = {1} it didn't set all to 1
 {
	for (i=0;i<MAX_BUFFER;++i)
	{
	TIMETIME_MASKS[i] = 1; //no longer query for the event until another alarm is set for it
	}
}

put_all_masks();//function that makes SURE that all of your positions in TIMETIME_MASKS are 1
  SET_ALARM_FOR(1,5.005);//just check to make sure that your alarm clock buffer and mask system is working




  for (;;)//infinite for loop looking to see if the monotonic clock time from the RTC at time start of thread + some ammount of seconds + some ammount of milliseconds is met
	{

		if(FLAGS[0] == 1) // FLAGS[0] is turned to 1 when RCT_CLOCK_STUFF loop gets a fresh time
		{

			//check_rcs_kills(); //this is the program that checks to see if any of the valve commands coming from the autopilot need to be turned off
			for (i = 1;i < MAX_BUFFER;++i)//check all of your timestamps to see if you need to set off any time alarms
		{
				if (TIMETIME[0] <= billytime[0]) //allways check to see if you have a master timeout
				{
				#ifdef show_killtime
				printf("\n %d\tKILLED WITH A billytime TOTAL %f	\n", my_id, billytime[0]);
				printf("\n%d \t got billytime \n	TOTAL %f	SECOND %f  MS %f\n", my_id, billytime[0], billytime[1], billytime[2]);
				#endif



				INTERUPTS[0] = 1;//Master KILL signal
				FLAGS[0] = 0;// puts down the new clock data flag

				break;

				}
				if (TIMETIME_MASKS[i] == 0)//if the mask is turned off for the current TIMETIME[i] slot, check to see if the time has come up yet
				{
					if (TIMETIME[i] <= billytime[0]) //compare the current timestamp to the current time and if it has expired, set your alarm
					{
					#ifdef show_killtime
					printf("\n %d\t TASK %d Just came due with billytime of %f	\n", my_id, i, billytime[0]);
					//printf("\n%d \t got billytime \n	TOTAL %f	SECOND %f  MS %f\n", my_id, billytime[0], billytime[1], billytime[2]);
					#endif


					TIMETIME_FLAGS[i] = 1; //this is your "ding" noise for whatever you needed to listen to time for an alarm
					TIMETIME_MASKS[i] = 1; //no longer query for the event until another alarm is set for it
					INTERUPTS[1] = i; //change value of INTERUPTS[1] from idle 0 to event i has come due

					FLAGS[0] = 0;// puts down the new clock data flag

					}

				}
			}//end for timestamp loop
		}

	FLAGS[0] = 0;// puts down the new clock data flag
	if (INTERUPTS[0] == 1 )//if you have set the master kill flag because FLAGS[0] was turned high break out of this loop
			{
			break;
			}
	usleep(KILL_RTC_QUERY_TICK_WAIT_TIME);
	}




#ifdef print_threads
printf("\n%d\t Ended \n",my_id);
#endif
  pthread_exit(NULL);
}


void *Pozyx_Serial_Port(void *id) 								//
{
  int my_id = (int)id;
#ifdef print_threads
printf("%d\t Started \n",my_id);
#endif

char fc;
int k; char temp;

//------------------------------------Begin-pozyx initialize--------------------
	//note pozyx is designated to port 0. To ensure the the hardware recognizes
	//pozyx is actually in port 0 you need to connect it to the odroid BEFORE
	//connecting the IMU
	if ((fc = serialOpen ("/dev/ttyACM0", 115200)) < 0)
	{
		fprintf (stderr, "Unable to open serial device: %s\n", strerror (errno)) ;
	}

	//Read in data from the serial buffer. Then clear the buffer 600 times
	for (k=0;k<600;k++)
	{
		temp = serialGetchar (fc);
		putchar(temp);
		fflush (stdout) ;
    }
//------------------------------------End-pozyx initialize--------------------




//------------------------------------Begin-pozyx get_data--------------------

int set_interface_attribs(int fd, int speed)
{
    struct termios tty;

    if (tcgetattr(fd, &tty) < 0) {
        printf("Error from tcgetattr: %s\n", strerror(errno));
        return -1;
    }

    cfsetospeed(&tty, (speed_t)speed);
    cfsetispeed(&tty, (speed_t)speed);

    tty.c_cflag |= (CLOCAL | CREAD);    /* ignore modem controls */
    tty.c_cflag &= ~CSIZE;
    tty.c_cflag |= CS8;         /* 8-bit characters */
    tty.c_cflag &= ~PARENB;     /* no parity bit */
    tty.c_cflag &= ~CSTOPB;     /* only need 1 stop bit */
    tty.c_cflag &= ~CRTSCTS;    /* no hardware flowcontrol */

    /* setup for non-canonical mode */
    tty.c_iflag &= ~(IGNBRK | BRKINT | PARMRK | ISTRIP | INLCR | IGNCR | ICRNL | IXON);
    tty.c_lflag &= ~(ECHO | ECHONL | ICANON | ISIG | IEXTEN);
    tty.c_oflag &= ~OPOST;

    /* fetch bytes as they become available */
    tty.c_cc[VMIN] = 1;
    tty.c_cc[VTIME] = 1;

    if (tcsetattr(fd, TCSANOW, &tty) != 0) {
        printf("Error from tcsetattr: %s\n", strerror(errno));
        return -1;
    }
    return 0;
}

double timer(void)
{
	long ns;
	double t_ns;
	double time;

	struct timespec spec;
	clock_gettime(CLOCK_REALTIME, &spec);

	ns = round(spec.tv_nsec);
	t_ns = ns;
	time = spec.tv_sec + (t_ns/1e9) - Epoch;

	//unsigned long time_in_micros = 100000 * s + spec.tv_usec;

	return time;
}

for(;;)
{

    char *portname = "/dev/ttyACM0";
    int fd, i,k=0,j=0, pozyx_len;
    char buf[1000];
    char pozyx_buf[100]={0};
    int readlen, start;
    char x[5], y[5], theta[5];
    int nx=0,ny=0,nt=0;
    long int X=0, Y=0, angle =0;
    float pozyx_timestamp=0;
    float angleo=0;

    fd = open(portname, O_RDWR | O_NOCTTY | O_SYNC);
    if (fd < 0)
    {
        printf("Error opening %s: %s\n", portname, strerror(errno));
	}
    //fd = serialOpen(&portname, 115200);    //hardcoded solution for set_interface_attribs
    //baudrate 115200, 8 bits, no parity, 1 stop bit
    set_interface_attribs(fd, B115200);
    //set_mincount(fd, 0);                /* set to pure timed read */


    readlen = read(fd, buf, sizeof(buf) - 1);
    printf("Readlen is: %d" , readlen);
	if (readlen > 0)
	{
		buf[readlen] = 0;
        pozyx_timestamp = timer(); //billytime[0]; // in shruthi's code billtime[0] replaced timer() -- need to verify that this is the correct timer to use.

		for(i=0;i<readlen;i++)
		{
			printf("BUF[%d] is: %d",i,buf[i]);
		    if(buf[i] == '*')
		    start = i;
		    break;
		}

			for(i= start+1; i<readlen; i++)
            {
				pozyx_buf[j] = buf[i];j++;
				if(buf[i] == '$')
				{
					pozyx_len = j;
					break;
				}
			}

            for(i=0;i<pozyx_len;i++)
		    {
				if(pozyx_buf[i] == ',')
				{
					k=i;
					break;
				}
				else
				{
					x[nx] = pozyx_buf[i];
					//putchar(x[nx]);
					nx++;
				}
		    }

		   X=atoi(x);

		   for(i=k+1;i<pozyx_len;i++)
		   {
				if(pozyx_buf[i] == ',')
				{
					k=i;
					break;
				}
				else
				{
					y[ny] = pozyx_buf[i];
					//putchar(y[ny]);
					ny++;
				}
		    }

		   Y=atoi(y);

		   printf("\n");printf("\n");
		   for(i=k+1;i<pozyx_len;i++)
		   {
				if(pozyx_buf[i] == '$')
				{
					k=i;
					break;
				}
				else
				{
					theta[nt] = pozyx_buf[i];
					//putchar(theta[nt]);
					nt++;
				}
		    }

			angle=atoi(theta);

			if(angle<0 || angle>360)
			angle = angleo;

            printf("Updating Pozyx Array\n");
			Pozyx[0] = X/10;
			Pozyx[1] = Y/10;
			Pozyx[2] = angle - theta_bias;
			Pozyx[3] = pozyx_timestamp;

			angleo=angle;

			for (i=0;i<5;i++)
			{
			   x[i] = 0;
			   y[i] = 0;
			   theta[i] = 0;
			}

			i=0;j=0;k=0;nx=0;ny=0;nt=0;

		   serialClose(fd);
	}

    else if (readlen < 0)
    {
		printf("Error from read: %d: %s\n", readlen, strerror(errno));
    }

    if (INTERUPTS[0] == 1)//if the master kill interrupt is sent, you are to shut down the serial streaming and empty the uart buffer
    {
        break;
    }
}
/* repeat read to get full message */
//------------------------------------End-pozyx get_data----------------------
#ifdef print_threads
printf("\n%d\t Ended \n",my_id);
#endif

  pthread_exit(NULL);
}






void *NS_SERIAL_PORT(void *id) 								//just the serial portion of NS so you can have a reading of current positional data and heading data in a global for consumption by ns_data
{
  int my_id = (int)id;
#define ROOMWATCH 7
#define GETVER 0
#define SETREPORTFLAGS 2 //size is 12 bytes
#define REPORT 3  // size if 4 4th byte is room ID (0 I think)
#define CONTINUOUSREPORT 4 //size is 4
#define KILLREPORT 5
#define SETBAUDRATE 9 //size is 4 (4th byte is baud 0 = 1200 1 = 19200 2 = 57600 3 = 115200 4 = 230400)
#define SETNSAMPLES 14
#define GETNSAMPLES 15 // size is 3

int fd ;
int baud = 1200;
fd = serialOpen ("/dev/ttyS0", baud) ;   // make my handle to call
int crc_checksum = 0;
int length;
int write();

int rolling_toavgx [MAX_BUFFER][MAX_BUFFER] ={ {0},{0}};  //ACTIVELY USED FOR ROLLING_AVERAGE() in NS program
int rolling_toavgy[MAX_BUFFER][MAX_BUFFER] = {{0},{0}};
int rolling_toavgintens[MAX_BUFFER][MAX_BUFFER] ={{0},{0}};

int badcrccount = 0;



char checksum(char input[], int len)
{
    unsigned char sum = 0;
    int i;
    sendbuff_NS[2] = 0;
    for(i = 0; i < len; i++)
    {
        sum += input[i];
    }
    input[2] = sum ^ 0xff;
    //printf("\n checksum counted %d \n", input[2]); // troubleshooting if needed
    return 0;
}

char erasebuffchar(char input[], int value)
{
    int i;

    for(i = 0; i < MAX_BUFFER; i++)
    {
        input[i] = value;
    }

    return 0;
}

int erasebuffint(int input[], int value)
{
    int i;

    for(i = 0; i < MAX_BUFFER; i++)
    {
        input[i] = value;
    }

    return 0;
}
//______________________________

int writebyte (int descriptor, char buffer[])
{
 printf("\nsending \t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t\n\n ", buffer[0], buffer[1], buffer[2], buffer[3], buffer[4], buffer[5],buffer[6], buffer[7], buffer[8], buffer[9], buffer[10], buffer[11]);
  write (descriptor, buffer,length); // use write command to send blah of length 3 to fd

return 0;
}

int readbyte (int descriptor, char buffer[])
{

char i;
i = 0;
int ii;
ii=0;
printf("\nreadbyteloop: \t");
     while (serialDataAvail (descriptor))
     {


		i = (serialGetchar (descriptor));
		printf ("%d\t", i);
		buffer [ii] = (i);
		ii = ii+1;

      fflush (stdout) ;		//this is a system call to empty the buffer
      }



    return 0;
}


int readbyte_cont (int descriptor)
{
//extern char FIFO_NS[];
extern int FIFO_NSpointer;
char i;
i = 0;


     if (serialDataAvail (descriptor))
     {


		i = (serialGetchar (descriptor));
		#ifdef show_raw_ns
		printf ("%d\t", i);
		#endif
		FIFO_NS[FIFO_NSpointer] = (i);
		FIFO_NSpointer = FIFO_NSpointer + 1;


      fflush (stdout) ;		//this is a system call to empty the buffer
    }


    return 0;
}


  //utility that reads the checksum from the input buffer
 int check_input_checksum()
{
    extern char rcvbuff_NS[];
    int sum = 0;
    int val = 0;
    int tosubtract = 0;
    int numtimes256 = 0;
    int checksumgood = 0; //this is your checksum value, there will be a checksum value = whatever the checksum is supposed to be or else a 0 indicating that the checksum did not match
    int i;
    int length = rcvbuff_NS[1];
    //printf("\nlength told to checker %d \n", length);
    for(i = 0; i < (length); i++)
    {
     if ((i != (0)) && (i != (2) ))
		{
        sum += (255 - (rcvbuff_NS[i]));
        //printf("\nI ended at %d  and  SUM came out as %d\n", i, sum);
		}
    }
        //sum = sum + (255 - (rcvbuff_NS[i])); //do one more time in order to get the sum correct

    //printf("\nFINAL I ended at %d  and  SUM came out as %d\n", i, sum);
    val = ((length -2) * 255);
    //printf("\nvalue of all blocks %d \n", val);
    tosubtract = (val - sum);
    //printf("\nvalue to subtract %d \n", tosubtract);
       numtimes256 = tosubtract / 256; //do this as int to drop the remainder

    //printf("roll down the count by 256 times %d  ", numtimes256);
    numtimes256 = numtimes256 * 256;
    //printf("the value to subtract from the value to subtract  %d\n", numtimes256);


    checksumgood = (255-(tosubtract - numtimes256));
    //printf("corrected checksumgood %d \n", checksumgood);


    if (checksumgood != rcvbuff_NS[2])
    {
		checksumgood = 0;
	}

    return (checksumgood);
}
//____________________________________________________________________



int kill_it(int discriptor) //if you have to reset the NS after it has been put into stream mode, this is the routine to break the stream
{

//______________________________________________________________KILL IT
//_____________________________________________________



erasebuffchar (rcvbuff_NS,0); //reset the incoming buffer
erasebuffchar (sendbuff_NS,0); //reset the incoming buffer
length = 3;
//printf("\n sending GETVERSION \t");
sendbuff_NS [0] = KILLREPORT;
sendbuff_NS [1] = length; //write the length of the message to 2nd byte in packet
checksum (sendbuff_NS,length); //call function to generate checksum byte and populate the 3rd byte of packet
writebyte (discriptor,sendbuff_NS); //send the byte packet out to device
printf("\nKILLED THE CONTINUOUS REPORT\n");
usleep(250000);  //wait for response
usleep(250000);  //wait for response

readbyte (discriptor,rcvbuff_NS);






//_____________________________________________________CHANGEBAUD_______________
usleep(250000);  //wait for response

printf("\n downing baud\n");
erasebuffchar (rcvbuff_NS,0); //reset the incoming buffer
erasebuffchar (sendbuff_NS,0); //reset the incoming buffer
length = 4;
sendbuff_NS [0] = SETBAUDRATE;
sendbuff_NS [1] = length; //write the length of the message to 2nd byte in packet
sendbuff_NS [3] = 0; //1 = 19200 2 = 57600
checksum (sendbuff_NS,length); //call function to generate checksum byte and populate the 3rd byte( sendbuff_NS[2] )of packet
writebyte (discriptor,sendbuff_NS); //send the byte packet out to device
serialClose (discriptor);
baud = 1200;
discriptor = serialOpen ("/dev/ttyS0", baud) ;   // make my handle to call with higher baud rate
readbyte (discriptor,rcvbuff_NS);
usleep(250000);  //wait for response
readbyte (discriptor,rcvbuff_NS);
usleep(250000);
readbyte (discriptor,rcvbuff_NS);



//______________________________________________________________

serialClose (discriptor);
return 0;
}





#ifdef print_threads
printf("%d\t Started \n",my_id);
#endif


int init_and_stream_NS(int fd) //this takes care of all of the setup of the NS device including setting how you want it to report the data coming back
{


//extern int numtimesglobalcounter;

extern int FLAGS[];// [0] is averageFLAG [1] is reportendFLAG [2] is transferFLAG





//__________________________________________________GETVERSION

length = 3;
//printf("\n sending GETVERSION \t");
sendbuff_NS [0] = GETVER;
sendbuff_NS [1] = length; //write the length of the message to 2nd byte in packet
checksum (sendbuff_NS,length); //call function to generate checksum byte and populate the 3rd byte of packet
writebyte (fd,sendbuff_NS); //send the byte packet out to device
printf("\nsent getversion\n");
usleep(2500000);  //wait for response
readbyte (fd,rcvbuff_NS);
crc_checksum = check_input_checksum();
printf("\nchecksum check of input is %d\n", crc_checksum);
//printf ("\nreceive buffer caught this:\n%d\t%d\t%d\t%d\t%d\t%d\t\n", rcvbuff_NS[0], rcvbuff_NS[1], rcvbuff_NS[2], rcvbuff_NS[3], rcvbuff_NS[4], rcvbuff_NS[5]) ;  //this grabs whatever is in the buffer at time of getchar
//_____________________________________________________




//_____________________________________________________CHANGEBAUD_______________

printf("\n upping baud\n");
erasebuffchar (rcvbuff_NS,0); //reset the incoming buffer
erasebuffchar (sendbuff_NS,0); //reset the incoming buffer
length = 4;
sendbuff_NS [0] = SETBAUDRATE;
sendbuff_NS [1] = length; //write the length of the message to 2nd byte in packet
sendbuff_NS [3] = 2; //1 = 19200 2 = 57600
checksum (sendbuff_NS,length); //call function to generate checksum byte and populate the 3rd byte( sendbuff_NS[2] )of packet
writebyte (fd,sendbuff_NS); //send the byte packet out to device
usleep(250000);  //wait for response
serialClose (fd);
usleep(250000);  //wait for response
baud = 57600;
fd = serialOpen ("/dev/ttyS0", baud) ;   // make my handle to call with higher baud rate
readbyte (fd,rcvbuff_NS);
crc_checksum = check_input_checksum();
printf("\nchecksum check of input is %d\n", crc_checksum);


//--------------------------------------------setthreshold

erasebuffchar (rcvbuff_NS,0); //reset the incoming buffer
erasebuffchar (sendbuff_NS,0); //reset the incoming buffer
length = 5;
sendbuff_NS [0] = 6; //6 is SETTHRESHOLD
sendbuff_NS [1] = length; //write the length of the message to 2nd byte in packet
sendbuff_NS [3] = 0; //hi byte
sendbuff_NS [4] = 0; //low byte
checksum (sendbuff_NS,length); //call function to generate checksum byte and populate the 3rd byte( sendbuff_NS[2] )of packet
writebyte (fd,sendbuff_NS); //send the byte packet out to device
usleep(250000);  //wait for response
printf("\nsetting the THRESHOLD");
readbyte (fd,rcvbuff_NS);
crc_checksum = check_input_checksum();
printf("\nchecksum check of input is %d\n", crc_checksum);
usleep(250000);  //wait for response

//______________________________________________________________
//_____________________________________________________SETREPORTFLAGS



//printf("\n sending setreportflags\n");
erasebuffchar (rcvbuff_NS,0); //reset the incoming buffer
erasebuffchar (sendbuff_NS,0); //reset the incoming buffer
length = 12;
sendbuff_NS [0] = SETREPORTFLAGS;
sendbuff_NS [1] = length; //write the length of the message to 2nd byte in packet
//checksum goes here and is called later down
sendbuff_NS [3] = 1; //turn on spot report position set to 1
sendbuff_NS [4] = 0; //srm ROOM 9 SPOT 1 TO ROOM 8 SPOT 0
sendbuff_NS [5] = 255; //SRM ROOM 4 SPOT 1 TO ROOM 7 SPOT 0 (WAS 12)
sendbuff_NS [6] = 255; //SRM ROOM 3 SPOT 1 TO ROOM 0 SPOT 0 (was 48) (either 48 for room 2)
sendbuff_NS [7] = 0; //MRM ROOM 9 SPOT 1 TO ROOM 8 SPOT 0
sendbuff_NS [8] = 0; //MRM ROOM 4 SPOT 1 TO ROOM 7 SPOT 0 (WAS 12)
sendbuff_NS [9] = 0; //MRM ROOM 3 SPOT 1 TO ROOM 0 SPOT 0
sendbuff_NS [10] = 0; //SA
sendbuff_NS [11] = 0; //SA



//sendbuff_NS [6] = 7; //
//sendbuff_NS [9] = 7; //
//sendbuff_NS [11] = 10 ; //minimum threshold for brightness
checksum (sendbuff_NS,length); //call function to generate checksum byte and populate the 3rd byte of packet
writebyte (fd,sendbuff_NS); //send the byte packet out to device
usleep(500000);  //wait for response
readbyte (fd,rcvbuff_NS);
crc_checksum = check_input_checksum();
printf("\nchecksum check of input is %d\n", crc_checksum);

printf("\nset the setreportflags\n");


//_____________________________________________________CONTINUOUS REPORT


//note that report end is the second to last byte and has a value of 0x06
//printf("\n sending Report\n");
usleep(500000);  //wait for response
erasebuffchar (rcvbuff_NS,0); //reset the incoming buffer
erasebuffchar (sendbuff_NS,0); //reset the incoming buffer
length = 4;
sendbuff_NS [0] = CONTINUOUSREPORT;
sendbuff_NS [1] = length; //write the length of the message to 2nd byte in packet
sendbuff_NS [3] = ROOMWATCH; //room number for the report
checksum (sendbuff_NS,length); //call function to generate checksum byte and populate the 3rd byte of packet
printf("\nLOOP NEXT!!\n");
writebyte (fd,sendbuff_NS); //send the byte packet out to device

//usleep(250000);  //wait for response
return 0;
}

int copytoDIGEST_NS(int i)//this routine is called when an end of line or end of continuous report is found in the report end checker()
{
	extern char FIFO_NS[];
	extern char DIGEST_NS[];
	extern int DIGEST_NSsize;
	i = i - 5 ; //adjust i in order to just copy what the message is
	int j = 0;
	for (j = 0; j <= i ; j++)
	{
		DIGEST_NS[j] = FIFO_NS[j];
		DIGEST_NSsize = j;
	}
return 0;
}


    //utility that goes through the received bytes and lets you know when the end of the report occurs
 int report_end_check_cont()
{
   extern char FIFO_NS[];
	extern int FLAGS[]; // [0] is averageFLAG [1] is reportendFLAG [2] is transferFLAG
   extern int FIFO_NSpointer;
   //extern int reportendFLAG;

    int i = 0;

    //printf("\nlength told to checker %d \n", length);
    for(i = 0; i <= (FIFO_NSpointer); ++i)
    {
		//EOL case
     if ( (FIFO_NS[(i-4)] == 0) && (FIFO_NS[(i-3)] == 5) && (FIFO_NS[(i-2)] == 226) && (FIFO_NS[(i-1)] == 6) && (FIFO_NS[i] == 18))
		{
                //printf("\nEOF FOUND! I = %d\n", i);
                copytoDIGEST_NS(i);//copy what was found to the DIGEST_NS[] array
                erasebuffchar(FIFO_NS,0); //erase the FIFO_NS and start over again
                FIFO_NSpointer = 0;

                //reportendFLAG = 2; //set the DIGEST_NSflag to break out of the infinite loop if you get an END OF REPORT
                FLAGS[(NS_POINTER +1)] = 2; // states that there is an end of line in the data ready flag that is looked at by the main for loop which will execute a break out of the forever loop this branch is not being developed and when the continuous branch is complete, copy the algorythm to this if branch in the main forever loop
                //averageFLAG = 1;
                FLAGS[(NS_POINTER +0)] = 1; //puts up the flag for averaging_1 or rolling average
                // [0] is averageFLAG [1] is reportendFLAG [2] is transferFLAG

                return i; //spit out the iteration number
                break;
		}
	if
	//End of report string, another string is to follow case
		( (FIFO_NS[(i-4)] == 0) && (FIFO_NS[(i-3)] == 5) && (FIFO_NS[(i-2)] == 241) && (FIFO_NS[(i-1)] == 6) && (FIFO_NS[i] == 3))
		{
                //printf("\nSTILL GOING FOUND! I = %d\n", i); //minus 2 for the I printed will give you the size of the message in the FIFO_NS buffer
                copytoDIGEST_NS(i);//copy what is in the FIFO_NS buffer over to the DIGEST_NS buffer
                erasebuffchar(FIFO_NS,0);//erase the FIFO_NS buffer
                FIFO_NSpointer = 0;//reset your pointer for where in the FIFO buffer you are
                //reportendFLAG = 1;
                FLAGS[(NS_POINTER +1)] = 1; // states that there is data ready and that there is still continuous data coming in from the NS this flag used by the main for loop and is the if branch that is currently being developed
                //averageFLAG = 1;
                FLAGS[(NS_POINTER +0)] = 1; //puts up the flag for averaging_1
                // [0] is averageFLAG [1] is reportendFLAG [2] is transferFLAG
                return i;
                break;
		}
    }

	return i;


}


 int check_input_checksum_DIGEST_NS()//this is the checksum program used once the NS has been switched to stream mode and it checks only the first report (100 bytes long)
{
    //data checked from here must come in the form of byte [0] is 0 byte [1] is length of message byte[2] is the checksum value byte [3-whatever] is data
    //this function looks at whatever array you send to it
    extern char DIGEST_NS[];
    int sum = 0;
    int val = 0;
    int numtimes256 = 0;
    int tosubtract = 0;
    int checksumgood = 0; //this is your checksum value, there will be a checksum value = whatever the checksum is supposed to be or else a 0 indicating that the checksum did not match
    int i;
    int length = DIGEST_NS[1];
    //printf("\nlength told to checker %d \n", length);
    for(i = 0; i < (length); i++)
    {
     if ((i != (0)) && (i != (2) ))
		{
        sum += (255 - (DIGEST_NS[i]));
        //printf("%d  ", sum);
        //if(i == length-1)
        //{printf("stopped at i of %d and value of %d\n",i,DIGEST_NS[i]);}
        //printf("\nI ended at %d  and  SUM came out as %d\n", i, sum);
        //printf("  %d  ",i);
		}
    }
        //sum = sum + (255 - (rcvbuff_NS[i])); //do one more time in order to get the sum correct

    //printf("\nFINAL I ended at inc count of %d  and  SUM came out as %d\n", i, sum - 1);
    val = ((length -2) * 255);
    //printf("\nvalue of all blocks %d \n", val);
    tosubtract = (val - sum);
    //printf("\nvalue to subtract %d \n", tosubtract);
    numtimes256 = tosubtract / 256; //do this as int to drop the remainder
    //printf("roll down the count by 256 times %d  ", numtimes256);
    numtimes256 = numtimes256 * 256;
    //printf("the value to subtract from the value to subtract  %d\n", numtimes256);


    checksumgood = (255-(tosubtract - numtimes256));
    //printf("corrected checksumgood %d \n", checksumgood);


    if (checksumgood != DIGEST_NS[2])//if your calculated checksum value does not match what the DIGEST_NS's checksum is, return a 0 indicating  a bad CRC
    {
		checksumgood = 0;
	}

    return (checksumgood);//the int returned by the function will either be the checksum value indicating that the CRC was good and will return a 0 indicating that the CRC was bad (you will throw away any good CRC's if they are ever 0 for the checksum value in DIGEST_NS[2]!
}
//____________________________________________________________________

int DECODEDIGEST_NS_3()//hard coded parser that looks at a DIGEST_NS[] array and seperates all of the raw values for all of the stars
{
//decodeDIGEST_NS_3 is designed to report all of the spot positions and intensities for room 0 spot 0 through room 7 spot 1
//room 0 spot 0 has numberx[1], numbery[1], intens[1] room 0 spot 1 has numberx[2], numbery[2], etc..
	extern char DIGEST_NS[];
	extern signed short numberx[];
	extern signed short numbery[];




	extern signed long intens[];
	//extern short xposition;
	//extern short yposition;
	//extern float thetaposition;

	//short tempx;
	//short tempy;
	//float temptheta;
	int STARTSPOT = 4;//fourth byte in is where to start numberx1



//room 0 spot 0

numberx[1] = (short) (((DIGEST_NS[STARTSPOT]) <<8) | (DIGEST_NS[(STARTSPOT +1)]));
//numberx1 = (short) (((0x58) <<8) | (0xb5));
numbery[1] = (short) (((DIGEST_NS[(STARTSPOT +2)]) <<8) | (DIGEST_NS[(STARTSPOT +3)]));
intens[1] = (signed long) (((DIGEST_NS[(STARTSPOT +4)]) <<8) | (DIGEST_NS[(STARTSPOT +5)]));

//room 0 spot 1
numberx[2] = (short) (((DIGEST_NS[(STARTSPOT +6)]) <<8) | (DIGEST_NS[(STARTSPOT +7)]));
numbery[2] = (short) (((DIGEST_NS[(STARTSPOT +8)]) <<8) | (DIGEST_NS[(STARTSPOT +9)]));
intens[2] = (signed long) (((DIGEST_NS[(STARTSPOT +10)]) <<8) | (DIGEST_NS[(STARTSPOT +11)]));

//room 1 spot 0
numberx[3] = (short) (((DIGEST_NS[(STARTSPOT +12)]) <<8) | (DIGEST_NS[(STARTSPOT +13)]));
numbery[3] = (short) (((DIGEST_NS[(STARTSPOT +14)]) <<8) | (DIGEST_NS[(STARTSPOT +15)]));
intens[3] = (signed long) (((DIGEST_NS[(STARTSPOT +16)]) <<8) | (DIGEST_NS[(STARTSPOT +17)]));

//room 1 spot 1
numberx[4] = (short) (((DIGEST_NS[(STARTSPOT +18)]) <<8) | (DIGEST_NS[(STARTSPOT +19)]));
numbery[4] = (short) (((DIGEST_NS[(STARTSPOT +20)]) <<8) | (DIGEST_NS[(STARTSPOT +21)]));
intens[4] = (signed long) (((DIGEST_NS[(STARTSPOT +22)]) <<8) | (DIGEST_NS[(STARTSPOT +23)]));

//room 2 spot 0
numberx[5] = (short) (((DIGEST_NS[(STARTSPOT +24)]) <<8) | (DIGEST_NS[(STARTSPOT +25)]));
numbery[5] = (short) (((DIGEST_NS[(STARTSPOT +26)]) <<8) | (DIGEST_NS[(STARTSPOT +27)]));
intens[5] = (signed long) (((DIGEST_NS[(STARTSPOT +28)]) <<8) | (DIGEST_NS[(STARTSPOT +29)]));

//room 2 spot 1
numberx[6] = (short) (((DIGEST_NS[(STARTSPOT +30)]) <<8) | (DIGEST_NS[(STARTSPOT +31)]));
numbery[6] = (short) (((DIGEST_NS[(STARTSPOT +32)]) <<8) | (DIGEST_NS[(STARTSPOT +33)]));
intens[6] = (signed long) (((DIGEST_NS[(STARTSPOT +34)]) <<8) | (DIGEST_NS[(STARTSPOT +35)]));

//room 3 spot 0
numberx[7] = (short) (((DIGEST_NS[(STARTSPOT +36)]) <<8) | (DIGEST_NS[(STARTSPOT +37)]));
numbery[7] = (short) (((DIGEST_NS[(STARTSPOT +38)]) <<8) | (DIGEST_NS[(STARTSPOT +39)]));
intens[7] = (signed long) (((DIGEST_NS[(STARTSPOT +40)]) <<8) | (DIGEST_NS[(STARTSPOT +41)]));

//room 3 spot 11111111111
numberx[8] = (short) (((DIGEST_NS[(STARTSPOT +42)]) <<8) | (DIGEST_NS[(STARTSPOT +43)]));
numbery[8] = (short) (((DIGEST_NS[(STARTSPOT +44)]) <<8) | (DIGEST_NS[(STARTSPOT +45)]));
intens[8] = (signed long) (((DIGEST_NS[(STARTSPOT +46)]) <<8) | (DIGEST_NS[(STARTSPOT +47)]));

//room 4 spot 0
numberx[9] = (short) (((DIGEST_NS[(STARTSPOT +48)]) <<8) | (DIGEST_NS[(STARTSPOT +49)]));
numbery[9] = (short) (((DIGEST_NS[(STARTSPOT +50)]) <<8) | (DIGEST_NS[(STARTSPOT +51)]));
intens[9] = (signed long) (((DIGEST_NS[(STARTSPOT +52)]) <<8) | (DIGEST_NS[(STARTSPOT +53)]));

//room 4 spot 1
numberx[10] = (short) (((DIGEST_NS[(STARTSPOT +54)]) <<8) | (DIGEST_NS[(STARTSPOT +55)]));
numbery[10] = (short) (((DIGEST_NS[(STARTSPOT +56)]) <<8) | (DIGEST_NS[(STARTSPOT +57)]));
intens[10] = (signed long) (((DIGEST_NS[(STARTSPOT +58)]) <<8) | (DIGEST_NS[(STARTSPOT +59)]));

//room 5 spot 0
numberx[11] = (short) (((DIGEST_NS[(STARTSPOT +60)]) <<8) | (DIGEST_NS[(STARTSPOT +61)]));
numbery[11] = (short) (((DIGEST_NS[(STARTSPOT +62)]) <<8) | (DIGEST_NS[(STARTSPOT +63)]));
intens[11] = (signed long) (((DIGEST_NS[(STARTSPOT +64)]) <<8) | (DIGEST_NS[(STARTSPOT +65)]));

//room 5 spot 1
numberx[12] = (short) (((DIGEST_NS[(STARTSPOT +66)]) <<8) | (DIGEST_NS[(STARTSPOT +67)]));
numbery[12] = (short) (((DIGEST_NS[(STARTSPOT +68)]) <<8) | (DIGEST_NS[(STARTSPOT +69)]));
intens[12] = (signed long) (((DIGEST_NS[(STARTSPOT +70)]) <<8) | (DIGEST_NS[(STARTSPOT +71)]));

//room 6 spot 0
numberx[13] = (short) (((DIGEST_NS[(STARTSPOT +72)]) <<8) | (DIGEST_NS[(STARTSPOT +73)]));
numbery[13] = (short) (((DIGEST_NS[(STARTSPOT +74)]) <<8) | (DIGEST_NS[(STARTSPOT +75)]));
intens[13] = (signed long) (((DIGEST_NS[(STARTSPOT +76)]) <<8) | (DIGEST_NS[(STARTSPOT +77)]));

//room 6 spot 1
numberx[13] = (short) (((DIGEST_NS[(STARTSPOT +78)]) <<8) | (DIGEST_NS[(STARTSPOT +79)]));
numbery[13] = (short) (((DIGEST_NS[(STARTSPOT +80)]) <<8) | (DIGEST_NS[(STARTSPOT +81)]));
intens[13] = (signed long) (((DIGEST_NS[(STARTSPOT +82)]) <<8) | (DIGEST_NS[(STARTSPOT +83)]));

//room 7 spot 0
numberx[14] = (short) (((DIGEST_NS[(STARTSPOT +84)]) <<8) | (DIGEST_NS[(STARTSPOT +85)]));
numbery[14] = (short) (((DIGEST_NS[(STARTSPOT +86)]) <<8) | (DIGEST_NS[(STARTSPOT +87)]));
intens[14] = (signed long) (((DIGEST_NS[(STARTSPOT +88)]) <<8) | (DIGEST_NS[(STARTSPOT +89)]));

//room 7 spot 1
numberx[15] = (short) (((DIGEST_NS[(STARTSPOT +90)]) <<8) | (DIGEST_NS[(STARTSPOT +91)]));
numbery[15] = (short) (((DIGEST_NS[(STARTSPOT +92)]) <<8) | (DIGEST_NS[(STARTSPOT +93)]));
intens[15] = (signed long) (((DIGEST_NS[(STARTSPOT +94)]) <<8) | (DIGEST_NS[(STARTSPOT +95)]));

// position data for whatever room is turned on for spot position reporting

	//posxy1room[0] = (signed short) (((DIGEST_NS[(XYPOS1ROOMSTARTSPOT)]) <<8) | (DIGEST_NS[(XYPOS1ROOMSTARTSPOT+1)]));
	//posxy1room[1] = (signed short) (((DIGEST_NS[(XYPOS1ROOMSTARTSPOT+2)]) <<8) | DIGEST_NS[(XYPOS1ROOMSTARTSPOT+3)]);
	//theta1room[0] = (float) ((((DIGEST_NS[(XYPOS1ROOMSTARTSPOT+4)]) <<8) | DIGEST_NS[(XYPOS1ROOMSTARTSPOT+5)])) / (float) (1<<13);

//theta1room[0] = (float) (((DIGEST_NS[(XYPOS1ROOMSTARTSPOT+4)]) <<8) | ((DIGEST_NS[(XYPOS1ROOMSTARTSPOT+5)]) / (float) (1<<13)));

//just trying something herrer
//theta1room[0] = (float) (DIGEST_NS[XYPOS1ROOMSTARTSPOT+4]<<8) + DIGEST_NS[XYPOS1ROOMSTARTSPOT+5];
//theta1room[0] = theta1room[0]/8192;

//debug for position data if working with only a room and spot position report is turned on

//xposition = (short) (((DIGEST_NS[105]) <<8) | (DIGEST_NS[(106)]));
//yposition = (short) (((DIGEST_NS[(107)]) <<8) | DIGEST_NS[(108)]);
//thetaposition = (float) ((((DIGEST_NS[109]) <<8) | DIGEST_NS[110])) / (float) (1<<13);
//same as above but was just checking
//tempx = (DIGEST_NS[105]<<8) + DIGEST_NS[106];
//tempy = (DIGEST_NS[107]<<8) + DIGEST_NS[108];
//temptheta = (float) (DIGEST_NS[109]<<8) + DIGEST_NS[110];
//temptheta = temptheta/8192;

//for (i = 1; i <= 15; ++i)//for room number 0 spot 0 to room 7 spot 1
//{
//printf("\n X%d %d, Y%d %d, intensity%d %ld \n ", i, (numberx[(i)]), i, (numbery[(i)]), i, (intens[(i)]));

//}
return 0;
}


int check_intensities(int minimumvalue)//function that looks at the returned  intensity of any given star that gets used in order to kick out data under a threshold
{

	extern int FLAGS[]; // [0] is averageFLAG [1] is reportendFLAG [2] is transferFLAG

	extern signed long intens[];


	int i;
	int x;

	for (i=1; i <=15 ; ++i)
		{
			if (i ==  1 ||i == 6 ||i == 7 ||i == 14) //active spots currently
			{
			//x = intens[i];
			//printf("intens %d\n",x);
				if ((intens[i]) <= (minimumvalue))
				{
				printf("intensity from star %d below minimums for intensity (was %ld), throwing away DIGEST_NS[]\n",i, intens[i]);
				x = 1; //set an int = to 1 indicating that the info in the current DIGEST_NS has at least one bad value

				}
				else
				{
					x = 0; //set the variable to indicate that you have readgins from the stars with intensities above the minimum threshold
				}
			}
		}




	return x;//this value gets returned into a definition of FLAGS[(NS_FLAGS + 4)] when this function is called
}

int ROLLING_AVERAGE_DIGEST_NS(int numtimes)//THIS WILL GIVE POSITION UPDATES EVERY TIME A NEW READING GETS DECODED BY DECODEDIGEST_NS_3 WITH THE OLDES DATA BEING ROLLED OUT OF THE WEIGHT
{

	extern int FLAGS[]; // [0] is averageFLAG [1] is reportendFLAG [2] is transferFLAG
	extern int numtimesglobalcounter;



	extern int toavgx[];
	extern int toavgy[];
	extern int toavgintens[];





	extern signed short numberx[];
	extern signed short numbery[];
	extern signed long intens[];



	//these arrays are from DIGEST_NS_3 for the room position soludiont from the NS






	extern int toavgintens[];


	extern int averaged_x[];//global variables for consumption that have whatever the rolling average was for star1 star6 star7 star14
	extern int averaged_y[];
	extern int averaged_intens[];

	int i;
	int j = 0;
	int k = 0;
	//int l = 0;



	if (FLAGS[(NS_POINTER + 0)] == 1)//when report_end_check states that there is data to begin averaging on do the following
	{
	if (numtimesglobalcounter == (MAX_BUFFER-1)) // if the function has been called with a full buffer, copy the history needed back to the begining of the buffers and set the numtimesglobalcounter to the appropriate position in order to have contiguous averaged data even rolling the buffer
	{
		k = numtimesglobalcounter - (numtimes-1); //value is needed in order to have a pointer to where the history you want to copy to the begining of the rolling_toavg buffers comes from
		printf("\n k is %d\n NUMTIMESGLOBALCOUNTER was %d\t numtimes is %d", k, numtimesglobalcounter, numtimes); // used for troubleshooting algorythm

		for (j=0; j <= (numtimes-1) ; ++j)
			{
			printf("\n L WAS %d\t\n",j); //used for troubleshooting algorythm
				for (i=1; i <=15 ; ++i)
				{
					if (i ==  1 ||i == 6 ||i == 7 ||i == 14) //copy the active spots currently into your history for the active spots
					{
					rolling_toavgx[j][i] = rolling_toavgx[j+k][i];
					rolling_toavgy[j][i] = rolling_toavgy[j+k][i];
					rolling_toavgintens[j][i] = rolling_toavgintens[j+k][i];


					}
				}
			}


		numtimesglobalcounter = (numtimes);//currently, just start over the rolling average, eventuall set it up to copy your rolling history
		printf("looped NUMTIMESGLOBALCOUNTER AND  COPIED HISTORY TOO counter set to %d\n\n", numtimesglobalcounter);





	}

	//printf("\nranonce\n");


	// AVERAGING routine for the position solution from DIGEST_NS_3



	//this should eventually replace the hard coded above
	for (i=1; i <=15 ; ++i)
		{
			if (i ==  1 ||i == 6 ||i == 7 ||i == 14) //active spots currently begin populating the rolling_toavgx[] data from the current star query
			{
			rolling_toavgx[numtimesglobalcounter][i] = numberx[i];//copy the current global value populated from decodeDIGEST_NS_3 () into the rolling average matrix
			rolling_toavgy[numtimesglobalcounter][i] = numbery[i];
			rolling_toavgintens[numtimesglobalcounter][i] = intens[i];
			}
		}
		//this is the end of what eventually replaces the hard coded above

	numtimesglobalcounter = numtimesglobalcounter + 1;//increment your count tracker
	if(numtimesglobalcounter <= numtimes)//check to see if the count tracker has met the needed averaging value if not tell the user if so provide the data and pop FLAGS NS_POINTER + 5
	{
		//add flag to indicate that you are still averaging data and nothing is available yet from rolling average
	printf("filling buffer, wait till %d is equal to %d\n",numtimesglobalcounter, numtimes);
	}
	//printf("flags 0 numtimesglobal counter %d \t",numtimesglobalcounter);

	if (numtimesglobalcounter >= numtimes)//if you have enough history in the buffers, go ahead and start your rolling averaging algorythm

		{
			//printf("\nMADE IT INTO THE LOOP with numtimes of %d\t and numtimesglobalcounter of %d\n" ,numtimes, numtimesglobalcounter);
			for (j=(numtimesglobalcounter); j >=((numtimesglobalcounter)-(numtimes-1)) ; j--) //the j variable looks back at the history of all the readings for numtimes number of readings
			{
			//printf("\n HERE HERE %d\t\n",j); //used for troubleshooting
				for (i=1; i <=15 ; ++i)
				{
					if (i ==  1 ||i == 6 ||i == 7 ||i == 14) //active spots currently
					{
					toavgx[i] = toavgx[i] + rolling_toavgx[j][i];
					toavgy[i] = toavgy[i] + rolling_toavgy[j][i];
					toavgintens[i] = toavgintens[i] + rolling_toavgintens[j][i];
					}
				}
			}

			//now that all of the history wanted has been added into a sum, devide by the number of times summed	(numtimes)
		for (i=1; i <=15 ; ++i)
				{
					if (i ==  1 ||i == 6 ||i == 7 ||i == 14) //active spots currently
					{
					toavgx[i] = toavgx[i] / numtimes;
					toavgy[i] = toavgy[i] / numtimes;
					toavgintens[i] = toavgintens[i] / numtimes;
					//copy what was averaged to a global that can be accesed by the star_analysis() function
					averaged_x[i] = toavgx[i];
					averaged_y[i] = toavgy[i];
					averaged_intens[i] = toavgintens[i];

					#ifdef report_raws_from_stars
					printf("STAR # %d  x avg %d, y avg %d, intens avg %d \n",i, toavgx[i], toavgy[i], toavgintens[i]);
					#endif

					}
				}
		FLAGS[(NS_POINTER + 5)] = 1; //set a flag for star analysis to know that there is a fresh value to analyze
		}



	}//end if FLAGS[(NS_POINTER +0] == 1





		//numtimesglobalcounter = 0;



	FLAGS[(NS_POINTER +0)] = 0; // put down the averaging flag because you don't want to keep averaging a stagnant value
	return 0;
}



int star_analysis()
{
	extern int FLAGS[];
	extern int averaged_intens[];
	extern int averaged_x[];//used in step 1A3
	extern int averaged_y[];
#define STARSCENTERPOINTER 50 //pointer used to shift the buffer up for averaged_x, averaged_y, averaged_intens globals which allows analyze_stars to use spare buffer space for averaging the data into a center point for further analysis

	float high_global_heading_NS = 0;//hyjackewd for star analysis
float low_global_heading_NS = 0;
float global_heading_NS = 0.00; //after you resolve the high and low averaged angle split

	//extern float high_global_heading_NS;
	//extern float low_global_heading_NS;
	//extern float global_heading_NS;



	//values for analyzing the vectors for diagonals of the square
 int diag_1_to_7 [2] = {0};//0 = x'11 1 = y'11
 int diag_6_to_14 [2] = {0};//0 = x'12 1 = y'12 of notes



 int midpoint_from_diags[2] = {0};// 0 = X'1 1 = Y'1


 //end values for step 1A1


	//values for analyzing the vectors for the square traced from points s1-s14 and their mid points ref step 1A2
 int horz_1_to_14 [2] = {0};//0 = x'211 1 = y'211
 int horz_6_to_7 [2] = {0};//0 = x'212 1 = y'212 of notes
 int vert_1_to_6 [2] = {0};//0 = x'221 1 = y'221
 int vert_7_to_14 [2] = {0};//0 = x'222 1 = y'222
 int midpoint_from_horz[2] = {0};// 0 = X'21 1 = Y'21
 int midpoint_from_vert[2] = {0};// 0 = X'22 1 = Y'22
 int midpoint_from_vert_horz_midpoints[2] = {0}; //0 is X'2 1 = Y'2
 //end values for step 1A2
 //derotated step 1A2 variables

 //end derotated step 1A2




//these variables got repurposed in version 14 to be the avg center from step 1A3 in the notes
	extern int current_centerpoint_x;//this is X'3 data fromaveraged_x[] etc is put together and divided by 4 to get the center point described by the 4 stars these variables are the centerpoint
	extern int current_centerpoint_y;//this is Y'3


	//end of values for step 1A3


	int delta_X = 0;//used in step 1B of notes  and is X'
	int delta_Y = 0;//used in step 1B of notes  and is Y'



	//begin step 2 variables
	int shifted_x [8] = {0} ; //0=x'1 1= x'6 2= x'7 3= x'14 4= x"211 5= x"212 6= x"221 7= x"222 shifted valuesfrom step 2 in notes
	int shifted_y [8] = {0} ; //just like above but y values

	//re-used the code for step 2 in later attempt at defining the raw vectors and angles and needed variables that made sense to me
	int raw_x [8] = {0} ; //0=x'1 1= x'6 2= x'7 3= x'14 4= x"211 5= x"212 6= x"221 7= x"222 shifted valuesfrom step 2 in notes
	int raw_y [8] = {0} ; //just like above but y values



	//begin step 3 variables see math for steps(2) of notes if confused vector u_x (and y) are the position vectors to the cartesian coord shifted points
	int vector_u_x[28] = {0}; //0 = O_S14' 1 = O_S1' 2 = O_S6' 3 = O_S7' 4 = O_MU, 5 = O_MR, 6 = O_MD, 7 = O_ML
	int vector_u_y[28] = {0};
	int vector_v_x[8] = {0};
	int vector_v_y[8] = {0};

	//needed some values for the raw vectors before the cartesian coordinate shift



	//magnitudes of all the points of u and v vectors for later use in despin delta_x delta_y

	float r_vector_u [8] = {0}; //driven by vector_u_x, vector_u_y and populated in step 3 just aafter definition of vector_u
	float r_vector_v = {0};

	float raw_r_vector_u [8] = {0}; //copy of above variable but with raw values and is used for millionth attempt at resolving position independent of sensor rotation angle


float angle [18] = {0.00}; //needed for acos of above vectors using cos ang = u.v/(|u||v|)
float raw_angle [18] = {0.00}; //needed for acos of above vectors using cos ang = u.v/(|u||v|)
int hi_lo_angle_mask [8] = {1}; //mask to let the averaging routine average the highs and the lows

int highcounter = 0; //this is used in order to see how many values have rotated from quadrant 1 to quadrant 4 after all of the corrections in order to fix the dead zone btw 0 and 2PI
int lowcounter = 0; //this is used in order to see how many values have rotated from quadrant 1 to quadrant 4 after all of the corrections in order to fix the dead zone btw 0 and 2PI
int normalcounter = 0;

float split = 0.00;

int constellation_geom[18] = {0};


//float polar_ang[8] = {0.00}; // just in case you have to do any transformations to any of the vectors after shifting the image to the center you have the angles to all of the stars at current averaged image





	//float side_1_to_14_raws;//x side side reserved for future geometry analysis
	//float side_6_to_7_raws;//x side
	//float side_1_to_6_raws;//y side
	//float side_14_to_7_raws;//y side


	//float side_1_to_14;//x side reserved for future geometry analysis
	//float side_6_to_7;//x side
	//float side_1_to_6;//y side
	//float side_14_to_7;//y side

	float negative_angle_from_highs = 0.00;
	float positive_angle_from_lows = 0.00;
			float negative_angle_from_normals = 0;
		float normal_global_heading_NS  = 0;




	int average_spacing = 0;


	int i = 0;

	if (FLAGS[(NS_POINTER +5)] == 1) // if fresh values came from rolling_average() or average_1()
	{


//STEP 1A1  here is the algorythm for finding the midpoints for the diagonal lines found in step 1A1 ends up giving you X'1 and Y'1 in midpoint_from_diags[]



diag_1_to_7 [0] = (averaged_x[1]+averaged_x[7])/2 ;//0 = x'11
diag_1_to_7 [1] = (averaged_y[1]+averaged_y[7])/2 ;// 1 = y'11
diag_6_to_14[0] = (averaged_x[6]+averaged_x[14])/2 ;//0 = x'12
diag_6_to_14[1] = (averaged_y[6]+averaged_y[14])/2 ;//1 = y'12 of notes


//printf("DIAG 1 to 7 x %d, y %d, 6 to 14 x %d, y %d\t", diag_1_to_7[0], diag_1_to_7[1], diag_6_to_14[0], diag_6_to_14[1]);


midpoint_from_diags[0] = (diag_1_to_7 [0] + diag_6_to_14[0])/2; //0 = X'1  (average the x midpoints for step 1A1)
midpoint_from_diags[1] = (diag_1_to_7 [1] + diag_6_to_14[1])/2; //1 = Y'1  average the y midpoints

//end diags midpoint find step 1A1


	//STEP 1A2 algorythm for finding the midpoints for the horizontals and verticals described by the 4 stars connected nodes
 horz_1_to_14 [0] = (averaged_x[1]+averaged_x[14])/2;//0 = x'211
 horz_1_to_14 [1] = (averaged_y[1]+averaged_y[14])/2;//1 = y'211

 horz_6_to_7 [0] = (averaged_x[6]+averaged_x[7])/2;//0 = x'212
 horz_6_to_7 [1] = (averaged_y[6]+averaged_y[7])/2;//1 = y'212 of notes


 vert_1_to_6 [0] = (averaged_x[1]+averaged_x[6])/2;//0 = x'221
 vert_1_to_6 [1] = (averaged_y[1]+averaged_y[6])/2;//1 = y'221


 vert_7_to_14 [0] = (averaged_x[7]+averaged_x[14])/2;//0 = x'222
 vert_7_to_14 [1] = (averaged_y[7]+averaged_y[14])/2;// 1 = y'222


 midpoint_from_horz[0] = (horz_1_to_14 [0] + horz_6_to_7[0])/2;// 0 = X'21
 midpoint_from_horz[1] = (horz_1_to_14 [1] + horz_6_to_7[1])/2;// 1 = Y'21

 midpoint_from_vert[0] = (vert_1_to_6 [0] + vert_7_to_14[0])/2;// 0 = X'22
 midpoint_from_vert[1] = (vert_1_to_6 [1] + vert_7_to_14[1])/2;// 1 = Y'22

 midpoint_from_vert_horz_midpoints[0] = (midpoint_from_horz[0] + midpoint_from_vert[0])/2; //0 is X'2
 midpoint_from_vert_horz_midpoints[1] = (midpoint_from_horz[1] + midpoint_from_vert[1])/2; // 1 = Y'2

 //end values for step 1A2

		//here is the algorythm for finding the averaged center by looking at the corner positions x and y values and then dividing by 4 from step 1A3 of the notes
	//Step 1A3


		for (i=1; i <=15 ; ++i)//loop used to find the center of the current set of stars 1,6,7,14
				{
					if (i ==  1 ||i == 6 ||i == 7 ||i == 14) //active spots currently
					{

					averaged_x[STARSCENTERPOINTER] = averaged_x[STARSCENTERPOINTER] + averaged_x[i]; //STARSCENTERPOINTER is just a name to describe the pointer shift in the global buffer averaged_BLAH[]
					averaged_y[STARSCENTERPOINTER] = averaged_y[STARSCENTERPOINTER] + averaged_y[i];
					averaged_intens[STARSCENTERPOINTER] = averaged_intens[STARSCENTERPOINTER] + averaged_intens[i];
					//printf("inputs into tSTAR ANALYSIS() STAR # %d  x avg %d, y avg %d, intens avg %d \n",i, toavgx[i], toavgy[i], toavgintens[i]);

						if (i ==  14)//if you have gone through all stars, now divide the stars sums by 4 (four stars)
						{

									averaged_x[STARSCENTERPOINTER] = averaged_x[STARSCENTERPOINTER] /4; //STARSCENTERPOINTER is just a name to describe the pointer shift in the global buffer averaged_BLAH[]
									averaged_y[STARSCENTERPOINTER] = averaged_y[STARSCENTERPOINTER] /4;
									averaged_intens[STARSCENTERPOINTER] = averaged_intens[ STARSCENTERPOINTER] /4;
									//you should now have the average x y and intens of all four stars

						}

					}
				}
		//end step 1A3


		//begin step 1B

		delta_X = (averaged_x[STARSCENTERPOINTER] + 	midpoint_from_vert_horz_midpoints[0] + midpoint_from_diags[0] )/3; //this is X'3 average the 3 derived center points to come up with what you are going to shift the image to center point with
		delta_Y = (averaged_y[STARSCENTERPOINTER] + 	midpoint_from_vert_horz_midpoints[1] + midpoint_from_diags[1] )/3; //this is Y'3 average the 3 derived center points to come up with what you are going to shift the image to center point with

		current_centerpoint_x = delta_X * -1;//used to output position not part of the math notes
		current_centerpoint_y = delta_Y * -1;//uesd to output position blah blah


		//end step 1B

		//begin step 2
		//translate S1, S6, S7, S14, midpoints from vert and horz so that the center of the image is in the center

		//0=x'1 1= x'6 2= x'7 3= x'14 4= x"211 5= x"212 6= x"221 7= x"222 shifted valuesfrom step 2 in notes, see page: math for steps(2)

	shifted_x [0] = averaged_x[14] - delta_X ; //0=x'14  shifted valuesfrom step 2 in notes
	shifted_x [1] = averaged_x[1] - delta_X ; //1= x'1  shifted valuesfrom step 2 in notes
	shifted_x [2] = averaged_x[6] - delta_X ; //2= x'6  shifted valuesfrom step 2 in notes
	shifted_x [3] = averaged_x[7] - delta_X ; //3= x'7
	shifted_x [4] = horz_1_to_14 [0] - delta_X ; //4= x"211
	shifted_x [5] = horz_6_to_7 [0] - delta_X ; //5= x"212
	shifted_x [6] = vert_1_to_6 [0] - delta_X ; //6= x"221
	shifted_x [7] = vert_7_to_14 [0] - delta_X ; //7= x"222

		//just like above but y values

	shifted_y [0] = averaged_y[14] - delta_Y ; //0=y'14  shifted valuesfrom step 2 in notes
	shifted_y [1] = averaged_y[1] - delta_Y ; //1= y'1  shifted valuesfrom step 2 in notes
	shifted_y [2] = averaged_y[6] - delta_Y ; //2= y'6  shifted valuesfrom step 2 in notes
	shifted_y [3] = averaged_y[7] - delta_Y ; //3= y'7
	shifted_y [4] = horz_1_to_14 [1] - delta_Y ; //4= y"211
	shifted_y [5] = horz_6_to_7 [1] - delta_Y ; //5= y"212
	shifted_y [6] = vert_1_to_6 [1] - delta_Y ; //6= y"221
	shifted_y [7] = vert_7_to_14 [1] - delta_Y ; //7= y"222


		//end step 2

		//now step 3
		//3A1
			//begin step 3 variables see math for steps(2) of notes if confused
	 //0 = O_S14' 1 = O_S1' 2 = O_S6' 3 = O_S7' 4 = O_MU, 5 = O_MR, 6 = O_MD, 7 = O_ML
	vector_u_x[0] = shifted_x [0];//0 = O_S14' x"14  val of u vector
	vector_u_x[1] = shifted_x [1];//1 = O_S1' x"1
	vector_u_x[2] = shifted_x [2];//2 = O_S6' x"6
	vector_u_x[3] = shifted_x [3];//3 = O_S7' x"7
	vector_u_x[4] = shifted_x [4];//4 = O_MU, x"211
	vector_u_x[5] = shifted_x [7];// 5 = O_MR, x"22
	vector_u_x[6] = shifted_x [5];//6 = O_MD, x"212
	vector_u_x[7] = shifted_x [6];// 7 = O_ML, x"221

	vector_u_y[0] = shifted_y [0];//0 = O_S14' x val of u vector
	vector_u_y[1] = shifted_y [1];//1 = O_S1'
	vector_u_y[2] = shifted_y [2];//2 = O_S6'
	vector_u_y[3] = shifted_y [3];//3 = O_S7'
	vector_u_y[4] = shifted_y [4];//4 = O_MU,
	vector_u_y[5] = shifted_y [7];// 5 = O_MR,
	vector_u_y[6] = shifted_y [5];
	vector_u_y[7] = shifted_y [6];

	//define the vector_v_x and y as 1, 0

	vector_v_x[0] = 1;
	vector_v_y[0] = 0;
	r_vector_v = ( sqrt( (vector_v_x[0]*vector_v_x[0]) + (vector_v_y[0]*vector_v_y[0]) ) );//take the magnitude for the inner dot product to find angles

		for (i = 0; i <8; ++i) //loop for inner dot product and angle corrections for a consistent output of heading
		{
			//( (vector_u_x[i]*vector_v_x[i]) + (vector_u_y[i]*vector_v_y[i]) )//u.v
			//( ( sqrt( (vector_u_x[i]*vector_u_x[i]) + (vector_u_y[i]*vector_u_y[i]) ) ) * ( sqrt( (vector_v_x[i]*vector_v_x[i]) + (vector_v_y[i]*vector_v_y[i]) ) ) )//|u|*|v|
		r_vector_u [i] = ( sqrt( (vector_u_x[i]*vector_u_x[i]) + (vector_u_y[i]*vector_u_y[i]) ) ); //take the magnitude of current point for inner dot product and the despinning of delta_x and delta_y that happens later later
		angle[i] = acos(	( ((vector_u_x[i])*(vector_v_x[0])) + (vector_u_y[i]*vector_v_y[0]) ) / ( r_vector_u[i] * r_vector_v ) ); //determine the angle between u[i] and v[i] and place in angle[i]
		//printf("\n ANGLE %d\t%f\n",i,(angle[i]*RAD_to_DEG));



	//make corrections for acos (angles that are in quadrants 3 and 4)

		if (vector_u_x[i] < 0 && vector_u_y[i] < 0) // correct for quadrant 3
		{
		angle[i] = (360/RAD_to_DEG)- angle [i];

		}
		if (vector_u_x[i] >= 0 && vector_u_y[i] < 0)//correct for quadrant 4
		{
		angle[i] = (360/RAD_to_DEG)- angle [i];

		}

		angle[(10+i)] = angle[i];//copy the raws for later consumption in the de-spin delta-x and delta-y
	//now that you have all of the vectors in the geometry you want, put them through  the good old dot product angle find routine	theta i = acos(ui.vi/|ui||vi|)





		//printf("\nPRE Corr ANGLE %d\t%f\n",i,(angle[i]*RAD_to_DEG)); //used for troubleshooting the relative angles before makeing all them agree

		}// end for loop


		//corrections for angles 0 through 7 to get them all agreeing with respect to the reference angle (v = 1,0)
		angle[0] =  (45/RAD_to_DEG)  - angle [0] ; //direction of star 14
		angle[1] =  (135/RAD_to_DEG) - angle [1] ;//direction of star 1
		angle[2] =  (225/RAD_to_DEG) - angle [2] ;//star 6
		angle[3] =  (315/RAD_to_DEG) - angle [3] ;//star 7
		angle[4] =  (90/RAD_to_DEG)  - angle [4] ;//mid point between 14 and 1
		angle[5] =  (360/RAD_to_DEG) - angle [5] ; //mid point between 14 and 7
		angle[6] =  (270/RAD_to_DEG) - angle [6] ; //midpoint between 7 and 6
		angle[7] =  (180/RAD_to_DEG) - angle [7] ;//midpoint between 6 and 1




			for (i = 0; i <8; ++i) // Now that all of the angles are giving the agreed upon reference angle, where will be a point where they undershoot and go negative where we will add 360 to it to make a bearing heading system between 0 and 360 deg like in airplanes (note that raw values are in radians)
			{
			if (angle[i] < 0)
			{
			angle[i] = (360/RAD_to_DEG) + angle[i];
			}
			#ifdef report_agreeing_corrected_relative_angles
			printf("ANGLE %d\t%f\n",i,(angle[i]*RAD_to_DEG)); //used for troubleshooting corrected for agreement relative angles
			#endif

			} // end for loop


		//	working on the dead zone between 0 and 2PI
			global_heading_NS = 0;
			for (i = 0;i<8;++i)//zero out the hit_low_mask after taking all of your averaging stuff from the split
		{hi_lo_angle_mask[i] = 3;}//set all masks to a default of 3


			negative_angle_from_normals = 0;//needed initializzations before getting into the below loop
			normal_global_heading_NS  = 0;
			FLAGS[(NS_POINTER +7)] = 0; //make sure that the split in angles flag is down
			for (i = 0; i < 8; ++i)//set up a method of storing the values that have already flipped from 0 to 2PI seperating lows from highs and averaging them with the weights
			{
			//all angles are even and set as such but if the following happens split them

			if (angle[i] > (angle[0] + 1))//if tcurrent angle is > than angle 0 by 1 radianan, there is a split or bad data and current angle gets marked as high side angles for the split averaging
			{
				#ifdef report_found_splits_between_angle_agreement
			printf("\tSPLIT with angle high %d", i);
			#endif
			FLAGS[(NS_POINTER +7)] = 1;//dead zone flag turned on
		//hi_lo_angle_mask[0] = 1;//pop a flag indicating that there was a split or bad data
			hi_lo_angle_mask[i] = 1;//whatever angle just got checked against angle 0 will be marked as a high value for seperate averaging
			//++highcounter; //this counter was used for taking the average after summing the highs and lows in the next loop

			}

			if (angle[i] < (angle[0] - 1))//if tcurrent angle is < than angle 0 by 1 radianan, there is a split or bad data and current angle gets marked as low side angles for the split averaging
			{
				#ifdef report_found_splits_between_angle_agreement
			printf("\tSPLIT with angle low %d", i);
			#endif
			FLAGS[(NS_POINTER +7)] = 1;//dead zone flag turned on
		//hi_lo_angle_mask[0] = 1;//pop a flag indicating that there was a split or bad data
			hi_lo_angle_mask[i] = 0;//whatever angle just got checked against angle 0 will be marked as a low value for seperate averaging
			//++lowcounter; //this counter was used for taking the average after summing the highs and lows in the next loop

			}
		if (hi_lo_angle_mask[i] ==3)
		{

		++normalcounter;

		normal_global_heading_NS = normal_global_heading_NS  + angle [i];
		global_heading_NS = global_heading_NS + angle[i];
		negative_angle_from_normals = negative_angle_from_normals + (angle[i]-(360/RAD_to_DEG));//this is a sum of the negative values used for the split weighted average performed below after this loop
		}
		if (hi_lo_angle_mask[i] ==1)
		{

		++highcounter;

		high_global_heading_NS = high_global_heading_NS + angle[i];
		negative_angle_from_highs = negative_angle_from_highs + (angle[i]-(360/RAD_to_DEG));//this is a sum of the negative values used for the split weighted average performed below after this loop

		}
		if (hi_lo_angle_mask[i] ==0)
		{

		++lowcounter;

		low_global_heading_NS = low_global_heading_NS + angle[i];
		positive_angle_from_lows = positive_angle_from_lows + angle[i];//this is a sum of the positive values used for the split weighted average performed below after this loop

		}


				if (i == 7)
				{


					if (lowcounter == 0 && highcounter == 0)
					{
						#ifdef report_found_splits_between_angle_agreement
						printf("NORMAL BEHAVIOUR");// you have a situation where angle[0] is the only low value and all of the others are high values just take the avearge
						#endif
						global_heading_NS = global_heading_NS / 8;
						//split = global_heading_NS;
					}



					if (highcounter == 0 && lowcounter !=0) //normal is negative and low is plus
					{
						global_heading_NS = global_heading_NS / normalcounter;
						high_global_heading_NS = high_global_heading_NS / highcounter;
						low_global_heading_NS = low_global_heading_NS / lowcounter;
						#ifdef report_found_splits_between_angle_agreement
						printf("\nNormal from low BEHAVIOUR\n");// you have a situation where angle[0] is the only low value and all of the others are high values
						printf("\naveraged normal %f number normal %d", global_heading_NS*RAD_to_DEG, normalcounter);
						printf("\naveraged high %f number high %d", high_global_heading_NS*RAD_to_DEG, highcounter);
						printf("\naveraged low %f number low %d", low_global_heading_NS*RAD_to_DEG, lowcounter);
					#endif

					split = ((positive_angle_from_lows + negative_angle_from_normals)/8);

					if (split < 0)
			{
			split = (6.283185)	+ split;
			//printf("\nflipped split");
			}
					global_heading_NS = split;
					}

					if (highcounter != 0 && lowcounter ==0) //normal is the low value and high negative split is positive
					{

						//printf("\nHigh from Normal BEHAVIOUR\n");// you have a situation where angle[0] is the only low value and all of the others are high values
						global_heading_NS = global_heading_NS / normalcounter;
					//printf("\naveraged normal %f number normal %d", global_heading_NS*RAD_to_DEG, normalcounter);
					high_global_heading_NS = high_global_heading_NS / highcounter;
					//printf("\naveraged high %f number high %d", high_global_heading_NS*RAD_to_DEG, highcounter);
					low_global_heading_NS = low_global_heading_NS / lowcounter;
					//printf("\naveraged low %f number low %d", low_global_heading_NS*RAD_to_DEG, lowcounter);


					split = ((normal_global_heading_NS  + negative_angle_from_highs)/8);

					if (split < 0)
			{
			split = (6.283185)	+ split;
			//printf("\nflipped split");
			}
				global_heading_NS = split;
					}



			//printf("\nthe SPLIT %f \n t \n",  (split * RAD_to_DEG));
			high_global_heading_NS = 0;
			low_global_heading_NS = 0;
			highcounter = 0;
			lowcounter = 0;
			positive_angle_from_lows = 0;
			negative_angle_from_highs = 0;

				}

			}


		//0=x'1 1= x'6 2= x'7 3= x'14 4= x"211 5= x"212 6= x"221 7= x"222 raw valuesfrom step 2 in notes, see page: math for steps(2)

	raw_x [0] = averaged_x[14] ; //0=x'14  shifted valuesfrom step 2 in notes
	raw_x [1] = averaged_x[1]; //1= x'1  shifted valuesfrom step 2 in notes
	raw_x [2] = averaged_x[6] ; //2= x'6  shifted valuesfrom step 2 in notes
	raw_x [3] = averaged_x[7]  ; //3= x'7
	raw_x [4] = horz_1_to_14 [0]; //4= x"211
	raw_x [5] = horz_6_to_7 [0] ; //5= x"212
	raw_x [6] = vert_1_to_6 [0] ; //6= x"221
	raw_x [7] = vert_7_to_14 [0]  ; //7= x"222

		//just like above but y values

	raw_y [0] = averaged_y[14] ; //0=y'14  shifted valuesfrom step 2 in notes
	raw_y [1] = averaged_y[1] ; //1= y'1  shifted valuesfrom step 2 in notes
	raw_y [2] = averaged_y[6] ; //2= y'6  shifted valuesfrom step 2 in notes
	raw_y [3] = averaged_y[7]; //3= y'7
	raw_y [4] = horz_1_to_14 [1]; //4= y"211
	raw_y [5] = horz_6_to_7 [1] ; //5= y"212
	raw_y [6] = vert_1_to_6 [1] ; //6= y"221
	raw_y [7] = vert_7_to_14 [1] ; //7= y"222

	//here I re-use the vector math to get my raw angles for all the corners and the midpoints (before being shifted)


	//use the angle correction routine that you came up with for the despun raw angles so that you know all of your values will be between 0 and 360
					//make corrections for acos (angles that are in quadrants 3 and 4)
	//define the vector_v_x and y as 1, 0

	//vector_v_x[0] = 1; //just a note, vector_v didn't change so you can skip all of this junk
	//vector_v_y[0] = 0; //just a note, vector_v didn't change so you can skip all of this junk
	//r_vector_v = ( sqrt( (vector_v_x[0]*vector_v_x[0]) + (vector_v_y[0]*vector_v_y[0]) ) );//take the magnitude for the inner dot product to find angles //just a note, vector_v didn't change so you can skip all of this junk
	printf("\n\nHeading  %f \n\n",(global_heading_NS * RAD_to_DEG));
		for (i = 0; i <8; ++i) //loop for inner atan2 angle corrections for a consistent output of heading
		{
			//at this point check to make sure that the stars angles stay in respective quadrants for the center of the constelation independent of rotation
			//( (vector_u_x[i]*vector_v_x[i]) + (vector_u_y[i]*vector_v_y[i]) )//u.v
			//( ( sqrt( (vector_u_x[i]*vector_u_x[i]) + (vector_u_y[i]*vector_u_y[i]) ) ) * ( sqrt( (vector_v_x[i]*vector_v_x[i]) + (vector_v_y[i]*vector_v_y[i]) ) ) )//|u|*|v|
		raw_r_vector_u [i] = ( sqrt( (raw_x[i]*raw_x[i]) + (raw_y[i]*raw_y[i]) ) ); //take the magnitude of current point for inner dot product and the despinning of delta_x and delta_y that happens later later

		raw_angle[i] = atan2(raw_y[i],raw_x[i]);//angle determination using 18.5 up
		//raw_angle[i] = acos(	( ((raw_x[i])*(vector_v_x[0])) + (raw_y[i]*vector_v_y[0]) ) / ( raw_r_vector_u[i] * r_vector_v ) ); //determine the angle between u[i] and v[i] and place in angle[i]//angle determination using 18.2





		if (raw_angle[i] < 0 ) // correct for going below 0
		{
		raw_angle[i] = (360/RAD_to_DEG)+ raw_angle [i];


		}



		raw_angle[10+i] = raw_angle[i]+ global_heading_NS;//take out the rotation so you can look at the angles without it
		#ifdef report_corrected_despin_stuff
		printf(" raw_r_u %f\t",raw_r_vector_u[i]);
		printf(" number %d, X %d, Y %d\t",i,raw_x[i], raw_y[i]);
		#endif

		if(raw_angle[10+i]>6.28319)//correct adjusted angles if they go past 360
		{
			raw_angle[10+i] = raw_angle[10+i] - 6.28319;
		}

		#ifdef report_corrected_despin_stuff
		printf(" ANGLE %d\t%f",i,(raw_angle[i]*RAD_to_DEG));

		printf(" Rotated ANGLE %d\t%f\t",i,(raw_angle[10+i]*RAD_to_DEG));

		#endif

		//put the corrected values of angle into an array for x and an array for y
		global_x_NS[i] = raw_r_vector_u[i] * cos(raw_angle[10+i]);
		global_y_NS[i] = raw_r_vector_u[i] * sin(raw_angle[10+i]);

		#ifdef report_corrected_despin_stuff
		printf(" X pos %f\t Y pos %f\n",global_x_NS[i],global_y_NS[i]);
		#endif
		}// end for loop

		//do some trig magic where you compare stars vectors or jedi mind tricks to make some position data (probably page 91 of personal notebook)
		/*troubleshooting stuff for sin and cos of stars
		printf("\n\nAgreeing 14  X %f and 7 X %f \nAgreeing 14 Y %f and 1 Y %f\n",global_x_NS[0],global_x_NS[3],global_y_NS[0],global_y_NS[1]);
		printf("\nAgreeing  1 X %f and 2 X %f \nAgreeing 3 Y %f and 2 Y %f\n",global_x_NS[1],global_x_NS[2],global_y_NS[3],global_y_NS[2]);
		printf("\nmidpoints Agreeing  i4 X %f and i5 X %f \nmidpoints Agreeing i6 Y %f and i7 %f\n",global_x_NS[4],global_x_NS[5],global_y_NS[6],global_y_NS[7]);
		*/
	//look at the spacing between the four stars
	//S1 to S14 top side
	constellation_geom[0] = sqrt((raw_x[1] - raw_x [0]) * (raw_x[1] - raw_x [0]) + (raw_y[1] - raw_y [0]) * (raw_y[1] - raw_y [0]));

	//S6 to S7 bottom side
	constellation_geom[1] = sqrt((raw_x[2] - raw_x [3]) * (raw_x[2] - raw_x [3]) + (raw_y[2] - raw_y [3]) * (raw_y[2] - raw_y [3]));
	//S1 to S6 w side
	constellation_geom[2] = sqrt((raw_x[1] - raw_x [2]) * (raw_x[1] - raw_x [2]) + (raw_y[1] - raw_y [2]) * (raw_y[1] - raw_y [2]));
	//S14 to S7 e side
	constellation_geom[3] = sqrt((raw_x[0] - raw_x [3]) * (raw_x[0] - raw_x [3]) + (raw_y[0] - raw_y [3]) * (raw_y[0] - raw_y [3]));
	//midpoint E to midpoint W
	constellation_geom[4] = sqrt((raw_x[7] - raw_x [6]) * (raw_x[7] - raw_x [6]) + (raw_y[7] - raw_y [6]) * (raw_y[7] - raw_y [6]));
	//midpoint N to midpoint S
	constellation_geom[5] = sqrt((raw_x[4] - raw_x [5]) * (raw_x[4] - raw_x [5]) + (raw_y[4] - raw_y [5]) * (raw_y[4] - raw_y [5]));
	//corner S14 to corner S6
	constellation_geom[6] = sqrt((raw_x[0] - raw_x [2]) * (raw_x[0] - raw_x [2]) + (raw_y[0] - raw_y [2]) * (raw_y[0] - raw_y [2]));
	//corner S7 to corner S1
	constellation_geom[7] = sqrt((raw_x[3] - raw_x [1]) * (raw_x[3] - raw_x [1]) + (raw_y[3] - raw_y [1]) * (raw_y[3] - raw_y [1]));

	#ifdef report_constelation_geometry
	printf("\nTop side %d\nBottom Side %d\nW side %d\nE side %d\nE to W mid %d\nN to S mid %d\nDiag 14 to 6 %d\nDiag 7 to 1%d\n",constellation_geom[0],constellation_geom[1],constellation_geom[2],constellation_geom[3],constellation_geom[4],constellation_geom[5],constellation_geom[6],constellation_geom[7]);

	printf("AVG SPACING %d\n",average_spacing);
	#endif
	average_spacing = (constellation_geom[0]+constellation_geom[1]+constellation_geom[2]+constellation_geom[3]+constellation_geom[4]+constellation_geom[5])/6;//come up with a ballpark baseline for the dimension of your coord system's global scale (used later for global position fix)
	//below math puts observer point into global coordinates
		//should be agreement between x 14(i=0) and x 7i=3 as well as y 1(i=1) and y14(i=0)
		//global 14
		global_x_NS[10] = average_spacing - global_x_NS[0];//to NW corner of table for star 14
		global_y_NS[10] = average_spacing -global_y_NS[0];
		//global 1
		global_x_NS[11] = global_x_NS[1] * -1; //star 1
		global_y_NS[11] = average_spacing - global_y_NS[1];
		//global 6
		global_x_NS[12] = global_x_NS[2] * -1;//star 6
		global_y_NS[12] = global_y_NS[2] *-1;
		//global 7
		global_x_NS[13] = average_spacing - global_x_NS[3];//star 7
		global_y_NS[13] = global_y_NS[3] * -1;
		//global i4
		global_x_NS[14] = (average_spacing/2) - global_x_NS[4];//first middle point
		global_y_NS[14] = average_spacing - global_y_NS[4];
		//global i5
		global_x_NS[15] = (average_spacing/2) - global_x_NS[5];//star 6
		global_y_NS[15] = global_y_NS[5] * -1;
		//global i6
		global_x_NS[16] = global_x_NS[6] * -1;//star 7
		global_y_NS[16] = (average_spacing/2) - global_y_NS[6];
		//global i7
		global_x_NS[17] = average_spacing - global_x_NS[7];//first middle point
		global_y_NS[17] = (average_spacing/2) - global_y_NS[7];


		/*
		printf("\nGlobal 14  X %f Y %f \n",global_x_NS[10],global_y_NS[10]);
		printf("Global 1  X %f Y %f \n",global_x_NS[11],global_y_NS[11]);
		printf("Global 6  X %f Y %f \n",global_x_NS[12],global_y_NS[12]);
		printf("Global 7  X %f Y %f \n",global_x_NS[13],global_y_NS[13]);
		//from midps

		printf("\n\nGlobal i4  X %f Y %f \n",global_x_NS[14],global_y_NS[14]);
		printf("Global i5  X %f Y %f \n",global_x_NS[15],global_y_NS[15]);
		printf("Global i6  X %f Y %f \n",global_x_NS[16],global_y_NS[16]);
		printf("Global i7  X %f Y %f \n",global_x_NS[17],global_y_NS[17]);
		*/
	//end millionth attempt to get position independant of rotation of sensor
	global_x_NS[18] = (global_x_NS[10] + global_x_NS[11] + global_x_NS[12] + global_x_NS[13] + global_x_NS[14] + global_x_NS[15] + global_x_NS[16] + global_x_NS[17])/8;
	global_y_NS[18] = (global_y_NS[10] + global_y_NS[11] + global_y_NS[12] + global_y_NS[13] + global_y_NS[14] + global_y_NS[15] + global_y_NS[16] + global_y_NS[17])/8;
	printf("\n\nYOU ARE HERE!!! X %f Y %f\n\n",global_x_NS[18],global_y_NS[18]);

		FLAGS[(NS_POINTER +5)] = 0; //put down the data ready flag so that you don't keep processing the same stale data in the above section
		FLAGS[(NS_POINTER +6)] = 1; //let thread NS_DATA know that there is a fresh value from the NS localization routine
	}



		return 0;
}



//main portion of NS_SERIAL
init_and_stream_NS(fd);
for (;;)//this loop is for while being in the continuous data streaming mode and you will be grabbing the incoming data and checking it for CRC's then making it available for NS_DATA via flags
{
if (INTERUPTS[0] == 1)//if the master kill interrupt is sent, you are to shut down the serial streaming and empty the uart buffer
{
	kill_it (fd);
	break;
}
//DIGEST_NS the data


readbyte_cont(fd);
report_end_check_cont(); //this fills the FIFO_NS buffer with what is coming in from readbyte_cont and then copies a complete string after an EOL or End of message but more to come is found on the serial FD
//report_end also turns on FLAGS[(NS_POINTER +0] (average flag) and FLAGS[(NS_POINTER +1] (reportendflag) to let what got grabbed get calculated or averaged
// [0] is averageFLAG [1] is reportendFLAG [2] is transferFLAG
//if (reportendFLAG == 1)
if (FLAGS[(NS_POINTER +1)] == 1) //if you have fresh data from the DIGEST_NS()
//reportendFLAG is 1 when an EOL statement is found from the data stream coming in on the serial
{
		FLAGS[(NS_POINTER +3)] = check_input_checksum_DIGEST_NS(); //this checks the checksum of the DIGEST_NS array that was just populated by report_end_check_count()
			if ((FLAGS[(NS_POINTER +3)]) == 0) //this value can only be zero from check_input_checksum_DIGEST_NS() if the CRC counted did not match what it was told by the NS indicating that the data is somehow garbled
			{
			++ badcrccount;
			printf("\nbad checksum on DIGEST_NS array from report_end_check error count %d\n", badcrccount);
			FLAGS[(NS_POINTER +1)] = 0; //puts the DIGEST_NS[] data ready flag back down and leaves the averaging flag however it is	now you wait until the report_end_check_count() finds another end of report and fills the DIGEST_NS[] for another batch of data
			}

			if ((FLAGS[(NS_POINTER +3)]) != 0) //if there is a value put into FLAGS 3 from the check_input_checksum_DIGEST_NS() then it is the CRC value that matches what NS told us and indicates that the data is probably good
			{
			DECODEDIGEST_NS_3(); //this is for just one room being checked R5S0 and R5S1 for example
			//check_intensities(9000);
			//printf("FLAGS[(NS_POINTER +4] is %d\n",FLAGS[(NS_POINTER +4]);
			FLAGS[(NS_POINTER +4)] = check_intensities(MININTENSITY); //if the intensity is under input value, FLAGS[(NS_POINTER +4] will be 1
				if (FLAGS[(NS_POINTER +4)] == 0)
				{
				ROLLING_AVERAGE_DIGEST_NS(NUMAVERAGE); //THIS GIVES A ROLLING AVERAGE OF THE DATA INSTEAD OF WAITING UNTIL NUMAVERAGE READING HAVE BEEN AVERAGED
				star_analysis();

				FLAGS[(NS_POINTER +1)] = 0;
				}

				if (FLAGS[(NS_POINTER +2)] == 1)
				{
				//COORDTRANS();//Shruthi code
				//transferFLAG = 0;
				FLAGS[(NS_POINTER +2)] = 0;
				//printf ("LOOP NO %d logic if loop %d", i, j);
				}


			}//end if FLAGS[(NS_POINTER +3] != 0
}

//if (reportendFLAG == 2)
if (FLAGS[(NS_POINTER +1)] == 2)// this needs to be updated once the above FLAGS[(NS_POINTER +1] == 1 section is complete where you run all one last time, then break out of the forever loop 8/8/16 -WV
{

{
		FLAGS[(NS_POINTER +3)] = check_input_checksum_DIGEST_NS(); //this checks the checksum of the DIGEST_NS array that was just populated by report_end_check_count()
			if (FLAGS[(NS_POINTER +3)] == 0) //this value can only be zero from check_input_checksum_DIGEST_NS() if the CRC counted did not match what it was told by the NS indicating that the data is somehow garbled
			{
			++ badcrccount;
			printf("\nbad checksum on DIGEST_NS array from report_end_check error count %d\n", badcrccount);
			FLAGS[(NS_POINTER +1)] = 0; //puts the DIGEST_NS[] data ready flag back down and leaves the averaging flag however it is	now you wait until the report_end_check_count() finds another end of report and fills the DIGEST_NS[] for another batch of data
			}

			if ((FLAGS[(NS_POINTER +3)]) != 0) //if there is a value put into FLAGS 3 from the check_input_checksum_DIGEST_NS() then it is the CRC value that matches what NS told us and indicates that the data is probably good
			{
			DECODEDIGEST_NS_3(); //this is for just one room being checked R5S0 and R5S1 for example
			//check_intensities(9000);
			//printf("FLAGS[(NS_POINTER +4] is %d\n",FLAGS[(NS_POINTER +4]);
			FLAGS[(NS_POINTER +4)] = check_intensities(MININTENSITY); //if the intensity is under input value, FLAGS[(NS_POINTER +4] will be 1
				if (FLAGS[(NS_POINTER +4)] == 0)
				{
				ROLLING_AVERAGE_DIGEST_NS(NUMAVERAGE); //THIS GIVES A ROLLING AVERAGE OF THE DATA INSTEAD OF WAITING UNTIL NUMAVERAGE READING HAVE BEEN AVERAGED
				star_analysis();

				FLAGS[(NS_POINTER +1)] = 0;
				}

				if (FLAGS[(NS_POINTER +2)] == 1)
				{
				//COORDTRANS();//Shruthi code
				//transferFLAG = 0;
				FLAGS[(NS_POINTER +2)] = 0;
				//printf ("LOOP NO %d logic if loop %d", i, j);
				}


			}//end if FLAGS[(NS_POINTER +3] != 0
}

	break;//this state flag and will exit the loop if an end of reports if given by the NS
	}










}

#ifdef print_threads
printf("\n%d\t Ended \n",my_id);
#endif
  pthread_exit(NULL);
}

void *NS_DATA(void *id) 								//
{

  int my_id = (int)id;
#ifdef print_threads
printf("%d\t Started \n",my_id);
#endif
    for (;;)
    {
    if (FLAGS[(NS_POINTER +6)] == 1)//do something with the data that just came in from the star analysis program that was compiled within NS_Serial

    {
	//your global data that just got populated was global_x_NS[18],global_y_NS[18],global_heading_NS
		FLAGS[(NS_POINTER +6)] = 0;//when you are done, put down the fresh data flag
	}

}

#ifdef print_threads
printf("\n%d\t Ended \n",my_id);
#endif

  pthread_exit(NULL);
}

void *IMU_SERIAL_PORT(void *id) 								//Initialize code adapted from gyro_gnc. the Serial portion of the IMU so there is a reading
                                                                //of the current inertial data and heading data in a global for use by the IMU_data
{
  int my_id = (int)id;
#ifdef print_threads
printf("%d\t Started \n",my_id);
#endif
//Initialize the IMU...Begin
	int i;
	char temp;
	char fi;
	char fs3[]= "@mode,A*2E\n";
	char fs2[]= "@asc_out,RPYIMU*26\n";
	char fs1[]= "@divider,5*38\n";
	char fs4[]= "@mode,C*2C\n";
	int c1 = sizeof(fs1);
	int c2 = sizeof(fs2);
	int c3 = sizeof(fs3);
	int c4 = sizeof(fs4);

	if ((fi = serialOpen ("/dev/ttyACM1", 115200)) < 0)
	{
		fprintf (stderr, "Unable to open serial device: %s\n", strerror (errno)) ;
	}

	for (i=0; i<100; i++)
	{
		serialGetchar (fi);
		fflush (stdout) ;
	}

	printf("\n");
    for (i=0; i<c2; i++)
	{
		serialPutchar(fi,fs2[i]);
	}

	for (i=0; i<c1; i++)
	{
		serialPutchar(fi,fs1[i]);
	}

	for (i=0; i<c3; i++)
	{
		serialPutchar(fi,fs3[i]);
	}

	for (i=0; i<c4; i++)
	{
		serialPutchar(fi,fs4[i]);
	}

	for (i=1; i<2000; i++)
	{
		serialGetchar (fi) ;
		fflush (stdout) ;
    }

	while(1)
	{
		temp = serialGetchar(fi);
		if(temp == '\n')
		{
			printf("\n\nIMU Initialization Done\n\n");
			break;
		}
	}
serialClose(fi);
//Initialize the IMU...End

//IMU Get data...Begin

for(;;)
  {


    //Declare variables
	char fd;
	i=0;                                //buffer reader
	int	j=0,p=0,n5=0,n6=0,n8=0;         //indexing variables
	int N[15];
	char c[1000],ax[8],ay[8],Gz[9], temp2;
	float X_acce,Y_acce,Gyro_z;             //variables where IMU data will be stored

	if ((fd = serialOpen ("/dev/ttyACM1", 115200)) < 0)
	{
		fprintf (stderr, "Unable to open serial device: %s\n", strerror (errno)) ;
	}

	//this loop uses the temp variable to read in values from the buffer
	//every time temp encounters a new line the lop breaks so that a subsequent
	//loop can read in the new buffer data
	while(1)
	{
		temp2 = serialGetchar(fd);
		if(temp2 == '\n')
		{
			break;
		}
	}

	//Read in all IMU data values from the buffer. Note size of c[i] is 1000
	while(1)
	{
		c[i] = serialGetchar(fd);
		if(c[i]=='\n')
			break;
		i++;
	}

	//want to see how many characters are in the array c[i].
	//c[i] is specified to be no larger than 1000.
//    printf("The size of c[i] is: %d'\n'", i);
    int q;
    for(q=0; q<i; q++)
    {
//		printf("c[%d] is: %d'\n'", q, c[q]);
	}
	p = i;

    //This loop checks to see if any of the characters in the
    //IMU dataset array are ','. If they are this loop will use
    //array N[15] to mark the index number of the location of ','
	for(i=0; i<p; i++)
	{
		if(c[i]==',')
		{
			N[j]=i;
			j++;
		}
	}

    //This loop populates the ax array with acceleration values in
    //...you guessed it, the x direction
	for(i=(N[4]+1); i<N[5]; i++)
	{
		ax[n5]=c[i];
		n5++;
	}

    //This loop populates the ay array with acceleration values in
    //the y direction
	for(i=(N[5]+1); i<N[6]; i++)
	{
		ay[n6]=c[i];
		n6++;
	}

    //This loop populates the Gz array with angular acceleration values
	for(i=(N[9]+1); i<N[10]; i++)
	{
		Gz[n8]=c[i];
		n8++;
	}

	//convert string values to decimal values using atof
	X_acce = atof(ax);
	Y_acce = atof(ay);
	Gyro_z = atof(Gz);

	//update IMU data array values IMU data array is global
//	printf("Updating IMU Array\n");
	IMU[0] = X_acce - ax_bias;          //x acceleration
	IMU[1] = Y_acce - ay_bias;          //y acceleration
	IMU[2] = Gyro_z - gyro_bias;        //angular acceleration???

	printf("IMU[0] in IMU_Serial_Port is: %f\n", IMU[0]);
	printf("IMU[1] in IMU_Serial_Port is: %f\n", IMU[1]);
	printf("IMU[2] in IMU_Serial_Port is: %f\n", IMU[2]);

	for(i=0;i<p;i++)
	{
		if(c[i]==0);
	}

	//reset array index values for next read
	n5=0;n6=0;n8=0;

	//close the serial port
	serialClose(fd);

	if(INTERUPTS[0] == 1)
        break;
   }
//IMU get data...End



//    sleep(1);
#ifdef print_threads
printf("\n%d\t Ended \n",my_id);
#endif

  pthread_exit(NULL);
}

void *IMU_DATA(void *id)
{
 int my_id = (int)id;
#ifdef print_threads
printf("%d\t Started \n",my_id);
#endif
    sleep(1);
#ifdef print_threads
printf("\n%d\t Ended \n",my_id);
#endif

  pthread_exit(NULL);
}

void *ZIGBEE_SERIAL_PORT(void *id) 								//
{

  int my_id = (int)id;
#ifdef print_threads
printf("%d\t Started \n",my_id);
#endif
    sleep(1);
#ifdef print_threads
printf("\n%d\t Ended \n",my_id);
#endif

  pthread_exit(NULL);
}

void *ZIGBEE_DATA(void *id) 								//
{

  int my_id = (int)id;
#ifdef print_threads
printf("%d\t Started \n",my_id);
#endif
    sleep(1);
#ifdef print_threads
printf("\n%d\t Ended \n",my_id);
#endif

  pthread_exit(NULL);
}


void *ADC(void *id) 								//ACCESS TO THE TWO ADC PORTS
{

  int my_id = (int)id;
#ifdef print_threads
printf("%d\t Started \n",my_id);
#endif

    FLAGS[1] = 1; //temp flag up for testing
    FLAGS[2] = 1; //temp flag up for testing

 int pressure_query_fuel_tank()//when queried reports fuel level and also looks for a minimum fuel pressure threshold that will cause an interrupt[2] to pop indicating RTB procedures should begin
{

        adcValue2 = analogRead (PORT_ADC2);
        adcValue2 = adcValue2 - 177;
        adcValue2 = adcValue2/ADC2_TO_PSI;
	//if manifold pressure is low while valves are not being fired turn on the low fuel light (should tell robot to prepare to return to its station and to let the user know)
	//was :if ((FLAGS[3] == 0) && (adcValue2 < 500)) //FLAGS [3] was going to be used to indicate if any of the RCS valves were open so that you don't check your fuel tank while drawing air for RCS but might not be needed
	if (adcValue2 < MIN_FUEL) //FLAGS [3] was going to be used to indicate if any of the RCS valves were open so that you don't check your fuel tank while drawing air for RCS but might not be needed
	{

		#ifdef show_pressures
		{printf("\nLOW PRESSURE\n");}
		#endif
	INTERUPTS[2] = 1; //this indicates to the current scheduled tasks thingy that it is time to think go home
	}
	FLAGS[2] = 0; //put down the fuel tank pressure query flag
	return 0;
}

 int pressure_query_rcs() //function made available to all threads used for populating the pressures with current values
    {
		// port_ADC1 is == to ADC.AIN0 0 to 200 psi pressure transducer 1015 if not connected
		// port_ADC2 is == to ADC.AIN1 0 to 500 psi pressure transducer 1015 if not connected
		//
		adcValue1 = analogRead (PORT_ADC1);
		adcValue1 = adcValue1 - 177; //zero the channel to match atmospheric pressure
		adcValue1 = adcValue1/ADC1_TO_PSI;


        #ifdef show_pressures
        {printf("\n Pressure 1  %d PSI	Pressure 2 %d PSI\t", adcValue1, adcValue2);}
        #endif
        FLAGS[1] = 0; //put down the rcs manifold pressure query flag
	return 0;
	}

 for(;;)
    {





        // Get a reading from the ADC's

        if (FLAGS[1] == 1)//a flag indicating that there is an RCS manifold pressure request
        {
		pressure_query_rcs();
		}
        if (FLAGS[2] == 1)//a flag indicating that there is a fuel tank level request
        {
		pressure_query_fuel_tank();
		}
        //printf("\n ADC reading %d	other adc %d", adcValue1, adcValue2);
      if (INTERUPTS[0] == 1) //break out of forever loop if interupt signal is sent
	{


		break;
	}
    usleep(MINIMUM_SOLENOID_LATENCY);   //this way you are not completely slamming the system and still looping within the the RCS valve latency
    }



#ifdef print_threads
printf("\n%d\t Ended \n",my_id);
#endif

  pthread_exit(NULL);
}

void *RCS(void *id) 								//RCS basic functions for solenoid valves
{

  int my_id = (int)id;
#ifdef print_threads
printf("%d\t Started \n",my_id);
#endif



int initialize_thrusters()//this part turns the gpio pin handling and sets the digital io pins to output for valve actuation
{

    wiringPiSetup ();
    pinMode (T1, OUTPUT) ;
    pinMode (T2, OUTPUT) ;
    pinMode (T3, OUTPUT) ;
    pinMode (T4, OUTPUT) ;
    pinMode (T5, OUTPUT) ;
    pinMode (T6, OUTPUT) ;
    pinMode (T7, OUTPUT) ;
    pinMode (T8, OUTPUT) ;
    //make sure your valves are turned off
digitalWrite (T1, HIGH) ;	// off
digitalWrite (T2, HIGH) ;	// off
digitalWrite (T3, HIGH) ;	// off
digitalWrite (T4, HIGH) ;	// off
digitalWrite (T5, HIGH) ;	// off
digitalWrite (T6, HIGH) ;	// off
digitalWrite (T7, HIGH) ;	// off
digitalWrite (T8, HIGH) ;	// off


    return 0;

}

  int kill_RCS()//this function just sends the command to turn off all RCS valves
 {
	 printf("\nTurning off all Valves\n");
	 FWD_OFF;
	 REV_OFF;
	 SLEFT_OFF;
	 SRIGHT_OFF;
	 RRIGHT_OFF;
	 RLEFT_OFF;


//digitalWrite (T1, HIGH) ;	// off
//digitalWrite (T2, HIGH) ;	// off
//digitalWrite (T3, HIGH) ;	// off
//digitalWrite (T4, HIGH) ;	// off
//digitalWrite (T5, HIGH) ;	// off
//digitalWrite (T6, HIGH) ;	// off
//digitalWrite (T7, HIGH) ;	// off
//digitalWrite (T8, HIGH) ;	// off

return 0;
}

int firevalve(int whichvalve, int on)
{
	//on = 1; // troubleshooting, this is so that the dang valve will turn on because I don't understand yet
     switch( whichvalve )
     {
        case 1 : printf( "\nTOGGLE 1\n" );

			if (on == 1)
			{


			printf("ON 1");

			digitalWrite (T1, LOW) ; // on


			return 0;
			break;
				// on
		}
			else if (on == 0)
			{
			digitalWrite (T1, HIGH) ;	// off
			printf("OFF 1");

   			return 0;
            break;
        }
        case 2 : printf( "\nTOGGLE 2\n" );
            if (on == 1)
			digitalWrite (T2, LOW) ;	// on
			else
			digitalWrite (T2, HIGH) ;	// off
   			printf("OFF 2");

   			return 0;
            break;

        case 3 : printf( "\nTOGGLE 3\n" );
			if (on == 1)
			digitalWrite (T3, LOW) ;	// on
			else
			digitalWrite (T3, HIGH) ;	// off
   			return 0;
            break;

        case 4 : printf( "\nTOGGLE 4\n" );
			if (on == 1)
			digitalWrite (T4, LOW) ;	// on
			else
			digitalWrite (T4, HIGH) ;	// off
   			return 0;
            break;

        case 5 : printf( "\nTOGGLE 5\n" );
            if (on == 1)
			digitalWrite (T5, LOW) ;	// on
			else
			digitalWrite (T5, HIGH) ;	// off
   			return 0;
            break;
		case 6 : printf( "\nTOGGLE 6\n" );
            if (on == 1)
			digitalWrite (T6, LOW) ;	// on
			else
			digitalWrite (T6, HIGH) ;	// off
   			return 0;
                   break;
        case 7 : printf( "\nTOGGLE 7\n" );
            if (on == 1)
			digitalWrite (T7, LOW) ;	// on
			else
			digitalWrite (T7, HIGH) ;	// off
   			return 0;
                   break;
        case 8 : printf( "\nTOGGLE 8\n" );
            if (on == 1)
			digitalWrite (T8, LOW) ;	// on
			else
			digitalWrite (T8, HIGH) ;	// off
   			return 0;
                   break;


        default  : printf( "default exit in rcs cases?\n" );
                   break;
     }







    return 0;
}


int SERVICEVALVECOMMANDBUFFER()//routine that looks at the VALVECOMMANDBUFFER and sets valve flags as well as actuates the corresponding relays on the relay board through the gpio this is one layer below the incoming commands
{
int i = 1;
	//VALVECOMMANDBUFFER[]
	if (VALVECOMMANDBUFFER[0] == 1)//just checking if the safety has been turned off
	{
		for (i = 1; i <= 8; ++i)
		{//-----------------------------------VALVEs 1 through 8 loop
		if (VALVECOMMANDBUFFER[i] == 1) //if a command in the valve firing buffer is set to fire
		{
			if (VALVEFLAGBUFFER[i] == 0) //check to see if the valve flag for that valve has been raised and if it is not (= 0) do the following
			{
				VALVEFLAGBUFFER[i] = 1;//raise the flag for the valve that is to fire so that this isn't called again until the turn off command in the valvve firing buffer is found
				firevalve(i,1); //use firevalve() to set the pin low signaling the relay to actuate
				printf("TURNED ON");
			}
			else
			{
				//printf("NADA"); //if the flag for the current valve is raised, it has already been fired and this tells the if statement to skip turning the pin low again
			}

		}
		if (VALVECOMMANDBUFFER[i] == 0) //if a command in the valve firing buffer is set to turn of for the ith valve do the following
		{
			if (VALVEFLAGBUFFER[i] == 1) //check to see if the valve flag for that valve has been lowered and if it has not, lower it
			{
				VALVEFLAGBUFFER[i] = 0;//lower the valve flag for the current valve that is being requested to be turned off
				firevalve(i,0); //set the gpio pin high for the ith valve's relay
				FLAGS[1] = 1; //send a pressure query after firing the valve
				printf("TURNED OFF ");
			}
			else
			{
				//printf("NADA"); //if the command to turn off the valve had already been flagged as turned off, skip sending the gpio pin high command
			}
		}

	 }







	}
	return 0;

}

//begin main part of this thread

initialize_thrusters();
SAFETYOFF;

for (;;)
{
	SERVICEVALVECOMMANDBUFFER();//looks at VALVECOMMANDBUFFER AND VALVECOMMANDFLAGS and if value changes, the corresponding valve is changed
	usleep(500);
	if (INTERUPTS[0] == 1) //break out of forever loop if interupt signal is sent
	{

		kill_RCS();
		//pthread_mutex_unlock(&count_mutex);
		break;
	}

}
//kill command called shut down everything
kill_RCS();

#ifdef print_threads
printf("\n%d\t Ended \n",my_id);
#endif

  pthread_exit(NULL);
}


void *GNC(void *id) 							//GNC basic function using North Star data
{
    //First step here is to read in data from the North Star.
    //Global x,y values are found at global_x_NS[18] and global y values are found at global_y_NS[18]
    //********Next need to contact the IMU to get both velocity and acceleration values for x, y, and theta******** -- JA
  int my_id = (int)id;
#ifdef print_threads
printf("%d\t Started \n",my_id);
#endif

//Define Matrix Functions
//void MatrixMultiply(int m, int p, int n, float A[m][p], float B[p][n],  float C[m][n]);
//void MatrixAdd(int m, int n, float A[m][n], float B[m][n], float C[m][n]);
//void MatrixSubtract(int m, int n, float A[m][n], float B[m][n], float C[m][n]);
//void MatrixTranspose(int m, int n, float A[m][n], float B[m][n]);
//int MatrixInversion(int n, float *A, float *AInverse);
//float covariance (float* x ,float* y, int size);
//float variance (float* x, int size);
//void navigate_left();
//void navigate_right();
//void navigate_fwd();
//void navigate(float x, float y, float gyro);


void MatrixMultiply(int m, int p, int n, float A[m][p], float B[p][n],  float C[m][n])
{

int i, j, k;
for (i=0;i<m;i++)
   for(j=0;j<n;j++)
      {
      C[i][j]=0;
      for (k=0;k<p;k++)
         C[i][j]= C[i][j]+A[i][k]*B[k][j];
      }
}

void MatrixAdd(int m, int n, float A[m][n], float B[m][n], float C[m][n])
{
int i, j;
for (i=0;i<m;i++)
   for(j=0;j<n;j++)
      C[i][j] = A[i][j] + B[i][j];
}

void MatrixSubtract(int m, int n, float A[m][n], float B[m][n], float C[m][n])
{

int i, j;
for (i=0;i<m;i++)
   for(j=0;j<n;j++)
      C[i][j] = A[i][j] - B[i][j];
}

void MatrixTranspose(int m, int n, float A[m][n], float B[m][n])
{

int i, j;
for (i=0;i<m;i++)
   for(j=0;j<n;j++)
      B[j][i]=A[i][j];
}

int MatrixInversion(int n, float *A, float *AInverse)
{
#define MAX_MATRIX 16

int i, j, iPass, imx, icol, irow;
float det, temp, pivot, factor;

if (n==1)
   {
   AInverse[0] = 1/A[0];
   return 1;
   }
det = 1;
for (i = 0; i < n; i++)
   {
   for (j = 0; j < n; j++)
      {
      AInverse[n*i+j] = 0;
      }
   AInverse[n*i+i] = 1;
   }
// The current pivot row is iPass.
// For each pass, first find the maximum element in the pivot column.
for (iPass = 0; iPass < n; iPass++)
   {
   imx = iPass;
   for (irow = iPass; irow < n; irow++)
      {
      if (fabs(A[n*irow+iPass]) > fabs(A[n*imx+iPass])) imx = irow;
      }
   // Interchange the elements of row iPass and row imx in both A and AInverse.
   if (imx != iPass)
      {
      for (icol = 0; icol < n; icol++)
         {
         temp = AInverse[n*iPass+icol];
         AInverse[n*iPass+icol] = AInverse[n*imx+icol];
         AInverse[n*imx+icol] = temp;
         if (icol >= iPass)
            {
            temp = A[n*iPass+icol];
            A[n*iPass+icol] = A[n*imx+icol];
            A[n*imx+icol] = temp;
            }
         }
      }
   // The current pivot is now A[iPass][iPass].
   // The determinant is the product of the pivot elements.
   pivot = A[n*iPass+iPass];
   det = det * pivot;
   if (det == 0)
      {
      return 0;
      }
   for (icol = 0; icol < n; icol++)
      {
      // Normalize the pivot row by dividing by the pivot element.
      AInverse[n*iPass+icol] = AInverse[n*iPass+icol] / pivot;
      if (icol >= iPass) A[n*iPass+icol] = A[n*iPass+icol] / pivot;
      }
   for (irow = 0; irow < n; irow++)
      // Add a multiple of the pivot row to each row.  The multiple factor
      // is chosen so that the element of A on the pivot column is 0.
      {
      if (irow != iPass) factor = A[n*irow+iPass];
      for (icol = 0; icol < n; icol++)
         {
         if (irow != iPass)
            {
            AInverse[n*irow+icol] -= factor * AInverse[n*iPass+icol];
            A[n*irow+icol] -= factor * A[n*iPass+icol];
            }
         }
      }
   }
   return 1;
}

  // ***************** Coariance function *******************

float covariance (float* x ,float* y, int size)
{
    float sumx = 0;
    float sumy = 0;
    float pro1 = 0;
    float Sum = 0;
    float pro = 0;
    float dif = 0;
    float cov=0;

    int i;

    for (i = 0; i < size; ++i)
    {
      sumx += x[i];
      sumy += y[i];

      pro1 = x[i]*y[i];
      Sum = Sum + pro1;
   }

   pro = (sumx*sumy)/size;
   dif = Sum - pro;
  if (size<2)
  return 0;
  else
  {
   cov = dif/(size-1);
   return cov;
  }

}

       // ***************** Variance function *******************

float variance (float* x, int size)
{
    float sumx = 0;
    float var = 0;
    float sum1 = 0;
    float mean =0;
    int i;

    for (i = 0; i < size; ++i)
    {
      sumx += x[i];
     }

   mean = sumx/size;

    for (i = 0; i < size; ++i)
    {
      sum1 = sum1 + ((x[i] - mean)*(x[i] - mean));
     }
    if (size<2)
    return 0;
    else
   {
    var = sum1/(float)(size-1);
    return var;
   }
   }

void navigate_left()
	{

		printf("\nnavigation started left \n");

			//digitalWrite(RIGHT1,LOW);		//original command from shruthi's
			//digitalWrite(RIGHT2,LOW);		//original command from shruthi's
			RRIGHT_ON;
		           delay(100);
		    RRIGHT_OFF;
			//digitalWrite(RIGHT1,HIGH);	//original command from shruthi's
		    //digitalWrite(RIGHT2,HIGH);	//original command from shruthi's


	}

	void navigate_right()
	{

		printf("\nnavigation started right \n");

			//digitalWrite(LEFT1,LOW);		//original command from shruthi's
			//digitalWrite(LEFT2,LOW);		//original command from shruthi's
			RLEFT_ON;
		           delay(100);
		    RLEFT_OFF;
			//digitalWrite(LEFT1,HIGH);		//original command from shruthi's
		    //digitalWrite(LEFT2,HIGH);		//original command from shruthi's

	}

	void navigate_fwd()
	{

		printf("\nnavigation started FWD\n");
			//digitalWrite( BACK1,LOW);		//original command from shruthi's
			//digitalWrite( BACK2,LOW);		//original command from shruthi's
			SLEFT_ON;
                        delay(100);
			SLEFT_OFF;
			//digitalWrite( BACK1,HIGH);	//original command from shruthi's
		    //digitalWrite( BACK2,HIGH);	//original command from shruthi's

	}

	                     // ***************** NAVIGATION function *******************

void navigate(float x, float y, float gyro)
	{

		printf("\nnavigation started\n");


		float Y1,Y2,X1,X2,theta, thetad,angle_diff;
		Y2 = Y_final;
		Y1 = y;
		X2 = X_final;
		X1 = x;
		printf("\nin d loop: xi = %f, yi = %f, xf = %f, yf = %f\n", X1,Y1,X2,Y2);
		if(Y1 == Y2)
		theta = 0;
		else if(X1 == X2)
		theta = pi;

		else
		{

		theta = atan((Y2-Y1)/(X2-X1));

	    }

		if(Y2>Y1 && X2>X1)
		{
			theta = theta;
		}

		else if(Y2>Y1 && X2<X1)
		{
			theta = pi + theta;
		}

		else if(Y2<Y1 && X2<X1)
		{
			theta = pi + theta;
		}

		else if(Y2<Y1 && X2>X1)
		{
			theta = 2*pi + theta;
		}


		else printf("\n\n\nERROR\n\n\n");

		thetad = theta * 180/(22/7);

		theta = thetad;
		printf("\ntheta = %f, phi = %f\n", theta, phi);


	 angle_diff = (phi-theta);

		if(angle_diff < -10 || angle_diff > 10)
		{
			printf("\n angle_diff = %f\n", angle_diff);

		if ((angle_diff > 0 && angle_diff<180)|| (angle_diff >-360 && angle_diff<-180))
		{
			if(gyro>-0.1)
			//printf("\n TURN LEFT\n");
			//printf("\n TURN LEFT\n");
			//printf("\n TURN LEFT\n");
			navigate_left();


			// turn right for 250 ms
		}
		else if ((angle_diff>-180 && angle_diff <0) || (angle_diff>180  && angle_diff< 360))
		{
			if(gyro<0.1)
			//printf("\n TURN RIGHT\n");
			//printf("\n TURN RIGHT\n");
			//printf("\n TURN RIGHT\n");
			navigate_right();

			// turn left for 250 ms
		}
	}

	  	else

		{
			//printf("\n MOVE FORWARD\n");
			//printf("\n MOVE FORWARD\n");
			//printf("\n MOVE FORWARD\n");
			navigate_fwd();
			// move forward for 250 ms

		}

	}


                  // ***************** KALMAN FILTER *******************

float A[4][4] = {{1,0,t,0},{ 0,1,0,t},{ 0,0,1,0},{ 0,0,0,1}};
float AT[4][4] = {{1,0,0,0},{0,1,0,0},{t,0,1,0},{0,t,0,1}};
float B[4][2]  = {{(t*t/2),0},{ 0,(t*t/2)},{ t,0},{ 0,t}};
float AX[4][1] = {{0},{0},{0},{0}};
float BIMU[4][1] = {{0},{0},{0},{0}};
float x_hat[4][1] = {{0},{0},{0},{0}};
float IMU_input[2][1] = {{0},{0}};
float AP[4][4];
float P0[4][4] = {{0,0,0,0},{ 0,0,0,0},{ 0,0,0,0},{ 0,0,0,0}};
float APA[4][4];
float Q[4][4] = {{0.00001,0.00001,0.00001,0.00001},{0.00001,0.00001,0.00001,0.00001},{0.00001,0.00001,0.00001,0.00001},{0.00001,0.00001,0.00001,0.00001}};
float P_hat[4][4];
float y_hat[2][1];
float z[2][1];
float H[2][4] = {{1,0,0,0},{ 0,1,0,0}};
float HT[4][2] = {{1,0},{0,1},{0,0},{0,0}};
float R[2][2] = {{0.01,0},{ 0,0.01}};
float HP[2][4];
float HPH[2][2];
float S_inv[2][2];
float K[4][2];
float KT[2][4];
float PH[4][2];
float Ky[4][1];
float I[4][4] = {{1,0,0,0},{ 0,1,0,0},{ 0,0,1,0},{ 0,0,0,1}};
float KH[4][4];
float iKH[4][4];
float P_n[4][4];
float Hx[2][1];
float X_n[4][1];
float S[2][2];
float Zxy[2][1] = {{0},{0}};
float VarX,VarY,VarXdot,VarYdot,Cov_XXdot,Cov_YYdot;
float theta;
float X0[4][1];
float F[4][4];
float FT[4][4];
float FP[4][4];
float FPF[4][4];
float KR[4][2];
float KRK[4][4];
int kalman_count =0;
float X_all[10][1];


void set_mincount(int fd, int mcount)
{
    struct termios tty;

    if (tcgetattr(fd, &tty) < 0) {
        printf("Error tcgetattr: %s\n", strerror(errno));
        return;
    }

    tty.c_cc[VMIN] = mcount ? 1 : 0;
    tty.c_cc[VTIME] = 10;        /* half second timer */

    if (tcsetattr(fd, TCSANOW, &tty) < 0)
        printf("Error tcsetattr: %s\n", strerror(errno));
}

void Kalman_position(float X_n[4][1], float IMU[3], float Pozyx[4])
{
	int i,j;

//	Pozyx_Getdata(Pozyx);

//  IMU_GetData(IMU);

    Zxy[0][0] = (Pozyx[0]/100) ;
    Zxy[1][0] = (Pozyx[1]/100) ;

	printf("IMU[0] in GNC thread is : %f\n", IMU[0]);
	printf("IMU[1] in GNC thread is : %f\n", IMU[1]);
    IMU_input[0][0] = IMU[0];
	IMU_input[1][0] = IMU[1];



	MatrixMultiply(4,4,1, A, X0,AX);
	MatrixMultiply(4,2,1, B, IMU_input,BIMU);
	MatrixAdd(4,1, AX, BIMU,x_hat);

	MatrixMultiply( 4, 4, 4, A, P0,AP);
	MatrixMultiply(4, 4, 4,AP, AT, APA);
	MatrixAdd(4,4, APA,Q,P_hat);

	MatrixMultiply(2,4, 1, H, x_hat,Hx);
	MatrixSubtract( 2,1,  Zxy, Hx,y_hat);

	MatrixMultiply(2, 4, 4,H, P_hat, HP);
	MatrixMultiply( 2, 4, 2, HP, HT,HPH);

	MatrixAdd(2,2, HPH,R,S);

	MatrixInversion(2,(float *)S, (float *)S_inv);

	MatrixMultiply(4, 4, 2, P_hat, HT, PH);
	MatrixMultiply(4,2,2, PH, S_inv,K);

	MatrixMultiply(4, 2, 1, K, y_hat, Ky);
	MatrixAdd(4,1,x_hat,Ky,X_n);

	MatrixMultiply(4,2,4 , K, H, KH);
	MatrixSubtract(4,4, I, KH, F);
	MatrixMultiply(4,4,4, F,P_hat, FP);
	MatrixTranspose(4,4,F,FT);
	MatrixTranspose(4,2, K, KT);
	MatrixMultiply(4,4,4,FP,FT , FPF);
	MatrixMultiply(4,2,2, K, R, KR);
	MatrixMultiply(4,2,4, KR, KT, KRK);
	MatrixAdd(4,4,FPF,KRK,P_n);


	for(i=0;i<4;i++)
	{
		X0[i][0] = X_n[i][0];
		for(j=0;j<4;j++)
		P0[i][j] = P_n[i][j];
	}

	kalman_count++;
	printf("\ncount = %d\n",kalman_count);
}


	//Debug
	printf("here 1\n");




    long ns;
	double t_ns;
	float sumA=0, sumax=0,sumay=0, sumgy=0;
	int count_gnc=0, i;
	float x,y, gyro;


	wiringPiSetup () ;


	pinMode(T2, OUTPUT);
	pinMode(T6, OUTPUT);
	pinMode(T1,  OUTPUT);
	pinMode(T5, OUTPUT);
	pinMode(T3,  OUTPUT);
	pinMode(T8, OUTPUT);


	digitalWrite (T2, HIGH) ;// off
	digitalWrite (T6, HIGH) ;// off
	digitalWrite (T1, HIGH) ;// off
	digitalWrite (T5, HIGH) ;// off
	digitalWrite (T3, HIGH) ;// off
	digitalWrite (T8, HIGH) ;// off


	struct timespec spec;
	clock_gettime(CLOCK_REALTIME, &spec);

	ns = round(spec.tv_nsec);
	t_ns = ns;

	Epoch = spec.tv_sec + (t_ns/1e9);

	//Debug
//	printf("Calling POZYX Initialize\n");
//	Pozyx_initialisation();
	//Debug
//	printf("Calling IMU Initialize\n");
//	IMU_initialise();



	for(count_gnc=0;count_gnc<100;count_gnc++)
	{
		//printf("\nPozx Data\n");
//		Pozyx_Getdata(Pozyx);
		//printf("\nIMU Data\n");
//		IMU_GetData(IMU);

		sumA  = sumA  + Pozyx[2];
		sumax = sumax + IMU[0];
		sumay = sumay + IMU[1];
		sumgy = sumgy + IMU[2];

		printf("\nX = %f, Y = %f, theta = %f, time = %f, sumA = %f\n", Pozyx[0], Pozyx[1], Pozyx[2], Pozyx[3], sumA);
		printf("\nax = %f, ay = %f, gy = %f\n", IMU[0], IMU[1], IMU[2]);

		delay(100);
    }

    printf("\nax = %f, ay = %d\n", sumA, count_gnc);
    theta_bias = sumA/count_gnc;
    ax_bias = sumax/count_gnc;
	ay_bias = sumay/count_gnc;
	gyro_bias = sumgy/count_gnc;


	printf("\n\ntheta_bias = %f, ax_bias = %f, ay_bias = %f, gyro_bias = %f\n\n",theta_bias, ax_bias, ay_bias,gyro_bias);

//    Pozyx_Getdata(Pozyx);

//	IMU_GetData(IMU);

    X0[0][0] = (Pozyx[0]/100) ;
    X0[1][0] = (Pozyx[1]/100) ;
    X0[2][0] = 0;
    X0[3][0] = 0;





    //this loop checks to see if the destination is reached -- if destination is not reached
    //signal is sent to relays to fire thrusters.
	for(i=0;i<10;i++)
	{
		Kalman_position(X_n, IMU, Pozyx);
		phi = Pozyx[2];
		if(phi<0)
		phi = phi +360;

		x = X_n[0][0];
		y = X_n[1][0];
		gyro = IMU[2];
		printf("\nPx = %f, X = %f: Py = %f, Y = %f, theta = %f, gyro_acce = %f",Pozyx[0], x*100, Pozyx[1], y*100,Pozyx[2], IMU[2] );

		if(y < (Y_final-0.1) || y > (Y_final+0.1) || x < (X_final-0.1) || x > (X_final+0.1))
		{

			printf("\n x = %f, y = %f\n", x,y);
			printf("naviagtion fcn\n");
		    navigate(x,y,gyro );
		}

		else
		{
			printf("\n Destination is reached\n");

			break;
		}
		printf("looped %d times\n", i);
	}





//sleep(1);
#ifdef print_threads
printf("\n%d\t Ended \n",my_id);
#endif

  pthread_exit(NULL);
}

int main(int argc, char *argv[])
{

  int id=0;//variable used for describing thread environment id's that get transfered into the threads so that if you need any data from the or some kind of identity information you have it

  pthread_t threads[THREADS];
  pthread_attr_t attr;

  /* Initialize mutex and condition variable objects */
  pthread_mutex_init(&count_mutex, NULL); 						//there is a count_mutex
  pthread_cond_init (&count_threshold_cv, NULL);				//there is a count_threshold_cv

  /* For portability, explicitly create threads in a joinable state */
  pthread_attr_init(&attr);
  pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_JOINABLE);

//RTC
 pthread_create(&threads[(id)], &attr, RTC, (void *)id);	//create the first thread pointed at watch_count passing long t1
 #ifdef print_threads
 printf("\nCreate Thread ID %d\n",(id));
 #endif


 //RTC_ALARM_CLOCKS
 ++id;
 pthread_create(&threads[(id)], &attr, RTC_ALARM_CLOCKS, (void *)id);	//create the first thread pointed at watch_count passing long t1
  #ifdef print_threads
 printf("\nCreate Thread ID %d\n",(id));
 #endif


 //NS_SERIAL_PORT
  ++id;//inc thread counter
   #ifdef print_threads
printf("\nCreate Thread ID %d\n",(id));
 #endif
  pthread_create(&threads[(id)], &attr, NS_SERIAL_PORT, (void *)id);	//create the first thread pointed at watch_count passing long t1


 //NS_DATA
 ++id;//inc thread counter
   #ifdef print_threads
printf("\nCreate Thread ID %d\n",(id));
 #endif
  pthread_create(&threads[(id)], &attr, NS_DATA, (void *)id);	//create the first thread pointed at watch_count passing long t1

 //IMU_SERIAL_PORT
 ++id;//inc thread counter
   #ifdef print_threads
printf("\nCreate Thread ID %d\n",(id));
 #endif
  pthread_create(&threads[(id)], &attr, IMU_SERIAL_PORT, (void *)id);	//create the first thread pointed at watch_count passing long t1

 //IMU_DATA
 ++id;//inc thread counter
   #ifdef print_threads
printf("\nCreate Thread ID %d\n",(id));
 #endif
  pthread_create(&threads[(id)], &attr, IMU_DATA, (void *)id);	//create the first thread pointed at watch_count passing long t1

 //ZIGBEE_SERIAL_PORT
 ++id;//inc thread counter
   #ifdef print_threads
printf("\nCreate Thread ID %d\n",(id));
 #endif
  pthread_create(&threads[(id)], &attr, ZIGBEE_SERIAL_PORT, (void *)id);	//create the first thread pointed at watch_count passing long t1

 //ZIGBEE_DATA
 ++id;//inc thread counter
  #ifdef print_threads
printf("\nCreate Thread ID %d\n",(id));
 #endif
  pthread_create(&threads[(id)], &attr, ZIGBEE_DATA, (void *)id);	//create the first thread pointed at watch_count passing long t1

 //ADC
 ++id;//inc thread counter
   #ifdef print_threads
printf("\nCreate Thread ID %d\n",(id));
 #endif
  pthread_create(&threads[id], &attr, ADC, (void *)(id));	//create the first thread pointed at watch_count passing long t1

 //RCS
 ++id;//inc thread counter
  #ifdef print_threads
printf("\nCreate Thread ID %d\n",(id));
 #endif
  pthread_create(&threads[id], &attr, RCS, (void *)(id));	//create the first thread pointed at watch_count passing long t1

 //GNC
 ++id;//inc thread counter
 #ifdef print_threads
printf("\nCreate Thread ID %d\n",(id));
 #endif
 pthread_create(&threads[id], &attr, GNC, (void *) (id));   //create the first thread pointed at watch_count passing long t1

 //Pozyx_Serial_Port
 ++id;//inc thread counter
 #ifdef print_threads
printf("\nCreate Thread ID %d\n",(id));
 #endif
 pthread_create(&threads[id], &attr, Pozyx_Serial_Port, (void *) (id));   //create the first thread pointed at watch_count passing long t1

//Pozyx_Data
// ++id;//inc thread counter
// #ifdef print_threads
//printf("\nCreate Thread ID %d\n",(id));
// #endif
// pthread_create(&threads[id], &attr, Pozyx_Data, (void *) (id));   //create the first thread pointed at watch_count passing long t1





   /* Clean up and exit */
  pthread_attr_destroy(&attr);
  pthread_mutex_destroy(&count_mutex);
  pthread_cond_destroy(&count_threshold_cv);
  pthread_exit (NULL);

}

