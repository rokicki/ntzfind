/* ntzfind 3.0 (horizontal shift not included in this version)
** A spaceship search program by "zdr" with modifications by Matthias Merzenich and Aidan Pierce and Tomas Rokicki
**
** Warning: this program uses a lot of memory (especially for wide searches).
*/

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <random>
#include <pthread.h>
#include "tab.cpp"

#define BANNER "ntzfind 3.0 by \"zdr\", Matthias Merzenich, Aidan Pierce, and Tomas Rokicki, 24 February 2018"
#define FILEVERSION ((unsigned long) 2016122101)  //yyyymmddnn, same as last qfind release (differs from the above)

#define MAXPERIOD 30
#define MAXWIDTH 10  // increasing this requires a few other changes
#define MIN_DUMP 20
#define DEFAULT_DEPTH_LIMIT 2000
#define NUM_PARAMS 13

#define P_WIDTH 1
#define P_PERIOD 2
#define P_OFFSET 3
#define P_DEPTH_LIMIT 4
#define P_SYMMETRY 5
#define P_MAX_LENGTH 6
#define P_INIT_ROWS 7
#define P_FULL_PERIOD 8
#define P_NUM_SHIPS 9
#define P_FULL_WIDTH 10
#define P_REORDER 11
#define P_DUMP 12

#define SYM_ASYM 1
#define SYM_ODD 2
#define SYM_EVEN 3
#define SYM_GUTTER 4

/*
 *   For multithreading, all of these are fixed or constant before any
 *   threads are created---or, their modification is restricted to when
 *   we hold the global lock (sp).
 */
const char *rule = "B3/S23" ;
int nttable[512] ;
int sp[NUM_PARAMS];
uint16_t **gInd3 ;
uint32_t *gcount ;
uint16_t *ev2Rows;               // lookup table that gives the evolution of a row with a blank row above and a specified row below
long long memusage ;
long long memlimit = 0x7000000000000000LL ;
int bc[8] = {0, 1, 1, 2, 1, 2, 2, 3};
int period, offset, width ;
uint16_t fpBitmask = 0;
int fwdOff[MAXPERIOD], backOff[MAXPERIOD], doubleOff[MAXPERIOD], tripleOff[MAXPERIOD];
char nttable2[512] ;

/*
** For each possible phase of the ship, equivRow[phase] gives the row that 
** is equivalent if the pattern is subperiodic with a specified period.
** equivRow2 is necessary if period == 12, 24, or 30, as then two subperiods
** need to be tested (e.g., if period == 12, we must test subperiods 4 and 6).
** twoSubPeriods is a flag that tells the program to test two subperiods.
*/

int equivRow[MAXPERIOD];
int equivRow2[MAXPERIOD];
int twoSubPeriods = 0;
int *gWork ;
int *rowHash ;
uint16_t *valorder ;
uint16_t *bbuf ;
int bbuf_left = 0 ;
int cachemem = 32 ; // megabytes for the cache
long long cachesize ;
struct cacheentry {
   uint16_t *p1, *p2, *p3 ;
   int abn, r ;
} ;
char * loadFile;
int numThreads = 4 ;
const int MAXTHREADS = 256 ;
class searchThread *threads ;
long long currentWork ; // below this, assigned; above or equal, waiting
int divergenceLevel ; // where we split by thread
/*
 *   These are per-thread (are modified by search).  So we embed them in
 *   a class.
 */
class searchThread {
public:
   searchThread() : pInd(0), pRemain(0), pRows(0), cache(0), lastNonempty(0),
                    rowNum(0), phase(0), shipNum(0), firstFull(0) { }
   void initializeThread(char *f) ;
   void search();
private:
   int getkey(uint16_t *p1, uint16_t *p2, uint16_t *p3, int abn);
   void setkey(int h, int v);
   void loadInitRows(char * file) ;
   int lookAhead(int a);
   int checkInteract(int a);
   void buffPattern(int theRow);
   void printPattern() ;
   uint16_t **pInd ;
   int *pRemain;
   uint16_t *pRows;
   int *lastNonempty;
   struct cacheentry *cache ;
   int phase, rowNum ;
   int shipNum, firstFull;
   char *buf;
   long long threadpad[8] ; // ensure threads don't share cachelines
} ;
pthread_mutex_t mmutex ;
void init_mutex() {
  pthread_mutex_init(&mmutex, NULL) ;
}
void get_global_lock() {
   pthread_mutex_lock(&mmutex) ;
}
void release_global_lock() {
   pthread_mutex_unlock(&mmutex) ;
}
pthread_t *p_thread ;
#define THREAD_RETURN_TYPE void *
#define THREAD_DECLARATOR
void spawn_thread(int i, THREAD_RETURN_TYPE(THREAD_DECLARATOR *p)(void *),
                                                                     void *o) {
   pthread_create(&(p_thread[i]), NULL, p, o) ;
}
void join_thread(int i) {
   pthread_join(p_thread[i], 0) ;
}
void *searchWorker(void *o) {
   searchThread *st = (searchThread *)o ;
   st->search() ;
   return 0 ;
}
/*
 *   Should I (my thread) do this work item?
 */
int forMeQ(long long v) {
   get_global_lock() ;
// printf("Query about %lld while %lld\n", v, currentWork) ;
   if (v > currentWork)
      fprintf(stderr, "Error; got a work item larger than expected") ;
   int r = 0 ;
   if (v == currentWork) {
      r = 1 ;
      currentWork++ ;
   }
   release_global_lock() ;
   return r ;
}

/*
 *   There should be no data declarations after this line; everything
 *   else should just be code.
 */

/* get_cpu_time() definition taken from
** http://stackoverflow.com/questions/17432502/how-can-i-measure-cpu-time-and-wall-clock-time-on-both-linux-windows/17440673#17440673
*/

//  Windows
#ifdef _WIN32
#include <Windows.h>
double get_cpu_time(){
    FILETIME a,b,c,d;
    if (GetProcessTimes(GetCurrentProcess(),&a,&b,&c,&d) != 0){
        //  Returns total user time.
        //  Can be tweaked to include kernel times as well.
        return
            (double)(d.dwLowDateTime |
            ((unsigned long long)d.dwHighDateTime << 32)) * 0.0000001;
    }else{
        //  Handle error
        return 0;
    }
}

//  Posix/Linux
#else
double get_cpu_time(){
    return (double)clock() / CLOCKS_PER_SEC;
}
#endif

void error(const char *s) {
   fprintf(stderr, "%s\n", s) ;
   exit(10) ;
}

void makePhases(){
   int i;
   for (i = 0; i < period; i++) backOff[i] = -1;
   i = 0;
   for (;;) {
      int j = offset;
      while (backOff[(i+j)%period] >= 0 && j < period) j++;
      if (j == period) {
         backOff[i] = period-i;
         break;
      }
      backOff[i] = j;
      i = (i+j)%period;
   }
   for (i = 0; i < period; i++)
      fwdOff[(i+backOff[i])%period] = backOff[i];
   for (i = 0; i < period; i++) {
      int j = (i - fwdOff[i]);
      if (j < 0) j += period;
      doubleOff[i] = fwdOff[i] + fwdOff[j];
   }
   for (i = 0; i <  period; i++){
      int j = (i - fwdOff[i]);
      if (j < 0) j += period;
      tripleOff[i] = fwdOff[i] + doubleOff[j];
   }
}

int gcd(int a, int b){
   int c;
   while (b){
      c = b;
      b = a % b;
      a = c;
   }
   return a;
}

int smallestDivisor(int b){
   int c = 2;
   while(b % c) ++c;
   return c;
}

void makeEqRows(int maxFactor, int a){
   int tempEquivRow[MAXPERIOD];
   int i,j;
   for(i = 0; i < period; ++i){
      tempEquivRow[i] = i;
      for(j = 0; j < maxFactor; ++j){
         tempEquivRow[i] += backOff[tempEquivRow[i] % period];
      }
      tempEquivRow[i] -= offset * maxFactor + i;
      if(a == 1) equivRow[i] = tempEquivRow[i];
      else equivRow2[i] = tempEquivRow[i];
   }
   for(i = 0; i < period; ++i){     // make equivRow[i] negative if possible
      if(tempEquivRow[i] > 0){
         if(a == 1) equivRow[i + tempEquivRow[i]] = -1 * tempEquivRow[i];
         else equivRow2[i + tempEquivRow[i]] = -1 * tempEquivRow[i];
      }
   }
}

int slowEvolveBit(int row1, int row2, int row3, int bshift){
   return nttable[(((row2>>bshift) & 2)<<7) | (((row1>>bshift) & 2)<<6)
                | (((row1>>bshift) & 4)<<4) | (((row2>>bshift) & 4)<<3)
                | (((row3>>bshift) & 7)<<2) | (((row2>>bshift) & 1)<<1)
                |  ((row1>>bshift) & 1)<<0];
}

void fasterTable() {
   int p = 0 ;
   for (int row1=0; row1<8; row1++)
      for (int row2=0; row2<8; row2++)
         for (int row3=0; row3<8; row3++)
            nttable2[p++] = slowEvolveBit(row1, row2, row3, 0) ;
}

int evolveBit(int row1, int row2, int row3, int bshift) {
   return nttable2[
      (((row1 << 6) >> bshift) & 0700) +
      (((row2 << 3) >> bshift) &  070) +
      (( row3       >> bshift) &   07)] ;
}

int evolveBit(int row1, int row2, int row3) {
   return nttable2[
      ((row1 << 6) & 0700) +
      ((row2 << 3) &  070) +
      ( row3       &   07)] ;
}

int evolveRow(int row1, int row2, int row3){
   int row4;
   int row1_s,row2_s,row3_s;
   int j,s = 0;
   if(sp[P_SYMMETRY] == SYM_ODD) s = 1;
   if(evolveBit(row1, row2, row3, width - 1)) return -1;
   if(sp[P_SYMMETRY] == SYM_ASYM && evolveBit(row1 << 2, row2 << 2, row3 << 2)) return -1;
   if(sp[P_SYMMETRY] == SYM_ODD || sp[P_SYMMETRY] == SYM_EVEN){
      row1_s = (row1 << 1) + ((row1 >> s) & 1);
      row2_s = (row2 << 1) + ((row2 >> s) & 1);
      row3_s = (row3 << 1) + ((row3 >> s) & 1);
   }
   else{
      row1_s = (row1 << 1);
      row2_s = (row2 << 1);
      row3_s = (row3 << 1);
   }
   row4 = evolveBit(row1_s, row2_s, row3_s);
   for(j = 1; j < width; j++)row4 += evolveBit(row1, row2, row3, j - 1) << j;
   return row4;
}
int evolveRowHigh(int row1, int row2, int row3, int bits){
   int row4=0;
   int row1_s,row2_s,row3_s;
   int j ;
   if(evolveBit(row1, row2, row3, width - 1)) return -1;
   row1_s = (row1 << 1);
   row2_s = (row2 << 1);
   row3_s = (row3 << 1);
   for(j = width-bits; j < width; j++)row4 += evolveBit(row1, row2, row3, j - 1) << j;
   return row4;
}
int evolveRowLow(int row1, int row2, int row3, int bits){
   int row4;
   int row1_s,row2_s,row3_s;
   int j,s = 0;
   if(sp[P_SYMMETRY] == SYM_ODD) s = 1;
   if(sp[P_SYMMETRY] == SYM_ASYM && evolveBit(row1 << 2, row2 << 2, row3 << 2)) return -1;
   if(sp[P_SYMMETRY] == SYM_ODD || sp[P_SYMMETRY] == SYM_EVEN){
      row1_s = (row1 << 1) + ((row1 >> s) & 1);
      row2_s = (row2 << 1) + ((row2 >> s) & 1);
      row3_s = (row3 << 1) + ((row3 >> s) & 1);
   }
   else{
      row1_s = (row1 << 1);
      row2_s = (row2 << 1);
      row3_s = (row3 << 1);
   }
   row4 = evolveBit(row1_s, row2_s, row3_s);
   for(j = 1; j < bits; j++)row4 += evolveBit(row1, row2, row3, j - 1) << j;
   return row4;
}

void sortRows(uint16_t *row, uint32_t totalRows) {
   uint32_t i;
   int64_t j;
   uint16_t t;
   for(i = 1; i < totalRows; ++i){
      t = row[i];
      j = i - 1;
      while(j >= 0 && gcount[row[j]] < gcount[t]){
         row[j+1] = row[j];
         --j;
      }
      row[j+1] = t;
   }
}
uint16_t *makeRow(int row1, int row2) ;
uint16_t *getoffset(int row12) {
   uint16_t *r = gInd3[row12] ;
   if (r == 0)
      r = makeRow(row12 >> width, row12 & ((1 << width) - 1)) ;
   return r ;
}
uint16_t *getoffset(int row1, int row2) {
   return getoffset((row1 << width) + row2) ;
}
void getoffsetcount(int row1, int row2, int row3, uint16_t* &p, int &n) {
   uint16_t *row = getoffset(row1, row2) ;
   p = row + row[row3] ;
   n = row[row3+1] - row[row3] ;
}
int getcount(int row1, int row2, int row3) {
   uint16_t *row = getoffset(row1, row2) ;
   return row[row3+1] - row[row3] ;
}
void genStatCounts() ;
void makeTables() {
   gInd3 = (uint16_t **)calloc(sizeof(*gInd3),(1LL<<(width*2))) ;
   rowHash = (int *)calloc(sizeof(int),(2LL<<(width*2))) ;
   for (int i=0; i<1<<(2*width); i++)
      gInd3[i] = 0 ;
   for (int i=0; i<2<<(2*width); i++)
      rowHash[i] = -1 ;
   ev2Rows = (uint16_t *)calloc(sizeof(*ev2Rows), (1LL << (width * 2)));
   gcount = (uint32_t *)calloc(sizeof(*gcount), (1LL << width));
   memusage += (sizeof(*gInd3)+sizeof(*ev2Rows)+2*sizeof(int)) << (width*2) ;
   uint32_t i;
   for(i = 0; i < 1 << width; ++i) gcount[i] = 0 ;
   for (int i=0; i<1<<(2*width); i++)
      ev2Rows[i] = 0 ;
   gWork = (int *)calloc(sizeof(int), 3LL << width) ;
   if (sp[P_REORDER] == 1)
      genStatCounts() ;
   if (sp[P_REORDER] == 2) {
      std::mt19937 mt_rand(time(0));
      for (int i=1; i<1<<width; i++)
         gcount[i] = 1 + (mt_rand() & 0x3fffffff) ;
   }
   if (sp[P_REORDER] == 3)
      for (int i=1; i<1<<width; i++)
         gcount[i] = 1 + gcount[i & (i - 1)] ;
   gcount[0] = 0 ;
   valorder = (uint16_t *)calloc(sizeof(uint16_t), 1LL << width) ;
   for (int i=0; i<1<<width; i++)
      valorder[i] = (1<<width)-1-i ;
   if (sp[P_REORDER] != 0)
      sortRows(valorder, 1<<width) ;
   // for threading, we need the whole table before we start
   // we need to multithread table generation too, but not initially
   for (int row1=0; row1<1<<width; row1++)
      for (int row2=0; row2<1<<width; row2++)
         makeRow(row1, row2) ;
}
// reduce fragmentation by allocating chunks larger than needed and
// parceling out the small pieces.
uint16_t *bmalloc(int siz) {
   if (siz > bbuf_left) {
      bbuf_left = 1 << (2 * width) ;
      memusage += 2*bbuf_left ;
      if (memusage > memlimit) {
         printf("Aborting due to excessive memory usage\n") ;
         exit(0) ;
      }
      bbuf = (uint16_t *)calloc(sizeof(uint16_t), bbuf_left) ;
   }
   uint16_t *r = bbuf ;
   bbuf += siz ;
   bbuf_left -= siz ;
   return r ;
}
void unbmalloc(int siz) {
   bbuf -= siz ;
   bbuf_left += siz ;
}
unsigned int hashRow(uint16_t *row, int siz) {
   unsigned int h = 0 ;
   for (int i=0; i<siz; i++)
      h = h * 3 + row[i] ;
   return h ;
}
uint16_t *makeRow(int row1, int row2) {
   int good = 0 ;
   int *gWork2 = gWork + (1 << width) ;
   int *gWork3 = gWork2 + (1 << width) ;
   if (width < 4) {
      for (int row3=0; row3<1<<width; row3++)
         gWork3[row3] = evolveRow(row1, row2, row3) ;
   } else {
      int lowbitcount = (width >> 1) + 1 ;
      int hibitcount = ((width + 1) >> 1) + 1 ;
      int hishift = lowbitcount - 2 ;
      int lowcount = 1 << lowbitcount ;
      for (int row3=0; row3<1<<lowbitcount; row3++)
         gWork2[row3] = evolveRowLow(row1, row2, row3, lowbitcount-1) ;
      for (int row3=0; row3<1<<width; row3 += 1<<hishift)
         gWork2[lowcount+(row3>>hishift)] =
                        evolveRowHigh(row1, row2, row3, hibitcount-1) ;
      for (int row3=0; row3<1<<width; row3++)
         gWork3[row3] = gWork2[row3 & ((1<<lowbitcount) - 1)] |
                        gWork2[lowcount+(row3 >> hishift)] ;
   }
   for (int row3i = 0; row3i < 1<<width; row3i++) {
      int row3 = valorder[row3i] ;
      int row23 = (row2 << width) + row3 ;
      int row4 = gWork3[row3] ;
      if (row4 < 0)
         continue ;
      if (row1 == 0)
         ev2Rows[row23] = row4 ;
      gWork2[good] = row3 ;
      gWork[good++] = row4 ;
   }
   uint16_t *row = bmalloc((1+(1<<width)+good)) ;
   for (int row3=0; row3 < 1<<width; row3++)
      row[row3] = 0 ;
   row[0] = 1 + (1 << width) ;
   for (int row3=0; row3 < good; row3++)
      row[gWork[row3]]++ ;
   row[1<<width] = 0 ;
   for (int row3=0; row3 < (1<<width); row3++)
      row[row3+1] += row[row3] ;
   for (int row3=good-1; row3>=0; row3--) {
      int row4 = gWork[row3] ;
      row[--row[row4]] = gWork2[row3] ;
   }
   unsigned int h = hashRow(row, 1+(1<<width)+good) ;
   h &= (2 << (2 * width)) - 1 ;
   while (1) {
      if (rowHash[h] == -1) {
         rowHash[h] = (row1 << width) + row2 ;
         break ;
      }
      if (memcmp(row, gInd3[rowHash[h]], 2*(1+(1<<width)+good)) == 0) {
         row = gInd3[rowHash[h]] ;
         unbmalloc(1+(1<<width)+good) ;
         break ;
      }
      h = (h + 1) & ((2 << (2 * width)) - 1) ;
   }
   gInd3[(row1<<width)+row2] = row ;
/*
 *   For debugging:
 *
   printf("R") ;
   for (int i=0; i<1+(1<<width)+good; i++)
      printf(" %d", row[i]) ;
   printf("\n") ;
   fflush(stdout) ;
 */
   return row ;
}

/*
 *   We calculate the stats using a 2 * 64 << width array.  We use a
 *   leading 1 to separate them.  Index 1 aaa bb cc dd represents
 *   the count for a result of aaa when the last two bits of row1, row2,
 *   and row3 were bb, cc, and dd, respectively.  We have to manage
 *   the edge conditions appropriately.
 */
void genStatCounts() {
   int *cnt = (int*)calloc((128 * sizeof(int)), 1LL << width) ;
   for (int i=0; i<128<<width; i++)
      cnt[i] = 0 ;
   int s = 0 ;
   if (sp[P_SYMMETRY] == SYM_ODD)
      s = 2 ;
   else if (sp[P_SYMMETRY] == SYM_EVEN)
      s = 1 ;
   else
      s = width + 2 ;
   // left side: never permit generation left of row4
   for (int row1=0; row1<2; row1++)
      for (int row2=0; row2<2; row2++)
         for (int row3=0; row3<2; row3++)
            if (evolveBit(row1, row2, row3) == 0)
               cnt[(1<<6) + (row1 << 4) + (row2 << 2) + row3]++ ;
   for (int nb=0; nb<width; nb++) {
      for (int row1=0; row1<8; row1++)
         for (int row2=0; row2<8; row2++)
            for (int row3=0; row3<8; row3++) {
               if (nb == width-1)
                  if ((((row1 >> s) ^ row1) & 1) ||
                      (((row2 >> s) ^ row2) & 1) ||
                      (((row3 >> s) ^ row3) & 1))
                     continue ;
               int row4b = evolveBit(row1, row2, row3) ;
               for (int row4=0; row4<1<<nb; row4++)
                  cnt[(((((1<<nb) + row4) << 1) + row4b) << 6) +
                    ((row1 & 3) << 4) + ((row2 & 3) << 2) + (row3 & 3)] +=
                     cnt[(((1<<nb) + row4) << 6) +
                       ((row1 >> 1) << 4) + ((row2 >> 1) << 2) + (row3 >> 1)] ;
            }
   }
   // right side; check left, and accumulate into gcount
   for (int row1=0; row1<4; row1++)
      for (int row2=0; row2<4; row2++)
         for (int row3=0; row3<4; row3++)
            if (sp[P_SYMMETRY] != SYM_ASYM ||
                evolveBit(row1<<1, row2<<1, row3<<1) == 0)
               for (int row4=0; row4<1<<width; row4++)
                  gcount[row4] +=
                     cnt[(((1<<width) + row4) << 6) +
                       (row1 << 4) + (row2 << 2) + row3] ;
   free(cnt) ;
}

void printInfo(int currentDepth, unsigned long long numCalcs, double runTime){
   if(currentDepth >= 0) printf("Current depth: %d\n", currentDepth - 2*period);
   printf("Calculations: ");
   printf("%llu\n", numCalcs);
   printf("CPU time: %f seconds\n",runTime);
   fflush(stdout);
}

void searchThread::buffPattern(int theRow){
   int firstRow = 2 * period;
   if(sp[P_INIT_ROWS]) firstRow = 0;
   int lastRow;
   int i, j;
   char *out = buf;
   for(lastRow = theRow - 1; lastRow >= 0; --lastRow)if(pRows[lastRow])break;
   
   for(i = firstRow; i <= lastRow; i += period){
      for(j = width - 1; j >= 0; --j){
         if((pRows[i] >> j) & 1) out += sprintf(out, "o");
         else out += sprintf(out, ".");
      }
      if(sp[P_SYMMETRY] != SYM_ASYM){
         if(sp[P_SYMMETRY] == SYM_GUTTER) out += sprintf(out, ".");
         if(sp[P_SYMMETRY] != SYM_ODD){
            if (pRows[i] & 1) out += sprintf(out, "o");
            else out += sprintf(out, ".");
         }
         for(j = 1; j < width; ++j){
            if((pRows[i] >> j) & 1) out += sprintf(out, "o");
            else out += sprintf(out, ".");
         }
      }
      out += sprintf(out, "\n");
   }
   out += sprintf(out, "Length: %d\n", lastRow - 2 * period + 1);
}

void searchThread::printPattern(){
   printf("%s", buf);
   fflush(stdout);
}
int searchThread::getkey(uint16_t *p1, uint16_t *p2, uint16_t *p3, int abn) {
   unsigned long long h = (unsigned long long)p1 +
      17 * (unsigned long long)p2 + 257 * (unsigned long long)p3 +
      513 * abn ;
   h = h + (h >> 15) ;
   h &= (cachesize-1) ;
   struct cacheentry &ce = cache[h] ;
   if (ce.p1 == p1 && ce.p2 == p2 && ce.p3 == p3 && ce.abn == abn) {
      return -2 + ce.r ;
   }
   ce.p1 = p1 ;
   ce.p2 = p2 ;
   ce.p3 = p3 ;
   ce.abn = abn ;
   return h ;
}
void searchThread::setkey(int h, int v) {
   cache[h].r = v ;
}
int searchThread::lookAhead(int a){
   int ri11, ri12, ri13, ri22, ri23;  //indices: first number represents vertical offset, second number represents generational offset
   uint16_t *riStart11, *riStart12, *riStart13, *riStart22, *riStart23;
   int numRows11, numRows12, numRows13, numRows22, numRows23;
   int row11, row12, row13, row22, row23;

   getoffsetcount(pRows[a - sp[P_PERIOD] - fwdOff[phase]],
                  pRows[a - fwdOff[phase]],
                  pRows[a], riStart11, numRows11) ;
   if (!numRows11)
      return 0 ;
   getoffsetcount(pRows[a - sp[P_PERIOD] - doubleOff[phase]],
                  pRows[a - doubleOff[phase]],
                  pRows[a - fwdOff[phase]], riStart12, numRows12) ;
   
   if(tripleOff[phase] >= sp[P_PERIOD]){
      int off = a + sp[P_PERIOD] - tripleOff[phase] ;
      if (off < 2 * sp[P_PERIOD]) { // always zero if here
         riStart13 = pRows + off ;
      } else {
         // must *not* point to stack here to keep cache consistent!
         riStart13 = pInd[off] + pRemain[off];
      }
      numRows13 = 1 ;
   } else {
      getoffsetcount(pRows[a - sp[P_PERIOD] - tripleOff[phase]],
                     pRows[a - tripleOff[phase]],
                     pRows[a - doubleOff[phase]], riStart13, numRows13) ;
   }
   int k = getkey(riStart11, riStart12, riStart13,
    (((pRows[a-doubleOff[phase]] << width) + pRows[a-tripleOff[phase]]) << 1)
        + (numRows13 == 1)) ;
   if (k < 0)
      return k+2 ;
   for(ri11 = 0; ri11 < numRows11; ++ri11){
      row11 = riStart11[ri11];
      for(ri12 = 0; ri12 < numRows12; ++ri12){
         row12 = riStart12[ri12] ;
         getoffsetcount(pRows[a - doubleOff[phase]],
                        row12, row11, riStart22, numRows22) ;
         if(!numRows22) continue;
         
         for(ri13 = 0; ri13 < numRows13; ++ri13){
            row13 = riStart13[ri13] ;
            getoffsetcount(pRows[a - tripleOff[phase]],
                           row13, row12, riStart23, numRows23) ;
            if(!numRows23) continue;
            
            for(ri23 = 0; ri23 < numRows23; ++ri23){
               row23 = riStart23[ri23] ;
               uint16_t *p = getoffset(row13, row23) ;
               for(ri22 = 0; ri22 < numRows22; ++ri22){
                  row22 = riStart22[ri22] ;
                  if (p[row22+1]!=p[row22]) {
                     setkey(k, 1) ;
                     return 1 ;
                  }
               }
            }
         }
      }
   }
   setkey(k, 0) ;
   return 0;
}

int searchThread::checkInteract(int a){
   int i;
   for(i = a - period; i > a - 2*period; --i){
      if(ev2Rows[(pRows[i] << width) + pRows[i + period]] != pRows[i + backOff[i % period]]) return 1;
   }
   return 0;
}
/*
 *   Symmetry breaking for asymmetric searches:
 *
 *   Return -1 if bitreverse(v) > v
 *   Return 0 if bitreverse(v) == v
 *   Return 1 if bitreverse(v) < v
 */
int checkPalindrome(int v) {
   for (int i=0; i+i<width; i++) {
      int t = ((v >> i) & 1) - ((v >> (width - 1 - i)) & 1) ;
      if (t)
         return t ;
   }
   return 0 ;
}
void searchThread::search(){
   uint32_t currRow = rowNum;    // currRow == index of current row
   int j;
   unsigned long long calcs, lastLong;
   int noship = 0;
   int totalShips = 0;
   calcs = 0;                    // calcs == "calculations" == number of times through the main loop
   uint32_t longest = 0;         // length of the longest partial seen so far
   lastLong = 0;                 // number of calculations at which longest was updated
   int buffFlag = 0;
   double ms = get_cpu_time();
   phase = currRow % period;
   int firstasymm = 0 ;
   long long workItem = 0 ;
   int local_num_ships = sp[P_NUM_SHIPS] ;
   if (sp[P_SYMMETRY] == SYM_ASYM)
      firstasymm = currRow ;
   for(;;){
      ++calcs;
      if(currRow > longest || !(calcs & 0xffffff)){
         if(currRow > longest){
            buffPattern(currRow);
            longest = currRow;
            buffFlag = 1;
            lastLong = calcs;
         }
         if((buffFlag && calcs - lastLong > 0xffffff) || !(calcs & 0xffffffff)){
            if(!(calcs & 0xffffffff)) buffPattern(currRow);
            get_global_lock() ;
            printPattern();
            printInfo(currRow,calcs,get_cpu_time()-ms);
            release_global_lock() ;
            buffFlag = 0;
         }
      }
      if(!pRemain[currRow]){
         if(shipNum && lastNonempty[shipNum] == currRow) --shipNum;
         --currRow;
         if(phase == 0) phase = period;
         --phase;
         if(sp[P_FULL_PERIOD] && firstFull == currRow) firstFull = 0;
         if(currRow < 2 * sp[P_PERIOD]){
            get_global_lock() ;
            printPattern();
            if(totalShips == 1)printf("Search complete: 1 spaceship found.\n");
            else printf("Search complete: %d spaceships found.\n",totalShips);
            printInfo(-1,calcs,get_cpu_time() - ms);
            release_global_lock() ;
            return;
         }
         continue;
      }
      --pRemain[currRow];
      pRows[currRow] = pInd[currRow][pRemain[currRow]];
      if (currRow <= firstasymm) {
         int palin = checkPalindrome(pRows[currRow]) ;
         if (palin < 0)
            continue ;
         if (palin == 0)
            firstasymm = currRow + 1 ;
         else
            firstasymm = currRow ;
      }
      if(sp[P_MAX_LENGTH] && currRow > sp[P_MAX_LENGTH] + 2 * period - 1 && pRows[currRow] != 0) continue;  //back up if length exceeds max length
      if(sp[P_FULL_PERIOD] && currRow > sp[P_FULL_PERIOD] && !firstFull && pRows[currRow]) continue;        //back up if not full period by certain length
      if(sp[P_FULL_WIDTH] && (pRows[currRow] & fpBitmask)){
         if(equivRow[phase] < 0 && pRows[currRow] != pRows[currRow + equivRow[phase]]){
            if(!twoSubPeriods || (equivRow2[phase] < 0 && pRows[currRow] != pRows[currRow + equivRow2[phase]])) continue;
         }
      }
      if(shipNum && currRow == lastNonempty[shipNum] + 2*period && !checkInteract(currRow)) continue;       //back up if new rows don't interact with ship
      if(!lookAhead(currRow)) continue ;
      if(sp[P_FULL_PERIOD] && !firstFull){
         if(equivRow[phase] < 0 && pRows[currRow] != pRows[currRow + equivRow[phase]]){
            if(!twoSubPeriods || (equivRow2[phase] < 0 && pRows[currRow] != pRows[currRow + equivRow2[phase]])) firstFull = currRow;
         }
      }
/*
      get_global_lock() ;
      printf("CurrRow %d divergence %d\n", currRow, divergenceLevel) ;
      release_global_lock() ;
 */
      if (currRow == divergenceLevel && !forMeQ(workItem++))
         continue ;
      ++currRow;
      ++phase;
      if(phase == period) phase = 0;
      if(currRow > sp[P_DEPTH_LIMIT]){
         noship = 0;
         for(j = 1; j <= 2 * period; ++j) noship |= pRows[currRow-j];
         if(!noship){
            if(!sp[P_FULL_PERIOD] || firstFull){
               get_global_lock() ;
               printf("\n");
               printPattern();
               ++totalShips;
               printf("Spaceship found. (%d)\n\n",totalShips);
               printInfo(currRow,calcs,get_cpu_time() - ms);
               local_num_ships-- ;
               fflush(stdout) ;
               release_global_lock() ;
            }
            ++shipNum;
            if(local_num_ships == 0){
               get_global_lock() ;
               if(totalShips == 1)printf("Search terminated: spaceship found.\n");
               else printf("Search terminated: %d spaceships found.\n",totalShips);
               release_global_lock() ;
               return;
            }
            for(lastNonempty[shipNum] = currRow - 1; lastNonempty[shipNum] >= 0; --lastNonempty[shipNum]) if(pRows[lastNonempty[shipNum]]) break;
            currRow = lastNonempty[shipNum] + 2 * period;
            phase = currRow % period;
            longest = lastNonempty[shipNum];
            continue;
         }
         else{
            get_global_lock() ;
            printPattern();
            printf("Search terminated: depth limit reached.\n");
            printf("Depth: %d\n", currRow - 2 * period);
            if(totalShips == 1)printf("1 spaceship found.\n");
            else printf("%d spaceships found.\n",totalShips);
            release_global_lock() ;
         }
         get_global_lock() ;
         printInfo(currRow,calcs,get_cpu_time() - ms);
         release_global_lock() ;
         return;
      }
      getoffsetcount(pRows[currRow - 2 * period],
                     pRows[currRow - period],
                     pRows[currRow - period + backOff[phase]],
                     pInd[currRow], pRemain[currRow]) ;
   }
}

void loadFail(){
   printf("Load from file %s failed\n",loadFile);
   exit(1);
}

signed int loadInt(FILE *fp){
   signed int v;
   if (fscanf(fp,"%d\n",&v) != 1) loadFail();
   return v;
}

long long loadUL(FILE *fp){
   long long v;
   if (fscanf(fp,"%lld\n",&v) != 1) loadFail();
   return v;
}

void searchThread::loadInitRows(char * file){
   FILE * fp;
   int i,j;
   char rowStr[MAXWIDTH];
   
   loadFile = file;
   fp = fopen(loadFile, "r");
   if (!fp) loadFail();
   
   for(i = 0; i < 2 * period; i++){
      if (fscanf(fp,"%s",rowStr) != 1)
         error("! early end on file when reading initial rows") ;
      for(j = 0; j < width; j++){
         pRows[i] |= ((rowStr[width - j - 1] == '.') ? 0:1) << j;
      }
   }
   fclose(fp);
}

void searchThread::initializeThread(char* file) {
   int i;
   pRows = (uint16_t *)calloc(1+sp[P_DEPTH_LIMIT], sizeof(uint16_t));
   pInd = (uint16_t **)calloc(1+sp[P_DEPTH_LIMIT], sizeof(uint16_t *));
   pRemain = (int *)calloc(1+sp[P_DEPTH_LIMIT], sizeof(int));
   lastNonempty = (int *)calloc(sizeof(int), (sp[P_DEPTH_LIMIT]/10));
   rowNum = 2 * period;
   for(i = 0; i < 2 * period; i++)pRows[i] = 0;
   if(sp[P_INIT_ROWS]) loadInitRows(file);
   for (int i=0; i<sp[P_DEPTH_LIMIT]; i++) {
      pInd[i] = gInd3[0] + gInd3[0][0] ;
      pRemain[i] = 0 ;
   }
   pRemain[2 * period] = gInd3[0][1] - gInd3[0][0] - 1 ;
   pInd[2 * period] = gInd3[0] + gInd3[0][0] ;
   if(sp[P_INIT_ROWS]){
      getoffsetcount(pRows[0], pRows[period], pRows[period+backOff[0]],
                     pInd[2*period], pRemain[2*period]) ;
   }
   cache = (struct cacheentry *)calloc(sizeof(cacheentry), cachesize) ;
   buf = (char *)calloc((2*sp[P_WIDTH] + 4), sp[P_DEPTH_LIMIT]);  // I think this gives more than enough space
   buf[0] = '\0';
}

void initializeSearch(char *f) {
   if(sp[P_MAX_LENGTH]) sp[P_DEPTH_LIMIT] = sp[P_MAX_LENGTH] + 2 * period;
   sp[P_DEPTH_LIMIT] += 2 * period;
   if(sp[P_FULL_PERIOD]) sp[P_FULL_PERIOD] += 2 * period - 1;
   if(gcd(period,offset) == 1) sp[P_FULL_PERIOD] = 0;
   if(sp[P_FULL_WIDTH] > sp[P_WIDTH]) sp[P_FULL_WIDTH] = 0;
   if(sp[P_FULL_WIDTH] && sp[P_FULL_WIDTH] < sp[P_WIDTH]){
      for(int i = sp[P_FULL_WIDTH]; i < sp[P_WIDTH]; ++i){
         fpBitmask |= (1 << i);
      }
   }
   p_thread = (pthread_t *)calloc(sizeof(pthread_t), numThreads) ;
   threads = (struct searchThread *)calloc(sizeof(searchThread), numThreads) ;
   for (int t=0; t<numThreads; t++)
      threads[t].initializeThread(f) ;
   divergenceLevel = 2 * period + 5 ;
}

void echoParams(){
   int i,j;
   printf("Rule: %s\n", rule) ;
   printf("Period: %d\n",sp[P_PERIOD]);
   printf("Offset: %d\n",sp[P_OFFSET]);
   printf("Width:  %d\n",sp[P_WIDTH]);
   if(sp[P_SYMMETRY] == SYM_ASYM) printf("Symmetry: asymmetric\n");
   else if(sp[P_SYMMETRY] == SYM_ODD) printf("Symmetry: odd\n");
   else if(sp[P_SYMMETRY] == SYM_EVEN) printf("Symmetry: even\n");
   else if(sp[P_SYMMETRY] == SYM_GUTTER) printf("Symmetry: gutter\n");
   if(sp[P_MAX_LENGTH]) printf("Max length: %d\n",sp[P_MAX_LENGTH]);
   else printf("Depth limit: %d\n",sp[P_DEPTH_LIMIT] - 2 * period);
   if(sp[P_FULL_PERIOD]) printf("Full period by depth %d\n",sp[P_FULL_PERIOD] - 2 * period + 1);
   if(sp[P_FULL_WIDTH]) printf("Full period width: %d\n",sp[P_FULL_WIDTH]);
   if(sp[P_NUM_SHIPS] == 1) printf("Stop search if a ship is found.\n");
   else printf("Stop search if %d ships are found.\n",sp[P_NUM_SHIPS]);
   if(!sp[P_REORDER]) printf("Use naive search order.\n");
   if (sp[P_REORDER] == 2) printf("Use randomized search order.\n");
   if (sp[P_REORDER] == 3) printf("Use min population search order.\n");
}

void usage(){
   printf("%s\n",BANNER);
   printf("\n");
   printf("Usage: \"zfind options\"\n");
   printf("  e.g. \"zfind B3/S23 p3 k1 w6 v\" searches Life (rule B3/S23) for\n");
   printf("  c/3 orthogonal spaceships with even bilateral symmetry and a\n");
   printf("  search width of 6 (full width 12).\n");
   printf("\n");
   printf("Available options:\n");
   printf("  bNN/sNN searches for spaceships in the specified rule (default: b3/s23)\n");
   printf("\n");
   printf("  pNN  searches for spaceships with period NN\n");
   printf("  kNN  searches for spaceships that travel NN cells every period\n");
   printf("  wNN  searches for spaceships with search width NN\n");
   printf("       (full width depends on symmetry type)\n");
   printf("\n");
   printf("  lNN  terminates the search if it reaches a depth of NN (default: %d)\n",DEFAULT_DEPTH_LIMIT);
   printf("  mNN  disallows spaceships longer than a depth of NN\n");
   printf("       (the spaceship length is approximately depth/period)\n");
   printf("  fNN  disallows spaceships that do not have the full period by a depth of NN\n");
   printf("  tNN  disallows full-period rows of width greater than NN\n");
   printf("  sNN  terminates the search if NN spaceships are found (default: 1)\n");
   printf("\n");
   printf("  a    searches for asymmetric spaceships\n");
   printf("  u    searches for odd bilaterally symmetric spaceships\n");
   printf("  v    searches for even bilaterally symmetric spaceships\n");
   printf("  g    searches for symmetric spaceships with gutters (empty center column)\n");
   printf("\n");
   printf("  o    uses naive search order (search will take longer when no ships exist)\n");
   printf("  r    uses randomized search order\n") ;
   printf("  n    uses popcount search order\n") ;
   printf("\n");
// printf("  e FF uses rows in the file FF as the initial rows for the search\n");
// printf("       (use the companion Golly python script to easily generate the\n");
// printf("       initial row file)\n");
// printf("\n");
// printf("\"zfind command file\" reloads the state from the specified file\n");
   printf("and performs the command. Available commands: \n");
// printf("  s    resumes search from the loaded state\n");
// printf("  p    outputs the pattern representing the loaded state\n");
   printf("  RNNN restricts memory usage to NNN megabytes\n") ;
   printf("  CNNN uses about NNN megabytes for lookahead cache\n") ;
}

void search() {
   for (int i=0; i<numThreads; i++)
      spawn_thread(i, searchWorker, &threads[i]) ;
   for (int i=0; i<numThreads; i++)
      join_thread(i) ;
}

int main(int argc, char *argv[]){
   init_mutex() ;
   printf("%s\n", BANNER) ;
   printf("-") ;
   for (int i=0; i<argc; i++)
      printf(" %s", argv[i]) ;
   printf("\n") ;
   sp[P_WIDTH] = 0;
   sp[P_PERIOD] = 0;
   sp[P_OFFSET] = 0;
   sp[P_DEPTH_LIMIT] = DEFAULT_DEPTH_LIMIT;
   sp[P_SYMMETRY] = 0;
   sp[P_MAX_LENGTH] = 0;
   sp[P_INIT_ROWS] = 0;
   sp[P_FULL_PERIOD] = 0;
   sp[P_NUM_SHIPS] = 1;
   sp[P_FULL_WIDTH] = 0;
   sp[P_REORDER] = 1;
   sp[P_DUMP] = 0;
   int skipNext = 0;
   int div1,div2;
   int s;
   if(argc == 2 && !strcmp(argv[1],"c")){
      usage();
      return 0;
   }
   const char *err ;
   parseRule(rule, nttable) ; // pick up default rule
   {
      for(s = 1; s < argc; s++){    //read input parameters
         if(skipNext){
            skipNext = 0;
            continue;
         }
         int sshift ;
         switch(argv[s][0]){
            case 'b': case 'B':     //read rule
               rule = argv[s] ;
               err = parseRule(argv[s], nttable) ;
               if (err != 0) {
                  fprintf(stderr, "Failed to parse rule %s\n", argv[s]) ;
                  exit(10) ;
               }
            break;
            case 'w': case 'W': sscanf(&argv[s][1], "%d", &sp[P_WIDTH]); break;
            case 'p': case 'P': sscanf(&argv[s][1], "%d", &sp[P_PERIOD]); break;
            case 'k': case 'K': sscanf(&argv[s][1], "%d", &sp[P_OFFSET]); break;
            case 'l': case 'L': sscanf(&argv[s][1], "%d", &sp[P_DEPTH_LIMIT]); break;
            case 'u': case 'U': sp[P_SYMMETRY] = SYM_ODD; break;
            case 'v': case 'V': sp[P_SYMMETRY] = SYM_EVEN; break;
            case 'a': case 'A': sp[P_SYMMETRY] = SYM_ASYM; break;
            case 'g': case 'G': sp[P_SYMMETRY] = SYM_GUTTER; break;
            case 'm': case 'M': sscanf(&argv[s][1], "%d", &sp[P_MAX_LENGTH]); break;
            case 'e': case 'E': sp[P_INIT_ROWS] = s + 1; skipNext = 1; break;
            case 'f': case 'F': sscanf(&argv[s][1], "%d", &sp[P_FULL_PERIOD]); break;
            case 's': case 'S': sscanf(&argv[s][1], "%d", &sp[P_NUM_SHIPS]); break;
            case 't': case 'T': sscanf(&argv[s][1], "%d", &sp[P_FULL_WIDTH]); break;
            case 'o': case 'O': sp[P_REORDER] = 0; break;
            case 'r':           sp[P_REORDER] = 2; break;
            case 'n':           sp[P_REORDER] = 3; break;
            case 'R': sscanf(&argv[s][1], "%lld", &memlimit) ; memlimit <<= 20 ; break ;
            case 'C': sscanf(&argv[s][1], "%d", &cachemem); break ;
            default:
               printf("Unrecognized option %s\n", argv[s]) ;
               exit(10) ;
         }
      }
   }
   fasterTable() ;
   cachesize = 32768 ;
   while (cachesize * sizeof(cacheentry) < 550000 * cachemem)
      cachesize <<= 1 ;
   if(!sp[P_WIDTH] || !sp[P_PERIOD] || !sp[P_OFFSET] || !sp[P_SYMMETRY]){
      printf("You must specify a width, period, offset, and symmetry type.\n");
      printf("For command line options, type 'zfind c'.\n");
      return 0;
   }
   width = sp[P_WIDTH];
   period = sp[P_PERIOD];
   offset = sp[P_OFFSET];
   echoParams();
   makePhases();                    //make phase tables for determining successor row indices
   if(gcd(period,offset) > 1){      //make phase tables for determining equivalent subperiodic rows
      div1 = smallestDivisor(gcd(period,offset));
      makeEqRows(period / div1,1);
      div2 = gcd(period,offset);
      while(div2 % div1 == 0) div2 /= div1;
      if(div2 != 1){
         twoSubPeriods = 1;
         div2 = smallestDivisor(div2);
         makeEqRows(period / div2,2);
      }
   }
   makeTables();                    //make lookup tables for determining successor rows
   initializeSearch(argv[sp[P_INIT_ROWS]]);    //initialize search based on input parameters
   printf("Starting search\n");
   fflush(stdout) ;
   ::search();
   return 0;
}
