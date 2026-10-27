// probSAT local-search SAT solver (Balint & Schoening style), built for NONCE benchmark instances.
// Input format: first line "nVars nClauses", then one clause per line: signed ints terminated by 0.
// On SAT: prints bitstring of length nVars (var1..varN) and exits 0. Runs until wall-clock limit otherwise.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
static int nV, nC;
static int *clStart, *clLen, *clLits;        // clauses
static int *occStart, *occList;             // per literal-index occurrences
static signed char *assign;                 // 0/1 per var (1-based)
static int *satCnt;                         // true literals per clause
static int *unsatList, *unsatPos, nUnsat;    // unsat clause set with O(1) removal
static unsigned long long rngState;
static inline unsigned long long xr(void){ rngState^=rngState<<13; rngState^=rngState>>7; rngState^=rngState<<17; return rngState; }
static inline int litIdx(int lit){ int v=lit<0?-lit:lit; return (v-1)*2 + (lit<0?1:0); }
static inline int litTrue(int lit){ int v=lit<0?-lit:lit; return lit>0 ? assign[v] : !assign[v]; }
static void unsatAdd(int c){ unsatPos[c]=nUnsat; unsatList[nUnsat++]=c; }
static void unsatDel(int c){ int p=unsatPos[c]; int last=unsatList[--nUnsat]; unsatList[p]=last; unsatPos[last]=p; unsatPos[c]=-1; }
static void flipVar(int v){
    // literal currently true for v: pos if assign==1 else neg
    int tLit = assign[v] ? v : -v;
    int fLit = -tLit;
    int ti=litIdx(tLit), fi=litIdx(fLit);
    for(int i=occStart[ti]; i<occStart[ti+1]; i++){ int c=occList[i]; if(--satCnt[c]==0) unsatAdd(c); }
    for(int i=occStart[fi]; i<occStart[fi+1]; i++){ int c=occList[i]; if(satCnt[c]==0) unsatDel(c); satCnt[c]++; }
    assign[v]^=1;
}
static inline int breakCount(int v){
    int tLit = assign[v] ? v : -v;
    int ti=litIdx(tLit), b=0;
    for(int i=occStart[ti]; i<occStart[ti+1]; i++){ int c=occList[i]; if(satCnt[c]==1) b++; }
    return b;
}
int main(int argc, char**argv){
    if(argc<5){ fprintf(stderr,"usage: probsab file seed beta maxSeconds\n"); return 2; }
    const char* path=argv[1];
    rngState = strtoull(argv[2],0,10) | 1ULL;
    double beta = atof(argv[3]);
    double maxSec = atof(argv[4]);
    FILE* f=fopen(path,"r"); if(!f){ perror("open"); return 2; }
    if(fscanf(f,"%d %d",&nV,&nC)!=2){ fprintf(stderr,"bad header\n"); return 2; }
    clStart=malloc(sizeof(int)*(nC+1)); clLen=malloc(sizeof(int)*nC);
    int cap=nC*4+16; clLits=malloc(sizeof(int)*cap); int nl=0;
    int *occCnt=calloc(2*nV,sizeof(int));
    for(int c=0;c<nC;c++){
        clStart[c]=nl; int len=0, lit;
        while(fscanf(f,"%d",&lit)==1 && lit!=0){
            if(nl>=cap){ cap*=2; clLits=realloc(clLits,sizeof(int)*cap); }
            clLits[nl++]=lit; occCnt[litIdx(lit)]++; len++;
        }
        clLen[c]=len;
    }
    clStart[nC]=nl; fclose(f);
    occStart=malloc(sizeof(int)*(2*nV+1)); int s=0;
    for(int i=0;i<2*nV;i++){ occStart[i]=s; s+=occCnt[i]; } occStart[2*nV]=s;
    occList=malloc(sizeof(int)*s);
    int *fill=malloc(sizeof(int)*2*nV); memcpy(fill,occStart,sizeof(int)*2*nV);
    for(int c=0;c<nC;c++) for(int j=clStart[c];j<clStart[c]+clLen[c];j++){ int li=litIdx(clLits[j]); occList[fill[li]++]=c; }
    free(fill); free(occCnt);
    assign=malloc(nV+1); satCnt=malloc(sizeof(int)*nC);
    unsatList=malloc(sizeof(int)*nC); unsatPos=malloc(sizeof(int)*nC);
    // precompute (1+b)^-beta table
    int TMAX=8192; double *wtab=malloc(sizeof(double)*(TMAX+1));
    for(int b=0;b<=TMAX;b++) wtab[b]=pow(1.0+b,-beta);
    struct timespec t0; clock_gettime(CLOCK_MONOTONIC,&t0);
    long long totalFlips=0;
    while(1){
        // (re)randomize assignment
        for(int v=1;v<=nV;v++) assign[v]=(xr()>>32)&1;
        memset(satCnt,0,sizeof(int)*nC);
        for(int c=0;c<nC;c++){ int sc=0; for(int j=clStart[c];j<clStart[c]+clLen[c];j++) if(litTrue(clLits[j])) sc++; satCnt[c]=sc; }
        nUnsat=0; for(int c=0;c<nC;c++){ unsatPos[c]=-1; if(satCnt[c]==0) unsatAdd(c); }
        long long flips=0; long long maxFlips=20000000LL;
        while(nUnsat>0 && flips<maxFlips){
            int c=unsatList[xr()%nUnsat];
            int base=clStart[c], len=clLen[c];
            double w[16]; double sum=0; int vars[16];
            for(int j=0;j<len;j++){ int lit=clLits[base+j]; int v=lit<0?-lit:lit; vars[j]=v; int b=breakCount(v); double wj = b<=TMAX ? wtab[b] : pow(1.0+b,-beta); w[j]=wj; sum+=wj; }
            double r=(xr()>>11)*(1.0/9007199254740992.0)*sum; int pick=len-1;
            for(int j=0;j<len;j++){ r-=w[j]; if(r<=0){ pick=j; break; } }
            flipVar(vars[pick]); flips++;
            if((flips&0x3FFF)==0){
                struct timespec tn; clock_gettime(CLOCK_MONOTONIC,&tn);
                double el=(tn.tv_sec-t0.tv_sec)+(tn.tv_nsec-t0.tv_nsec)/1e9;
                if(el>maxSec) return 1;
            }
        }
        totalFlips+=flips;
        if(nUnsat==0){
            for(int v=1;v<=nV;v++) putchar(assign[v]?'1':'0');
            putchar('\n'); fflush(stdout);
            fprintf(stderr,"SAT flips=%lld\n",totalFlips);
            return 0;
        }
        struct timespec tn; clock_gettime(CLOCK_MONOTONIC,&tn);
        double el=(tn.tv_sec-t0.tv_sec)+(tn.tv_nsec-t0.tv_nsec)/1e9;
        if(el>maxSec) return 1;
    }
}
