/* vanishing_count.c — does the geometric winding count vanish exactly at L's zeros, and count N(T)? */
#include <stdio.h>
#include <math.h>
static int chi3(long n){long r=n%3;return r==1?1:(r==2?-1:0);}
int main(){
  long N=100000;
  static double amp[100001], lnn[100001];
  for(long n=1;n<=N;n++){ amp[n]=chi3(n)/sqrt((double)n); lnn[n]=log((double)n); }
  /* known chi3 zeros up to ~56 (the spectral resonances to compare against) */
  double Z[]={8.0397,11.2492,15.7046,18.2620,20.4558,24.0594,26.5779,28.2182,30.7450,33.8974,
              35.6084,37.5518,39.4852,42.6164,44.1206,46.2741,47.5141,50.3751,52.4967,54.1938,55.6426};
  int nZ=21;
  double gmin=5.5,gmax=56.0,dg=0.02, thr=0.045;
  printf("=== winding-count vanishings  vs  L-zeros (chi3, N=%ld) ===\n",N);
  double p2=9,p1=9,pg=0; int nd=0; double D[300];
  for(double g=gmin;g<=gmax+1e-9;g+=dg){
    double re=0,im=0;
    for(long n=1;n<=N;n++){ if(amp[n]!=0){ double ph=g*lnn[n]; re+=amp[n]*cos(ph); im-=amp[n]*sin(ph);} }
    double a=sqrt(re*re+im*im);
    if(p1<p2 && p1<a && p1<thr){ D[nd++]=pg; }
    p2=p1;p1=a;pg=g-dg;
  }
  printf("found %d winding-vanishings (|S_N|<%.3f) in [%.1f,%.1f]:\n",nd,thr,gmin,gmax);
  int matched=0;
  for(int i=0;i<nd;i++){ double best=1e9;int bj=0;
    for(int j=0;j<nZ;j++){double d=fabs(D[i]-Z[j]); if(d<best){best=d;bj=j;}}
    printf("  vanish g=%7.3f  ->  zero %7.3f   (|diff|=%.3f)%s\n",D[i],Z[bj],best, best<0.05?"  MATCH":"  *** unmatched");
    if(best<0.05) matched++;
  }
  /* completeness: every zero hit? */
  int hit=0;
  for(int j=0;j<nZ;j++){ double best=1e9; for(int i=0;i<nd;i++){double d=fabs(D[i]-Z[j]); if(d<best)best=d;} if(best<0.05)hit++; }
  printf("\nmatched %d/%d vanishings to a zero;  %d/%d zeros captured by a vanishing\n",matched,nd,hit,nZ);
  printf("\n=== count:  winding-vanishings(<T)  vs  N(T)=(T/2pi)[log(3T/2pi)-1] ===\n");
  for(double T=20;T<=56;T+=12){ int c=0; for(int i=0;i<nd;i++) if(D[i]<T)c++;
    double NT=(T/(2*M_PI))*(log(3*T/(2*M_PI))-1.0);
    printf("  T=%2.0f:  vanishings=%2d   N(T)~%4.1f\n",T,c,NT); }
  return 0;
}
