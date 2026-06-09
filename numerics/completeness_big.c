#include <stdio.h>
#include <math.h>
static int chi3(long n){long r=n%3;return r==1?1:(r==2?-1:0);}
int main(){
  long N=120000;
  static double amp[120001], lnn[120001];
  for(long n=1;n<=N;n++){ amp[n]=chi3(n)/sqrt((double)n); lnn[n]=log((double)n); }
  /* chi3 zeros up to ~120 (from the verified record) */
  double Z[]={8.0397,11.2492,15.7046,18.2620,20.4558,24.0594,26.5779,28.2182,30.7450,33.8974,35.6084,37.5518,39.4852,42.6164,44.1206,46.2741,47.5141,50.3751,52.4967,54.1938,55.6426,57.5841,60.0269,62.2061,63.1770,65.2949,66.6231,69.5130,70.8198,72.6561,74.0054,75.6224,78.2175,79.6380,81.6120,82.4703,84.4123,86.3276,88.6526,89.6464,91.3356,92.7535,94.3944,96.8743,98.1265,99.5335,101.3750,102.1164,104.7654,106.2461,107.9703,109.1376,110.5234,112.1548,114.2171,115.8981,117.3698,118.2994};
  int nZ=58;
  double dg=0.02, thr=0.05; double p2=9,p1=9,pg=0; int nd=0; static double D[2000];
  for(double g=5.5;g<=120.0+1e-9;g+=dg){
    double re=0,im=0;
    for(long n=1;n<=N;n++){ if(amp[n]!=0){ double ph=g*lnn[n]; re+=amp[n]*cos(ph); im-=amp[n]*sin(ph);} }
    double a=sqrt(re*re+im*im);
    if(p1<p2 && p1<a && p1<thr) D[nd++]=pg;
    p2=p1;p1=a;pg=g-dg;
  }
  int matched=0,hit=0,spurious=0;
  for(int i=0;i<nd;i++){double b=1e9;for(int j=0;j<nZ;j++){double d=fabs(D[i]-Z[j]);if(d<b)b=d;} if(b<0.06)matched++; else spurious++;}
  for(int j=0;j<nZ;j++){double b=1e9;for(int i=0;i<nd;i++){double d=fabs(D[i]-Z[j]);if(d<b)b=d;} if(b<0.06)hit++;}
  printf("=== completeness to gamma=120 (N=%ld) ===\n",N);
  printf("  winding-vanishings=%d   matched-to-zero=%d   spurious(extra)=%d   zeros-captured=%d/%d\n",nd,matched,spurious,hit,nZ);
  printf("  count vs N(T):\n");
  for(double T=30;T<=120;T+=30){int c=0;for(int i=0;i<nd;i++)if(D[i]<T)c++; int z=0;for(int j=0;j<nZ;j++)if(Z[j]<T)z++;
    double NT=(T/(2*M_PI))*(log(3*T/(2*M_PI))-1.0);
    printf("    T=%3.0f: vanishings=%2d  zeros=%2d  N(T)~%5.1f\n",T,c,z,NT);}
  /* off-line sweep: min |L(sigma+it)| for sigma off 1/2, t in [3,120] */
  long M=20000;
  printf("=== off-line sweep: min |L(sigma+it)|, t in [3,120] (no off-line zero if >>0) ===\n");
  for(double sig=0.60; sig<=0.95; sig+=0.10){
    double mn=1e9,mt=0;
    for(double t=3;t<=120;t+=0.04){
      double re=0,im=0;
      for(long n=1;n<=M;n++){int c=chi3(n);if(c){double w=c*exp(-sig*lnn[n]);double ph=t*lnn[n];re+=w*cos(ph);im-=w*sin(ph);}}
      double a=sqrt(re*re+im*im); if(a<mn){mn=a;mt=t;}
    }
    printf("    sigma=%.2f (off line by %.2f): min|L|=%.4f at t=%.1f\n",sig,fabs(sig-0.5),mn,mt);
  }
  return 0;
}
