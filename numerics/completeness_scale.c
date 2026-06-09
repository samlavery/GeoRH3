#include <stdio.h>
#include <math.h>
static int chi3(long n){long r=n%3;return r==1?1:(r==2?-1:0);}
int main(){
  long N=200000;
  static double amp[200001], lnn[200001];
  for(long n=1;n<=N;n++){ amp[n]=chi3(n)/sqrt((double)n); lnn[n]=log((double)n); }
  double Z[]={8.0397,11.2492,15.7046,18.2620,20.4558,24.0594,26.5779,28.2182,30.7450,33.8974,35.6084,37.5518,39.4852,42.6164,44.1206,46.2741,47.5141,50.3751,52.4967,54.1938,55.6426,57.5841,60.0269,62.2061,63.1770,65.2949,66.6231,69.5130,70.8198,72.6561,74.0054,75.6224,78.2175,79.6380,81.6120,82.4703,84.4123,86.3276,88.6526,89.6464,91.3356,92.7535,94.3944,96.8743,98.1265,99.5335,101.3750,102.1164,104.7654,106.2461,107.9703,109.1376,110.5234,112.1548,114.2171,115.8981,117.3698,118.2994,120.2552,121.2788,123.8905,125.0108,126.3973,128.0527,128.9372,130.8114,133.0324,133.9909,135.8209,136.8264,138.0954,139.9983,141.6478,143.6385,144.2517,145.9196,147.2242,148.6031,150.7165,152.3185,153.1907,154.8152,156.1365,157.1484,159.7183,160.5683,162.4151,163.4180,164.6743,166.0663,167.8677,169.5983,170.8475,172.3076,173.0602,174.9714,175.9301,178.2562,179.5188,180.4314};
  int nZ=100;
  double dg=0.02, thr=0.05; double p2=9,p1=9,pg=0; int nd=0; static double D[4000];
  for(double g=5.5;g<=180.5;g+=dg){
    double re=0,im=0;
    for(long n=1;n<=N;n++){ if(amp[n]!=0){ double ph=g*lnn[n]; re+=amp[n]*cos(ph); im-=amp[n]*sin(ph);} }
    double a=sqrt(re*re+im*im);
    if(p1<p2 && p1<a && p1<thr) D[nd++]=pg;
    p2=p1;p1=a;pg=g-dg;
  }
  int matched=0,hit=0,spur=0;
  for(int i=0;i<nd;i++){double b=1e9;for(int j=0;j<nZ;j++){double d=fabs(D[i]-Z[j]);if(d<b)b=d;} if(b<0.07)matched++; else spur++;}
  for(int j=0;j<nZ;j++){double b=1e9;for(int i=0;i<nd;i++){double d=fabs(D[i]-Z[j]);if(d<b)b=d;} if(b<0.07)hit++;}
  printf("=== completeness to gamma=180 (100 zeros, N=%ld) ===\n",N);
  printf("  vanishings=%d  matched=%d  spurious=%d  captured=%d/%d\n",nd,matched,spur,hit,nZ);
  for(double T=45;T<=180;T+=45){int c=0;for(int i=0;i<nd;i++)if(D[i]<T)c++;int z=0;for(int j=0;j<nZ;j++)if(Z[j]<T)z++;
    double NT=(T/(2*M_PI))*(log(3*T/(2*M_PI))-1.0); printf("    T=%3.0f: vanishings=%2d  zeros=%2d  N(T)~%5.1f\n",T,c,z,NT);}
  long M=40000;
  printf("=== off-line sweep to t=180, closer to the line ===\n");
  for(double sig=0.55; sig<=0.85; sig+=0.10){
    double mn=1e9,mt=0;
    for(double t=3;t<=180;t+=0.03){double re=0,im=0;
      for(long n=1;n<=M;n++){int c=chi3(n);if(c){double w=c*exp(-sig*lnn[n]);double ph=t*lnn[n];re+=w*cos(ph);im-=w*sin(ph);}}
      double a=sqrt(re*re+im*im); if(a<mn){mn=a;mt=t;}}
    printf("    sigma=%.2f (off %.2f): min|L|=%.4f at t=%.1f\n",sig,fabs(sig-0.5),mn,mt);
  }
  return 0;
}
