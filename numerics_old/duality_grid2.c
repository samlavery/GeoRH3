/* duality_grid2.c — expanded chi3 trace-identity grid, two kernels.
 * K1 resolvent (1/gamma^2):  sum Lambda chi3 (n^-s - n^-s')  ==  (1/2)[psi-]  - sum_rho[1/(s-r)-1/(s'-r)]
 * K2 squared   (1/gamma^4): -sum Lambda chi3 ln n (n^-s - n^-s') == (1/4)[psi'-] + sum_rho[1/(s-r)^2-1/(s'-r)^2]
 * Prime side is the RAW von Mangoldt sum (primes, incl. powers) — independent of how zeros were found.
 * High-Re pairs make K2's prime side converge to 12+ digits; K2's zero side truncates at ~1e-10. */
#include <stdio.h>
#include <math.h>
#include <stdlib.h>
static int chi3(long n){long r=n%3;return r==1?1:(r==2?-1:0);}
static double digamma(double x){double r=0;while(x<8){r-=1.0/x;x+=1;}double f=1.0/(x*x);
  r+=log(x)-0.5/x-f*(1.0/12-f*(1.0/120-f/252));return r;}
static double trigamma(double x){double r=0;while(x<8){r+=1.0/(x*x);x+=1;}double f=1.0/(x*x);
  r+=1.0/x+0.5*f+(f/x)*(1.0/6-f*(1.0/30-f/42));return r;}
int main(){
  long NMAX=200000000;                       /* 2e8 */
  double sv[8]={1.5,2,2.5,3,4,5,6,7}; double S0[8]={0},S1[8]={0};
  char*isc=calloc(NMAX+1,1);
  for(long p=2;p<=NMAX;p++) if(!isc[p]){
    for(long m=2*p;m<=NMAX;m+=p) isc[m]=1;
    double lp=log((double)p); long pk=p;
    while(pk<=NMAX){int c=chi3(pk); if(c){double ln=log((double)pk); for(int j=0;j<8;j++){double t=c*lp*exp(-sv[j]*ln); S0[j]+=t; S1[j]+=t*ln;}} if(pk>NMAX/p)break; pk*=p;} }
  free(isc);
  double*G=malloc(4000*sizeof(double)); long ng=0; FILE*f=fopen("lchi3_zeros_record.txt","r"); char line[512];
  while(fgets(line,sizeof line,f)){long idx;double g;if(sscanf(line," %ld %lf",&idx,&g)==2&&g>1.0&&ng<4000)G[ng++]=g;} fclose(f);
  double cut[4]={500,1000,2000,3502};
  /* ---- K1 resolvent ---- */
  double r1[4][2]={{2,3},{2,4},{3,5},{1.5,2.5}}; int r1i[4][2]={{1,3},{1,4},{3,5},{0,2}};
  printf("=== KERNEL 1: resolvent (1/gamma^2)   prime = sum Lambda chi3 (n^-s - n^-s') ===\n");
  printf("pair        prime           corrected diff at Gmax= 500 / 1000 / 2000 / 3502\n");
  for(int k=0;k<4;k++){double s=r1[k][0],sp=r1[k][1],sig=s-.5,sgp=sp-.5,prime=S0[r1i[k][0]]-S0[r1i[k][1]];
    double dg=0.5*(digamma((s+1)/2)-digamma((sp+1)/2));
    printf("(%.1f,%.1f) %14.10f  ",s,sp,prime);
    for(int c=0;c<4;c++){double T=cut[c],zr=0; for(long i=0;i<ng;i++){double g=G[i];if(g>T)break;double g2=g*g;zr+=2*(sig/(sig*sig+g2)-sgp/(sgp*sgp+g2));}
      double tail=(s-sp)/M_PI*((log(3*T/(2*M_PI))+1)/T); printf("%9.1e ",prime-(dg-(zr+tail)));} printf("\n"); }
  /* ---- K2 squared resolvent, high-Re pairs ---- */
  double r2[5][2]={{3,5},{4,6},{3,6},{4,7},{5,7}}; int r2i[5][2]={{3,5},{4,6},{3,6},{4,7},{5,7}};
  printf("\n=== KERNEL 2: squared resolvent (1/gamma^4)   prime = -sum Lambda chi3 ln n (n^-s - n^-s') ===\n");
  printf("pair        prime           corrected diff at Gmax= 500 / 1000 / 2000 / 3502\n");
  for(int k=0;k<5;k++){double s=r2[k][0],sp=r2[k][1],sig=s-.5,sgp=sp-.5,prime=-(S1[r2i[k][0]]-S1[r2i[k][1]]);
    double tg=0.25*(trigamma((s+1)/2)-trigamma((sp+1)/2));
    printf("(%.0f,%.0f) %16.12f  ",s,sp,prime);
    for(int c=0;c<4;c++){double T=cut[c],zr=0; for(long i=0;i<ng;i++){double g=G[i];if(g>T)break;double g2=g*g,a=sig*sig+g2,b=sgp*sgp+g2;
        zr+=2*((sig*sig-g2)/(a*a)-(sgp*sgp-g2)/(b*b));}
      /* tail ~ 6(sig^2-sgp^2)/pi * [ln(3T/2pi)/3+1/9]/T^3 */
      double tail=3*(sig*sig-sgp*sgp)/M_PI*((log(3*T/(2*M_PI))/3.0+1.0/9)/(T*T*T));
      printf("%9.1e ",prime-(tg+zr+tail));} printf("\n"); }
  return 0;
}
