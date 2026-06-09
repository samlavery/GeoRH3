/* duality_battery.c — falsification grid for the chi3 trace identity (explicit formula).
 * For pairs (s,s'), s,s'>1:   PRIME side  ==  ZERO side
 *   sum_n Lambda(n) chi3(n)(n^-s - n^-s')   ==   (1/2)[psi((s+1)/2)-psi((s'+1)/2)] - sum_rho K(gamma)
 *   K(gamma) = 2[ sig/(sig^2+gamma^2) - sig'/(sig'^2+gamma^2) ],  sig=s-1/2, sig'=s'-1/2.
 * Per-kernel analytic tail (gamma>T):  (s-s')/pi * [ln(3T/2pi)+1]/T   (leading 1/gamma^2 term, dN=(1/2pi)ln(3g/2pi)dg).
 * Normalization: Lambda(s,chi3)=(3/pi)^((s+1)/2)Gamma((s+1)/2)L, eps=1, center 1/2, chi3(2)=-1, p=3 omitted (chi3(3^k)=0).
 * Prime side includes prime POWERS. Cutoff table shows corrected diff flatten while raw diff tracks the tail. */
#include <stdio.h>
#include <math.h>
#include <stdlib.h>
static int chi3(long n){long r=n%3;return r==1?1:(r==2?-1:0);}
static double digamma(double x){double r=0;while(x<6){r-=1.0/x;x+=1.0;}double f=1.0/(x*x);
  r+=log(x)-0.5/x-f*(1.0/12.0 - f*(1.0/120.0 - f*(1.0/252.0)));return r;}
int main(){
  long NMAX=100000000;                       /* 1e8 : ~7 digits for min(Re s)>=2 */
  double sval[6]={1.5,2.0,2.5,3.0,4.0,5.0}; double S[6]={0,0,0,0,0,0};
  char*isc=calloc(NMAX+1,1);
  for(long p=2;p<=NMAX;p++) if(!isc[p]){
    for(long m=2*p;m<=NMAX;m+=p) isc[m]=1;
    double lp=log((double)p); long pk=p;
    while(pk<=NMAX){ int c=chi3(pk); if(c){ double ln=log((double)pk); for(int j=0;j<6;j++) S[j]+=c*lp*exp(-sval[j]*ln);} if(pk>NMAX/p) break; pk*=p; } }
  free(isc);
  /* read zeros */
  long CAP=4000; double*G=malloc(CAP*sizeof(double)); long ng=0;
  FILE*f=fopen("lchi3_zeros_record.txt","r"); char line[512];
  while(fgets(line,sizeof line,f)){long idx;double g;if(sscanf(line," %ld %lf",&idx,&g)==2&&g>1.0&&ng<CAP)G[ng++]=g;}
  fclose(f);
  /* pairs as (s, s', prime_index_s, prime_index_s') */
  double ss[4][2]={{2,3},{2,4},{3,5},{1.5,2.5}}; int pi[4][2]={{1,3},{1,4},{3,5},{0,2}};
  double cut[4]={500,1000,2000,3502};
  for(int k=0;k<4;k++){ double s=ss[k][0],sp=ss[k][1];
    double prime=S[pi[k][0]]-S[pi[k][1]];
    double sig=s-0.5, sigp=sp-0.5, digam=0.5*(digamma((s+1)/2)-digamma((sp+1)/2));
    printf("\n=== pair (s,s')=(%.1f,%.1f)   prime side = %.12f ===\n",s,sp,prime);
    printf("  Gmax     zero_raw        tail          zero+tail->RHS   diff(corr)   diff(raw)\n");
    for(int c=0;c<4;c++){ double T=cut[c], zr=0;
      for(long i=0;i<ng;i++){ double g=G[i]; if(g>T) break; double g2=g*g; zr+=2.0*( sig/(sig*sig+g2) - sigp/(sigp*sigp+g2) ); }
      double tail=(s-sp)/M_PI*((log(3.0*T/(2*M_PI))+1.0)/T);
      double rhs_corr=digam-(zr+tail), rhs_raw=digam-zr;
      printf("  %5.0f  %14.10f  %12.3e   %14.10f  %9.2e   %9.2e\n",T,zr,tail,rhs_corr,prime-rhs_corr,prime-rhs_raw);
    }
  }
  printf("\nPASS if diff(corr) shrinks with Gmax and lands near precision for all pairs.\n");
  return 0;
}
