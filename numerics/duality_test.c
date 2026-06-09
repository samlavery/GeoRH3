/* duality_test.c — Weil explicit-formula duality for L(chi3):  PRIME side  ==  ZERO side.
 * Difference form (B, log(q/pi), 1/rho counterterms all cancel), s=2, s'=3:
 *   sum_n Lambda(n) chi3(n) (n^-2 - n^-3)            [PRIME / geometric side]
 *      ==  (1/2)[psi(3/2)-psi(2)]  -  sum_rho [1/(2-rho) - 1/(3-rho)]   [ZERO / spectral side]
 * rho = 1/2 +- i gamma_n  (chi3 real => conjugate pairs; imaginary parts cancel).
 * The two sides are computed from completely disjoint data (primes vs the 3580 computed zeros). */
#include <stdio.h>
#include <math.h>
#include <stdlib.h>
static int chi3(long n){long r=n%3;return r==1?1:(r==2?-1:0);}
int main(){
  /* ---- PRIME side: Lambda via smallest-prime sieve up to NMAX ---- */
  long NMAX=20000000;
  char *isc=calloc(NMAX+1,1);
  double LEFT=0;
  for(long p=2;p<=NMAX;p++){ if(!isc[p]){ /* p prime */
      for(long m=2*p;m<=NMAX;m+=p) isc[m]=1;
      double lp=log((double)p); long pk=p;
      while(pk<=NMAX){ int c=chi3(pk); if(c){ double a=(double)pk; LEFT += c*lp*(1.0/(a*a) - 1.0/(a*a*a)); } if(pk> NMAX/p) break; pk*=p; } } }
  /* ---- ZERO side: read the 3580 gamma_n, sum 2*Re[1/(2-rho)-1/(3-rho)] ---- */
  FILE*f=fopen("lchi3_zeros_record.txt","r"); if(!f){printf("no record file\n");return 1;}
  char line[512]; double Zsum=0; long cnt=0; double gmax=0;
  while(fgets(line,sizeof line,f)){ long idx; double g;
    if(sscanf(line," %ld %lf",&idx,&g)==2 && g>1.0){ double g2=g*g;
      /* 2*Re[1/(2-(1/2+ig)) - 1/(3-(1/2+ig))] = 2[ (3/2)/(9/4+g^2) - (5/2)/(25/4+g^2) ] */
      Zsum += 2.0*( 1.5/(2.25+g2) - 2.5/(6.25+g2) ); cnt++; if(g>gmax)gmax=g; } }
  fclose(f);
  double digam = 0.5 - log(2.0);              /* (1/2)[psi(3/2)-psi(2)] = (1-2ln2)/2 */
  double RIGHT = digam - Zsum;
  /* analytic tail for the missing zeros gamma>gmax: -2 * integral_{gmax}^inf (1/g^2) dN, dN=(1/2pi)ln(3g/2pi)dg */
  double T=gmax, a=3.0/(2*M_PI);
  double tail = -(1.0/M_PI) * ( (log(a*T)+1.0)/T );   /* = -2*int (1/g^2) dN  (leading) */
  double RIGHT_t = digam - (Zsum + tail);
  printf("PRIME side  (sum over primes, NMAX=2e7)     = %.12f\n", LEFT);
  printf("ZERO  side  (3580 zeros, no tail)           = %.12f   diff = %.2e\n", RIGHT, LEFT-RIGHT);
  printf("ZERO  side  (+ analytic tail gamma>%.0f)     = %.12f   diff = %.2e\n", gmax, RIGHT_t, LEFT-RIGHT_t);
  printf("zeros used = %ld, gamma_max = %.1f\n", cnt, gmax);
  free(isc); return 0;
}
