/* helix_accumulator.c — the ACTUAL geometric helix winding sum (no analytic L).
 * Integers placed on the area-law helix: radius R(n)=sqrt(C*n), amp 1/R(n) ~ n^{-1/2},
 * winding phase 2*ln R(n) = ln n + ln C.  Readout (gauge C=1):
 *     S_N(g) = sum_{n<=N} chi3(n) * n^{-1/2} * e^{-i g ln n}
 * As integers accumulate, the signed winding vectors CANCEL exactly at a zero of L(chi3),
 * and do NOT cancel off a zero.  This is the construction emitting the zero, geometrically. */
#include <stdio.h>
#include <math.h>
#include <complex.h>
static int chi3(long n){long r=n%3;return r==1?1:(r==2?-1:0);}
int main(){
  long double g1 = 8.03973715568146668171362321417296580279L; /* a true L(chi3) zero  */
  long double g2 = 30.74504026138249573780824181050617135037L; /* zero #9               */
  long double gnz= 9.30L;                                       /* a NON-zero (mid-gap)  */
  printf("# Geometric helix winding accumulator |S_N(g)| as integers accumulate\n");
  printf("#        N      |S_N| at zero g1      |S_N| at zero g9      |S_N| off-zero g=9.30\n");
  long double complex Sz1=0,Sz9=0,Sn=0;
  long cp[]={1000,10000,100000,1000000,10000000,100000000,400000000};int ci=0;
  for(long n=1;n<=400000000L;n++){int c=chi3(n);if(c){
      long double ln=logl((long double)n),amp=c/sqrtl((long double)n);
      long double cz1=cosl(g1*ln),sz1=sinl(g1*ln),cz9=cosl(g2*ln),sz9=sinl(g2*ln),cn=cosl(gnz*ln),sn=sinl(gnz*ln);
      Sz1+=amp*(cz1 - I*sz1); Sz9+=amp*(cz9 - I*sz9); Sn+=amp*(cn - I*sn);}
    if(ci<7&&n==cp[ci]){printf("  %11ld   %.8Le   %.8Le   %.8Le\n",n,cabsl(Sz1),cabsl(Sz9),cabsl(Sn));ci++;}}
  printf("# at the zeros |S_N| decays toward 0 as the winding cancels (~N^{-1/2}); off-zero it sits O(1).\n");
  return 0;
}
