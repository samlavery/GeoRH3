"""
EXP2 -- EISENSTEIN-PRIME SPIRAL: phasor drift = accumulated Eisenstein-prime ARGUMENT (holonomy),
        built from FTA in Z[omega].  log/sqrt MINIMIZED -- the drift is a sum of LATTICE ANGLES.

KEY 6th-root structure (the genuine handle):
  Every rational integer n factors in Z[omega].  A rational prime p:
    p=1 mod3  SPLITS: p = pi * conj(pi), pi an Eisenstein prime at a lattice angle in [0,pi/3).
    p=2 mod3  INERT:  p itself is an Eisenstein prime; its 'angle' is degenerate (the inert direction).
    p=3       RAMIFIES: 3 = -omega^2 (1-omega)^2, the ramified direction (angle pi/6, the mirror axis).
  So n = prod p^{e_p} has an Eisenstein factorization, and we can read a GEOMETRIC ANGLE Theta(n)
  = sum over prime factors of (their Eisenstein lattice argument), an FTA-ADDITIVE quantity
  (Theta(mn)=Theta(m)+Theta(n)) -- a log-free multiplicative character on the geometry.

3D OBJECT (printed first):
  place integer n on a spiral: angle = Theta(n) (Eisenstein-prime holonomy, in pi/3-sector units),
  radius grows by SHELL (the k-th loop), height z = loop index k.  Explicit:
     Point3D(n) = ( R(n)cos Theta(n), R(n) sin Theta(n), z(n) )
  We test several radial laws R(n) (the only place an analytic scale can sneak in; we try
  pure-geometric ones first: R = (#shells so far), R = sqrt of count etc.)

PHASOR drift law swept:
  phase(n, w) = w * DRIFT(n), DRIFT in:
     (A) Theta(n)   -- the Eisenstein-prime holonomy angle  (PURE lattice angle, NO log)
     (B) Theta(n) measured in absolute radians from actual pi at split primes
     (C) per-prime log p  (CONTROL -- the analytic disguise)
  weight = chi3(n)  (the inert/split sign).  amplitude = 1/sqrt(n) (needed only to match scale;
  also try amplitude = 1 to see if geometry alone localizes).

VANISHING: |sum_n chi3(n) * amp(n) * e^{i w * DRIFT(n)}| at the exact chi3 zeros.
HONESTY: if DRIFT(n) is proportional to log n, it's the disguise. We MEASURE the correlation
  of Theta(n) with log n and report it. The whole point: is the Eisenstein angle holonomy
  something OTHER than log n that still localizes the zeros?
"""
import numpy as np

ZEROS = [8.0397371556814667, 11.2492062077729352, 15.7046191767216256,
         18.2619974956931276, 20.4557708077424929, 24.0594148564934508,
         26.5778687357745853, 28.2181645062333861]

def chi3(n):
    r = n % 3
    return 1 if r == 1 else (-1 if r == 2 else 0)

N = 200000
# sieve smallest prime factor
spf = np.zeros(N+1, dtype=np.int64)
for i in range(2, N+1):
    if spf[i]==0:
        spf[i::i] = np.where(spf[i::i]==0, i, spf[i::i])

# Eisenstein argument of a rational prime p:
#  split p (=1 mod3): pi=a+b*omega with N=a^2-ab+b^2=p. Its argument is the lattice angle. We pick the
#     representative in the first sector and use its true argument (in radians).
#  inert p (=2 mod3): p is prime in Z[omega]; assign the inert 'unit-cell' argument = pi/3 (a sector edge)
#  ramified p=3: argument = pi/6 (the D6 mirror axis where 3 ramifies).
import math
def split_prime_arg(p):
    # find a,b>0 with a^2-ab+b^2=p, return atan2 of the lab-plane point a*(1,0)+b*(cos60,sin60)
    for a in range(1, int(math.isqrt(p))+2):
        for b in range(0, int(math.isqrt(p))+2):
            if a*a-a*b+b*b==p:
                x=a+b/2.0; y=b*math.sqrt(3)/2.0
                ang=math.atan2(y,x)
                if 0<=ang<math.pi/3+1e-9:
                    return ang
    return None

# precompute prime Eisenstein args
prime_arg = {}
def get_prime_arg(p):
    if p in prime_arg: return prime_arg[p]
    if p==3: v=math.pi/6
    elif p%3==1:
        v=split_prime_arg(p)
        if v is None: v=0.0
    else: v=math.pi/3   # inert
    prime_arg[p]=v; return v

# Build Theta(n) = sum over prime factors (with multiplicity) of get_prime_arg(p)  -- FTA additive
Theta = np.zeros(N+1)
logn = np.zeros(N+1)
for n in range(2, N+1):
    p = spf[n]
    Theta[n] = Theta[n//p] + get_prime_arg(p)
    logn[n] = np.log(n)

n_arr = np.arange(1, N+1)
chi = np.array([chi3(n) for n in n_arr])
Th = Theta[1:N+1]

print("=== EXP2: Eisenstein-prime holonomy angle Theta(n) (FTA-additive lattice angle, no log) ===")
print("prime Eisenstein args (radians):")
for p in [2,3,5,7,11,13,7,19,31]:
    print(f"   p={p:3d} ({'split' if p%3==1 else ('inert' if p%3==2 else 'ramif')}): arg={get_prime_arg(p):.5f}  (in pi/3 units: {get_prime_arg(p)/(np.pi/3):.4f})")
print(f"\nTheta(n) sample (FTA-additive holonomy):")
for n in [2,3,4,5,6,7,12,49,1000]:
    print(f"   n={n:5d}: Theta={Th[n-1]:8.4f}   log n={np.log(n):7.4f}   Theta/log n={Th[n-1]/np.log(n):.4f}")

# HONESTY: correlation of Theta(n) with log n
m = n_arr>10
cc = np.corrcoef(Th[m], logn[1:N+1][m])[0,1]
slope = np.polyfit(logn[1:N+1][m], Th[m],1)
print(f"\nHONESTY: corr(Theta, log n) = {cc:.4f};  Theta ~ {slope[0]:.4f}*log n + {slope[1]:.4f}")
print("  (if corr~1 and slope const, Theta IS log n in disguise; if not, it's genuinely new structure)")

amp_sqrt = 1.0/np.sqrt(n_arr)
amp_one  = np.ones_like(n_arr, dtype=float)

def collapse(w, drift, amp):
    return abs(np.sum(chi*amp*np.exp(1j*w*drift)))

print("\n=== collapse at chi3 zeros: DRIFT=Theta (Eisenstein holonomy), amp=1/sqrt(n) ===")
print(f"{'gamma':>9} {'|Theta-drift|':>14} {'|log-drift(ctrl)|':>18}")
for g in ZEROS:
    print(f"{g:9.4f} {collapse(g,Th,amp_sqrt):14.5f} {collapse(g,logn[1:N+1],amp_sqrt):18.5f}")
print("\nbetween-zero controls:")
for g in [3.0,5.0,13.0,22.0]:
    print(f"{g:9.4f} {collapse(g,Th,amp_sqrt):14.5f} {collapse(g,logn[1:N+1],amp_sqrt):18.5f}")
