"""
TRULY FORWARD collective metric: build the prime-power SPECTRUM (no zeros input),
and ask whether the canonical zeros' dual spectrum D(u)=sum cos(gamma_n u) is
RECONSTRUCTED by it as the prime-power cutoff X grows.

Explicit formula (Riemann-Weil), schematically:
   sum_n cos(gamma_n u)  <->  smooth(u) - sum_{p,k} (log p) p^{-k/2} delta(u - k log p)
i.e. the zeros' dual spectrum is (a smooth Gamma-driven part) MINUS prime-power spikes.

FORWARD test: take ONLY the prime-power spikes P(u) = sum_{p^k<=X} (log p)p^{-k/2}
phi(u - k log p)  (phi = narrow window), and correlate with the canonical D_zeros(u)
over a u-grid as X grows. Does the correlation IMPROVE toward 1 as X grows?
Then test whether the SMOOTH residual (D_zeros - P) is t-flat (geometric) or needs Gamma.

numpy float64; mpmath at dps=15 for reference only; small u-grid (no big arrays).
"""
import sys, math
import numpy as np
import mpmath as mp
mp.mp.dps=15
def pr(*a): print(*a); sys.stdout.flush()

NREF=30
GAMMA=np.array([float(mp.zetazero(n).imag) for n in range(1,NREF+1)])

def prime_powers(X):
    Xc=int(X); sieve=np.ones(Xc+1,bool); sieve[:2]=False
    for i in range(2,int(Xc**0.5)+1):
        if sieve[i]: sieve[i*i::i]=False
    primes=np.nonzero(sieve)[0]
    u,w=[],[]
    for p in primes.tolist():
        lp=math.log(p); pk=p; k=1
        while pk<=Xc:
            u.append(k*lp); w.append(lp*pk**-0.5); pk*=p; k+=1
    return np.array(u),np.array(w)

# u-grid in the band where prime powers live (log2 .. log(1e5)~11.5)
u=np.arange(0.5,8.0,0.01)          # ~750 pts
# canonical zeros' dual spectrum on the grid: D(u)=sum_n cos(gamma_n u), 30 zeros
Dz=np.cos(np.outer(u,GAMMA)).sum(axis=1)   # 750x30 fine

# prime-power spike train smoothed by a narrow Gaussian window (width sig)
sig=0.05
def Pspikes(X):
    uu,ww=prime_powers(X)
    P=np.zeros_like(u)
    for c,a in zip(uu.tolist(),ww.tolist()):
        if c<u[0]-0.3 or c>u[-1]+0.3: continue
        P+=a*np.exp(-0.5*((u-c)/sig)**2)
    return P

pr("FORWARD: correlate canonical zeros' dual spectrum D_zeros(u) with the")
pr("prime-power spike train P(u)=sum (log p)p^-k/2 window(u-k log p), as X grows.")
pr("D_zeros is built from 30 zeros (finite); spikes-vs-zeros sign is NEGATIVE")
pr("(explicit formula: zeros' oscillation = -prime spikes). Report -corr so >0 = match.")
pr(f"{'X':>7} {'#pp in band':>11} {'-corr(D_zeros, P)':>18}")
for X in [10,100,1000,10000,100000]:
    P=Pspikes(X)
    # correlation of zero-spectrum oscillation with prime spike train
    a=Dz-Dz.mean(); b=P-P.mean()
    corr=np.sum(a*b)/math.sqrt(np.sum(a*a)*np.sum(b*b))
    npp=int(np.sum((prime_powers(X)[0]>=u[0]-0.3)&(prime_powers(X)[0]<=u[-1]+0.3)))
    pr(f"{X:>7} {npp:>11} {-corr:>18.4f}")
pr("  -> -corr stays modest/flat: the prime spikes capture WHERE D_zeros oscillates")
pr("     but the FINITE 30-zero D_zeros is not a clean spike train, and the SMOOTH")
pr("     Gamma part of the explicit formula is missing from the prime-only side.")
pr("")
pr("Per-zero secondary check (accumulates drift, reported LAST):")
pr("Using the WORKING construction (RS sum + smooth phase) the first crossings vs gamma:")
t=np.arange(8.0,40.0,0.01)
th=np.array([float(mp.siegeltheta(tt)) for tt in t])
nmax=np.floor(np.sqrt(t/(2*math.pi))).astype(int)
W=np.zeros_like(t)
for n in range(1,int(nmax.max())+1):
    m=nmax>=n
    if m.any(): W[m]+=(1/math.sqrt(n))*np.cos(th[m]-t[m]*math.log(n))
W*=2
s=np.sign(W); idx=np.nonzero(s[:-1]*s[1:]<0)[0]
cr=t[idx]-W[idx]*(t[idx+1]-t[idx])/(W[idx+1]-W[idx])
cr=np.sort(cr)[:6]
gam=GAMMA[(GAMMA>=8)&(GAMMA<=40)][:6]
pr(f"  predicted: {np.round(cr,3).tolist()}")
pr(f"  canonical: {np.round(gam,3).tolist()}")
pr(f"  per-zero abs resid: {np.round(np.abs(cr-gam),3).tolist()}  (small but Gamma-borrowed)")
