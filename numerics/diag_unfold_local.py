#!/usr/bin/env python3
"""
Robustness: is the slight over-rigidity (<s^2>=1.13 < GUE 1.27) an artifact of
unfolding with the asymptotic N_smooth, or real?

Test by re-unfolding with a LOCAL fit: fit a smooth (cubic-spline / high-order
polynomial) to the empirical staircase n vs gamma, use that as the unfolding map.
If <s^2> moves toward 1.273, the deficit was an unfolding artifact.
Also compare to the same statistics computed for an actual GUE matrix of equal N,
and to the well-known Riemann-zeta behavior (which is ~GUE with tiny finite-size
deviations of the SAME sign).
"""
import numpy as np

def load_gammas(path='lchi3_zeros_record.txt'):
    g=[]
    with open(path) as f:
        for line in f:
            line=line.strip()
            if not line or line.startswith('#'): continue
            g.append(float(line.split()[1]))
    return np.array(sorted(g))
g=load_gammas(); N=len(g)
idx=np.arange(1,N+1)

# --- unfolding A: asymptotic N_smooth ---
def Nsmooth(t):
    return (t/(2*np.pi))*np.log(3*t/(2*np.pi)) - t/(2*np.pi)
xA=Nsmooth(g); spA=np.diff(xA)

# --- unfolding B: local polynomial fit to empirical staircase ---
# Fit log-domain: n(gamma) ~ smooth. Use high-degree poly in gamma.
coef=np.polyfit(g, idx, 12)
xB=np.polyval(coef, g); spB=np.diff(xB)

# --- unfolding C: monotone cubic on (gamma, idx) sampled coarsely then eval ---
# subsample every 20th point to get the smooth trend, spline-interp
from numpy import interp
sel=np.arange(0,N,15)
# smooth idx at selected gammas by local average is not needed; idx is already smooth-ish
xC=np.interp(g, g[sel], idx[sel]); spC=np.diff(xC)

# --- reference: real GUE eigenvalues, N=3580, unfolded by semicircle ---
rng=np.random.default_rng(0)
M=(rng.standard_normal((N,N))+1j*rng.standard_normal((N,N)))/np.sqrt(2)
H=(M+M.conj().T)/2
ev=np.sort(np.linalg.eigvalsh(H))
# unfold by semicircle: N(E)= (N/(2pi))( E sqrt(4N-E^2)/(2N) *? )... use empirical rank smoothing
# simpler: unfold GUE by its known mean staircase via polynomial of the rank
cg=np.polyfit(ev, np.arange(1,N+1), 12)
xg=np.polyval(cg, ev); spg=np.diff(xg)

def stats(sp,name):
    sp=sp[sp>0]
    sp=sp/sp.mean()
    print(f"{name:28s} <s>={sp.mean():.4f} <s^2>={np.mean(sp**2):.4f} "
          f"std={sp.std():.4f} frac(s<0.1)={np.mean(sp<0.1):.4f}")

print("GUE target:  <s^2>=1.273 std=0.522 frac(s<0.1)~0.001")
print("Poisson:     <s^2>=2.000 std=1.000 frac(s<0.1)~0.095")
print("-"*70)
stats(spA,"chi3 asymptotic unfold")
stats(spB,"chi3 poly-12 local unfold")
stats(spC,"chi3 linear-interp unfold")
stats(spg,"true GUE matrix (N=3580)")
print("-"*70)
print("If chi3 <s^2> tracks the true-GUE-matrix value (also <1.273 at finite N due")
print("to unfolding), the 'over-rigidity' is a finite-N/unfolding artifact, not real.")
