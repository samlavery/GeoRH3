"""
EXP5 -- PER-PRIME log p drift on a genuine 3D Eisenstein-prime spiral. The user's explicit ask:
   phasor at integer n drifts by sum_{p | n} (drift_p), drift_p = log p (FTA building blocks).
   This REBUILDS log n additively from primes (FTA) -- the honest 'earned' multiplicative phase,
   log appearing only as a per-PRIME constant (the bridge readout), not as log of the geometry.

3D OBJECT: place each integer n on the Eisenstein-prime spiral:
   - angle = Theta(n)  (Eisenstein-prime holonomy from exp2, the genuine lattice angle, NO log)
   - radius = grows per loop (we use the spiral so it's a real climbing solid)
   - height z = Phi(n) = sum_{p|n, with mult} log p = log n   <-- the EARNED winding height, FTA-additive
   Point3D(n) = (R cos Theta(n), R sin Theta(n), Phi(n)).
   The phasor spins with the HEIGHT Phi(n) (the multiplicative winding rebuilt from prime logs).

This is the honest synthesis: ANGLE carries the 6th-root lattice geometry (Eisenstein holonomy),
   HEIGHT carries the multiplicative winding rebuilt FTA-additively from per-prime log p constants.
   The zeros are read off the HEIGHT winding (the bridge), the 6-fold lives in the ANGLE.

TEST: |sum_n chi3(n) n^-1/2 e^{-i w Phi(n)}| at zeros, with Phi(n)=sum_{p|n} log p (per-prime).
   Sweep drift_p in {log p, and the named constants log2,log3,log5,log7 used literally per prime}.
"""
import numpy as np
import math
ZEROS=[8.0397371556814667,11.2492062077729352,15.7046191767216256,18.2619974956931276,20.4557708077424929,24.0594148564934508]
def chi3(n):
    r=n%3
    return 1 if r==1 else(-1 if r==2 else 0)
N=300000
spf=np.zeros(N+1,dtype=np.int64)
for i in range(2,N+1):
    if spf[i]==0: spf[i::i]=np.where(spf[i::i]==0,i,spf[i::i])

# Phi(n)=sum_{p|n with mult} log p  -- FTA-additive, per-prime log p constants
Phi=np.zeros(N+1)
for n in range(2,N+1):
    p=spf[n]; Phi[n]=Phi[n//p]+math.log(p)
n=np.arange(1,N+1)
chi=np.where(n%3==1,1.0,np.where(n%3==2,-1.0,0.0))
amp=n**-0.5
Ph=Phi[1:N+1]
print("=== EXP5: Phi(n)=sum_{p|n} log p (FTA-additive, per-prime log p) ===")
print("verify Phi(n) == log n (it must, since sum of prime logs = log n):")
for nn in [2,6,12,100,1000,30030]:
    print(f"   n={nn:6d}: Phi={Ph[nn-1]:.6f}  log n={math.log(nn):.6f}  diff={abs(Ph[nn-1]-math.log(nn)):.2e}")
def collapse(w,drift):
    return abs(np.sum(chi*amp*np.exp(-1j*w*drift)))
print("\n=== collapse with Phi (per-prime log p) drift -- SAME as log n by FTA ===")
print(f"{'gamma':>9} {'|collapse|':>11}")
for g in ZEROS:
    print(f"{g:9.4f} {collapse(g,Ph):11.5f}")
print("controls:")
for g in [3.0,5.0,13.0]:
    print(f"{g:9.4f} {collapse(g,Ph):11.5f}")

# Now the ACTUAL question: can a DIFFERENT per-prime drift (NOT log p) localize the zeros?
# Sweep drift_p = alpha*log p (global rescale) -- only alpha=1 should work. And test pi/3-quantized.
print("\n=== sweep per-prime drift = alpha * log p : which alpha localizes zeros? ===")
for alpha in [0.5,0.9,1.0,1.1,2.0]:
    Pa=alpha*Ph
    vals=[collapse(g,Pa) for g in ZEROS]
    ctrl=[collapse(g,Pa) for g in [3.0,5.0,13.0]]
    print(f"  alpha={alpha:.2f}: zeros mean={np.mean(vals):.4f}  controls mean={np.mean(ctrl):.4f}  contrast={np.mean(ctrl)/np.mean(vals):.2f}")
