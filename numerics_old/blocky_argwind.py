"""
blocky_argwind.py
=================
Trigger 2 showed: arg V(t) winding fires self-boundaries, half of which land on zeros to
1e-3. This file pins down the REAL winding law of the resultant V(t)=L(1/2+it) as a 2-vector,
and tests the self-consistent feedback rule honestly.

Questions:
 (1) How much does arg V(t) wind between consecutive exact zeros? (per-block, with fluctuation)
 (2) Is "zeros = points where V crosses the negative-real axis / Im V changes sign with Re V<0"
     -- i.e. arg V hits an odd multiple of pi? Then a SELF rule "advance arg V by pi" is exact.
 (3) The swept signed AREA feedback: dA = (1/2)(x dy - y dx) of the resultant. Does the area
     between consecutive zeros quantize?
"""
import numpy as np
import mpmath as mp
from blocky_helix_build import compute_exact_zeros, chi3

mp.mp.dps = 25
Q = 3
GAMMA = compute_exact_zeros(65)
gap = np.diff(GAMMA)

# resultant vector V(t) = L(1/2+it) as (Re, Im), computed EXACTLY via mpmath
def Vexact(t):
    s = mp.mpf(1)/2 + 1j*mp.mpf(str(t))
    z = mp.power(3,-s)*(mp.zeta(s, mp.mpf(1)/3) - mp.zeta(s, mp.mpf(2)/3))
    return float(mp.re(z)), float(mp.im(z))

print("="*78)
print("(1) WINDING of arg V(t) between consecutive EXACT zeros (block-by-block)")
print("="*78)
# sample arg V densely, unwrap, measure delta-arg across each [gamma_k, gamma_{k+1}]
tlo, thi = 7.5, GAMMA[20]+0.3
ts = np.arange(tlo, thi, 0.01)
V = np.array([Vexact(t) for t in ts])
arg = np.unwrap(np.arctan2(V[:,1], V[:,0]))
def arg_at(t): return np.interp(t, ts, arg)
print(f"  {'k':>3} {'gamma_k':>9} {'gap':>7} {'d(argV)/pi over block':>22}")
dwind = []
for k in range(18):
    a0, a1 = arg_at(GAMMA[k]), arg_at(GAMMA[k+1])
    w = (a1-a0)/np.pi
    dwind.append(w)
    print(f"  {k:3d} {GAMMA[k]:9.4f} {gap[k]:7.4f} {w:22.4f}")
dwind = np.array(dwind)
print(f"\n  mean winding/pi per block = {np.mean(dwind):.4f}  std = {np.std(dwind):.4f}")
print(f"  => if mean~1 with small std, 'advance argV by pi' is the self-consistent boundary law.")
print(f"     if mean~2, zeros are HALF as frequent as pi-crossings (need pi vs 2pi resolution).")

print("\n" + "="*78)
print("(2) Is each zero an arg V == k*pi crossing? (resultant lands ON the real axis)")
print("="*78)
# At a true zero V=0, so arg is undefined; but just OFF the zero arg passes through a
# specific value. Test: sign of Im V at the zero crossing, and whether Re V dominates.
for k in range(8):
    g = GAMMA[k]
    vm = Vexact(g-0.02); vp = Vexact(g+0.02)
    print(f"  gamma={g:8.4f}  V(g-)= ({vm[0]:+.4f},{vm[1]:+.4f})  V(g+)=({vp[0]:+.4f},{vp[1]:+.4f})")
print("  (V passes THROUGH the origin at each zero -> arg flips by pi: the half-turn is real)")

print("\n" + "="*78)
print("(3) SWEPT SIGNED AREA feedback between consecutive zeros (does it quantize?)")
print("="*78)
# A(t) = (1/2) integral (x dy - y dx) of the resultant curve V(t). Area swept per block.
x, y = V[:,0], V[:,1]
dx, dy = np.gradient(x, ts), np.gradient(y, ts)
dA = 0.5*(x*dy - y*dx)
Acum = np.concatenate([[0], np.cumsum(0.5*(dA[1:]+dA[:-1])*np.diff(ts))])
def A_at(t): return np.interp(t, ts, Acum)
print(f"  {'k':>3} {'gamma_k':>9} {'swept signed area in block':>26} {'/gap':>9}")
areas=[]
for k in range(16):
    a = A_at(GAMMA[k+1]) - A_at(GAMMA[k])
    areas.append(a)
    print(f"  {k:3d} {GAMMA[k]:9.4f} {a:26.5f} {a/gap[k]:9.4f}")
areas=np.array(areas)
print(f"\n  mean area/block={np.mean(areas):.4f} std={np.std(areas):.4f} "
      f"-> quantized? cv={np.std(areas)/abs(np.mean(areas)):.3f}")
