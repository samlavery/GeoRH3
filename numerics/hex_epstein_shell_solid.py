"""
EXP6b -- build the SHELL solid as real 3D annuli and confirm cancellation at more zeros.
The 3D object: each Eisenstein integer (a,b) at hex point (a+b/2, b sqrt3/2), LIFTED to height
z = norm m = a^2-ab+b^2 (the algebraic invariant). Shells = horizontal slices at integer heights m.
Each shell m is a real ring of r(m) lattice points. The chi3-weighted shell phasor is
  P_m = (r(m)/6) * m^{-1/2} * e^{-i w log m}  (length=algebraic shell weight, angle from norm winding).
The vector sum over shells collapses at chi3 zeros (mod zeta). This is genuine 2D-lattice geometry.
"""
import mpmath as mp
mp.mp.dps=20
ZEROS=[8.0397371556814667,11.2492062077729352,15.7046191767216256,18.2619974956931276,
       20.4557708077424929,24.0594148564934508,26.5778687357745853,28.2181645062333861]
def Lh(s): return mp.power(3,-s)*(mp.zeta(s,mp.mpf(1)/3)-mp.zeta(s,mp.mpf(2)/3))
import numpy as np, math
# build shells: r(m) and the actual lattice points per shell
B=300
from collections import defaultdict
shell=defaultdict(list)
for a in range(-B,B+1):
    for b in range(-B,B+1):
        m=a*a-a*b+b*b
        if m>0 and m<=4000:
            shell[m].append((a+b/2.0, b*math.sqrt(3)/2.0))
print("=== EXP6b: real 3D shell solid (hex points lifted to height = norm m) ===")
print(f"{'m':>5} {'r(m)':>5} {'r/6=sum chi3(d)':>16}  sample lattice pts (x,y) at height z=m")
for m in [1,3,4,7,12,13,49]:
    pts=shell[m]
    sp=", ".join(f"({x:.2f},{y:.2f})" for x,y in pts[:3])
    print(f"{m:5d} {len(pts):5d} {len(pts)/6:16.1f}  {sp} ... (z={m})")

def r6(m): return len(shell.get(m,[]))/6.0
def shellsum(w,reg,M):
    tot=mp.mpf(0)
    s=mp.mpf(1)/2+1j*w
    for m in range(1,M+1):
        w6=r6(m)
        if w6==0:continue
        tot+=w6*mp.power(m,-s)*mp.e**(-reg*m)
    return tot
print("\n=== shell-sum cancellation at ALL listed chi3 zeros (Abel reg=0.002, M=4000) ===")
reg=mp.mpf('0.002')
print(f"{'gamma':>9} {'|E_shell|':>11} {'|E_shell/zeta|=|L|':>18}")
for g in ZEROS:
    Es=shellsum(g,reg,4000)
    zz=mp.zeta(mp.mpf(1)/2+1j*g)
    print(f"{g:9.4f} {float(abs(Es)):11.5f} {float(abs(Es/zz)):18.5f}")
print("\ncontrols (between chi3 zeros, away from zeta zeros):")
for g in [3.0,5.0,9.0,17.0]:
    Es=shellsum(g,reg,4000)
    zz=mp.zeta(mp.mpf(1)/2+1j*g)
    print(f"{g:9.4f} {float(abs(Es)):11.5f} {float(abs(Es/zz)):18.5f}  |L true|={float(abs(Lh(mp.mpf(1)/2+1j*g))):.4f}")
