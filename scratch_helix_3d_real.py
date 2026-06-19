"""
USE THE ACTUAL HELIX CURVE.  helix p r k = (r*k*cos 2pi k, r*k*sin 2pi k, p*k).
Radial growth r = A = pi/6.  Integers area-packed by the pi/3 gauge:
  area gauge C = 2*A*ds = (pi/3)^2;  R_n^2 = C*n  =>  R_n = (pi/3) sqrt(n).
  On the curve R = A*k  =>  k_n = R_n/A = 2 sqrt(n).  So integer n sits at PARAMETER k_n = 2 sqrt(n),
  i.e. at the genuine 3-D point  P_n = helix(p)(pi/6)(2 sqrt n)  -- radius, WINDING angle, height all real.
"""
import numpy as np

A     = np.pi/6     # radial growth (the curve's radius coefficient r)
pitch = 1.0         # height pitch p
C     = (np.pi/3)**2

def helix(k):       # the actual 3-D helix curve point at parameter k
    R = A*k
    ang = 2*np.pi*k
    return np.array([R*np.cos(ang), R*np.sin(ang), pitch*k]), R, ang, pitch*k

def site(n):        # integer n on the curve, area-packed: k_n = 2 sqrt(n)
    return helix(2*np.sqrt(n))

print("3-D HELIX SITES  P_n = (R cos2pi k, R sin2pi k, p k),  k_n = 2 sqrt(n):")
for n in [1, 2, 3, 4, 5, 7, 16, 100]:
    P, R, ang, z = site(n)
    print(f"  n={n:3d}:  P=({P[0]:+7.3f},{P[1]:+7.3f},{P[2]:7.3f})   R={R:.4f} [(pi/3)sqrt(n)={np.pi/3*np.sqrt(n):.4f}]   wind={ang:8.3f} rad   z={z:.3f}")

print("\nEQUAL-AREA placement (the pi/3 gauge): disk area pi*R_n^2 grows by exactly pi*C per integer:")
for n in [1, 2, 3, 4, 5]:
    _, R, _, _ = site(n)
    _, Rm, _, _ = site(n-1) if n > 1 else (None, 0.0, None, None)
    print(f"  n={n}:  pi*R_n^2={np.pi*R**2:8.4f}   increment={np.pi*(R**2-Rm**2):.4f}   pi*C={np.pi*C:.4f}")

print("\nFROBENIUS x p = a SPIRAL SELF-SIMILARITY of the curve (site n -> site pn):")
print("   radius, height AND winding-angle all scale by sqrt(p)=sqrt(q) -- the helix maps onto itself:")
for (n, pp) in [(1, 2), (1, 3), (2, 5), (1, 7)]:
    P1, R1, a1, z1 = site(n)
    P2, R2, a2, z2 = site(pp*n)
    print(f"   n={n}, p={pp}:  R2/R1={R2/R1:.4f}   z2/z1={z2/z1:.4f}   angle2/angle1={a2/a1:.4f}   sqrt(p)={np.sqrt(pp):.4f}")

print("""
THE HELIX, USED:  integers sit at real 3-D points on (r k cos2pi k, r k sin2pi k, p k); the pi/3
gauge area-packs them so radius = (pi/3)sqrt(n) (the sigma=1/2 baseline); and Frobenius x p is the
spiral self-similarity that scales the WHOLE point -- radius, height, winding -- by sqrt(q).  The
sqrt(q)-purity is the curve's self-similarity ratio, read off the actual 3-D winding geometry.
""")
