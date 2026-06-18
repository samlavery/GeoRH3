"""
Everything in 3-D.

Frame: the climb axis z = the height / arc length.  The phasors spin in the plane
transverse to z.  Number n sits on the climbing helix at radius √n (the eigenvalue —
it GROWS with each step), spinning at rate log n.

Full fiber sum at climb-height y (all phasors, accumulated):
    transverse drift  D(y) = Σ_n n^{-1/2} e^{-i y log n}  = ζ(1/2 + i y)
    climb             z    = y
At a generic height the sum drifts off the axis.  At a CROSSING the transverse drift
cancels and the whole 3-D sum lands ON the climb axis — the vanishing / no-drift event.

The eigenvalue is the 3-D radius √k (grows with each vanishing); the crossing is the
point on the climb axis at that height.
"""

import mpmath as mp

mp.mp.dps = 22
M = 12
gamma = [mp.im(mp.zetazero(k)) for k in range(1, M + 1)]


def D(y):
    return mp.zeta(mp.mpf(1) / 2 + 1j * mp.mpf(y))


print("=" * 70)
print("FULL FIBER SUM in 3-D:  (x,y) = transverse drift,  z = climb height")
print("=" * 70)
print(f"{'climb z':>10} {'x = Re D':>12} {'y = Im D':>12} {'transverse radius |D|':>22}")
for y in [8, 14.1347, 18, 21.0220, 25.0109]:
    t = D(y)
    r = abs(t)
    flag = "   ON AXIS — vanishing" if r < 1e-3 else ""
    print(f"{y:>10} {float(mp.re(t)):>12.4f} {float(mp.im(t)):>12.4f} {float(r):>22.5f}{flag}")

print("\n" + "=" * 70)
print("CROSSINGS as 3-D points on the climb axis (transverse drift = 0)")
print("        eigenvalue = 3-D radius √k  (grows with each vanishing)")
print("=" * 70)
print(f"{'k':>3} {'climb z = γ_k':>16} {'3-D point (x,y,z)':>26} {'eigenvalue √k':>16}")
for k, g in enumerate(gamma, 1):
    R = mp.sqrt(k)
    print(f"{k:>3} {float(g):>16.4f}    (0, 0, {float(g):>8.4f})    {float(R):>14.4f}")

print("\neigenvalue (3-D radius) grows with each vanishing:")
print("   √k :", [round(float(mp.sqrt(k)), 3) for k in range(1, M + 1)])

print("\neigenvalue determinant  det(zI − A) = Π_k (z − √k):")
for z in [0, 2, 4]:
    Dz = mp.fprod([z - mp.sqrt(k) for k in range(1, M + 1)])
    print(f"   z = {z}:  det = {float(Dz):.4e}")

# the helix the eigenvalue rides: radius √k climbing to height γ_k, spinning to angle γ_k
print("\n" + "=" * 70)
print("the climbing helix the source modes ride (radius √k, climb γ_k):")
print("=" * 70)
print(f"{'k':>3} {'radius √k':>12} {'helix point (√k·cos γ, √k·sin γ, γ)':>40}")
for k, g in enumerate(gamma[:8], 1):
    R = mp.sqrt(k)
    x = R * mp.cos(g); yv = R * mp.sin(g)
    print(f"{k:>3} {float(R):>12.4f}    ({float(x):>8.4f}, {float(yv):>8.4f}, {float(g):>8.4f})")
