"""
helix3d.py -- the integers in 3D.  Radius and rotation are pinned (R=sqrt(n), theta=gamma*log n);
now add the axial coordinate z.  Even arc-length spacing on a sqrt(n)-radius spiral => z ~ log n.
Report the genuine 3D pitch (axial rise per turn) and the per-turn radial scaling -- the third
dimension the 2D fuzz could not see.
"""
import numpy as np
g = 8.0397371556814666817   # first chi3 zero (the winding rate / pitch parameter)
N = 4000
n = np.arange(1, N + 1)
R = np.sqrt(n)              # radius (pinned)
theta = g * np.log(n)      # winding angle (pinned: log rotation, rate gamma)
z = np.log(n)              # axial height (even arc-length on a growing-radius spiral)
x, y = R * np.cos(theta), R * np.sin(theta)
sign = np.where(n % 3 == 1, 1.0, np.where(n % 3 == 2, -1.0, 0.0))

# --- the genuine 3D pitch: one full turn is d(theta)=2pi -> d(log n)=2pi/gamma -> dz=2pi/gamma ---
pitch = 2 * np.pi / g
radial_scale = np.exp(np.pi / g)          # radius multiplies by e^{pi/gamma} each turn
print(f"3D helix for gamma = {g:.4f}  (gamma is the PITCH parameter):")
print(f"   axial pitch  (rise per 2pi turn) z: dz = 2pi/gamma      = {pitch:.5f}")
print(f"   radial scale (radius x per turn)   : e^(pi/gamma)        = {radial_scale:.5f}")
print(f"   => a LOGARITHMIC CONE: radius = e^(z/2), self-similar per turn (each turn: +{pitch:.3f} up, x{radial_scale:.3f} out)")

# integers per turn at height z (the cone flares): n -> n*e^{2pi/gamma}
for nn in (10, 100, 1000):
    per_turn = nn * (np.exp(2 * np.pi / g) - 1)
    print(f"   near n={nn:5d}: ~{per_turn:6.1f} integers in the next full turn   (radius {np.sqrt(nn):.2f})")

# --- the three chi3 fibres are three interleaved strands; show their first points in 3D ---
print("\n   the 3 fibres are 3 interleaved strands (every 3rd integer):")
for lbl, r in [("+ (n=1 mod3)", 1), ("- (n=2 mod3)", 2), ("silent (0)", 0)]:
    idx = np.where(n % 3 == r)[0][:3]
    pts = [(round(float(x[i]), 2), round(float(y[i]), 2), round(float(z[i]), 2)) for i in idx]
    print(f"      {lbl}: {pts}")

# --- looking DOWN the axis (project out z) recovers the 2D phasor sum -> the zero ---
w = sign * n ** (-0.5)
proj = abs(np.sum(w * np.exp(1j * theta)))
print(f"\n   project down the z-axis (drop height) -> |2D chi3 sum| = {proj:.5f}  (the cancellation / the zero)")
print(f"   so the zero lives in the xy-shadow; the z-axis (pitch {pitch:.3f}) is the dimension it cannot see.")
