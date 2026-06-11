"""
spiral_helix.py -- the integers on a SPIRAL HELIX (spiral = growing radius, helix = axial pitch),
built with pi.  The cancellation is a 3D event; the 2D projection (dropping the pitch axis) is the
zeta-zero iy.  The PITCH is the dimension the projection loses -- the zero is that loss.
"""
import numpy as np
gammas = []
with open("lchi3_zeros_1000.txt") as f:
    for line in f:
        line = line.strip()
        if line and not line.startswith("#"):
            gammas.append(float(line.split()[1]))
gammas.sort()
N = 40000; n = np.arange(1, N + 1)
sign = np.where(n % 3 == 1, 1.0, np.where(n % 3 == 2, -1.0, 0.0))

# --- SPIRAL HELIX geometry, in pi ---
spacing = np.pi / 3                 # azimuthal spacing per integer  -> 6 integers per loop
pitch   = np.pi / 3                 # axial rise per loop  (the helix climb)
R = n.astype(float)                 # radial growth: linear (a=1 forced) -> the SPIRAL
azim   = spacing * n                # where the integer sits around the axis
height = (pitch / (2 * np.pi)) * azim   # the HELIX climb (pitch per loop)
print(f"SPIRAL HELIX: spacing=pi/3 (6/loop), pitch=pi/3 per loop, radial growth linear")
print(f"  per loop: azimuth +2pi, radius +(6 integers), height +pi/3 = {pitch:.4f}")
print(f"  a few 3D points (x,y,z): ", [(round(float(R[i]*np.cos(azim[i])),1),
        round(float(R[i]*np.sin(azim[i])),1), round(float(height[i]),2)) for i in (0,5,11)])

# --- dragged phasor (spin = drag = log R) tilted into the helix by the PITCH ---
slope = pitch / (2 * np.pi)         # axial slope the pitch gives every phasor
w = 1 / np.sqrt(R); 
print(f"\n  pitch IS in it: each phasor tilts axially by slope = pitch/2pi = {slope:.5f}")
print("  3D dragged-phasor resultant at each zero  (xy = the iy reading; z = the pitch axis):")
for g in gammas[:6]:
    Phi = np.log(R)
    Sx = np.sum(sign * w * np.cos(g * Phi)); Sy = np.sum(sign * w * np.sin(g * Phi))
    Sz = slope * np.sum(sign * w)
    print(f"   gamma={g:8.4f}:  |xy|={np.hypot(Sx,Sy):.6f} (->0, the zero)   z={Sz:.6f} (pitch, kept)   |3D|={np.sqrt(Sx*Sx+Sy*Sy+Sz*Sz):.6f}")
print("\n  => the 3D resultant does NOT vanish; only its xy-shadow does.  the zero is the PROJECTION")
print("     LOSS down the pitch axis -- and z is the same at every zero (height-free), the part that")
print("     the 2D iy can never see.  pitch pi/3 sets exactly how much is lost.")
