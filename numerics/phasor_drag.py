"""
phasor_drag.py -- the cancellation as a 3D alignment of DRAGGED phasors (2D shadow = iy = gamma).

Sam's curve:  radial growth e^6 per loop, integer spacing pi/3 (=> 6 integers/loop), pitch pi/3 per loop.
Sam's idea:   the phasors SPIN relative to the curve.  Test the drag = fractional radial growth d(log R):
              the cumulative spin Phi_n = log R_n.  On a cone R = (e^6)*k, log R = log n + const -> the
              log-winding the zeros need, EARNED from the radial growth (not placed at log positions).
Then the dragged phasors should CANCEL exactly at the chi3 zeros.  Control: drag relative to ANGLE
(linear) should NOT cancel.
"""
import numpy as np
spacing = np.pi/3; pitch = np.pi/3; rad_per_loop = np.exp(6)
N = 8000; n = np.arange(1, N+1); k = n/6.0
R = rad_per_loop * k                 # radius: linear, e^6 per loop (the cone)
theta = spacing * n                  # geometric winding angle
z = pitch * k                        # axial height: pitch per loop

# --- PHASOR DRAG = cumulative fractional radial growth ---
Phi = np.log(R)                      # spin dragged by the radius
off = Phi - np.log(n)                # should be constant = 6 - log 6
print(f"drag Phi_n = log R_n;   Phi_n - log n at n=10,100,1000,8000 = "
      f"{off[9]:.4f}, {off[99]:.4f}, {off[999]:.4f}, {off[7999]:.4f}   (const = 6 - log6 = {6-np.log(6):.4f})")
print("  -> the drag gives EXACTLY log n + offset; the offset 6 - log6 comes from the e^6 radial growth.\n")

gammas = []
with open("lchi3_zeros_1000.txt") as f:
    for line in f:
        line = line.strip()
        if line and not line.startswith("#"):
            gammas.append(float(line.split()[1]))
gammas.sort()
sign = np.where(n % 3 == 1, 1.0, np.where(n % 3 == 2, -1.0, 0.0))
w = sign * n ** (-0.5)

print("3D cancellation: |sum chi3 * w * e^{-i gamma * Phi}|  at the zeros (drag = log R):")
for g in gammas[:8]:
    d = abs(np.sum(w * np.exp(-1j * g * Phi)))
    print(f"   gamma={g:8.4f}:  defect = {d:.5f}")

print("\nCONTROL: drag relative to ANGLE (Phi=theta, linear winding), rescaled to same mean rate:")
Phi_lin = theta * (np.log(1000) / theta[999])    # rescale so slope ~ matches
for g in gammas[:4]:
    d = abs(np.sum(w * np.exp(-1j * g * Phi_lin)))
    print(f"   gamma={g:8.4f}:  defect = {d:.5f}")
