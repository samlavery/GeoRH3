"""
helix3d_drag.py -- LINEAR-growth cone + phasor drag, diagnostic.

Two questions, separated:
  (A) PHASE: with the correct radial weight n^{-1/2}, which "spin relative to the curve" rho(n) makes
      the chi3 phasors cancel at the actual zeros?  defect(rho)=mean_g|sum chi3(n) n^{-1/2} e^{-i g rho}|.
  (B) WEIGHT: does the linear cone's own radius give that n^{-1/2}?  i.e. is R_n ~ c*sqrt(n)?

Geometry (user spec): radial growth e^6 per loop (LINEAR / Archimedean), arc spacing pi/3, pitch pi/3.
"""
import numpy as np

gammas = []
with open("lchi3_zeros_1000.txt") as f:
    for line in f:
        line = line.strip()
        if line and not line.startswith("#"):
            gammas.append(float(line.split()[1]))
gammas.sort()
Z = np.array(gammas[:15])
M = 60000
n = np.arange(1, M + 1)
sign = np.where(n % 3 == 1, 1.0, np.where(n % 3 == 2, -1.0, 0.0))

def defect(rho, w):
    rho = np.asarray(rho, float)
    return float(np.mean([abs(np.sum(w * np.exp(-1j * g * rho))) for g in Z]))

# ---- build the e^6 linear cone, place integers by arc length pi/3 ----
A = np.exp(6.0) / (2 * np.pi)
phi_grid = np.linspace(0.0, 4000.0, 4_000_00)
integrand = np.sqrt(A**2 * (1 + phi_grid**2) + (1/6)**2)
s_grid = np.concatenate([[0.0], np.cumsum(0.5*(integrand[1:]+integrand[:-1])*np.diff(phi_grid))])
s_n = n * (np.pi / 3)
phi_n = np.interp(s_n, s_grid, phi_grid)
R_n_e6 = A * phi_n

# ===== (A) PHASE: exact L-weight n^{-1/2}; which drog cancels? =====
w_exact = sign * n ** (-0.5)
print("(A) PHASE test  (weight fixed = n^{-1/2}; small defect = phasors cancel at the zeros):")
print("    spin relative to ...                                         defect")
print("    " + "-" * 70)
for name, rho in [
    ("log n         (scale / e-folds of progress  -- L-function)", np.log(n)),
    ("log(arc s_n)  (e-folds of ARC length        ~ log n)      ", np.log(s_n)),
    ("sqrt(n)       (geometric winding azimuth)                 ", np.sqrt(n)),
    ("n             (arc length, linear)                        ", n.astype(float)),
    ("n^0.25                                                    ", n ** 0.25),
]:
    print(f"    {name}   {defect(rho, w_exact):.5f}")
print("    => only the LOGARITHMIC (scale-invariant) spin cancels; geometric sqrt(n)/n do not.")

# ===== (B) WEIGHT: does a CLEAN sqrt(n) cone carry both weight and phase? =====
# clean area-law cone: R_n = c*sqrt(n).  Then 1/R = n^{-1/2}/c (the weight) AND 2 log R = log n + const.
c = 1.0
R_clean = c * np.sqrt(n)
w_cone = sign / R_clean                     # the cone's OWN radial weight
print("\n(B) WEIGHT test  (clean area-law cone R_n = sqrt(n) -- the cone supplies the weight 1/R):")
print(f"    radial drag 2*log R_n  with cone weight 1/R : defect = {defect(2*np.log(R_clean), w_cone):.5f}")
print(f"    winding drag (R_n itself ~ sqrt n)          : defect = {defect(R_clean, w_cone):.5f}")
print("    => clean cone: the RADIAL-SCALE drag (2 log R = log n) cancels; the winding (sqrt n) does not.")
print("       The same sqrt(n) radius gives BOTH the n^{-1/2} weight (1/R) and the log-n phase (2 log R).")

# ===== how 'clean' is the e^6 cone, and where does sqrt(n) kick in? =====
print("\n(C) the e^6 cone vs sqrt(n):  R_n/sqrt(n) by decade (flat tail => area law has kicked in):")
for lo, hi in [(1, 10), (100, 1000), (10000, 30000), (50000, 60000)]:
    seg = R_n_e6[lo-1:hi] / np.sqrt(n[lo-1:hi])
    print(f"    n in [{lo:6d},{hi:6d}]:  R/sqrt(n) ~ {seg.mean():.3f}  (spread {seg.std():.3f})")
print("    => with e^6 growth the area-law sqrt(n) is reached only at large n; small n is R~n (linear),")
print("       which is why the e^6 weight 1/R muddied the cancellation.  Smaller growth pulls it in.")
