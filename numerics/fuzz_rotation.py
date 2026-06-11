"""
fuzz_rotation.py -- fuzz the phasor ROTATION profile rho(n); measure the cancellation defect at the
actual chi3 zeros.  phasor_n = chi3(n) * n^{-1/2} * exp(-i gamma rho(n)).  defect = |sum| at gamma_n
(small => the phasors genuinely cancel there).  No conclusions -- just which rho cancels.
"""
import numpy as np
gammas = []
with open("lchi3_zeros_1000.txt") as f:
    for line in f:
        line = line.strip()
        if line and not line.startswith("#"):
            gammas.append(float(line.split()[1]))
gammas.sort()
Z = gammas[:12]
M = 20000
n = np.arange(1, M + 1)
sign = np.where(n % 3 == 1, 1.0, np.where(n % 3 == 2, -1.0, 0.0))
w = sign * n ** (-0.5)

def defect(rho):
    return float(np.mean([abs(np.sum(w * np.exp(-1j * g * rho))) for g in Z]))

print("  rotation profile rho(n)          mean defect at the 12 zeros (small = cancels)")
print("  " + "-" * 64)
for name, rho in [("n        (linear / Archimedean)", n.astype(float)),
                  ("sqrt(n)  (Archimedean angle)  ", np.sqrt(n)),
                  ("n^0.25                        ", n ** 0.25),
                  ("log n    (L-function)         ", np.log(n))]:
    print(f"  {name}   {defect(rho):.5f}")

print("\n  interpolate linear -> log via rho_alpha = (n^alpha - 1)/alpha  (alpha->0 is log):")
for a in (1.0, 0.5, 0.25, 0.1, 0.05, 0.02):
    print(f"     alpha={a:4.2f} : defect = {defect((n ** a - 1) / a):.5f}")
print(f"     alpha=0.00 (log) : defect = {defect(np.log(n)):.5f}")
