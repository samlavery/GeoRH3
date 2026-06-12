"""
do_it_right.py -- the complete construction, everything earned from the radial growth R ~ n^a.

  radius:   R_n ~ n^a            (radial growth; a=1 is linear, e^6 per loop)
  AMPLITUDE: weight = 1/sqrt(R)  = n^{-a/2}   (the 2D wave amplitude on the cone -- EARNED)
  WINDING:   drag  = log R       = a*log n    (phasor spins by the fractional radius -- EARNED)
  phasor_n = chi3(n) * (1/sqrt R) * exp(-i gamma * log R)

The cancellation (3D dragged-phasor alignment) is sum = chi3 * n^{-a/2} * e^{-i gamma a log n}
                                                    = L( a/2 + i a gamma ).
Its zeros sit on Re = a/2.  The chi3 zeros are on Re = 1/2 -> so ONLY a=1 cancels.  That FORCES
linear radial growth, and a=1 makes weight = n^{-1/2}: the SAME 1/2 is the wave-amplitude exponent,
the radial rate, and sigma.  Everything else (radial scale e^6, pitch, spacing) is gauge.
"""
import numpy as np
gammas = []
with open("lchi3_zeros_1000.txt") as f:
    for line in f:
        line = line.strip()
        if line and not line.startswith("#"):
            gammas.append(float(line.split()[1]))
gammas.sort()
N = 8000; n = np.arange(1, N + 1); logn = np.log(n)
sign = np.where(n % 3 == 1, 1.0, np.where(n % 3 == 2, -1.0, 0.0))

def defect(a, g):                       # cancellation defect, weight & winding both from R~n^a
    return abs(np.sum(sign * n ** (-a / 2.0) * np.exp(-1j * g * a * logn)))

print("FORCING: radial-growth exponent a  (R ~ n^a)  ->  cancellation at the chi3 zeros")
print("  weight = 1/sqrt(R) = n^{-a/2}  (sigma = a/2);  drag winding = log R = a*log n")
print("  " + "-" * 62)
for a in (0.5, 0.8, 0.9, 1.0, 1.1, 1.5, 2.0):
    d = np.mean([defect(a, g) for g in gammas[:6]])
    flag = "  <== cancels (zeros are on sigma=1/2)" if d < 0.05 else ""
    print(f"   a={a:.1f}  (weight n^-{a/2:.2f}, sigma={a/2:.2f}) : mean defect = {d:.5f}{flag}")
print("\n  => a=1 forced: LINEAR radial growth  <=>  weight n^{-1/2}  <=>  sigma=1/2.")
print("     one 1/2, three roles: wave-amplitude exponent, radial rate, critical line.\n")

print("GAUGE: radial scale (e^6 vs e^2 vs 1) only rescales amplitude; the zero does not move:")
g = gammas[0]
for scale, lbl in [(np.exp(6), 'e^6'), (np.exp(2), 'e^2'), (1.0, '1')]:
    R = scale * n
    d = abs(np.sum(sign * (1 / np.sqrt(R)) * np.exp(-1j * g * np.log(R))))
    print(f"   radial scale {lbl:4s}: defect at gamma_1 = {d:.6f}  (= floor/sqrt(scale); zero fixed)")

print("\nFULL CONSTRUCTION at Sam's e^6 cone (a=1), cancellation at the first zeros:")
R = np.exp(6) * (n / 6.0)               # e^6 per loop, 6 integers/loop
w = 1 / np.sqrt(R); Phi = np.log(R)
for g in gammas[:6]:
    print(f"   gamma={g:8.4f}: |sum chi3 * (1/sqrt R) * e^(-i gamma log R)| = {abs(np.sum(sign*w*np.exp(-1j*g*Phi))):.7f}")
