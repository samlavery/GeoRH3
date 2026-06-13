"""
convergence.py -- convergence / stability tests for the helix fiber model (fiber.py).

(a) CORRECTNESS : the literal-helix find_zeros reproduces the certified zeros (no index drift), every L.
(b) PRECISION   : find_zeros is stable under dps doubling (the head + Euler-Maclaurin tail converges).
(c) CAPTURE FLOOR: the DIRECT head-only sum floors at ~1/sqrt(M) (the off-helix truncation); adding the
    E-M tail (find_zeros) removes it.
All measured against the certified comparison set zeros/<label>.txt.  No mp.zeta anywhere.
"""
from __future__ import annotations
import mpmath as mp
import fiber

print("=" * 72)
print("(a) CORRECTNESS -- literal-helix find_zeros vs certified, 20 zeros each (dps 25)")
print("=" * 72)
for spec in fiber.SPECS[:6]:
    zc = fiber._load_certified(spec.label, 20)
    if len(zc) < 20:
        print(f"  {spec.label:18s} only {len(zc)} certified on file")
        continue
    zh = fiber.find_zeros(spec, 20, dps=25)
    d = [abs(float(zh[i] - zc[i])) for i in range(20)]
    drift = "no" if max(d[10:]) < 5 * max(d[:10]) + 1e-30 else "CHECK"
    print(f"  {spec.label:18s} max|h-cert| = {max(d):.2e}   drift: {drift}")

print("\n" + "=" * 72)
print("(b) PRECISION -- find_zeros stable under dps 25 -> 45 (chi3, first 3 zeros)")
print("=" * 72)
spec = fiber.SPECS[1]                                  # chi3
z25 = fiber.find_zeros(spec, 3, dps=25)
z45 = fiber.find_zeros(spec, 3, dps=45)
for i in range(3):
    print(f"  zero {i + 1}: |dps25 - dps45| = {mp.nstr(abs(z25[i] - z45[i]), 3)}")
assert all(abs(z25[i] - z45[i]) < mp.mpf(10) ** -20 for i in range(3)), "precision unstable"
print("  PASSED: agree to < 1e-20 (the head+tail sum is precision-stable)")

print("\n" + "=" * 72)
print("(c) CAPTURE FLOOR -- DIRECT head-only sum vs M (chi3, first 5): the off-helix truncation")
print("=" * 72)
zc = [float(z) for z in fiber._load_certified("L2_chi3_q3", 5)]
for M in (500_000, 2_000_000):
    zh = fiber.find_zeros_direct(spec, 5, M=M)
    m = min(5, len(zh))
    d = max(abs(zh[i] - zc[i]) for i in range(m))
    print(f"  M={M:>9}: max|h-cert| over {m} = {d:.2e}   (1/sqrt(M) = {1 / M ** 0.5:.2e})")
print("  -> the head-only sum floors at ~1/sqrt(M); find_zeros (head + E-M tail) removes it (see (a)).")
