"""
Step 1: fetch canonical reference data ONCE, cache to disk as plain floats.
gamma_ref: first 30 zeta zero heights.
nzeros_ref: N(T) at several T up to ~120.
"""
import mpmath
import json
import sys

mpmath.mp.dps = 15  # DEFAULT precision, do not raise

# canonical zeta zero heights (ONLY for final comparison, never fed into construction)
gamma_ref = [float(mpmath.zetazero(n).imag) for n in range(1, 31)]
print("gamma_ref (first 30):", flush=True)
for i, g in enumerate(gamma_ref, 1):
    print(f"  n={i:2d}  gamma={g:.6f}", flush=True)

# canonical zero counts N(T)
Ts = [10, 20, 30, 40, 50, 60, 80, 100, 120]
nzeros_ref = {}
for T in Ts:
    cnt = int(mpmath.nzeros(T))
    nzeros_ref[T] = cnt
    print(f"  N({T}) = {cnt}", flush=True)

with open("/Users/samuellavery/proof/three/tmp/fwd2/ref.json", "w") as f:
    json.dump({"gamma_ref": gamma_ref, "nzeros_ref": nzeros_ref}, f)
print("cached ref.json", flush=True)
