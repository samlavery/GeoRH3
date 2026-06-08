import mpmath, json, sys
mpmath.mp.dps = 15
# canonical gamma_n, first 30 (used ONLY for final comparison)
gamma_ref = [float(mpmath.zetazero(n).imag) for n in range(1, 31)]
# zero-counting function N(T) at several T (the TRUE density to compare crossing-count against)
Ts = [20, 30, 40, 50, 60, 70, 80, 90, 100, 110, 119]
nz = {T: int(mpmath.nzeros(T)) for T in Ts}
out = {"gamma_ref": gamma_ref, "nzeros": nz}
with open("/Users/samuellavery/proof/three/tmp/fwd2/ref.json", "w") as f:
    json.dump(out, f)
print("gamma_ref[:10] =", [round(g,4) for g in gamma_ref[:10]])
print("nzeros:", nz)
sys.stdout.flush()
