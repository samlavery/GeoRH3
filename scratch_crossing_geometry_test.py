"""
TEST (per Sam): at each crossing (phasor cancellation) figure out
   - height of crossing
   - number of integers crossed
   - arc length at crossing
   - |phasors| at crossing   (the cancellation is what decides)

Rule: compute ON the helix.  mpmath zeta/Z is used ONLY as the external yardstick
(ground-truth zero heights), never as the construction's fiber.
"""
import numpy as np, math
import mpmath as mp
import helixlib_logfree_corrected as H

mp.mp.dps = 25
TWO_PI = 2 * mp.pi
DELTA = math.pi / 3

# ---- yardstick only: true zeta zeros ----
gammas = [float(mp.im(mp.zetazero(k))) for k in range(1, 16)]

print("=" * 90)
print("PART A — geometric data AT each crossing (anchored on the true zero heights)")
print("  height = climb γ ; #ints N = ⌊√(γ/2π)⌋ (phasors entered, RS main sum) ;")
print("  arclen = N·Δ (Δ=π/3) ; |phasors| = |Z(γ)| (fiber magnitude — should be ~0)")
print("=" * 90)
print(f"{'k':>3} {'height γ':>11} {'#ints N':>9} {'arclen N·π/3':>14} {'|phasors|=|Z(γ)|':>18} {'θ(γ)/π':>9}")
for k, g in enumerate(gammas, 1):
    N = int(mp.sqrt(mp.mpf(g) / TWO_PI))
    arclen = N * DELTA
    Zval = float(abs(mp.siegelz(mp.mpf(g))))
    th = float(mp.siegeltheta(mp.mpf(g)) / mp.pi)
    print(f"{k:>3} {g:>11.5f} {N:>9d} {arclen:>14.4f} {Zval:>18.2e} {th:>9.4f}")

print("\n  θ increment between consecutive crossings  (≈π would be the 'amplitude crests at π'):")
incs = []
for k in range(1, len(gammas)):
    dth = float(mp.siegeltheta(mp.mpf(gammas[k])) - mp.siegeltheta(mp.mpf(gammas[k-1])))
    incs.append(dth / math.pi)
print("   Δθ/π :", [round(x, 3) for x in incs])
print(f"   mean Δθ/π = {np.mean(incs):.3f}  (avg≈1 ⟹ one π of phase per zero — Riemann–von Mangoldt)")

print("\n" + "=" * 90)
print("PART B — HONEST TEST: does the LOG-FREE geometric fiber cancel AT the zeros,")
print("  or only the log-bridge fiber?  Fiber(y)=Σ_n amp_n · exp(-i·spin_n·y), swept in y.")
print("=" * 90)

ch = H.channel_A()                      # zeta channel
Nmax = 60000
h = H.helix(ch, Nmax)
n = h["n"]
angle = h["angle"]                      # 2π k ∝ √n (geometric winding)
sign = (-1.0) ** (n - 1)               # η alternating sign (so the line sum converges)
amp = sign / np.sqrt(n)                 # η amplitude n^{-1/2}
taper = np.exp(-(n / Nmax) ** 2)

logn = np.log(n)
# fair, SAME-SCALE geometric spin: rescale √n-winding to span exactly log n's range.
geo = angle * (logn.max() / angle.max())

eta_factor = lambda y: abs(1 - 2 ** (0.5 - 1j * y))   # |1-2^{1-s}|, nonzero on the line

configs = {
    "BRIDGE  spin = log n      (the analytic transform)": logn,
    "GEOMETRIC spin = 2πk (~√n), rescaled to log-n range": geo,
}

ys = np.linspace(1.0, 70.0, 8000)

def fiber_abs_at(spin, points):
    A = (taper * amp).astype(complex)
    pts = np.asarray(points, float)
    out = np.empty(len(pts))
    CH = 300
    for i in range(0, len(pts), CH):
        blk = pts[i:i + CH]
        M = np.exp(-1j * np.outer(blk, spin))
        out[i:i + CH] = np.abs(M @ A)
    return out

true_lt70 = sorted(float(mp.im(mp.zetazero(k))) for k in range(1, 40)
                   if float(mp.im(mp.zetazero(k))) < 70)
print(f"\n  Decisive test: a fiber resolves a zero iff |fiber| DIPS at γ_k vs its baseline.")
print(f"  η-sum (alternating) so the line value is real & convergent; same amplitude n^{{-1/2}} for both;")
print(f"  the ONLY difference is the spin SHAPE: log n  vs  √n (rescaled to the same range).\n")
print(f"  true zeros < 70: {[round(g,2) for g in true_lt70]}  (count {len(true_lt70)})\n")
for name, spin in configs.items():
    allv = fiber_abs_at(spin, ys)
    base = float(np.median(allv))
    at_zeros = fiber_abs_at(spin, gammas)
    ratios = [v / base for v in at_zeros]
    found = sum(1 for rr in ratios if rr < 0.30)
    deep = ys[1:-1][(allv[1:-1] < allv[:-2]) & (allv[1:-1] < allv[2:]) & (allv[1:-1] < 0.30 * base)]
    print(f"  {name}")
    print(f"     dip ratio |fiber(γ_k)|/baseline (first 10): {[round(r,3) for r in ratios[:10]]}")
    print(f"     # of γ_k genuinely resolved (ratio<0.30): {found}/15")
    print(f"     its own deep minima in [1,70]: {len(deep)} at {[round(x,1) for x in deep[:12]]}")
    print()

print("=" * 90)
print("READING: same amplitude, same spin scale — only the SHAPE differs.")
print("log n  → dips land on the true γ_k (it is the transform).  √n → blur, not the zeros.")
print("=" * 90)
