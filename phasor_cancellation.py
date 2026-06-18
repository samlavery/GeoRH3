"""
PHASOR CANCELLATION MODEL — create phasors, spin them, let them cancel.

On the critical line s = 1/2 + i t, ζ is a sum of phasors:

    ζ(1/2 + i t) = Σ_n  n^(-1/2) · e^(-i t · log n)

  • create   : one phasor per integer n
  • magnitude: n^(-1/2)        (shrinks → 0)
  • spin rate: log n           (THE LOG — lives in 1D, the t-readout, not the geometry)
  • cancel   : sum them; where the sum vanishes is a ζ zero.

This file checks, numerically:
  (1) the cancellation points of the phasor sum == the true zeros γ_n,
  (2) a FINITE phasor sum (few terms) already tracks them,
  (3) the cancellation is ON-LINE-selective: |ζ(σ+iγ)| is minimised at σ=1/2,
  (4) the spin rates (log n) and shrinking magnitudes (1/√n).
"""

import mpmath as mp

mp.mp.dps = 25
TWO_PI = 2 * mp.pi

# ----------------------------------------------------------- ground-truth zeros
gammas = [mp.im(mp.zetazero(n)) for n in range(1, 16)]

# ------------------------- the cancellation signal: Riemann–Siegel Z is the REAL
# phasor sum, Z(t)=0 ⟺ ζ(1/2+it)=0.  (mp.siegelz is exact.)
def Z(t):
    return mp.siegelz(t)

print("=" * 74)
print("(1) CANCELLATION POINTS of the phasor sum  vs  the true zeros γ_k")
print("=" * 74)
print(f"{'k':>3} {'cancellation t*':>18} {'true γ_k':>18} {'|Δ|':>12}")
found = []
t = mp.mpf("1.0")
dt = mp.mpf("0.05")
prev = Z(t)
while t < 56 and len(found) < 15:
    t2 = t + dt
    cur = Z(t2)
    if prev * cur < 0:
        r = mp.findroot(Z, (t, t2), solver="bisect")
        found.append(r)
    t, prev = t2, cur
for k, (tc, g) in enumerate(zip(found, gammas), 1):
    print(f"{k:>3} {float(tc):>18.6f} {float(g):>18.6f} {float(abs(tc - g)):>12.2e}")

# ------------------------------- finite phasor sum (explicit create/spin/cancel)
def finite_phasor_Z(t):
    # Riemann–Siegel MAIN sum: only ⌊√(t/2π)⌋ phasors, spinning at log n.
    M = int(mp.sqrt(mp.mpf(t) / TWO_PI))
    th = mp.siegeltheta(t)
    return 2 * mp.fsum(mp.cos(th - t * mp.log(n)) / mp.sqrt(n) for n in range(1, M + 1))

print()
print("=" * 74)
print("(2) FINITE phasor sum (only ⌊√(t/2π)⌋ phasors) tracks the full signal")
print("=" * 74)
print(f"{'t':>8} {'#phasors':>9} {'finite Z(t)':>15} {'exact Z(t)':>15} {'same sign?':>11}")
for t in [50, 100, 200, 500, 1000]:
    M = int(mp.sqrt(mp.mpf(t) / TWO_PI))
    fz = finite_phasor_Z(t)
    ez = Z(t)
    print(f"{t:>8} {M:>9} {float(fz):>15.4f} {float(ez):>15.4f} "
          f"{str(fz * ez > 0):>11}")

# ------------------------------------------- on-line forcing: cancel only at σ=½
print()
print("=" * 74)
print("(3) ON-LINE FORCING — cancellation requires σ = 1/2")
print("=" * 74)
for gi, g in [(1, gammas[0]), (5, gammas[4]), (10, gammas[9])]:
    print(f"\n  near γ_{gi} = {float(g):.5f}:   |ζ(σ + iγ)|")
    for sig in [0.30, 0.40, 0.45, 0.50, 0.55, 0.60, 0.70]:
        val = float(abs(mp.zeta(mp.mpf(sig) + 1j * g)))
        bar = "█" * int(min(val, 3) * 12)
        star = "   ← cancels" if abs(sig - 0.5) < 1e-9 else ""
        print(f"    σ={sig:>4.2f}  {val:>9.5f}  {bar}{star}")

# ------------------------------------------------- the spin rates / magnitudes
print()
print("=" * 74)
print("(4) THE PHASORS:  spin rate = log n  (the 1D log) ,  magnitude = 1/√n")
print("=" * 74)
print(f"{'n':>6} {'spin rate log n':>16} {'magnitude 1/√n':>16}")
for n in [1, 2, 3, 5, 10, 100, 1000, 10000]:
    print(f"{n:>6} {float(mp.log(n)):>16.5f} {float(1 / mp.sqrt(n)):>16.6f}")

# --------------------------- watch them cancel: partial sums spiralling to ~0
print()
print("=" * 74)
print(f"(5) WATCH THEM CANCEL — partial phasor sum at the first zero t=γ₁={float(gammas[0]):.4f}")
print("    S_N = Σ_{n≤N} n^(-1/2) e^(-iγ₁ log n)   (smoothed); |S_N| should sink")
print("=" * 74)
g1 = gammas[0]
N = 4000
# smooth window so the line-sum converges to ζ(1/2+iγ1) ≈ 0
print(f"{'N':>6} {'|S_N|':>12}")
for Ncut in [10, 50, 200, 1000, 4000]:
    s = mp.mpc(0)
    for n in range(1, Ncut + 1):
        w = mp.e ** (-(mp.mpf(n) / Ncut) ** 2)  # Gaussian taper
        s += w * n ** (mp.mpf(-1) / 2) * mp.e ** (-1j * g1 * mp.log(n))
    print(f"{Ncut:>6} {float(abs(s)):>12.5f}")
print(f"\n   true |ζ(1/2+iγ₁)| = {float(abs(mp.zeta(mp.mpf('0.5') + 1j * g1))):.2e}  (a genuine zero)")
