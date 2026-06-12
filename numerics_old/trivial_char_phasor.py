#!/usr/bin/env python3
"""
trivial_char_phasor.py
======================

The phasor-drag construction (do_it_right.py / phasor_drag.py / helix_fibre_*.py) applied
to the TRIVIAL character chi(n)=1  ->  the Riemann zeta function zeta(s).  Goes beyond the
existing helix_fibre_trivial.py by adding: the on-zero vs off-zero contrast, the AFE main
sum of length sqrt(gamma/2pi), Cesaro/Abel smoothing, and a structured-pattern hunt.

chi3 (mean-zero) cancels RAW:   sum_{n<=M} chi3(n) n^{-1/2} e^{-i g log n}  -> 0  at the chi3 zeros.
trivial (NOT mean-zero, pole at s=1):  sum_{n<=M} n^{-1/2} e^{-i g log n}  does NOT -> 0 raw.

We test, honestly, four routes to (try to) recover the zeta zeros, and quantify the contrast.
"""

import numpy as np
import mpmath as mp

mp.mp.dps = 30

# ---- zeta nontrivial zeros (imag parts) + off-zero control midpoints --------
NZ = 12
zg = [float(mp.im(mp.zetazero(k))) for k in range(1, NZ + 1)]
off = [(zg[i] + zg[i + 1]) / 2 for i in range(NZ - 1)]
print("zeta zeros (imag):", ", ".join(f"{g:.4f}" for g in zg[:8]))
print()


def raw(gamma, M):
    """sum_{n<=M} n^{-1/2} e^{-i gamma log n}  = sum n^{-(1/2+i gamma)} (truncated zeta)."""
    n = np.arange(1, M + 1)
    return np.sum(n ** (-0.5 - 1j * gamma))


# ============================================================================
# (A) RAW partial sum -- expected to DIVERGE ~ M^{1/2} (the s=1 pole), no cancellation
# ============================================================================
print("=" * 78)
print("(A) RAW  S(g,M) = sum_{n<=M} n^{-1/2} e^{-i g log n}.  chi3 -> 0; trivial -> ?")
print("=" * 78)
Ms = (1000, 10000, 100000, 1000000)
print(f"{'gamma':>10} |" + "".join(f" |S|@M={M:<8}" for M in Ms))
for g in zg[:6]:
    print(f"{g:10.4f} |" + "".join(f" {abs(raw(g, M)):11.3f}" for M in Ms))
print("  -- off-zero controls --")
for g in off[:6]:
    print(f"{g:10.4f} |" + "".join(f" {abs(raw(g, M)):11.3f}" for M in Ms))
print()
M0 = 1000000
on_m = np.mean([abs(raw(g, M0)) for g in zg[:8]])
off_m = np.mean([abs(raw(g, M0)) for g in off[:8]])
print(f"  M={M0}: mean|S| on-zero={on_m:.3f}  off-zero={off_m:.3f}  ratio={on_m/off_m:.3f}")
print(f"  (if raw worked, on/off << 1; expect ~1 -> raw does NOT see the zeros)")
print(f"  |S|/sqrt(M) on-zero = {on_m/np.sqrt(M0):.4f}  (the ~M^1/2 pole-driven growth)")
print()


# ============================================================================
# (B) SMOOTH SUBTRACTION  R = S - M^{1-s}/(1-s)   (remove the s=1 pole / DC term)
#     This is the existing helix_fibre_trivial.py route -- it recovers the zeros.
# ============================================================================
print("=" * 78)
print("(B) R = S - M^{1-s}/(1-s)  (subtract the smooth/pole part).  -> 0 at zeta zeros?")
print("=" * 78)


def reg(gamma, M):
    s = mp.mpc(0.5, gamma)
    S = mp.fsum(mp.power(n, -s) for n in range(1, M + 1))
    return complex(S - mp.power(M, 1 - s) / (1 - s))


Msb = (1000, 10000, 100000, 1000000)
print(f"{'gamma':>10} |" + "".join(f" |R|@M={M:<8}" for M in Msb))
for g in zg[:6]:
    print(f"{g:10.4f} |" + "".join(f" {abs(reg(g, M)):11.5f}" for M in Msb))
print("  -- off-zero controls (should converge to |zeta(1/2+it)| != 0) --")
for g in off[:6]:
    zt = abs(complex(mp.zeta(mp.mpc(0.5, g))))
    print(f"{g:10.4f} |" + "".join(f" {abs(reg(g, M)):11.5f}" for M in Msb) + f"  [|zeta|={zt:.3f}]")
print()


# ============================================================================
# (C) APPROXIMATE FUNCTIONAL EQUATION main sum, length N* = floor(sqrt(g/2pi))
#     zeta(1/2+it) ~ sum_{n<=N*} n^{-s} + chi(s) sum_{n<=N*} n^{-(1-s)} + ...
#     Test (C1) the short main sum alone, (C2) the symmetrized AFE.
# ============================================================================
print("=" * 78)
print("(C) APPROX FUNCTIONAL EQ, main-sum length N* = floor(sqrt(gamma/2pi))")
print("=" * 78)


def chi_factor(s):
    """zeta(s) = chi(s) zeta(1-s);  chi(s) = 2^s pi^{s-1} sin(pi s/2) Gamma(1-s)."""
    return (mp.power(2, s) * mp.power(mp.pi, s - 1)
            * mp.sin(mp.pi * s / 2) * mp.gamma(1 - s))


def afe(gamma):
    s = mp.mpc(0.5, gamma)
    Nstar = int(mp.floor(mp.sqrt(gamma / (2 * mp.pi))))
    Nstar = max(Nstar, 1)
    main = mp.fsum(mp.power(n, -s) for n in range(1, Nstar + 1))
    dual = mp.fsum(mp.power(n, -(1 - s)) for n in range(1, Nstar + 1))
    return Nstar, complex(main), complex(main + chi_factor(s) * dual)


print(f"{'gamma':>10} | N* | |main only| | |symmetrized AFE| | |true zeta|")
for g in zg[:8]:
    Nstar, m, a = afe(g)
    zt = abs(complex(mp.zeta(mp.mpc(0.5, g))))
    print(f"{g:10.4f} | {Nstar:2d} | {abs(m):11.5f} | {abs(a):16.6f} | {zt:.2e}")
print("  -- off-zero controls (symmetrized AFE should ~ |zeta| != 0) --")
for g in off[:6]:
    Nstar, m, a = afe(g)
    zt = abs(complex(mp.zeta(mp.mpc(0.5, g))))
    print(f"{g:10.4f} | {Nstar:2d} | {abs(m):11.5f} | {abs(a):16.6f} | {zt:.3f}")
print()


# ============================================================================
# (D) STRUCTURED-PATTERN HUNT: does |S(g,M)| - (pole growth) carry a signal?
#     The smooth subtraction says S(g,M) ~ M^{1-s}/(1-s) + zeta(s).  So
#         S(g,M) - M^{1-s}/(1-s)  ->  zeta(s),  which -> 0 at the zeros.
#     Equivalently the RAW sum, de-trended by the pole term, IS the zeta signal.
#     Quantify how cleanly the de-trended residual tracks zeta on and off zeros.
# ============================================================================
print("=" * 78)
print("(D) PATTERN: raw sum de-trended by the pole term -> recovers zeta(1/2+it)")
print("=" * 78)
M = 10**6
print(f"   at M={M}:  |[S - M^(1-s)/(1-s)] - zeta(1/2+it)|  (should be tiny, ~next E-M term)")
for g in list(zg[:4]) + list(off[:4]):
    s = mp.mpc(0.5, g)
    S = mp.fsum(mp.power(n, -s) for n in range(1, M + 1))
    resid = abs(complex(S - mp.power(M, 1 - s) / (1 - s) - mp.zeta(s)))
    print(f"   gamma={g:8.4f}:  residual = {resid:.3e}   (|zeta|={abs(complex(mp.zeta(s))):.4f})")
print()


# ============================================================================
# CONTRAST with chi3: mean-zero -> raw cancels, no subtraction needed
# ============================================================================
print("=" * 78)
print("CONTRAST: chi3 (mean-zero) RAW sum at its first zero -- cancels with NO subtraction")
print("=" * 78)


def chi3(n):
    r = n % 3
    return 1 if r == 1 else (-1 if r == 2 else 0)


def L3(s):
    return mp.power(3, -s) * (mp.zeta(s, mp.mpf(1) / 3) - mp.zeta(s, mp.mpf(2) / 3))


g3 = float(mp.im(mp.findroot(L3, mp.mpc(0.5, 8.0))))
print(f"  chi3 first zero gamma = {g3:.5f}")
for M in (1000, 10000, 100000, 1000000):
    s = mp.mpc(0.5, g3)
    S = mp.fsum(chi3(nn) * mp.power(nn, -s) for nn in range(1, M + 1))
    print(f"    M={M:>8}: |S_raw chi3| = {float(abs(S)):.4e}   (-> 0, no pole to remove)")
print()
print("  The single quantitative difference: mean over one period.")
print(f"    chi3:    sum_a chi3(a) = 1 + (-1) + 0 = 0   (mean-zero -> DC cancels for free)")
print(f"    trivial: sum_a 1       = 1                  (DC survives -> the s=1 pole)")
print("  That nonzero mean IS the pole that must be subtracted; everything else is identical.")
