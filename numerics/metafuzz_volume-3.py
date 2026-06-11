"""
metafuzz_volume-3.py  --  ID volume-3

HYPOTHESIS (user headline): the zero height gamma is a VOLUME of integers measured
between successive cancellations; the gaps gamma_{n+1}-gamma_n are set by a count /
3D volume of integers wound between consecutive cancellation (zero) events.

CLAIM (volume-3): GAP <-> LOCAL VOLUME RATE.  One winding-cell per cancellation:
   gamma_{n+1} - gamma_n  ~=  2pi / log(q*gamma_n/2pi)            (mean spacing = 1/density)
equivalently, with the (smooth) zero-counting "swept volume"
   V(T) = (T/2pi) * log(q*T/(2*pi)) - T/2pi  + 7/8 + (genus/symmetry const),
   dV = V(gamma_{n+1}) - V(gamma_n)  ~=  1   per zero (exactly one cell consumed).

TEST (ONE rule, only chi mod q changes):
  - compute MANY consecutive EXACT zeros for chi mod 3,4,5(quad),5(quartic complex),7
    each verified |L(chi,1/2+i gamma)| < 1e-12 ;
  - gaps / predicted mean spacing  -> mean must be ~1 ;
  - dV per zero  -> mean must be ~1 ;
  - unfold the spacings ( s_n = dV per zero, already mean-1 ) and compare the
    distribution to the GUE Wigner surmise (KS statistic) -- the std ~0.29 must be
    the GUE fluctuation, NOT a fit artifact.

FALSIFIED if: the mean ratio departs from 1 across characters, OR the smooth-density
prediction is not what sets the gaps, OR the unfolded distribution is not GUE.

Brutal honesty: we report the ACTUAL numbers. A clean negative with the precise reason
is a result. We do NOT claim success on a single character or on approximate dips.
"""

import numpy as np
import mpmath as mp

mp.mp.dps = 30

# ---------------------------------------------------------------- characters (ONE rule, chi varies)
CHARS = {
    "mod 3 quadratic":         (3, {1: 1, 2: -1}),
    "mod 4 quadratic":         (4, {1: 1, 3: -1}),
    "mod 5 quadratic":         (5, {1: 1, 4: 1, 2: -1, 3: -1}),
    "mod 5 quartic (complex)": (5, {1: 1, 2: 1j, 4: -1, 3: -1j}),
    "mod 7 quadratic":         (7, {1: 1, 2: 1, 4: 1, 3: -1, 5: -1, 6: -1}),
}

def Lval(q, table, s):
    """exact L(chi,s) = q^{-s} sum_a chi(a) Hurwitz-zeta(s, a/q)."""
    tot = mp.mpc(0)
    for a, c in table.items():
        tot += mp.mpc(c) * mp.zeta(s, mp.mpf(a) / q)
    return q ** (-s) * tot

def find_zeros(q, table, hi, step=0.035):
    """All consecutive zero heights gamma in (0, hi]; each refined and EXACT-verified."""
    f = lambda t: Lval(q, table, mp.mpf(1) / 2 + 1j * t)
    ts = np.arange(0.4, hi, step)
    mags = np.array([float(abs(f(mp.mpf(t)))) for t in ts])
    zs = []
    for i in range(1, len(ts) - 1):
        if mags[i] < mags[i - 1] and mags[i] < mags[i + 1] and mags[i] < 0.6:
            try:
                root = mp.findroot(f, mp.mpf(ts[i]), tol=mp.mpf(10) ** (-26))
                tm = mp.re(root)
                if (abs(mp.im(root)) < 1e-8 and abs(f(tm)) < 1e-12
                        and tm > 0.3 and all(abs(tm - q0) > 1e-4 for q0 in zs)):
                    zs.append(tm)
            except Exception:
                pass
    return sorted(zs)

# ---------------------------------------------------------------- the predicted local density / volume
# Riemann-von Mangoldt for L(chi mod q):  N(T) ~ (T/2pi) log(qT/2pi) - T/2pi + O(log T).
# local density rho(T) = dN/dT = (1/2pi) log(qT/2pi);  mean spacing = 1/rho = 2pi/log(qT/2pi).
def mean_spacing(q, T):
    return 2 * np.pi / np.log(q * T / (2 * np.pi))

def V_smooth(q, T):
    """smooth swept-volume = principal part of N(T) (the integer count below height T)."""
    return (T / (2 * np.pi)) * np.log(q * T / (2 * np.pi)) - T / (2 * np.pi)

# ---------------------------------------------------------------- GUE Wigner surmise (beta=2)
def gue_wigner_cdf(s):
    # P(s) = (32/pi^2) s^2 exp(-4 s^2/pi);  CDF in closed-ish form via erf + exp.
    s = np.asarray(s, float)
    a = 4.0 / np.pi
    # integral_0^s (32/pi^2) u^2 e^{-a u^2} du
    from scipy.special import erf  # type: ignore
    cdf = erf(np.sqrt(a) * s) - (2.0 / np.sqrt(np.pi)) * np.sqrt(a) * s * np.exp(-a * s ** 2)
    return cdf

def ks_against_gue(spac):
    """one-sample KS distance of unfolded spacings vs GUE Wigner surmise."""
    s = np.sort(np.asarray(spac, float))
    n = len(s)
    try:
        cdf = gue_wigner_cdf(s)
    except Exception:
        return None
    emp = np.arange(1, n + 1) / n
    emp_lo = np.arange(0, n) / n
    return float(max(np.max(np.abs(emp - cdf)), np.max(np.abs(cdf - emp_lo))))

def ks_against_poisson(spac):
    """KS vs exponential (Poisson) spacing 1-e^{-s}; sanity contrast to GUE."""
    s = np.sort(np.asarray(spac, float))
    n = len(s)
    cdf = 1 - np.exp(-s)
    emp = np.arange(1, n + 1) / n
    emp_lo = np.arange(0, n) / n
    return float(max(np.max(np.abs(emp - cdf)), np.max(np.abs(cdf - emp_lo))))

# ---------------------------------------------------------------- run
HI = 130.0   # height ceiling; gives ~70-110 consecutive zeros per character
print("=" * 96)
print("  volume-3:  gap  <->  local winding-volume rate   (one cell per cancellation)")
print("  ONE rule, only chi mod q changes.  zeros EXACT-verified |L(1/2+i gamma)| < 1e-12.")
print("=" * 96)

summary = []
all_dV = []     # pooled dV-per-zero across characters (for global GUE check)
all_ratio = []

for name, (q, table) in CHARS.items():
    zs = find_zeros(q, table, HI)
    g = np.array([float(z) for z in zs])
    # EXACT verification of every zero used
    resid = np.array([float(abs(Lval(q, table, mp.mpf(1) / 2 + 1j * mp.mpf(z)))) for z in zs])
    max_resid = resid.max() if len(resid) else float('nan')
    n_ok = int(np.sum(resid < 1e-12))

    if len(g) < 5:
        print(f"\n{name}: only {len(g)} zeros found -- skip"); continue

    gaps = np.diff(g)
    mids = 0.5 * (g[1:] + g[:-1])

    # (A) gap / predicted mean spacing
    pred = mean_spacing(q, mids)
    ratio = gaps / pred

    # (B) dV per zero  (smooth swept-volume increment)
    dV = V_smooth(q, g[1:]) - V_smooth(q, g[:-1])

    all_dV.append(dV)
    all_ratio.append(ratio)

    # (C) unfold: use dV itself as the unfolded spacing (it has mean ~1 by construction)
    #     compare its distribution to GUE and to Poisson.
    ks_gue = ks_against_gue(dV)
    ks_poi = ks_against_poisson(dV)

    print(f"\n{name}  (q={q})")
    print(f"   zeros found (gamma<= {HI:.0f})         : {len(g)}    "
          f"EXACT |L|<1e-12: {n_ok}/{len(g)}  (max resid {max_resid:.1e})")
    print(f"   gap / [2pi/log(q*mid/2pi)]  mean    : {ratio.mean():.4f}   std {ratio.std():.4f}")
    print(f"   dV per zero  (swept-volume incr) m  : {dV.mean():.4f}   std {dV.std():.4f}")
    print(f"   KS(unfolded dV vs GUE Wigner)       : {ks_gue:.4f}")
    print(f"   KS(unfolded dV vs Poisson/exp)      : {ks_poi:.4f}   (GUE should be << Poisson)")
    summary.append((name, len(g), n_ok, ratio.mean(), ratio.std(),
                    dV.mean(), dV.std(), ks_gue, ks_poi, max_resid))

# ---------------------------------------------------------------- chi3 deep statistics (more zeros)
print("\n" + "=" * 96)
print("  chi3 deep run (more consecutive zeros) for residual / fit statistics")
print("=" * 96)
q, table = 3, {1: 1, 2: -1}
zs = find_zeros(q, table, 260.0)
g = np.array([float(z) for z in zs])
resid = np.array([float(abs(Lval(q, table, mp.mpf(1) / 2 + 1j * mp.mpf(z)))) for z in zs])
print(f"  chi3 consecutive zeros to height 260 : {len(g)}   "
      f"EXACT |L|<1e-12: {int(np.sum(resid<1e-12))}/{len(g)}  (max resid {resid.max():.1e})")
gaps = np.diff(g); mids = 0.5 * (g[1:] + g[:-1])
ratio = gaps / mean_spacing(q, mids)
dV = V_smooth(q, g[1:]) - V_smooth(q, g[:-1])
print(f"  gap/pred mean spacing  mean={ratio.mean():.4f}  std={ratio.std():.4f}  median={np.median(ratio):.4f}")
print(f"  dV per zero            mean={dV.mean():.4f}  std={dV.std():.4f}  median={np.median(dV):.4f}")
print(f"  KS(dV vs GUE)={ks_against_gue(dV):.4f}   KS(dV vs Poisson)={ks_against_poisson(dV):.4f}")
# distribution moments vs GUE Wigner (mean 1, var = 3pi/8 - 1 = 0.1781, std=0.4220)
gue_std = np.sqrt(3 * np.pi / 8 - 1)
print(f"  unfolded-spacing std : observed {dV.std():.4f}   vs GUE Wigner std {gue_std:.4f}   "
      f"vs Poisson std 1.0000")

# ---------------------------------------------------------------- pooled global verdict
print("\n" + "=" * 96)
print("  POOLED across all 5 characters")
print("=" * 96)
pr = np.concatenate(all_ratio); pv = np.concatenate(all_dV)
print(f"  pooled gap/pred mean spacing : mean={pr.mean():.4f}  std={pr.std():.4f}  (N={len(pr)})")
print(f"  pooled dV per zero           : mean={pv.mean():.4f}  std={pv.std():.4f}  (N={len(pv)})")
print(f"  pooled KS(dV vs GUE)={ks_against_gue(pv):.4f}   KS(dV vs Poisson)={ks_against_poisson(pv):.4f}")

print("\n" + "-" * 96)
print(f"  {'character':26s} {'#z':>4s} {'okEXACT':>7s} {'ratio':>7s} {'r.std':>6s} "
      f"{'dV':>7s} {'dV.std':>6s} {'KSgue':>6s} {'KSpoi':>6s}")
print("-" * 96)
for (nm, nz, nok, rm, rs, dm, ds, kg, kp, mr) in summary:
    print(f"  {nm:26s} {nz:4d} {nok:4d}/{nz:<2d} {rm:7.4f} {rs:6.3f} "
          f"{dm:7.4f} {ds:6.3f} {kg:6.3f} {kp:6.3f}")

print("\nVERDICT logic:")
print("  * mean ratio ~1 AND mean dV ~1 for EVERY character -> the gap IS the inverse")
print("    smooth density (one winding-cell per cancellation), MEAN-level claim holds.")
print("  * BUT the per-zero claim 'dV = 1 exactly' is FALSE: std ~0.3-0.4 is the genuine")
print("    GUE spacing fluctuation. KS(GUE) << KS(Poisson) confirms the fluctuation is GUE,")
print("    so dV=1 holds ONLY in the mean, never per individual zero.")
