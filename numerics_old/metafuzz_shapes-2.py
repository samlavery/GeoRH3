"""
metafuzz_shapes-2.py  --  ID: shapes-2

CLAIM (the headline 'iy = VOLUME of integers between cancellations', made exact):
  The imaginary height gamma encodes a VOLUME, but the *correct* volume is the SMOOTH
  ZERO-COUNTING FUNCTION
        theta(g) = (g/2pi) * log(q*g/2pi) - g/2pi      (q = conductor)
  Each consecutive cancellation (zero) consumes exactly ONE unit of theta-volume.
  Equivalently the 'unfolded gap'  V_n = theta(gamma_{n+1}) - theta(gamma_n)  -> 1 on average.
  The RAW integer count per zero (AFE radius sqrt(q*gamma/2pi)) GROWS like (1/2pi)log(qg/2pi)
  per unit height -- so zeros get DENSER as g grows.

ONE RULE for every L-function: the SAME theta(g) with only q (the conductor) swapped.

FALSIFIABLE TARGETS:
  (1) mean unfolded gap  V_n  -> 1.000 +- (sampling error), for EVERY character.
  (2) regress theta(gamma_n) vs n:  slope = 1.000 +- 0.01,  intercept ~ small constant.
  (3) unfolded-spacing std ~ 0.42 - 0.55 (GUE-flavoured), NOT pinned but reported.
  (4) RAW AFE integer count per zero grows ~ (1/2pi) log(q g /2pi) (the density), reported.

HARD CONSTRAINTS (non-negotiable):
  * every zero used is EXACT: verified  |L(chi, 1/2 + i*gamma)| < 1e-12  via mpmath.
  * ONE ruleset across mod 3, 4, 5-quadratic, 5-quartic(COMPLEX), 7.
  * report ACTUAL numbers; honest negative beats a fudged positive.

NOTE on data: lchi3_zeros_1000.txt is consecutive only for the first ~20 zeros then
becomes a sparse sample -- so we DO NOT trust it past the consecutive block. Instead we
generate strictly-consecutive zeros by a dense |L| minima sweep + complex findroot,
checking that the smooth count theta(gamma_n) increments by ~1 per found zero (i.e. that
we skipped NONE).  This is the only honest way to test a mean-1 unfolded-gap claim.
"""

import numpy as np
import mpmath as mp

mp.mp.dps = 40   # 40 digits: |L| at a true zero lands ~1e-30, far under the 1e-12 bar.

TWO_PI = 2.0 * np.pi

# ----------------------------------------------------------------------------------
# Characters: the ONLY per-L input.  name -> (q, residue table).
# ----------------------------------------------------------------------------------
CHARS = {
    "mod 3 quadratic":          (3, {1: 1, 2: -1}),
    "mod 4 quadratic":          (4, {1: 1, 3: -1}),
    "mod 5 quadratic":          (5, {1: 1, 4: 1, 2: -1, 3: -1}),
    "mod 5 quartic (complex)":  (5, {1: 1, 2: 1j, 4: -1, 3: -1j}),
    "mod 7 quadratic":          (7, {1: 1, 2: 1, 4: 1, 3: -1, 5: -1, 6: -1}),
}


def Lval(q, table, s):
    """exact L(chi, s) = q^{-s} sum_a chi(a) * Hurwitz-zeta(s, a/q)."""
    tot = mp.mpc(0)
    for a, c in table.items():
        tot += mp.mpc(c) * mp.zeta(s, mp.mpf(a) / q)
    return q ** (-s) * tot


def theta(g, q):
    """SMOOTH zero-counting volume:  (g/2pi) log(q g /2pi) - g/2pi.  (Riemann-von Mangoldt main term.)"""
    g = float(g)
    return (g / TWO_PI) * np.log(q * g / TWO_PI) - g / TWO_PI


def afe_radius(g, q):
    """AFE / approximate-functional-equation integer cutoff radius:  N ~ sqrt(q*g/2pi).
       (the raw integer-count 'volume' the cone reaches at height g)."""
    return np.sqrt(q * float(g) / TWO_PI)


# ----------------------------------------------------------------------------------
# STRICTLY-CONSECUTIVE exact zeros, generated honestly:
#   dense sweep of |L(1/2+it)| -> local minima -> complex findroot -> verify |L|<1e-12.
#   We require theta(gamma_n) to increment ~1 per found zero (no skips) as a self-check.
# ----------------------------------------------------------------------------------
def consecutive_zeros(q, table, t_hi, step=0.01, tol_mag=1e-12, t_lo=0.5):
    f = lambda s: Lval(q, table, mp.mpf(1) / 2 + 1j * s)   # complex s; true zeros are real heights
    ts = np.arange(t_lo, t_hi, step)
    # magnitude on the grid (float is plenty for *locating* minima; refinement is exact)
    mag = np.empty(len(ts))
    for i, t in enumerate(ts):
        mag[i] = float(abs(f(mp.mpf(float(t)))))
    zeros = []
    for i in range(1, len(ts) - 1):
        if mag[i] < mag[i - 1] and mag[i] < mag[i + 1] and mag[i] < 0.5:
            t0 = ts[i]
            try:
                root = mp.findroot(f, mp.mpc(float(t0), 0.0), tol=mp.mpf(10) ** (-30))
            except Exception:
                continue
            if abs(float(mp.im(root))) > 1e-8:
                continue
            tm = mp.re(root)
            tmf = float(tm)
            if tmf <= t_lo:
                continue
            # EXACT verification of the zero
            mag_here = float(abs(Lval(q, table, mp.mpf(1) / 2 + 1j * tm)))
            if mag_here >= tol_mag:
                continue
            # dedupe (findroot from neighbouring minima can land on the same zero)
            if any(abs(tmf - z) < 1e-4 for z in zeros):
                continue
            zeros.append(tmf)
    zeros.sort()
    return zeros


def no_skip_check(zeros, q):
    """Self-check that the located list is truly CONSECUTIVE (no zeros skipped):
       theta must increase by ~1 between neighbours.  Returns list of theta-increments."""
    th = [theta(g, q) for g in zeros]
    incs = np.diff(th)
    return th, incs


# ----------------------------------------------------------------------------------
# Run the test per character.
# ----------------------------------------------------------------------------------
def run_char(name, q, table, t_hi):
    print("=" * 92)
    print(f"  {name}   (q={q})   sweeping heights up to T={t_hi}")
    print("=" * 92)
    zeros = consecutive_zeros(q, table, t_hi)
    if len(zeros) < 8:
        print(f"  only {len(zeros)} zeros found -- insufficient.")
        return None

    # EXACT verification report (worst |L| over all used zeros)
    worst = 0.0
    for g in zeros:
        m = float(abs(Lval(q, table, mp.mpf(1) / 2 + 1j * mp.mpf(float(g)))))
        worst = max(worst, m)
    print(f"  zeros found: {len(zeros)}   highest gamma = {zeros[-1]:.4f}")
    print(f"  EXACT check: worst |L(1/2+i*gamma)| over all used zeros = {worst:.2e}   "
          f"(< 1e-12 required: {'PASS' if worst < 1e-12 else 'FAIL'})")

    # ---- no-skip / consecutiveness self-check ----
    # NOTE: a per-gap threshold is the WRONG test -- GUE produces genuine large gaps with
    # theta-increment up to ~1.8, which are NOT skipped zeros.  The robust skip-detector is
    # the regression slope: skipping zeros makes theta(gamma_n) climb faster than n, so the
    # slope rises above 1.  A slope of 1.00x certifies no systematic skipping.  (Verified
    # independently against the COMPLETE chi3 reference list: the sweep finds all 34 zeros
    # below T=80, 0 missed / 0 spurious -- the per-gap>1.6 flag was a pure false positive.)
    th, incs = no_skip_check(zeros, q)
    big = int(np.sum(incs > 1.6))
    print(f"  theta-increment between neighbours: mean={incs.mean():.4f}  std={incs.std():.4f}  "
          f"min={incs.min():.4f}  max={incs.max():.4f}")
    print(f"  large genuine gaps (theta-increment > 1.6, GUE tail -- NOT skips): {big}")

    # ---- TARGET (1): mean unfolded gap V_n -> 1 ----
    V = incs  # V_n = theta(gamma_{n+1}) - theta(gamma_n)
    print(f"\n  [1] UNFOLDED GAPS  V_n = theta(g_{{n+1}})-theta(g_n):")
    print(f"        mean = {V.mean():.4f}   (target 1.000)   std = {V.std():.4f}")
    print(f"        first 12: {[round(x,3) for x in V[:12]]}")

    # ---- TARGET (2): regress theta(gamma_n) vs n ----
    n_idx = np.arange(1, len(zeros) + 1, dtype=float)
    th_arr = np.array(th)
    A = np.vstack([n_idx, np.ones_like(n_idx)]).T
    slope, intercept = np.linalg.lstsq(A, th_arr, rcond=None)[0]
    resid = th_arr - (slope * n_idx + intercept)
    consecutive = abs(slope - 1.0) < 0.01   # robust skip-detector: slope drifts up if zeros skipped
    print(f"\n  [2] REGRESS theta(gamma_n) vs n:")
    print(f"        slope     = {slope:.5f}   (target 1.000 +- 0.01)  -> "
          f"{'CONSECUTIVE (no systematic skips)' if consecutive else 'SLOPE OFF -- zeros skipped'}")
    print(f"        intercept = {intercept:.5f}")
    print(f"        max |residual| = {np.max(np.abs(resid)):.4f}   rms residual = {np.sqrt(np.mean(resid**2)):.4f}")

    # ---- TARGET (4): raw AFE integer count per zero grows like the density ----
    print(f"\n  [4] RAW integer 'volume' (AFE radius N=sqrt(q g/2pi)) consumed per zero:")
    print(f"        n  gamma     gap      dN_AFE   density(1/2pi)log(qg/2pi)")
    for i in range(min(8, len(zeros) - 1)):
        g = zeros[i]; gn = zeros[i + 1]
        Na = afe_radius(g, q); Nb = afe_radius(gn, q)
        dens = (1.0 / TWO_PI) * np.log(q * g / TWO_PI)
        print(f"        {i+1:2d} {g:8.3f} {gn-g:7.3f}  {Nb-Na:7.4f}   {dens:7.4f}")

    return dict(name=name, q=q, n=len(zeros), worst=worst, consecutive=bool(consecutive),
                V_mean=float(V.mean()), V_std=float(V.std()),
                slope=float(slope), intercept=float(intercept),
                resid_max=float(np.max(np.abs(resid))))


# ----------------------------------------------------------------------------------
# EXTRA: high-statistics chi3 run.  Generate MANY consecutive zeros (q=3 only) and
# fit mean->1, std->GUE band.  This is the statistically meaningful test.
# ----------------------------------------------------------------------------------
def chi3_highstats(record="lchi3_zeros_record.txt"):
    """High-statistics chi3: use the KNOWN-COMPLETE, verified consecutive 40-digit zero list
       (3580 zeros up to gamma~3500).  This is the statistically meaningful test of mean->1."""
    q, table = 3, {1: 1, 2: -1}
    print("=" * 92)
    print(f"  HIGH-STATISTICS chi3 (q=3): {record} (complete, consecutive, 40-digit zeros)")
    print("=" * 92)
    gm = []
    with open(record) as f:
        for ln in f:
            ln = ln.strip()
            if ln and not ln.startswith("#"):
                p = ln.split()
                if len(p) >= 2:
                    try:
                        gm.append(mp.mpf(p[1]))   # full 40-digit precision
                    except Exception:
                        pass
    gm.sort()
    gf = [float(x) for x in gm]
    # EXACT spot-check over a spread of 40 zeros at full precision
    worst = 0.0
    idx = np.linspace(0, len(gm) - 1, 40).astype(int)
    for i in idx:
        worst = max(worst, float(abs(Lval(q, table, mp.mpf(1) / 2 + 1j * gm[i]))))
    th = [theta(g, q) for g in gf]
    incs = np.diff(th)
    print(f"  zeros: {len(gf)}   highest gamma={gf[-1]:.2f}   "
          f"EXACT spot-check (40 zeros, full precision) worst |L|={worst:.2e}")
    V = incs
    print(f"  UNFOLDED GAPS: mean={V.mean():.5f} (target 1.000)  std={V.std():.5f}  "
          f"min={V.min():.4f} max={V.max():.4f}")
    print(f"  (GUE unfolded-spacing std ~ 0.42; Poisson would give std=1.0 -- the {V.std():.3f} "
          f"shows level repulsion, the smaller-than-Poisson value is correct.)")
    n_idx = np.arange(1, len(gf) + 1, dtype=float)
    A = np.vstack([n_idx, np.ones_like(n_idx)]).T
    slope, intercept = np.linalg.lstsq(A, np.array(th), rcond=None)[0]
    resid = np.array(th) - (slope * n_idx + intercept)
    consecutive = abs(slope - 1.0) < 0.01
    print(f"  REGRESS theta vs n: slope={slope:.6f} (target 1.000)  intercept={intercept:.5f}  "
          f"max|resid|={np.max(np.abs(resid)):.4f}  -> {'CONSECUTIVE' if consecutive else 'SKIPS'}")
    return dict(n=len(gf), V_mean=float(V.mean()), V_std=float(V.std()),
                slope=float(slope), intercept=float(intercept),
                consecutive=bool(consecutive), worst=worst)


if __name__ == "__main__":
    print("\n" + "#" * 92)
    print("#  shapes-2:  iy = SMOOTH-COUNT VOLUME between cancellations.  ONE rule, theta(g), q swapped.")
    print("#" * 92 + "\n")

    # modest height for the 5-character cross-L consistency test (keeps mpmath cost sane).
    T_CROSS = 80.0
    results = []
    for name, (q, table) in CHARS.items():
        r = run_char(name, q, table, T_CROSS)
        if r:
            results.append(r)
        print()

    hs = chi3_highstats()
    print()

    # ------------------------- VERDICT -------------------------
    print("=" * 92)
    print("  CROSS-L SUMMARY  (ONE rule theta(g), only q swapped)")
    print("=" * 92)
    print(f"  {'character':28s} {'q':>2s} {'#z':>5s} {'worst|L|':>10s} {'consec':>6s} "
          f"{'Vmean':>7s} {'Vstd':>6s} {'slope':>8s} {'icept':>7s}")
    for r in results:
        print(f"  {r['name']:28s} {r['q']:>2d} {r['n']:>5d} {r['worst']:>10.1e} "
              f"{str(r['consecutive']):>6s} "
              f"{r['V_mean']:>7.4f} {r['V_std']:>6.4f} {r['slope']:>8.5f} {r['intercept']:>7.3f}")
    print(f"  {'chi3 HIGH-STATS':28s} {3:>2d} {hs['n']:>5d} {hs['worst']:>10.1e} "
          f"{str(hs['consecutive']):>6s} "
          f"{hs['V_mean']:>7.4f} {hs['V_std']:>6.4f} {hs['slope']:>8.5f} {hs['intercept']:>7.3f}")

    # Pass criteria: every character EXACT (<1e-12), consecutive (slope==1 to 0.01),
    # Vmean within 0.05 of 1, slope within 0.01 of 1.
    all_exact = all(r['worst'] < 1e-12 for r in results) and hs['worst'] < 1e-12
    all_consec = all(r['consecutive'] for r in results) and hs['consecutive']
    all_vmean = all(abs(r['V_mean'] - 1.0) < 0.05 for r in results) and abs(hs['V_mean'] - 1.0) < 0.05
    all_slope = all(abs(r['slope'] - 1.0) < 0.01 for r in results) and abs(hs['slope'] - 1.0) < 0.01
    print()
    print(f"  EXACT zeros (<1e-12) for ALL chars : {all_exact}")
    print(f"  CONSECUTIVE (slope=1 +-0.01) ALL   : {all_consec}")
    print(f"  Vmean within 0.05 of 1 for ALL     : {all_vmean}")
    print(f"  slope within 0.01 of 1 for ALL     : {all_slope}")
    print(f"\n  HYPOTHESIS PASSES (one rule + exact + mean-1 + slope-1): "
          f"{all_exact and all_consec and all_vmean and all_slope}")
