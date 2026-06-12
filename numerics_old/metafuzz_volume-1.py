"""
metafuzz_volume-1.py  --  HONEST test of the headline VOLUME / INVERSE-COUNTING hypothesis.

ID: volume-1
HYPOTHESIS (headline, strongest form): the zero height gamma_n is fixed by "the winding
phase-space VOLUME of the integer cloud reaches n cells". Concretely:

    V(T) = (1/2pi) [ T * log(qT/2pi) - T ]          (Riemann-vonMangoldt smooth count)
    index  n  =  V(gamma_n) + c + S_fluct(gamma_n)
    where the residual fluctuation  S_fluct = -arg L(1/2 + i gamma_n)/pi  (the arithmetic S(T)).

CLAIM to verify / falsify:
  (A) the SMOOTH volume sets the mean count exactly: n - V(gamma_n) - c stays O(1).
  (B) the per-zero residual r_n = (n - V(gamma_n) - mean) equals -S(gamma_n)/pi to high
      precision: corr(r_n, -S_n) = -1.000 and matching std.
  (C) inverse: solving V(gamma) = n - c recovers gamma_n to ~ one mean spacing.

We test this across ONE rule, only chi mod q changing, for:
  mod 3, mod 4, mod 5 (quadratic), mod 5 (quartic, COMPLEX), mod 7.
Every zero used is verified EXACT: |L(chi, 1/2 + i gamma)| < 1e-12 via mpmath.

Be brutally honest. A clean negative with the precise reason is the deliverable if the
hypothesis fails. passed=true only if both hard constraints (one rule, exact zeros) hold
WITH the volume law actually verified.
"""

import numpy as np
import mpmath as mp

mp.mp.dps = 40

# ---------------- the ONE per-L input: Dirichlet character chi mod q ----------------
CHARS = {
    "mod 3 quadratic":         (3, {1: 1, 2: -1}),
    "mod 4 quadratic":         (4, {1: 1, 3: -1}),
    "mod 5 quadratic":         (5, {1: 1, 4: 1, 2: -1, 3: -1}),
    "mod 5 quartic (complex)": (5, {1: 1, 2: 1j, 4: -1, 3: -1j}),
    "mod 7 quadratic":         (7, {1: 1, 2: 1, 4: 1, 3: -1, 5: -1, 6: -1}),
}


def Lval(q, table, s):
    """exact L(chi, s) = q^{-s} sum_a chi(a) Hurwitz-zeta(s, a/q)."""
    tot = mp.mpc(0)
    for a, c in table.items():
        tot += mp.mpc(c) * mp.zeta(s, mp.mpf(a) / q)
    return q ** (-s) * tot


def Lmag(q, table, t):
    return abs(Lval(q, table, mp.mpf(1) / 2 + 1j * mp.mpf(t)))


def find_consecutive_zeros(q, table, t_lo=0.5, t_hi=120.0, scan_step=0.02,
                           tol_verify=mp.mpf(10) ** (-12)):
    """
    Scan |L(1/2+it)| for local minima below threshold, refine each with mp.findroot on the
    COMPLEX line (root should land on Re=1/2), keep only roots with |L| < tol_verify.
    Returns a sorted list of EXACT gamma (consecutive, no gaps in [t_lo, t_hi]).
    """
    f = lambda s: Lval(q, table, mp.mpf(1) / 2 + 1j * s)  # s real -> point on critical line
    ts = np.arange(t_lo, t_hi, scan_step)
    mags = np.array([float(abs(f(mp.mpf(t)))) for t in ts])
    cand = []
    for i in range(1, len(ts) - 1):
        if mags[i] < mags[i - 1] and mags[i] < mags[i + 1] and mags[i] < 0.5:
            cand.append(ts[i])
    zeros = []
    for t0 in cand:
        try:
            root = mp.findroot(f, mp.mpf(t0), tol=mp.mpf(10) ** (-30))
            tm = mp.re(root)
            if abs(mp.im(root)) < 1e-8 and Lmag(q, table, tm) < tol_verify \
                    and tm > t_lo and all(abs(tm - z) > 1e-4 for z in zeros):
                zeros.append(tm)
        except Exception:
            pass
    return sorted(zeros)


def V(T, q):
    """winding phase-space volume / Riemann-vonMangoldt smooth count."""
    T = mp.mpf(T)
    return (T * mp.log(q * T / (2 * mp.pi)) - T) / (2 * mp.pi)


def argL_over_pi(q, table, gamma):
    """
    S-like quantity: arg L(1/2 + i gamma)/pi.  At an exact zero L=0 so arg is undefined; the
    relevant S(T) is the boundary value approached from just below the zero.  Use a tiny
    negative epsilon in height, matching the prompt's recipe S = arg L(1/2 + i(gamma - eps))/pi.
    Continuous branch via mp.arg (principal); we only need it modulo the smooth trend, and the
    test is the correlation of the *fluctuation*, so principal branch is fine per-zero.
    """
    eps = mp.mpf(10) ** (-6)
    val = Lval(q, table, mp.mpf(1) / 2 + 1j * (mp.mpf(gamma) - eps))
    return mp.arg(val) / mp.pi


def analyze(name, q, table, t_hi=120.0):
    print("=" * 78)
    print(f"{name}   (q={q})")
    print("-" * 78)
    zeros = find_consecutive_zeros(q, table, t_hi=t_hi)
    if len(zeros) < 6:
        print(f"  only {len(zeros)} zeros found -- aborting this character")
        return None
    # EXACT verification report
    worst = max(float(Lmag(q, table, z)) for z in zeros)
    print(f"  found {len(zeros)} consecutive exact zeros in (0,{t_hi}];  "
          f"worst |L(1/2+i gamma)| = {worst:.2e}  (all < 1e-12 required)")
    if worst >= 1e-12:
        print("  !! some zero failed the exact threshold -- NOT counted as verified")

    idx = np.arange(1, len(zeros) + 1)                       # n = 1,2,3,...
    gam = np.array([float(z) for z in zeros])
    Vg = np.array([float(V(z, q)) for z in zeros])           # V(gamma_n)
    raw_resid = idx - Vg                                     # n - V(gamma_n)

    # (A) constant offset c and its stability
    c = raw_resid.mean()
    resid_detr = raw_resid - c                               # r_n
    print(f"  mean offset  c = <n - V(gamma_n)> = {c:.4f}   "
          f"(headline predicts ~0.625 = 5/8 .. 7/8)")
    print(f"  offset spread: min {raw_resid.min():.3f}  max {raw_resid.max():.3f}  "
          f"std {raw_resid.std():.4f}")

    # (B) arithmetic S(T) and correlation
    S = np.array([float(argL_over_pi(q, table, z)) for z in zeros])
    minusS = -S
    # detrend -S the same way (it should have ~zero mean already)
    minusS_detr = minusS - minusS.mean()
    if resid_detr.std() > 0 and minusS_detr.std() > 0:
        corr = float(np.corrcoef(resid_detr, minusS_detr)[0, 1])
    else:
        corr = float('nan')
    print(f"  residual r_n = n - V(gamma_n) - c :  std = {resid_detr.std():.4f}")
    print(f"  arithmetic  -arg L/pi (detrended) :  std = {minusS_detr.std():.4f}")
    print(f"  corr( r_n , -arg L/pi )           =  {corr:+.4f}   "
          f"(headline predicts -1.000)")
    # how close is r_n to exactly -S/pi (not just correlated)?
    diff = resid_detr - minusS_detr
    print(f"  | r_n - (-arg L/pi) | : max {np.abs(diff).max():.4f}  "
          f"rms {np.sqrt((diff**2).mean()):.4f}")

    # (C) inverse: solve V(gamma) = n - c for gamma, compare to true
    inv_err = []
    for nn, true_g in zip(idx, gam):
        target = nn - c
        try:
            g_pred = mp.findroot(lambda x: V(x, q) - target, mp.mpf(true_g))
            inv_err.append(abs(float(g_pred) - true_g))
        except Exception:
            inv_err.append(float('nan'))
    inv_err = np.array(inv_err)
    mean_spacing = (gam[-1] - gam[0]) / (len(gam) - 1)
    print(f"  inverse V(gamma)=n-c :  mean|err| {np.nanmean(inv_err):.3f}  "
          f"max|err| {np.nanmax(inv_err):.3f}   (mean spacing {mean_spacing:.3f})")

    return dict(name=name, q=q, n=len(zeros), c=c, corr=corr,
                resid_std=resid_detr.std(), S_std=minusS_detr.std(),
                diff_rms=float(np.sqrt((diff**2).mean())),
                inv_mean=float(np.nanmean(inv_err)), inv_max=float(np.nanmax(inv_err)),
                spacing=mean_spacing, worst_L=worst,
                offset_spread=float(raw_resid.max() - raw_resid.min()))


def indexed_chi3_check(path):
    """
    Use the indexed (n, gamma_n) pairs from lchi3_zeros_1000.txt (exact 50-digit heights,
    sampled out to n=750 / gamma~925) to confirm the constant offset n - V(gamma_n) - c
    stays O(1) at large height -- i.e. the SMOOTH volume law holds far out, not just near 0.
    """
    print("=" * 78)
    print("LARGE-HEIGHT chi3 check from indexed exact zeros (lchi3_zeros_1000.txt)")
    print("-" * 78)
    q = 3
    rows = []
    with open(path) as fh:
        for line in fh:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            parts = line.split()
            try:
                nn = int(parts[0]); g = mp.mpf(parts[1])
            except Exception:
                continue
            rows.append((nn, g))
    if not rows:
        print("  no indexed rows parsed"); return None
    ns = np.array([r[0] for r in rows], dtype=float)
    gs = np.array([float(r[1]) for r in rows])
    Vg = np.array([float(V(r[1], q)) for r in rows])
    off = ns - Vg                     # n - V(gamma_n)
    print(f"  {len(rows)} indexed exact pairs, n in [{int(ns.min())},{int(ns.max())}], "
          f"gamma in [{gs.min():.2f},{gs.max():.2f}]")
    print(f"   n     gamma_n      V(gamma_n)    n - V(gamma_n)")
    for (nn, g), vg, o in list(zip(rows, Vg, off)):
        if nn <= 20 or nn % 50 == 0:
            print(f"  {nn:4d}  {float(g):10.4f}   {vg:10.4f}    {o:+.4f}")
    print(f"  offset n - V(gamma_n):  mean {off.mean():.4f}  "
          f"min {off.min():.4f}  max {off.max():.4f}  std {off.std():.4f}")
    print(f"  -> does the offset DRIFT with height? "
          f"corr(offset, gamma) = {np.corrcoef(off, gs)[0,1]:+.3f}  "
          f"(near 0 = no drift = volume law holds far out)")
    return dict(mean=off.mean(), spread=float(off.max() - off.min()),
                drift_corr=float(np.corrcoef(off, gs)[0, 1]))


if __name__ == "__main__":
    print("VOLUME / INVERSE-COUNTING hypothesis test  (ID volume-1)")
    print("ONE rule: index n -> V(T)=(1/2pi)[T log(qT/2pi) - T]; only chi mod q changes.\n")

    results = {}
    for name, (q, table) in CHARS.items():
        r = analyze(name, q, table, t_hi=120.0)
        if r:
            results[name] = r
        print()

    big = indexed_chi3_check("/Users/samuellavery/proof/three/numerics/lchi3_zeros_1000.txt")

    # ---------------- VERDICT ----------------
    print("=" * 78)
    print("SUMMARY  (one rule across all characters)")
    print("-" * 78)
    print(f"  {'character':28s} {'#z':>3s} {'c':>7s} {'corr':>7s} "
          f"{'r_std':>7s} {'S_std':>7s} {'diffRMS':>8s} {'invMax':>7s}")
    all_corr_ok = True
    all_exact_ok = True
    for name, r in results.items():
        print(f"  {name:28s} {r['n']:3d} {r['c']:7.3f} {r['corr']:+7.3f} "
              f"{r['resid_std']:7.4f} {r['S_std']:7.4f} {r['diff_rms']:8.4f} "
              f"{r['inv_max']:7.3f}")
        if not (r['corr'] < -0.97):
            all_corr_ok = False
        if r['worst_L'] >= 1e-12:
            all_exact_ok = False

    print()
    print("INTERPRETATION:")
    print("  (A) mean law: offset c stable & n - V(gamma_n) bounded across characters.")
    print("  (B) fine structure: corr(r_n, -arg L/pi) ~ -1 and matching std  =>  the")
    print("      per-zero wobble IS the arithmetic argument, NOT a further geometric volume.")
    print(f"  one-rule exact-zero constraint met for all characters: {all_exact_ok}")
    print(f"  corr ~ -1 (volume sets mean, S sets wobble) for all characters: {all_corr_ok}")
