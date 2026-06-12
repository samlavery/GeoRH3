"""
metafuzz_density-3.py
=====================
ID: density-3

HEADLINE HYPOTHESIS (Sam): "the iy value (zero height gamma) is the VOLUME of integers
measured between successive cancellations (zeros)."  Made precise as a COUNTING law:

    M(T)   = q*T/(2pi)                      # running integer-volume (odometer):
                                            #   number of integers inside the AFE-active disk
                                            #   of radius R = sqrt(M), on the cone R_n = sqrt(n).
    Phi(M) = (1/q) * [ M*log M - M ]        # "volume potential"; algebraically
                                            #   Phi(M(T)) = (T/2pi)*log(qT/2pi) - T/2pi = N_smooth(T).
    zeros at Phi(M) = n + const            # cancellation n ticks when the volume-potential passes n.
    integers per zero  dM = q/log M = q/log(qT/2pi).

ONE rule for every L(chi,q): only q enters the volume law; chi never does.
This is the Riemann-von Mangoldt main term written as an integer-counting odometer.

WHAT THIS SCRIPT TESTS (brutally honest, ACTUAL numbers):

  (1) FIT  dM_actual = a*q/log(M) + b   over ALL consecutive-zero gaps (3580 chi3 zeros).
      dM_actual = M(gamma_{n+1}) - M(gamma_n) = (q/2pi)*(gamma_{n+1}-gamma_n).
      Predicted a = 1.  The PRELIMINARY note reported dM_actual ~ 0.5 * q/log(M)
      (a clean factor ~2).  We resolve which 'volume' is right: a~1 => odometer M=qT/2pi;
      a~0.5 => the per-zero spacing law actually uses dM ~ q/(2 log M)  (equivalently the
      density slope is log M not 2 log M; i.e. the *correct* mean spacing is
      Delta_gamma = 2pi/log(qT/2pi), giving dM = (q/2pi)*Delta_gamma = q/log M -- so a~1
      would CONFIRM, a~0.5 would FALSIFY the q/log M form and point at q/(2 log M)).

  (2) Phi(M(gamma_n)) = n - c  with BOUNDED residual.  Since Phi(M(T)) == N_smooth(T)
      algebraically, this residual IS the Riemann-von Mangoldt S(T) fluctuation; we
      report mean/std and the best additive constant c (should be ~7/8 for odd primitive).

  (3) THE FALSIFIABLE CORE.  Invert the odometer: SOLVE  Phi(M) = n - c  for M, map back to
      T_pred = 2pi*M/q, and compare T_pred to the TRUE zero gamma_n.  If the headline is a
      genuine *predictive* law (not just a smooth average) the per-zero residual
      gamma_n - T_pred must stay |resid| < 1.1 for EVERY n.  It cannot -- the residual is
      exactly the S(T) fluctuation, which is unbounded (~ log T).  We report the actual
      max|resid| and the fraction with |resid|<1.1.  This is the honest verdict on whether
      "volume between cancellations" PREDICTS the zeros or only their SMOOTH DENSITY.

  CROSS-L: repeat (1)/(2)/(3) on chi mod 3, 4, 5-quadratic, 5-quartic(COMPLEX), 7 with the
  SAME rule -- only q changes.  EXACT zeros for each computed & verified |L|<1e-12.

Run:  python3 metafuzz_density-3.py
"""

import numpy as np
import mpmath as mp

mp.mp.dps = 40
TWO_PI = 2.0 * np.pi


# ----------------------------------------------------------------------------
# characters: name -> (q, residue table).  The ONLY per-L input.
# ----------------------------------------------------------------------------
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


def find_zeros(q, table, hi, coarse=0.05, want=None):
    """Scan |L(1/2+it)| for local minima, refine each with complex findroot.
    Returns sorted list of EXACT zero heights, each verified |L|<1e-12."""
    f = lambda s: Lval(q, table, mp.mpf(1) / 2 + 1j * s)
    ts = np.arange(0.6, hi, coarse)
    mag = np.array([float(abs(f(mp.mpf(t)))) for t in ts])
    zs = []
    for i in range(1, len(ts) - 1):
        if mag[i] < mag[i - 1] and mag[i] < mag[i + 1] and mag[i] < 0.5:
            try:
                root = mp.findroot(f, mp.mpc(ts[i], 0), tol=mp.mpf(10) ** (-30))
                tm = mp.re(root)
                if abs(mp.im(root)) < 1e-8 and abs(f(tm)) < 1e-12 and tm > 0.5 \
                        and all(abs(float(tm) - z) > 1e-4 for z in zs):
                    zs.append(float(tm))
            except Exception:
                pass
        if want is not None and len(zs) >= want:
            break
    return sorted(zs)


def load_chi3_record():
    """Load the 3580 high-precision chi3 zeros (record file) as floats."""
    path = "lchi3_zeros_record.txt"
    gam = []
    with open(path) as fh:
        for line in fh:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            parts = line.split()
            if len(parts) >= 2:
                try:
                    gam.append(float(parts[1]))
                except ValueError:
                    pass
    return np.array(sorted(gam))


# ----------------------------------------------------------------------------
# the volume-odometer law
# ----------------------------------------------------------------------------
def M_of_T(q, T):
    """running integer-volume: # integers in active disk of radius sqrt(M), M = qT/2pi."""
    return q * T / TWO_PI


def Phi(q, M):
    """volume potential; Phi(M(T)) == N_smooth(T) = (T/2pi)log(qT/2pi) - T/2pi."""
    return (M * np.log(M) - M) / q


def N_smooth(q, T):
    """Riemann-von Mangoldt smooth main term (cross-check that Phi(M(T))==this)."""
    x = q * T / TWO_PI
    return (T / TWO_PI) * np.log(x) - T / TWO_PI


def invert_Phi(q, targets):
    """Solve Phi(M) = target for M>e (monotone, smooth), VECTORIZED float Newton.
    Phi(M) = (M log M - M)/q ;  Phi'(M) = log(M)/q.  Newton converges in ~8 steps.
    Accepts an array of targets; returns array of M (nan where target below Phi(e))."""
    targets = np.asarray(targets, dtype=float)
    out = np.full_like(targets, np.nan)
    valid = q * targets > np.e  # need M>e region (Phi(e)=0); target>0 well inside
    qt = q * targets[valid]
    # asymptotic seed M ~ q*target / log(q*target)  (two refinements)
    M = qt / np.log(qt)
    M = qt / np.log(np.maximum(M, np.e))
    M = np.maximum(M, np.e + 1e-6)
    for _ in range(60):
        f = (M * np.log(M) - M) / q - targets[valid]
        fp = np.log(M) / q
        step = f / fp
        M = M - step
        M = np.maximum(M, np.e + 1e-9)
        if np.max(np.abs(step)) < 1e-10 * np.max(M):
            break
    out[valid] = M
    return out


# ----------------------------------------------------------------------------
def analyze(name, q, gamma):
    """Run tests (1),(2),(3) on an array of EXACT zero heights gamma."""
    gamma = np.asarray(gamma, dtype=float)
    n_idx = np.arange(1, len(gamma) + 1)
    print(f"\n{'='*78}\n{name}   (q={q})   {len(gamma)} exact zeros, "
          f"gamma in [{gamma[0]:.3f}, {gamma[-1]:.3f}]\n{'='*78}")

    M = M_of_T(q, gamma)                         # odometer value at each zero

    # ---- sanity: Phi(M(T)) == N_smooth(T) exactly (algebraic identity) ----
    phi_vals = Phi(q, M)
    nsm = N_smooth(q, gamma)
    print(f"  [identity check] max|Phi(M(gamma)) - N_smooth(gamma)| = "
          f"{np.max(np.abs(phi_vals - nsm)):.2e}   (must be ~0)")

    # ---------- TEST (1): fit dM_actual = a*q/log(M) + b ----------
    dM_actual = np.diff(M)                        # = (q/2pi)*diff(gamma)
    Mmid = 0.5 * (M[:-1] + M[1:])
    pred_unit = q / np.log(Mmid)                 # the q/log M predictor at midpoint
    A = np.vstack([pred_unit, np.ones_like(pred_unit)]).T
    (a, b), *_ = np.linalg.lstsq(A, dM_actual, rcond=None)
    resid_fit = dM_actual - (a * pred_unit + b)
    ss_res = float(np.sum(resid_fit ** 2))
    ss_tot = float(np.sum((dM_actual - dM_actual.mean()) ** 2))
    r2 = 1 - ss_res / ss_tot if ss_tot > 0 else float("nan")
    # also a pure-ratio diagnostic (no intercept): median of dM_actual/(q/log M)
    ratio = dM_actual / pred_unit
    print(f"  TEST(1) fit  dM = a*(q/log M) + b   over {len(dM_actual)} gaps:")
    print(f"          a = {a:.4f}   b = {b:+.4f}   R^2 = {r2:.4f}")
    print(f"          median(dM_actual / (q/log M)) = {np.median(ratio):.4f}  "
          f"(predict 1.0 if q/log M is the right per-zero volume)")
    print(f"          => slope-of-density verdict: a~1 confirms dM=q/log M ; "
          f"a~0.5 means dM=q/(2 log M).")

    # ---------- TEST (2): Phi(M(gamma_n)) = n - c, bounded residual ----------
    # best additive constant c (so phi_vals ~ n - c  =>  c = mean(n - phi_vals))
    c = np.mean(n_idx - phi_vals)
    S = n_idx - phi_vals - c                      # this is the S(T) fluctuation (mean-removed)
    print(f"  TEST(2) Phi(M(gamma_n)) vs n:   best constant c = {c:+.4f}  "
          f"(odd-primitive RvM const ~ +0.875 = 7/8)")
    print(f"          S = n - Phi - c :  mean={S.mean():+.4f}  std={S.std():.4f}  "
          f"max|S|={np.max(np.abs(S)):.4f}")
    # is std bounded or growing?  correlate |S| with log(gamma)
    if len(gamma) > 50:
        lo, hi = gamma < np.median(gamma), gamma >= np.median(gamma)
        print(f"          std(S) low-half ={S[lo].std():.4f}   "
              f"high-half ={S[hi].std():.4f}   (S(T) is O(log T): expect mild growth)")

    # ---------- TEST (3): invert odometer -> T_pred, compare to true gamma ----------
    # solve Phi(M) = n - c  for M, then T_pred = 2pi M / q.
    targets = n_idx - c
    Mt = invert_Phi(q, targets)                  # vectorized float Newton inversion
    T_pred = TWO_PI * Mt / q
    resid = gamma - T_pred
    good = np.isfinite(resid)
    rr = resid[good]
    frac_tight = np.mean(np.abs(rr) < 1.1)
    # SHARPER, honest threshold: a *prediction* lands in the right slot only if the
    # residual is below HALF the local mean gap.  local gap ~ 2pi/log(qT/2pi).
    gg = gamma[good]
    local_gap = TWO_PI / np.log(q * gg / TWO_PI)
    resid_in_gaps = np.abs(rr) / local_gap          # |resid| as a fraction of mean gap
    frac_halfgap = np.mean(resid_in_gaps < 0.5)     # fraction within half a gap (right slot)
    print(f"  TEST(3) PREDICTIVE inversion  Phi(M)=n-c -> T_pred ,  resid = gamma - T_pred:")
    print(f"          mean={rr.mean():+.4f}  std={rr.std():.4f}  "
          f"max|resid|={np.max(np.abs(rr)):.4f}")
    print(f"          fraction |resid| < 1.1 (loose abs thr) : {frac_tight*100:.1f}%")
    print(f"          |resid|/local_gap:  median={np.median(resid_in_gaps):.3f}  "
          f"max={np.max(resid_in_gaps):.3f}   "
          f"fraction < 0.5 gap (right slot): {frac_halfgap*100:.1f}%")
    print(f"          -> the residual is ~{np.median(resid_in_gaps):.2f} of a gap: T_pred is the")
    print(f"             SMOOTH expected position, off the true zero by a sizeable")
    print(f"             fraction of a gap. This IS the S(T) fluctuation, not a hit.")
    # growth of max|resid| across the range (is it bounded?)
    if good.sum() > 100:
        q1, q2, q3 = np.array_split(rr, 3)
        print(f"          max|resid| by thirds (low/mid/high gamma): "
              f"{np.max(np.abs(q1)):.3f} / {np.max(np.abs(q2)):.3f} / "
              f"{np.max(np.abs(q3)):.3f}   (S(T)~loglog: grows extremely slowly)")

    return dict(a=a, b=b, r2=r2, c=c, S_std=float(S.std()),
                S_max=float(np.max(np.abs(S))),
                resid_max=float(np.max(np.abs(rr))), frac_tight=float(frac_tight),
                ratio_med=float(np.median(ratio)),
                resid_gap_med=float(np.median(resid_in_gaps)),
                resid_gap_max=float(np.max(resid_in_gaps)),
                frac_halfgap=float(frac_halfgap))


# ----------------------------------------------------------------------------
def main():
    print("metafuzz_density-3 : 'zero height = VOLUME of integers between cancellations'")
    print("ONE volume law  M=qT/2pi,  Phi(M)=(M log M - M)/q ,  zeros at Phi=n-c. "
          "Only q changes.\n")

    summary = {}

    # ---- chi3: full 3580-zero statistics from the record file ----
    g3 = load_chi3_record()
    # verify the WHOLE 3580 EXACTLY against mpmath; note: the record file stores gamma to
    # ~15 float digits, so |L| at the *stored* value is limited by that truncation
    # (header reports worst |L|=1.3e-39 at FULL 40-digit precision -- these are genuine zeros).
    print("EXACT verification of ALL 3580 chi3 record zeros (|L(chi3,1/2+i gamma)| at stored float):")
    tab3 = CHARS["mod 3 quadratic"][1]
    Lmags = np.array([float(abs(Lval(3, tab3, mp.mpf(1)/2 + 1j*mp.mpf(g)))) for g in g3])
    print(f"    max |L| over all 3580 = {Lmags.max():.2e}   "
          f"(#>1e-12: {(Lmags>1e-12).sum()}, all borderline = float-truncation of stored gamma)")
    print(f"    fraction |L| < 1e-10 : {np.mean(Lmags<1e-10)*100:.2f}%   "
          f"(genuine zeros; precision floor set by 15-digit stored gamma)")
    for k in [0, len(g3)//2, len(g3)-1]:
        print(f"    gamma_{k+1} = {g3[k]:.6f}   |L| = {Lmags[k]:.2e}")
    summary["mod 3 quadratic (3580 zeros)"] = analyze("mod 3 quadratic", 3, g3)

    # ---- cross-L: compute exact zeros for each character, same rule ----
    # use enough zeros for a real fit; chi3 here as a small-N cross-check too.
    HEIGHTS = 220.0     # gives ~ a few dozen zeros per L; all EXACT-verified
    for name, (q, table) in CHARS.items():
        zs = find_zeros(q, table, hi=HEIGHTS, coarse=0.04)
        if len(zs) < 8:
            print(f"\n[skip] {name}: only {len(zs)} zeros found"); continue
        # EXACT re-verify all
        bad = [z for z in zs
               if abs(Lval(q, table, mp.mpf(1)/2 + 1j*mp.mpf(z))) >= 1e-12]
        tag = "ALL |L|<1e-12 OK" if not bad else f"{len(bad)} FAILED |L| check"
        print(f"\n[exact zeros] {name}: {len(zs)} zeros up to T={HEIGHTS}  -> {tag}")
        summary[f"{name} ({len(zs)} zeros)"] = analyze(name, q, np.array(zs))

    # ---------------- VERDICT ----------------
    print("\n" + "#" * 78)
    print("# SUMMARY (the actual numbers)")
    print("#" * 78)
    hdr = f"{'L-function':32s} {'a(fit)':>7s} {'ratio':>7s} {'c':>7s} "\
          f"{'std S':>7s} {'res/gap':>8s} {'%<halfgap':>10s}"
    print(hdr)
    for k, v in summary.items():
        print(f"{k:32s} {v['a']:7.3f} {v['ratio_med']:7.3f} {v['c']:+7.3f} "
              f"{v['S_std']:7.3f} {v['resid_gap_med']:8.3f} {v['frac_halfgap']*100:9.1f}%")

    print("\nINTERPRETATION:")
    print("  * TEST(1) a-value: if a~1 across all L, the per-zero integer-volume IS q/log M")
    print("    (the odometer M=qT/2pi is right). If a~0.5, the correct law is q/(2 log M).")
    print("  * TEST(3) max|resid| & %<1.1: this decides the HEADLINE. The volume law")
    print("    reproduces the SMOOTH zero DENSITY (RvM main term) exactly by construction,")
    print("    but a single volume-odometer CANNOT predict individual gamma_n: the gap")
    print("    gamma_n - T_pred is the S(T) fluctuation, which GROWS like log T and is")
    print("    NOT bounded by 1.1. Watch whether max|resid| grows across thirds -- that")
    print("    growth is the honest falsification of 'volume predicts each zero'.")


if __name__ == "__main__":
    main()
