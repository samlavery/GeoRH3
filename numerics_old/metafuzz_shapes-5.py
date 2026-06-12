"""
metafuzz_shapes-5.py  --  ID shapes-5
======================================================================================
USER HEADLINE HYPOTHESIS:
  "the iy value (zero height gamma) represents the VOLUME of integers measured between
   successive cancellations (zeros)"  --  the zero heights / gaps are set by a count or
   3D volume of integers between consecutive cancellation events.

CLAIM (shapes-5):  VOLUME-GAP DENSITY LAW.  The number of NEW integers wound onto the
cone to advance from cancellation n to n+1 is NOT constant -- it grows like log(gamma).
So "volume between cancellations" is the count of integers in the cone annulus between
two AFE cutoff radii, and this predicts the gap via the classical density law.

FALSIFIABLE INVARIANTS (one ruleset, only q changes):
  (1) gap_n * log(q*gamma_n/2pi)  -->  2pi = 6.28318...   (constant, flat, no drift)
  (2) theta-volume increment  V_n = theta(gamma_{n+1}) - theta(gamma_n)  -->  1
  (3) AFE annular integer count dN_int = sqrt(q*g_{n+1}/2pi) - sqrt(q*g_n/2pi)
        -- is this ~constant ("one fibre-balanced pair per cancellation") or does it grow?

theta(g) here = the *mean* zero-counting function N(g) for L(chi mod q):
    N(g) ~ (g/2pi)*log(q*g/2pi) - g/2pi  (+ O(log g))
so theta-increment between true consecutive zeros should -> 1 (one zero per step).

METHOD:
  - Regenerate the FIRST K strictly-consecutive zeros for each character via a dense
    grid scan + mpmath.findroot (guarantees consecutiveness; the stored 1000-zero file
    is only consecutive through ~#20 then strides by 50).
  - VERIFY every zero: |L(chi, 1/2 + i*gamma)| < 1e-12.
  - Test invariants (1)(2)(3); fit to the predicted constants; report residuals + trend.
  - Cross-L: mod 3, mod 4, mod 5-quadratic, mod 5-QUARTIC(complex), mod 7; ONLY q changes.
  - chi3 long run (first ~300 consecutive zeros) for statistics.

HARD CONSTRAINTS:  exact zeros (|L|<1e-12); ONE rule for all characters; report ACTUAL
numbers; a clean negative with the precise reason is a valid (valuable) outcome.
"""
import numpy as np
import mpmath as mp
import functools

mp.mp.dps = 30   # ample for 1e-12 zero checks and findroot polishing

PI = mp.pi

# ---------- characters: name -> (q, residue-table dict) ; the ONLY per-L input ----------
CHARS = {
    "mod 3 quadratic":          (3, {1: 1, 2: -1}),
    "mod 4 quadratic":          (4, {1: 1, 3: -1}),
    "mod 5 quadratic":          (5, {1: 1, 4: 1, 2: -1, 3: -1}),
    "mod 5 quartic (complex)":  (5, {1: 1, 2: 1j, 4: -1, 3: -1j}),
    "mod 7 quadratic":          (7, {1: 1, 2: 1, 4: 1, 3: -1, 5: -1, 6: -1}),
}


def Lval(q, table, s):
    """exact L(chi,s) = q^{-s} sum_a chi(a) Hurwitz-zeta(s, a/q)."""
    tot = mp.mpc(0)
    for a, c in table.items():
        tot += mp.mpc(c) * mp.zeta(s, mp.mpf(a) / q)
    return q ** (-s) * tot


def _est_hi(q, K):
    """Estimate the height of the K-th zero from the mean density, with margin.
       N(T) ~ (T/2pi) log(qT/2pi); invert crudely so we scan just far enough."""
    T = 10.0
    for _ in range(60):
        N = (T / (2 * np.pi)) * np.log(max(q * T / (2 * np.pi), 1.0001))
        if N >= K + 4:
            break
        T *= 1.25
    return T * 1.15 + 20.0


def consecutive_zeros(q, table, K, t_lo=0.4, t_hi=None, coarse=0.05):
    """
    Return the first K STRICTLY consecutive positive zero heights gamma of L(chi mod q),
    each refined by findroot and verified |L| < 1e-12.  Scan |L| on a grid (step `coarse`,
    finer than the smallest gap so no zero is skipped), take every strict local minimum
    below threshold, polish with findroot.  Consecutiveness guaranteed by the grid being
    finer than the mean gap (>~1 here) by a large margin.
    """
    if t_hi is None:
        t_hi = _est_hi(q, K)
    # f accepts t real (grid scan) OR complex (findroot probes off the real axis); both work
    # because Lval takes a complex s.  Zero of L on the line <=> real root t=gamma.
    f = lambda t: Lval(q, table, mp.mpf(1) / 2 + 1j * t)
    ts = np.arange(float(t_lo), float(t_hi), coarse)
    mags = np.array([float(abs(f(mp.mpf(float(t))))) for t in ts])
    zeros = []
    for i in range(1, len(ts) - 1):
        if mags[i] < mags[i - 1] and mags[i] < mags[i + 1] and mags[i] < 0.5:
            try:
                root = mp.findroot(f, mp.mpc(float(ts[i]), 0), tol=mp.mpf(10) ** (-25))
                g = mp.re(root)
                if abs(mp.im(root)) < mp.mpf(10) ** (-8) and g > mp.mpf(t_lo):
                    if abs(f(g)) < mp.mpf(10) ** (-12):
                        if all(abs(g - z) > mp.mpf("1e-4") for z in zeros):
                            zeros.append(g)
            except Exception:
                pass
    zeros = sorted(zeros)[:K]
    return zeros


def theta_count(q, g):
    """Mean zero-counting function N(g) for L(chi mod q):
       N(g) = (g/2pi)*log(q*g/(2pi)) - g/2pi  (leading + first correction; const term dropped).
       Increment between true consecutive zeros should -> 1."""
    g = mp.mpf(g)
    return (g / (2 * PI)) * mp.log(q * g / (2 * PI)) - g / (2 * PI)


def afe_radius(q, g):
    """AFE cutoff radius: number of integers effectively summed ~ sqrt(q*g/2pi) winding events.
       (The functional-equation balance point N ~ sqrt(q t / 2pi).)  Returns the cutoff in
       integer-count units; annular integer count between two zeros = difference of these."""
    return mp.sqrt(q * mp.mpf(g) / (2 * PI))


def analyze(name, q, table, K):
    print("=" * 92)
    print(f"  {name}   (q={q})   --  first {K} strictly-consecutive zeros")
    print("=" * 92)
    zs = consecutive_zeros(q, table, K)
    if len(zs) < 3:
        print(f"  !! only found {len(zs)} zeros -- skipping")
        return None

    # VERIFY exact
    worst = max(float(abs(Lval(q, table, mp.mpf(1) / 2 + 1j * g))) for g in zs)
    print(f"  found {len(zs)} consecutive zeros; gamma_1={float(zs[0]):.6f} ... "
          f"gamma_{len(zs)}={float(zs[-1]):.4f}")
    print(f"  EXACT verify: worst |L(1/2+i*gamma)| = {worst:.2e}   "
          f"({'PASS <1e-12' if worst < 1e-12 else 'FAIL'})")

    g = np.array([float(x) for x in zs])
    gaps = np.diff(g)                                   # gap_n = g_{n+1} - g_n
    gmid = g[:-1]                                       # evaluate density at lower zero

    # Invariant (1):  gap_n * log(q*gamma_n/2pi)  -> 2pi
    inv1 = gaps * np.log(q * gmid / (2 * np.pi))
    # Invariant (2):  theta-volume increment -> 1
    theta = np.array([float(theta_count(q, x)) for x in zs])
    inv2 = np.diff(theta)
    # Invariant (3):  AFE annular integer count
    rad = np.array([float(afe_radius(q, x)) for x in zs])
    dN_int = np.diff(rad)

    print(f"  --- invariant (1): gap_n * log(q*gamma_n/2pi)  [predict -> 2pi={2*np.pi:.5f}] ---")
    print(f"      mean = {inv1.mean():.5f}   std = {inv1.std():.5f}   "
          f"first = {inv1[0]:.4f}   last = {inv1[-1]:.4f}")
    # trend: linear fit of inv1 vs index
    idx = np.arange(len(inv1))
    slope1 = np.polyfit(idx, inv1, 1)[0] if len(inv1) > 2 else float('nan')
    print(f"      trend slope (per zero) = {slope1:+.5f}   "
          f"(flat => density law holds; drift => not 2pi)")

    print(f"  --- invariant (2): theta-increment N(g_{{n+1}})-N(g_n)  [predict -> 1] ---")
    print(f"      mean = {inv2.mean():.5f}   std = {inv2.std():.5f}   "
          f"first = {inv2[0]:.4f}   last = {inv2[-1]:.4f}")

    print(f"  --- invariant (3): AFE annular integer count sqrt(q*g_{{n+1}}/2pi)-sqrt(q*g_n/2pi) ---")
    print(f"      mean = {dN_int.mean():.5f}   std = {dN_int.std():.5f}   "
          f"first = {dN_int[0]:.4f}   last = {dN_int[-1]:.4f}")
    slope3 = np.polyfit(idx, dN_int, 1)[0] if len(dN_int) > 2 else float('nan')
    print(f"      trend slope (per zero) = {slope3:+.6f}   "
          f"(if ~constant => 'one fibre pair / cancellation'; if shrinking => not)")

    # Correlation: does dN_int track 1/gap (= local density)?  The user's literal claim
    # ("volume of integers between cancellations" sets the gap) predicts dN_int ~ 1/gap.
    inv_gap = 1.0 / gaps
    if len(dN_int) > 2:
        corr = np.corrcoef(dN_int, inv_gap)[0, 1]
        print(f"  --- corr( dN_int , 1/gap ) = {corr:+.4f}  "
              f"(user claim: integer-volume sets gap => want strong + corr) ---")
    print()
    return dict(name=name, q=q, g=g, gaps=gaps, inv1=inv1, inv2=inv2,
                dN_int=dN_int, worst=worst)


# ----------------------------------------------------------------------------------
print("\n" + "#" * 92)
print("# shapes-5: VOLUME-GAP DENSITY LAW  --  is the zero gap set by an integer-count / volume?")
print("#" * 92 + "\n")

results = {}
# cross-L: ONE rule, only q & chi change.  Moderate K each (these findroot scans are exact).
for name, (q, table) in CHARS.items():
    K = 40
    results[name] = analyze(name, q, table, K)

# ----------------------------------------------------------------------------------
# chi3 LONG RUN for statistics (first ~300 consecutive zeros) -- the headline density test
# ----------------------------------------------------------------------------------
print("=" * 92)
print("  chi3 LONG RUN  --  first ~300 consecutive zeros (statistics on the density law)")
print("=" * 92)
q3, t3 = 3, {1: 1, 2: -1}
zs_long = consecutive_zeros(q3, t3, 300, coarse=0.05)
worst_long = max(float(abs(Lval(q3, t3, mp.mpf(1) / 2 + 1j * g))) for g in zs_long)
g = np.array([float(x) for x in zs_long])
print(f"  found {len(g)} consecutive chi3 zeros up to gamma={g[-1]:.3f}; "
      f"worst |L| = {worst_long:.2e} ({'PASS' if worst_long < 1e-12 else 'FAIL'})")
gaps = np.diff(g)
gmid = g[:-1]
inv1 = gaps * np.log(q3 * gmid / (2 * np.pi))
theta = np.array([float(theta_count(q3, x)) for x in zs_long])
inv2 = np.diff(theta)

# fit inv1 = a + b*log(gamma) to see if it is genuinely flat at 2pi
X = np.log(q3 * gmid / (2 * np.pi))
A = np.vstack([np.ones_like(X), X]).T
coef, *_ = np.linalg.lstsq(A, inv1, rcond=None)
resid = inv1 - A @ coef
print(f"  invariant (1) gap*log(q*g/2pi):  mean = {inv1.mean():.5f}  (predict 2pi={2*np.pi:.5f})")
print(f"     std = {inv1.std():.5f}   RMS resid about mean = {(inv1-inv1.mean()).std():.5f}")
print(f"     linear fit  inv1 = a + b*log(q*g/2pi):  a={coef[0]:.4f}  b={coef[1]:+.5f}  "
      f"(b~0 & a~2pi => clean density law)")
print(f"  invariant (2) theta-increment:   mean = {inv2.mean():.5f}  std = {inv2.std():.5f}  "
      f"(predict 1.0)")

# How fast does the RAW integer count between cancellations grow?  (user: 'volume grows like log')
rad = np.array([float(afe_radius(q3, x)) for x in zs_long])
dN_int = np.diff(rad)
print(f"  AFE annular integer count dN_int:  first={dN_int[0]:.3f}  mid={dN_int[len(dN_int)//2]:.3f}  "
      f"last={dN_int[-1]:.3f}  mean={dN_int.mean():.3f}")
print(f"     -> raw integer-volume per cancellation is "
      f"{'NOT constant (grows/shrinks)' if dN_int.std()/abs(dN_int.mean())>0.1 else 'roughly constant'}")
# does dN_int ~ 1/gap?
print(f"     corr(dN_int, 1/gap) = {np.corrcoef(dN_int, 1.0/gaps)[0,1]:+.4f}")

# ----------------------------------------------------------------------------------
# VERDICT
# ----------------------------------------------------------------------------------
print("\n" + "#" * 92)
print("# VERDICT")
print("#" * 92)
all_inv1 = []
all_inv2 = []
for name, r in results.items():
    if r is None:
        continue
    all_inv1.append((name, r['inv1'].mean(), r['inv1'].std(), r['worst']))
    all_inv2.append((name, r['inv2'].mean(), r['inv2'].std()))

print("  Invariant (1)  gap_n * log(q*gamma_n/2pi)  vs  2pi = %.5f :" % (2 * np.pi))
for name, m, s, w in all_inv1:
    dev = (m - 2 * np.pi) / (2 * np.pi) * 100
    print(f"     {name:26s}: mean={m:.4f}  std={s:.4f}  ({dev:+.1f}% off 2pi)  |L|worst={w:.1e}")
print("  Invariant (2)  theta-increment  vs  1.0 :")
for name, m, s in all_inv2:
    print(f"     {name:26s}: mean={m:.4f}  std={s:.4f}  ({(m-1)*100:+.1f}% off 1)")

print("\n  NOTE: invariant (1) is the MEAN density law (Riemann-von Mangoldt). It holds on")
print("  AVERAGE for every L (that is textbook). The sharp question the user asks is whether")
print("  the INDIVIDUAL gap is *set by* an integer count -- i.e. whether dN_int (or any fixed")
print("  integer volume) PREDICTS each gap, not just the average. Watch invariant (1)'s std and")
print("  the dN_int<->1/gap correlation: large std / weak corr => the volume law is only a mean,")
print("  individual zero positions are NOT pinned by a per-cancellation integer count.")
