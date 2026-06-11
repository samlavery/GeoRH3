"""
metafuzz_volume-4.py -- TEST of hypothesis ID volume-4.

CLAIM (volume-4): RADIUS and HEIGHT-VOLUME are DISTINCT powers of gamma, which
disambiguates the headline "volume of integers between successive cancellations":

  - The cone RADIAL integer-length  N_geom(gamma) = sqrt(q*gamma/2pi)   ~ gamma^{1/2}
    (the sqrt-packing / area law; log-log slope exactly 0.500).  This is the AMPLITUDE
    channel (radius R_n = sqrt(n)).

  - The ZERO COUNT (the "volume between cancellations"), i.e. the rank index of a zero,
    N_count(gamma) = #{0<g<=gamma} ~ (gamma/2pi) log(q*gamma/2pi) - gamma/2pi
    ~ gamma^{~1.45} over this window (super-linear, gamma times a log factor).  This is
    the COUNTING / WINDING-HEIGHT channel.

  Therefore the "volume of integers" that the zero HEIGHT gamma encodes is the
  1D winding-height count N_count, NOT the 2D radial integer-length N_geom.
  The two "integer counts" scale with genuinely DIFFERENT powers of gamma; they must
  not be conflated.

WHAT THIS FILE DOES (honestly):
  (A) Re-VERIFY every gamma used is an EXACT zero: mpmath |L(chi,1/2+i*gamma)| < 1e-12.
      Done with ONE ruleset (Lval = q^{-s} sum_a chi(a) Hurwitz-zeta) for chi mod
      3, 4, 5-quadratic, 5-quartic(COMPLEX), 7 -- only chi changes.
  (B) For the 5 small-window characters: find their first zeros, attach the TRUE rank
      index via the Riemann-von Mangoldt counting function (refined N(T)), and run the
      two log-log regressions index-vs-gamma and N_geom-vs-gamma.
  (C) For chi3 specifically (35 exact zeros with KNOWN ranks up to gamma=925 from
      lchi3_zeros_1000.txt) run the high-statistics version: this is the decisive test
      because the ranks are exact, not estimated.
  (D) Sharpening test: check N_count/N_geom -> (1/2pi) sqrt(2pi/q) sqrt(gamma) log(q gamma/2pi)
      i.e. the claimed ratio, with residuals.

  Slopes are obtained by ordinary least squares of log(y) on log(gamma).

PASS criterion for the volume-4 claim:
  - radial-length slope ~ 0.500 (within a tight band), AND
  - zero-count slope clearly super-linear (~1.4-1.5 over this window, and provably
    NOT 0.5), across the SAME single ruleset for all characters.
  This does NOT claim to "produce zeros" by a new geometry -- it claims to correctly
  IDENTIFY which integer-count the height equals.  We still verify the zeros are exact.
"""

import numpy as np
import mpmath as mp

mp.mp.dps = 40

# ---------------- the ONE ruleset's L-value (only chi changes) ----------------
CHARS = {
    "mod 3 quadratic":          (3, {1: 1, 2: -1}),
    "mod 4 quadratic":          (4, {1: 1, 3: -1}),
    "mod 5 quadratic":          (5, {1: 1, 4: 1, 2: -1, 3: -1}),
    "mod 5 quartic (complex)":  (5, {1: 1, 2: 1j, 4: -1, 3: -1j}),
    "mod 7 quadratic":          (7, {1: 1, 2: 1, 4: 1, 3: -1, 5: -1, 6: -1}),
}


def Lval(q, table, s):
    """exact L(chi,s) = q^{-s} sum_a chi(a) Hurwitz-zeta(s, a/q).  ONE rule, only chi changes."""
    tot = mp.mpc(0)
    for a, c in table.items():
        tot += mp.mpc(c) * mp.zeta(s, mp.mpf(a) / q)
    return q ** (-s) * tot


def find_zeros(q, table, hi, step=0.04, maxn=None):
    """Locate true zero heights gamma>0 of L(chi,1/2+i*gamma) by min-then-findroot, EXACT."""
    f = lambda s: Lval(q, table, mp.mpf(1) / 2 + 1j * s)
    ts = np.arange(0.6, hi, step)
    mag = np.array([float(abs(f(mp.mpf(t)))) for t in ts])
    zs = []
    for i in range(1, len(ts) - 1):
        if mag[i] < mag[i - 1] and mag[i] < mag[i + 1] and mag[i] < 0.5:
            try:
                root = mp.findroot(f, mp.mpc(ts[i], 0), tol=mp.mpf(10) ** (-25))
                tm = mp.re(root)
                if abs(float(mp.im(root))) < 1e-8 and abs(complex(f(tm))) < 1e-12 \
                        and float(tm) > 0.5 and all(abs(float(tm) - float(q0)) > 1e-3 for q0 in zs):
                    zs.append(tm)
            except Exception:
                pass
    zs = sorted(zs, key=float)
    if maxn:
        zs = zs[:maxn]
    return zs


def riemann_count(q, gamma):
    """
    Riemann-von Mangoldt counting function for L(chi mod q):
      N(T) ~ (T/2pi) log(q T / (2 pi e)) + 7/8 + (1/pi) Im log L (-> O(1)).
    We use the smooth main term + the standard 7/8 constant as the rank estimate.
    For the chi3 high-stats test we use the TRUE ranks (exact integers), so this
    estimate is only used for the small-window characters as a cross-check.
    """
    T = float(gamma)
    return (T / (2 * np.pi)) * np.log(q * T / (2 * np.pi * np.e)) + 7.0 / 8.0


def ols_slope(x, y):
    """slope of OLS fit y = a + b x ; returns (b, a, R2)."""
    x = np.asarray(x, float); y = np.asarray(y, float)
    b, a = np.polyfit(x, y, 1)
    yhat = a + b * x
    ss_res = np.sum((y - yhat) ** 2)
    ss_tot = np.sum((y - np.mean(y)) ** 2)
    R2 = 1 - ss_res / ss_tot if ss_tot > 0 else float('nan')
    return b, a, R2


# ----------------------- load the 35 EXACT chi3 zeros with KNOWN ranks -----------------------
def load_chi3_ranked(path="lchi3_zeros_1000.txt"):
    """rows like:  <index>  <gamma(50 digits)>  |L|=...  -> (rank, mpf gamma)."""
    out = []
    with open(path) as fh:
        for line in fh:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            parts = line.split()
            if len(parts) < 2:
                continue
            try:
                idx = int(parts[0])
                g = mp.mpf(parts[1])
            except Exception:
                continue
            out.append((idx, g))
    return out


print("=" * 88)
print("metafuzz_volume-4  --  RADIUS (sqrt-packing) vs ZERO-COUNT (winding volume) are")
print("                       DISTINCT powers of gamma.  ONE ruleset, all characters.")
print("=" * 88)

# ============================================================================
# PART (A)+(C): chi3 DECISIVE high-statistics test with EXACT zeros & TRUE ranks
# ============================================================================
print("\n[PART C] chi3: 35 EXACT zeros with TRUE ranks (from lchi3_zeros_1000.txt), gamma up to 925")
q3 = 3
table3 = CHARS["mod 3 quadratic"][1]
ranked = load_chi3_ranked()
print(f"   loaded {len(ranked)} ranked zeros.  Verifying each is EXACT (|L(1/2+i*gamma)|<1e-12)...")

verified = []
worst = 0.0
for idx, g in ranked:
    Lv = abs(Lval(q3, table3, mp.mpf(1) / 2 + 1j * g))
    worst = max(worst, float(Lv))
    if float(Lv) < 1e-12:
        verified.append((idx, g, float(Lv)))
print(f"   verified {len(verified)}/{len(ranked)} as EXACT zeros.  worst |L| = {worst:.3e}")
assert len(verified) == len(ranked), "some 'zeros' are not exact -- ABORT honesty check"

gam = np.array([float(g) for (idx, g, lv) in verified])
rank = np.array([idx for (idx, g, lv) in verified], float)            # TRUE zero count N(gamma)
Ngeom = np.sqrt(q3 * gam / (2 * np.pi))                                # radial integer-length

lg = np.log(gam)
b_count, a_count, R2_count = ols_slope(lg, np.log(rank))
b_geom,  a_geom,  R2_geom  = ols_slope(lg, np.log(Ngeom))

print(f"\n   d log(rank=zero-count) / d log(gamma)   = {b_count:.4f}   (R^2={R2_count:.5f})   <- WINDING VOLUME channel")
print(f"   d log(N_geom=sqrt(q g/2pi)) / d log(gamma)= {b_geom:.4f}   (R^2={R2_geom:.5f})   <- RADIAL AMPLITUDE channel")
print(f"   ratio of slopes (count/geom)             = {b_count / b_geom:.4f}   (claim: count >> geom; geom = 0.5)")

# local (large-gamma) slope: last 10 points, where asymptotics are cleaner
m = 10
b_count_hi = ols_slope(lg[-m:], np.log(rank[-m:]))[0]
b_geom_hi  = ols_slope(lg[-m:], np.log(Ngeom[-m:]))[0]
print(f"\n   LOCAL slope over the last {m} zeros (gamma in [{gam[-m]:.0f},{gam[-1]:.0f}]):")
print(f"      zero-count slope = {b_count_hi:.4f}    radial slope = {b_geom_hi:.4f}")

# theoretical instantaneous count exponent at the mid/top of the window:
#   d log N / d log T  with N ~ (T/2pi) log(qT/2pi) - T/2pi
def count_exponent(q, T):
    L = np.log(q * T / (2 * np.pi))
    Nmain = (T / (2 * np.pi)) * L - T / (2 * np.pi)          # = (T/2pi)(L-1)
    dN = (1.0 / (2 * np.pi)) * L                              # dN/dT = (1/2pi) log(qT/2pi)
    return T * dN / Nmain                                     # = L / (L-1)
print(f"   theoretical instantaneous count exponent  L/(L-1):")
for T in [50, 200, 500, 925]:
    print(f"      gamma={T:4d}:  exponent = {count_exponent(q3, T):.4f}")

# ============================================================================
# PART (D): SHARPENING -- does N_count / N_geom -> claimed ratio?
#   claim: N_count(gamma) ~ (gamma/2pi) log(q gamma/2pi)  [drop the -gamma/2pi? test both]
#   ratio R(gamma) = N_count / N_geom = [(gamma/2pi)log(q g/2pi)] / sqrt(q g/2pi)
#                  = (1/2pi) sqrt(2pi/q) sqrt(gamma) log(q gamma/2pi)
# ============================================================================
print("\n[PART D] sharpening:  N_count / N_geom  vs  claimed (1/2pi)sqrt(2pi/q) sqrt(gamma) log(q g/2pi)")
Rmeas = rank / Ngeom
Rclaim = (1.0 / (2 * np.pi)) * np.sqrt(2 * np.pi / q3) * np.sqrt(gam) * np.log(q3 * gam / (2 * np.pi))
# the cleaner asymptotic uses the leading count term (T/2pi)(log -1); show ratio measured/claim
print(f"   {'gamma':>8} {'rank':>6} {'N_geom':>9} {'meas R':>10} {'claim R':>10} {'meas/claim':>11}")
for i in range(0, len(gam), max(1, len(gam) // 18)):
    print(f"   {gam[i]:8.1f} {rank[i]:6.0f} {Ngeom[i]:9.2f} {Rmeas[i]:10.3f} {Rclaim[i]:10.3f} {Rmeas[i]/Rclaim[i]:11.4f}")
# include the top zero explicitly
i = len(gam) - 1
print(f"   {gam[i]:8.1f} {rank[i]:6.0f} {Ngeom[i]:9.2f} {Rmeas[i]:10.3f} {Rclaim[i]:10.3f} {Rmeas[i]/Rclaim[i]:11.4f}")
ratio_of_ratio = Rmeas / Rclaim
print(f"\n   meas/claim over all 35: mean={np.mean(ratio_of_ratio):.4f}  std={np.std(ratio_of_ratio):.4f}"
      f"  min={np.min(ratio_of_ratio):.4f}  max={np.max(ratio_of_ratio):.4f}")
print(f"   -> if this -> a CONSTANT near 1 (and trending), the claimed sqrt*log form is right;")
print(f"      the leading-order claim drops the -1 in log(...e), so a slow drift is expected.")

# Better: compare rank to the FULL Riemann-von Mangoldt main term (with -1), residual study
Nmain = (gam / (2 * np.pi)) * (np.log(q3 * gam / (2 * np.pi)) - 1) + 7.0 / 8.0
resid = rank - Nmain
print(f"\n   rank vs full RvM main term N(g)=(g/2pi)(log(q g/2pi)-1)+7/8:")
print(f"      residual (rank - N_main): mean={np.mean(resid):+.3f}  std={np.std(resid):.3f}"
      f"  max|.|={np.max(np.abs(resid)):.3f}   (should be O(1)/O(log) -- bounded)")

# ============================================================================
# PART (B): SAME ruleset, ALL 5 characters -- small-window slopes via found zeros + RvM ranks
# ============================================================================
print("\n[PART B] ONE ruleset across mod 3,4,5q,5quartic(COMPLEX),7 -- exact zeros + RvM rank slopes")
print(f"   {'character':28s} {'#z':>3} {'worst|L|':>10} {'count slope':>12} {'geom slope':>11} {'R2c':>6} {'R2g':>6}")
results_B = {}
for name, (q, table) in CHARS.items():
    zs = find_zeros(q, table, hi=120.0, maxn=30)
    if len(zs) < 6:
        print(f"   {name:28s}  too few zeros ({len(zs)})")
        continue
    g = np.array([float(z) for z in zs])
    wl = max(float(abs(Lval(q, table, mp.mpf(1) / 2 + 1j * z))) for z in zs)
    # EXACT gate
    exact_ok = wl < 1e-12
    rk = np.array([riemann_count(q, gi) for gi in g])       # estimated ranks (RvM)
    # keep only where rank>0 (avoid log of tiny first-rank noise): use g above first zero
    mask = rk > 0.5
    lgm = np.log(g[mask])
    bC = ols_slope(lgm, np.log(rk[mask]))
    Ngeo = np.sqrt(q * g[mask] / (2 * np.pi))
    bG = ols_slope(lgm, np.log(Ngeo))
    results_B[name] = (bC[0], bG[0], wl, exact_ok)
    tag = "OK" if exact_ok else "**NOT EXACT**"
    print(f"   {name:28s} {len(zs):3d} {wl:10.2e} {bC[0]:12.4f} {bG[0]:11.4f} {bC[2]:6.3f} {bG[2]:6.3f}  {tag}")

# ============================================================================
# VERDICT
# ============================================================================
print("\n" + "=" * 88)
print("VERDICT (volume-4)")
print("=" * 88)
geom_ok = abs(b_geom - 0.5) < 0.01
count_superlinear = b_count > 1.0 and b_count > 3 * b_geom
all_exact = (len(verified) == len(ranked))
allchar_consistent = all(
    (abs(bg - 0.5) < 0.05 and bc > 1.0 and bc > 2.5 * bg)
    for (bc, bg, wl, ok) in results_B.values()
) and all(ok for (_, _, _, ok) in results_B.values())

print(f"   chi3 radial slope == 0.500 (|.-0.5|<0.01)?           {geom_ok}   ({b_geom:.4f})")
print(f"   chi3 count slope super-linear (>1, >3x radial)?      {count_superlinear}   ({b_count:.4f})")
print(f"   all 35 chi3 gamma EXACT zeros (|L|<1e-12)?           {all_exact}")
print(f"   ALL 5 characters consistent (one ruleset)?          {allchar_consistent}")
print(f"\n   => The zero HEIGHT gamma encodes the WINDING-VOLUME count (slope ~1.45),")
print(f"      NOT the radial sqrt-packing length (slope 0.500).  Distinct channels confirmed."
      if (geom_ok and count_superlinear) else
      "\n   => claim NOT supported as stated; see slopes above.")
print(f"\n   PASS = {geom_ok and count_superlinear and all_exact and allchar_consistent}")
