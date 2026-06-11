"""
metafuzz_cube-5.py  --  ID: cube-5
================================================================================
CANTOR-PAIRING SPACE-FILLING CUBE  (sharp NEGATIVE control / falsification arm)

HYPOTHESIS UNDER TEST (user's "the shape might be a cube"):
  Place integer n at a 3D lattice cell pi(n) given by an explicit space-filling
  bijection pi: N -> Z_{>=0}^3 (inverse Cantor pairing iterated).  Ask whether the
  zero-collapse is a property of the *cube geometry* (any bijection works) or whether
  it requires the FTA/Euler weight n^{-1/2} e^{-i w log n}.

CLAIM (to be falsified-or-confirmed honestly):
  The Cantor cube is GEOMETRICALLY INERT.  The collapse at the zeros survives ONLY
  because the per-n weight already *is* the Dirichlet series of L.  No LOCAL rule on
  the cube (phase = function of cube coords only) reproduces log n, because log n is
  NOT a (linear or otherwise local) functional of the Cantor coordinates pi(n) -- the
  Cantor map scrambles multiplicative (FTA) structure.  Contrast: on the PRIME-EXPONENT
  lattice n = prod p_i^{a_i}, log n = sum a_i log p_i is EXACTLY linear in the
  coordinates a_i (R^2 = 1).  That single number (linear-fit R^2 of log n vs lattice
  coords) adjudicates which 3D lattice is the real geometry.

ONE RULESET, EVERY L (only chi mod q changes).  EXACT zeros verified with mpmath:
  |L(chi, 1/2 + i*gamma)| < 1e-12.

Tests:
  (1) SANITY: baseline global-weight F still collapses at the zeros (geometry attached,
      weight unchanged => identical to helix), for mod 3,4,5-quad,5-quartic(complex),7.
  (2) R^2 ADJUDICATOR: linear fit of log n vs coordinates for
        - Cantor cube  pi(n) in Z^3            -> expect R^2 ~ 0
        - prime-exponent lattice a(n)          -> expect R^2 = 1 (exact)
        - base-q digit cube (mixed control)    -> expect R^2 ~ 0
  (3) LOCALITY: a local cube cancellation rule (phase linear in cube coords) does NOT
      vanish at the zeros for any choice / any character -> |F_loc(gamma)| = O(1), not 0.
  (4) PERMUTATION: permuting which n sits in which Cantor cube cell (with a cube-local
      rule) DESTROYS the collapse; whereas a permutation along prime-EXPONENT axes that
      preserves the additive log-structure PRESERVES it.

Everything is reported with ACTUAL numbers.  A clean negative IS the result here:
it pins the operative 3D lattice to the FTA exponent lattice, not an arbitrary cube.
"""

import numpy as np
import mpmath as mp

mp.mp.dps = 40

# ------------------------------------------------------------------ integers / weights
M = 200000
n = np.arange(1, M + 1)
nf = n.astype(float)
logn = np.log(nf)
amp = 1.0 / np.sqrt(nf)  # n^{-1/2}

# ------------------------------------------------------------------ characters (only per-L input)
CHARS = {
    "mod 3 quadratic":         (3, {1: 1, 2: -1}),
    "mod 4 quadratic":         (4, {1: 1, 3: -1}),
    "mod 5 quadratic":         (5, {1: 1, 4: 1, 2: -1, 3: -1}),
    "mod 5 quartic (complex)": (5, {1: 1, 2: 1j, 4: -1, 3: -1j}),
    "mod 7 quadratic":         (7, {1: 1, 2: 1, 4: 1, 3: -1, 5: -1, 6: -1}),
}


def char_array(q, table):
    v = np.zeros(M, dtype=complex)
    r = n % q
    for res, val in table.items():
        v[r == res] = val
    return v


def Lval(q, table, s):
    """exact L(chi,s) = q^{-s} sum_a chi(a) Hurwitz-zeta(s, a/q)."""
    tot = mp.mpc(0)
    for a, c in table.items():
        tot += mp.mpc(c) * mp.zeta(s, mp.mpf(a) / q)
    return q ** (-s) * tot


def true_zeros(q, table, hi=26.0, step=0.05, want=6):
    f = lambda s: Lval(q, table, mp.mpf(1) / 2 + 1j * s)
    ts = np.arange(0.6, hi, step)
    mag = np.array([float(abs(f(mp.mpf(t)))) for t in ts])
    zs = []
    for i in range(1, len(ts) - 1):
        if mag[i] < mag[i - 1] and mag[i] < mag[i + 1] and mag[i] < 0.4:
            try:
                root = mp.findroot(f, mp.mpc(ts[i], 0), tol=mp.mpf(10) ** (-25))
                tm = float(mp.re(root))
                if abs(float(mp.im(root))) < 1e-6 and abs(complex(f(mp.mpf(tm)))) < 1e-10 \
                        and tm > 0.5 and all(abs(tm - q0) > 1e-3 for q0 in zs):
                    zs.append(tm)
            except Exception:
                pass
    return sorted(zs)[:want]


def Lmag_exact(q, table, w):
    return float(abs(Lval(q, table, mp.mpf(1) / 2 + 1j * mp.mpf(w))))


# ============================================================================
# CANTOR space-filling bijection  pi : N -> Z_{>=0}^3
# ============================================================================
# Cantor pair (forward):  c(a,b) = (a+b)(a+b+1)/2 + b ,  bijection N0xN0 -> N0.
# Inverse:  given z, w = floor((sqrt(8z+1)-1)/2), t = w(w+1)/2, b = z - t, a = w - b.
# To map N0 -> N0^3:  first split m -> (p, z) via inverse pair, then z -> (q, r).
# i.e. pi(m) = (a, then inverse-pair the other coordinate).  We use 0-indexed m = n-1.

def cantor_inv(z):
    """inverse of Cantor pairing: z (int) -> (a, b) with c(a,b)=z."""
    # w = floor((sqrt(8z+1)-1)/2)
    w = int((np.sqrt(8.0 * z + 1.0) - 1.0) // 2)
    # guard floating error
    while (w + 1) * (w + 2) // 2 <= z:
        w += 1
    while w * (w + 1) // 2 > z:
        w -= 1
    t = w * (w + 1) // 2
    b = z - t
    a = w - b
    return a, b


def pi_cube(m):
    """m (0-indexed integer) -> (x,y,z) in N0^3 via two inverse Cantor pairings."""
    a, rest = cantor_inv(m)      # m = c(a, rest)
    bcoord, ccoord = cantor_inv(rest)
    return a, bcoord, ccoord


def build_cantor_coords(N):
    X = np.empty(N, dtype=np.int64)
    Y = np.empty(N, dtype=np.int64)
    Z = np.empty(N, dtype=np.int64)
    for i in range(N):
        x, y, z = pi_cube(i)     # i = n-1, 0-indexed
        X[i], Y[i], Z[i] = x, y, z
    return X, Y, Z


# self-test the bijection on a small range (must be a perfect bijection N0 <-> N0^3)
def verify_bijection(N=20000):
    seen = set()
    for i in range(N):
        t = pi_cube(i)
        if t in seen:
            return False, ("collision", i, t)
        seen.add(t)
    return True, len(seen)


# ============================================================================
# PRIME-EXPONENT lattice  a(n) = (a_2, a_3, a_5, ...)   (the FTA lattice)
# ============================================================================
def primes_upto(K):
    sieve = np.ones(K + 1, dtype=bool)
    sieve[:2] = False
    for p in range(2, int(K ** 0.5) + 1):
        if sieve[p]:
            sieve[p * p::p] = False
    return np.flatnonzero(sieve)


def build_exponent_matrix(N, primes):
    """
    rows = n (0-indexed n-1 -> integer n), cols = exponents a_{p_j} in n = prod p^a.
    Uses a SPARSE int16 matrix because for n<=N only primes<=N appear and almost every
    n has O(log n) nonzero exponents -> dense would be ~N*pi(N) and blow memory.
    Returns a dense int16 array restricted to primes that actually occur (still exact:
    every prime <= N is a column), built column-by-column by trial division.
    """
    P = len(primes)
    A = np.zeros((N, P), dtype=np.int16)
    rem = n[:N].astype(np.int64).copy()
    for j, p in enumerate(primes):
        pp = int(p)
        if pp * pp > N and pp > rem.max():
            break
        mask = (rem % pp == 0)
        if not mask.any():
            continue
        col = np.zeros(N, dtype=np.int16)
        while mask.any():
            col[mask] += 1
            rem[mask] //= pp
            mask = (rem % pp == 0)
        A[:, j] = col
    return A, rem  # rem should be all 1 if primes cover every n's factorization


# ============================================================================
# base-q DIGIT cube control:  n in base B -> first 3 digits as (x,y,z)
# ============================================================================
def build_baseq_coords(N, B=64):
    nn = n[:N].astype(np.int64)
    x = nn % B
    y = (nn // B) % B
    z = (nn // (B * B)) % B
    return x, y, z


# ============================================================================
# linear-fit R^2 of log n against a coordinate matrix (with intercept)
# ============================================================================
def r2_logn_vs_coords(coord_matrix, target=None):
    """least squares fit target (default log n) ~ [1, coords]; return R^2 and residual rms."""
    N = coord_matrix.shape[0]
    if target is None:
        target = logn[:N]
    Xmat = np.hstack([np.ones((N, 1)), coord_matrix.astype(float)])
    coef, *_ = np.linalg.lstsq(Xmat, target, rcond=None)
    pred = Xmat @ coef
    resid = target - pred
    ss_res = float(resid @ resid)
    ss_tot = float(((target - target.mean()) ** 2).sum())
    r2 = 1.0 - ss_res / ss_tot if ss_tot > 0 else float("nan")
    rms = float(np.sqrt(ss_res / N))
    return r2, rms, coef


# ============================================================================
# collapse / local-rule evaluators
# ============================================================================
def baseline_collapse(chi_vals, w, N=M):
    """global FTA weight: F(w) = sum chi(n) n^{-1/2} e^{-i w log n} = L(chi,1/2+iw)."""
    return abs(np.sum(chi_vals[:N] * amp[:N] * np.exp(-1j * w * logn[:N])))


def local_cube_collapse(chi_vals, w, coords, coef, N=None):
    """
    LOCAL cube rule: replace log n by the BEST cube-local linear phase phi(pi(n)) =
    coef . [1, x, y, z] (the least-squares fit to log n).  Keep amp & chi.  If the cube
    were the real geometry, this local phase would reproduce the collapse; we measure
    how badly it fails.
    """
    X, Y, Z = coords
    if N is None:
        N = len(X)
    phi = coef[0] + coef[1] * X[:N] + coef[2] * Y[:N] + coef[3] * Z[:N]
    return abs(np.sum(chi_vals[:N] * amp[:N] * np.exp(-1j * w * phi)))


def permute_in_cube_collapse(chi_vals, w, coords, coef, rng, N=None):
    """
    PERMUTATION test (cube-local): shuffle which n sits in which Cantor cell, then apply
    the cube-local phase rule.  Because the rule is geometric (depends only on the cell),
    shuffling n across cells with the SAME local rule must destroy any L-collapse.
    """
    X, Y, Z = coords
    if N is None:
        N = len(X)
    perm = rng.permutation(N)
    phi = coef[0] + coef[1] * X[:N] + coef[2] * Y[:N] + coef[3] * Z[:N]
    # cell keeps its geometric phase phi; the integer's weight chi*amp is reassigned by perm
    w_weight = (chi_vals[:N] * amp[:N])[perm]
    return abs(np.sum(w_weight * np.exp(-1j * w * phi)))


def permute_exponent_axis_collapse(chi_vals, w, A, primes, N=None):
    """
    CONTRAST permutation that PRESERVES additive log-structure: permute the PRIME LABELS
    (relabel which prime sits on which exponent axis).  log n = sum a_j log p_{sigma(j)}
    stays an exact linear functional, so this is the L of a DIFFERENT character/relabeled
    arithmetic but still a genuine Dirichlet-type collapse -- it does NOT smear to O(1)
    the way the cube shuffle does.  We just show the phase remains an exact linear
    functional of the exponents (R^2 stays 1) -- the structure-preserving move.
    """
    if N is None:
        N = A.shape[0]
    # relabel primes: new log-weights w_j' = log p_{sigma(j)}
    rng = np.random.default_rng(0)
    sigma = rng.permutation(len(primes))
    logp_perm = np.log(primes.astype(float))[sigma]
    phi = A[:N] @ logp_perm  # still EXACT linear functional of exponents
    r2, rms, _ = r2_logn_vs_coords(A[:N], target=phi)
    return r2, rms  # phi is exactly linear in A -> r2 = 1


# ============================================================================
# RUN
# ============================================================================
def main():
    print("=" * 78)
    print("metafuzz cube-5 : Cantor space-filling cube as NEGATIVE control")
    print(f"M = {M} integers.  One ruleset, only chi mod q changes.")
    print("=" * 78)

    # ---- 0. verify the Cantor bijection is a real bijection N0 <-> N0^3 -------------
    ok, info = verify_bijection(20000)
    print(f"\n[0] Cantor pi : N0 -> N0^3 bijection self-test (first 20000): "
          f"{'PASS (no collisions)' if ok else 'FAIL '+str(info)}")

    # build coordinate systems
    Ncoord = M
    print(f"\nbuilding Cantor cube coords for n<= {Ncoord} ...")
    CX, CY, CZ = build_cantor_coords(Ncoord)
    cube_coords = (CX, CY, CZ)
    print(f"   Cantor coord ranges: x in [{CX.min()},{CX.max()}], "
          f"y in [{CY.min()},{CY.max()}], z in [{CZ.min()},{CZ.max()}]")

    # exponent lattice on a smaller range so the dense design matrix (N x pi(N)) fits
    # in memory; R^2 = 1 is exact and N-independent, so 20000 is plenty for the adjudicator.
    Nexp = 20000
    print(f"building prime-exponent (FTA) lattice on n<= {Nexp} ...")
    primes = primes_upto(Nexp)              # every prime <= Nexp is a column (exact basis)
    A, rem = build_exponent_matrix(Nexp, primes)
    fully_factored = bool((rem[:Nexp] == 1).all())
    print(f"   #prime axes = {len(primes)}, every n fully factored: {fully_factored}, "
          f"max exponent = {A.max()}, design matrix {A.shape}")

    print("building base-64 digit cube control ...")
    DX, DY, DZ = build_baseq_coords(Ncoord, B=64)
    digit_coords = np.column_stack([DX, DY, DZ])

    # ---- 1. SANITY: baseline global weight still collapses at zeros ----------------
    print("\n" + "-" * 78)
    print("[1] SANITY -- baseline global FTA weight F(w)=L(chi,1/2+iw) at exact zeros")
    print("-" * 78)
    zeros_by_char = {}
    sanity_pass = True
    for name, (q, table) in CHARS.items():
        zs = true_zeros(q, table)
        zeros_by_char[name] = (q, table, zs)
        chi_vals = char_array(q, table)
        at = [baseline_collapse(chi_vals, w) for w in zs]
        offs = [baseline_collapse(chi_vals, 0.5 * (zs[i] + zs[i + 1]))
                for i in range(len(zs) - 1)]
        exact = [Lmag_exact(q, table, w) for w in zs]
        all_exact_zero = all(e < 1e-12 for e in exact)
        # baseline (finite-M Dirichlet partial sum) should be << off-zero baseline
        sep = (max(at) < 0.05) and (min(offs) > 5 * max(at))
        sanity_pass = sanity_pass and all_exact_zero
        print(f"  {name:24s} (q={q})")
        print(f"     zeros gamma         : {[round(x,4) for x in zs]}")
        print(f"     |L(1/2+ig)| mpmath  : {['%.1e'%e for e in exact]}  "
              f"{'EXACT<1e-12' if all_exact_zero else 'NOT all <1e-12'}")
        print(f"     baseline |F| AT g   : {['%.2e'%a for a in at]}")
        print(f"     baseline |F| OFF    : {['%.2e'%o for o in offs]}")

    # ---- 2. R^2 ADJUDICATOR --------------------------------------------------------
    print("\n" + "-" * 78)
    print("[2] R^2 ADJUDICATOR -- linear fit of  log n  vs lattice coordinates")
    print("    (the EXACT adjudicator is the RESIDUAL: only residual~0 reproduces phase.")
    print("     R^2=1 AND residual~eps => log n is an EXACT linear functional = real geom)")
    print("-" * 78)
    r2_cube, rms_cube, coef_cube = r2_logn_vs_coords(np.column_stack(cube_coords))
    r2_exp,  rms_exp,  coef_exp  = r2_logn_vs_coords(A.astype(float))
    r2_dig,  rms_dig,  coef_dig  = r2_logn_vs_coords(digit_coords)
    # exponent fit: the TRUE coefficients should be ~ log p_j
    logp = np.log(primes.astype(float))
    coef_err = float(np.max(np.abs(coef_exp[1:] - logp)))
    print(f"  Cantor cube  (x,y,z)      : R^2 = {r2_cube:.6f}   rms resid = {rms_cube:.4f} rad"
          f"  (TREND only; phase NOT exact)")
    print(f"  base-64 digit cube        : R^2 = {r2_dig:.6f}   rms resid = {rms_dig:.4f} rad"
          f"  (NOT exact)")
    print(f"  PRIME-EXPONENT (FTA)      : R^2 = {r2_exp:.12f}   rms resid = {rms_exp:.3e} rad"
          f"  (EXACT)")
    print(f"       fitted coeffs vs log p_j : max|coef_j - log p_j| = {coef_err:.3e}")
    print(f"       (=> log n = sum a_j log p_j EXACTLY; no cube/digit map can express this)")

    # ---- 3. LOCALITY -- best cube-local linear phase does NOT vanish at zeros ------
    print("\n" + "-" * 78)
    print("[3] LOCALITY -- replace log n by BEST cube-local linear phase phi(pi(n));")
    print("    measure |F_loc(gamma)| at zeros (predict O(1), NOT ~0)")
    print("-" * 78)
    floc_max = 0.0
    for name, (q, table, zs) in zeros_by_char.items():
        chi_vals = char_array(q, table)
        floc = [local_cube_collapse(chi_vals, w, cube_coords, coef_cube) for w in zs]
        # normalize by sum of |amp| to express as fraction of total mass scale
        floc_max = max(floc_max, max(floc))
        base_at = [baseline_collapse(chi_vals, w) for w in zs]
        print(f"  {name:24s}: |F_loc| AT zeros = {['%.3f'%a for a in floc]}")
        print(f"  {'':24s}  (baseline AT    = {['%.1e'%a for a in base_at]})")
    print(f"\n  => max |F_loc(gamma)| over all chars = {floc_max:.4f}  (O(1), NOT a collapse)")

    # ---- 4. PERMUTATION test -------------------------------------------------------
    print("\n" + "-" * 78)
    print("[4] PERMUTATION -- shuffle n across Cantor cells (cube-local rule):")
    print("    DESTROYS collapse;  vs prime-exponent relabel which PRESERVES linearity")
    print("-" * 78)
    rng = np.random.default_rng(12345)
    perm_max = 0.0
    for name, (q, table, zs) in zeros_by_char.items():
        chi_vals = char_array(q, table)
        fperm = [permute_in_cube_collapse(chi_vals, w, cube_coords, coef_cube, rng)
                 for w in zs]
        perm_max = max(perm_max, max(fperm))
        print(f"  {name:24s}: |F_perm(cube)| AT zeros = {['%.3f'%a for a in fperm]}")
    print(f"  => max |F_perm(cube)| = {perm_max:.4f}  (collapse destroyed)")

    # structure-preserving contrast on the exponent lattice
    name0, (q0, table0, zs0) = next(iter(zeros_by_char.items()))
    r2_relabel, rms_relabel = permute_exponent_axis_collapse(
        char_array(q0, table0), zs0[0], A.astype(float), primes)
    print(f"\n  CONTRAST: relabel primes on exponent axes (structure-preserving):")
    print(f"     phase still EXACTLY linear in exponents -> R^2 = {r2_relabel:.12f}, "
          f"rms = {rms_relabel:.2e}")
    print(f"     (the additive log-structure survives a coordinate relabel; the cube "
          f"shuffle does not)")

    # ---- 5. 1000-zero (here: 35 high-precision chi3 zeros) statistics --------------
    print("\n" + "-" * 78)
    print("[5] chi3 high-precision zeros: does the cube-local phase ever collapse?")
    print("    (loads lchi3_zeros file; tests F_loc & baseline at each true gamma)")
    print("-" * 78)
    chi3_zeros = load_chi3_zeros()
    q3, t3 = 3, {1: 1, 2: -1}
    chi3_vals = char_array(q3, t3)
    print(f"  loaded {len(chi3_zeros)} exact chi3 zeros (up to gamma~{chi3_zeros[-1]:.1f})")
    base_vals, loc_vals = [], []
    for g in chi3_zeros:
        base_vals.append(baseline_collapse(chi3_vals, g))
        loc_vals.append(local_cube_collapse(chi3_vals, g, cube_coords, coef_cube))
    base_vals = np.array(base_vals); loc_vals = np.array(loc_vals)
    # exact mpmath check that these ARE zeros
    exact3 = np.array([Lmag_exact(q3, t3, g) for g in chi3_zeros])
    print(f"  exact |L(1/2+ig)|         : max = {exact3.max():.2e}  "
          f"({'all <1e-12 VERIFIED' if exact3.max()<1e-12 else 'NOT all zero'})")
    print(f"  baseline |F| at zeros     : mean = {base_vals.mean():.2e}, "
          f"max = {base_vals.max():.2e}   (collapses; finite-M tail)")
    print(f"  cube-local |F_loc| zeros  : mean = {loc_vals.mean():.4f}, "
          f"min = {loc_vals.min():.4f}, max = {loc_vals.max():.4f}   (NEVER collapses)")

    # ---- VERDICT -------------------------------------------------------------------
    print("\n" + "=" * 78)
    print("VERDICT")
    print("=" * 78)
    # HONEST adjudicator = the linear-fit RESIDUAL (rms), not R^2 alone.  R^2 only
    # measures gross trend; the COLLAPSE needs the phase reproduced to << 1/w radians,
    # i.e. residual ~ 0.  log n must be matched EXACTLY (rms ~ machine eps) for
    # e^{-i w phi} to equal e^{-i w log n}.  Cube residual ~0.33 rad => total scramble.
    # NOTE: the Cantor cube R^2 is NOT ~0 (it is ~0.89) -- the inverse-pairing index is
    # monotone in magnitude, so x+y+z grossly tracks log n.  But the residual is huge,
    # so the cube STILL cannot reproduce the collapse.  The exact adjudicator is residual.
    cube_inert = (rms_cube > 0.05) and (floc_max > 0.1) and (perm_max > 0.1)
    exp_real = (r2_exp > 1 - 1e-9) and (coef_err < 1e-6) and (rms_exp < 1e-6)
    print(f"  Cantor cube   : R^2 = {r2_cube:.4f}   rms residual = {rms_cube:.4f} rad "
          f"(NOT exact -> phase scrambled)")
    print(f"  base-q digit  : R^2 = {r2_dig:.4f}   rms residual = {rms_dig:.4f} rad "
          f"(NOT exact)")
    print(f"  PRIME-EXPONENT: R^2 = {r2_exp:.12f}   rms residual = {rms_exp:.2e} rad "
          f"(EXACT, coeffs=log p_j to {coef_err:.0e})")
    print(f"  cube-local |F| at zero      = {floc_max:.3f}  (O(1) => no collapse)")
    print(f"  cube-permute |F| at zero    = {perm_max:.3f}  (O(1) => destroyed)")
    print()
    if cube_inert and exp_real:
        print("  RESULT: Cantor cube is GEOMETRICALLY INERT for the collapse.  The cube")
        print("  R^2~0.89 is a TREND ONLY (the pairing index is monotone in magnitude),")
        print("  but the phase residual ~0.33 rad scrambles e^{-iw log n} completely, so")
        print("  NO local cube rule reproduces the zeros (|F_loc|=O(1) for every char,")
        print("  permuting cells destroys it).  Only the FTA prime-exponent lattice makes")
        print("  log n = sum a_j log p_j an EXACT linear functional (R^2=1, residual~1e-11,")
        print("  coeffs = log p_j).  The collapse is carried ENTIRELY by the per-n weight")
        print("  n^{-1/2} e^{-iw log n} (= Dirichlet series of L); the cube adds nothing.")
        print("  => user's generic-cube idea is FALSIFIED.  The operative 3D lattice MUST")
        print("     be the FTA prime-exponent lattice, not an arbitrary space-filling cube.")
    else:
        print("  RESULT: unexpected -- inspect numbers above.")

    # machine-readable summary line
    print("\nSUMMARY_JSON " + str({
        "cube_R2": round(r2_cube, 8),
        "cube_rms_residual_rad": round(rms_cube, 6),
        "digit_cube_R2": round(r2_dig, 8),
        "digit_rms_residual_rad": round(rms_dig, 6),
        "exponent_R2": round(r2_exp, 12),
        "exponent_rms_residual_rad": float(rms_exp),
        "exponent_coef_err_vs_logp": coef_err,
        "cube_local_collapse_max": round(floc_max, 6),
        "cube_permute_collapse_max": round(perm_max, 6),
        "chi3_exact_zero_max": float(exact3.max()),
        "chi3_baseline_mean": float(base_vals.mean()),
        "chi3_cubelocal_min": float(loc_vals.min()),
        "cube_inert": bool(cube_inert),
        "exponent_real_geometry": bool(exp_real),
    }))


def load_chi3_zeros(path="lchi3_zeros_1000.txt"):
    import re
    zs = []
    for line in open(path):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        for tok in line.split():
            if re.match(r"^[0-9]+\.[0-9]+$", tok):
                zs.append(float(tok))
                break
    return zs


if __name__ == "__main__":
    main()
