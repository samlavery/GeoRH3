"""
metafuzz_cube-1.py  --  HYPOTHESIS cube-1: PRIME-EXPONENT LATTICE ('cube' = N^infinity).

CLAIM (verbatim spec):
  Replace the helix/cone by the infinite integer lattice of prime-exponent vectors.
  Each integer n = prod_i p_i^{a_i} is the lattice point a(n)=(a_1,a_2,...) in Z_{>=0}^infinity,
  one axis per prime.  NO log in the geometry: coordinates are exponents a_i (pure integers, FTA).
  Axis i carries an intrinsic per-prime frequency f_i = log p_i (the ONLY place log enters: the
  external bridge wind n <-> n^{it}, exactly as RULE EIGHT permits).
  ONE universal cancellation rule, identical for every L:
      F(w) = sum_{lattice points a} chi(a) * exp(-(1/2 + i w) <a, f>)
  with <a,f> = sum_i a_i log p_i = log n  and  chi(a) = prod_i chi(p_i)^{a_i}.
  Because the phase is a LINEAR functional of the lattice coordinate (FTA bridge
  log(mn)=log m+log n  <=>  additivity of exponent vectors), summing the lattice geometric
  series per-axis reproduces the Euler product
      prod_p (1 - chi(p) p^{-1/2 - i w})^{-1} = L(chi, 1/2 + i w).
  Collapse F(w)=0 <=> w is a nontrivial zero height gamma.
  'Volume between cancellations' = #lattice points with <a,f> <= log N_AFE,
  N_AFE = sqrt(q*gamma/2pi).

This script TESTS that honestly.  It does NOT edit the baseline.

WHAT THIS IS, MATHEMATICALLY (stated up front so we don't fool ourselves):
  The lattice sum  sum_a chi(a) exp(-(1/2+iw)<a,f>)  is, by FTA, an EXACT REORDERING of the
  Dirichlet series  sum_{n>=1} chi(n) n^{-1/2-iw}.  So TEST 1 (it matches the baseline F to
  machine precision) is a TAUTOLOGY, not a discovery -- the two are literally the same sum
  reindexed (the chi(a) on a non-squarefree lattice point factorizes to chi(n), and exp(-(.)<a,f>)
  = n^{-(.)}).  The baseline already shows that Dirichlet series collapses at the gammas.
  The genuinely NEW content of cube-1, if any, is:
    (A) per-axis closure: does summing each prime axis as an independent geometric series and
        MULTIPLYING (the Euler product) give the SAME function as the additive lattice sum, and
        does the finite product vanish only at gamma?  -- This is the real Euler-product claim.
    (B) the VOLUME law: is gamma actually 'set by' a count of lattice points between zeros, i.e.
        does V(gamma) = #{a : <a,f> <= log sqrt(q gamma/2pi)} track the zero-counting law N(T)?
  Tests 1-2 are sanity/identity checks; tests 3-5 are where the hypothesis lives or dies.
"""

import numpy as np
import mpmath as mp

mp.mp.dps = 40

# ---------------------------------------------------------------------------
# Characters: the ONLY per-L input.  Identical ruleset otherwise.
# ---------------------------------------------------------------------------
CHARS = {
    "mod 3 quadratic":          (3, {1: 1, 2: -1}),
    "mod 4 quadratic":          (4, {1: 1, 3: -1}),
    "mod 5 quadratic":          (5, {1: 1, 4: 1, 2: -1, 3: -1}),
    "mod 5 quartic (complex)":  (5, {1: 1, 2: 1j, 4: -1, 3: -1j}),
    "mod 7 quadratic":          (7, {1: 1, 2: 1, 4: 1, 3: -1, 5: -1, 6: -1}),
}

# ---------------------------------------------------------------------------
# Exact L via Hurwitz zeta (same as baseline Lval); used for |L|<1e-12 checks.
# ---------------------------------------------------------------------------
def Lval(q, table, s):
    tot = mp.mpc(0)
    for a, c in table.items():
        tot += mp.mpc(c) * mp.zeta(s, mp.mpf(a) / q)
    return q ** (-s) * tot

def chi_of(table, q, n):
    """Completely multiplicative chi(n): chi(n)=0 if gcd(n,q)>1 else value of n mod q's coset."""
    r = n % q
    return complex(table.get(r, 0))

# ---------------------------------------------------------------------------
# THE CUBE-1 LATTICE SUM.
# Build it the lattice way: enumerate integers n<=M, factor each into exponent vector a(n),
# compute <a,f> = sum a_i log p_i (we verify this equals log n to machine precision),
# chi(a) = prod chi(p_i)^{a_i} (we verify this equals chi(n)).
# F(w) = sum_a chi(a) exp(-(1/2+iw)<a,f>).
# ---------------------------------------------------------------------------

def sieve_primes(limit):
    s = np.ones(limit + 1, dtype=bool)
    s[:2] = False
    for i in range(2, int(limit**0.5) + 1):
        if s[i]:
            s[i*i::i] = False
    return np.nonzero(s)[0]

def smallest_prime_factor(limit):
    spf = np.arange(limit + 1)
    for i in range(2, int(limit**0.5) + 1):
        if spf[i] == i:  # i is prime
            sel = np.arange(i*i, limit + 1, i)
            mask = spf[sel] == sel
            spf[sel[mask]] = i
    return spf

def factor_exponents(n, spf):
    """Return dict {prime: exponent} via repeated SPF division (pure-integer FTA)."""
    fac = {}
    while n > 1:
        p = int(spf[n])
        e = 0
        while n % p == 0:
            n //= p
            e += 1
        fac[p] = e
    return fac

def build_lattice(M, q, table):
    """
    Returns, for n=1..M:
      logn_lattice[n] = <a(n), f> built from exponent vector (NOT np.log(n))
      chi_lattice[n]  = prod chi(p)^{a_p} built multiplicatively (NOT table[n%q])
    so we can verify they equal the direct log(n) / chi(n) to machine precision.
    """
    spf = smallest_prime_factor(M)
    primes = sieve_primes(M)
    logp = {int(p): mp.log(int(p)) for p in primes}  # f_i = log p_i  (the ONLY log)

    logn_lat = np.zeros(M + 1)
    chi_lat = np.zeros(M + 1, dtype=complex)
    chi_lat[1] = 1.0
    logn_lat[1] = 0.0
    # per-prime chi value (chi at the prime axis generator)
    chi_p = {int(p): chi_of(table, q, int(p)) for p in primes}

    for n in range(2, M + 1):
        fac = factor_exponents(n, spf)
        # <a,f> = sum a_p * log p   -- assembled from integer exponents
        val = mp.mpf(0)
        c = 1.0 + 0.0j
        for p, e in fac.items():
            val += e * logp[p]
            c *= chi_p[p] ** e
        logn_lat[n] = float(val)
        chi_lat[n] = c
    return logn_lat, chi_lat

def F_lattice(w, sigma, logn_lat, chi_lat):
    """F(w) = sum_{n=2..M, n=1} chi(a) exp(-(sigma+iw)<a,f>).  Lattice-assembled."""
    nrange = np.arange(1, len(logn_lat))
    L = logn_lat[1:]
    c = chi_lat[1:]
    return np.sum(c * np.exp(-(sigma + 1j * w) * L))

def F_baseline(w, sigma, q, table, M):
    """Baseline helix F: chi(n) n^{-sigma} exp(-i w log n) with direct log(n)."""
    n = np.arange(1, M + 1)
    r = n % q
    chi = np.array([table.get(int(x), 0) for x in r], dtype=complex)
    logn = np.log(n.astype(float))
    return np.sum(chi * n.astype(float) ** (-sigma) * np.exp(-1j * w * logn))

# ---------------------------------------------------------------------------
# Euler-product (per-axis geometric series) closure.
# Each prime axis summed independently: geometric series in chi(p) p^{-(sigma+iw)} gives
# Euler factor  (1 - chi(p) p^{-(sigma+iw)})^{-1}.  Product over primes <= P.
# ---------------------------------------------------------------------------
def euler_product(w, sigma, q, table, P):
    primes = sieve_primes(P)
    prod = mp.mpc(1)
    s = mp.mpf(sigma) + 1j * mp.mpf(w)
    for p in primes:
        p = int(p)
        chip = chi_of(table, q, p)
        if chip == 0:
            continue
        factor = mp.mpc(1) / (mp.mpc(1) - mp.mpc(chip) * mp.mpf(p) ** (-s))
        prod *= factor
    return complex(prod)

# ---------------------------------------------------------------------------
# Load exact chi3 zeros from file.
# ---------------------------------------------------------------------------
def load_chi3_zeros(path):
    zeros = {}
    with open(path) as fh:
        for line in fh:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            parts = line.split()
            try:
                idx = int(parts[0])
                gamma = mp.mpf(parts[1])
            except (ValueError, IndexError):
                continue
            zeros[idx] = gamma
    return zeros

ZERO_FILE = "/Users/samuellavery/proof/three/numerics/lchi3_zeros_1000.txt"


def banner(s):
    print("\n" + "=" * 78)
    print(s)
    print("=" * 78)


# ===========================================================================
# TEST 1: lattice sum == baseline helix to machine precision (identity check)
# ===========================================================================
def test1(M=20000):
    banner("TEST 1: lattice sum reproduces baseline helix F (EXPECTED: identity, tautology)")
    print(f"M = {M} integers.  For each chi, compare F_lattice(w) vs F_baseline(w) at sample w.")
    ws = [3.0, 8.03973715568, 14.7, 25.1]
    worst_overall = 0.0
    for name, (q, table) in CHARS.items():
        logn_lat, chi_lat = build_lattice(M, q, table)
        # First verify the lattice ASSEMBLY equals direct values (FTA bridge sanity)
        n = np.arange(1, M + 1).astype(float)
        logn_direct = np.log(n)
        log_err = np.max(np.abs(logn_lat[1:] - logn_direct))
        chi_direct = np.array([table.get(int(x) % q, 0) for x in np.arange(1, M + 1)], dtype=complex)
        chi_err = np.max(np.abs(chi_lat[1:] - chi_direct))
        worst = 0.0
        for w in ws:
            a = F_lattice(w, 0.5, logn_lat, chi_lat)
            b = F_baseline(w, 0.5, q, table, M)
            worst = max(worst, abs(a - b))
        worst_overall = max(worst_overall, worst, log_err, chi_err)
        print(f"  {name:26s}: max|<a,f>-log n|={log_err:.2e}  "
              f"max|chi_lat-chi|={chi_err:.2e}  max|F_lat-F_base|={worst:.2e}")
    ok = worst_overall < 1e-6
    print(f"  => lattice == helix (FTA reordering): {'PASS' if ok else 'FAIL'}  "
          f"(worst {worst_overall:.2e})")
    return ok


# ===========================================================================
# TEST 2: |F(gamma)| -> 0 as M grows; |F(midpoint)| = O(1); cross-check mpmath |L|<1e-12
# ===========================================================================
def test2(zeros):
    banner("TEST 2: chi3 -- |F_lattice(gamma)|->0 as M grows; |F(midpoint)|=O(1); mpmath |L|<1e-12")
    q, table = 3, CHARS["mod 3 quadratic"][1]
    gammas = [float(zeros[i]) for i in range(1, 21)]
    print("  First 20 chi3 zeros.  mpmath |L(1/2+i gamma)| (EXACT zero check):")
    Lexact = [float(abs(Lval(q, table, mp.mpf(1)/2 + 1j * mp.mpf(zeros[i])))) for i in range(1, 21)]
    all_exact = all(e < 1e-12 for e in Lexact)
    print(f"    max mpmath |L| over 20 zeros = {max(Lexact):.2e}   "
          f"(<1e-12 ? {'YES' if all_exact else 'NO'})")

    Ms = [2000, 20000, 200000]
    print("\n  |F_lattice(gamma)| as M grows (should DECREASE; partial sum of conditionally-conv. series):")
    print(f"    {'gamma':>12s}", *[f"M={m:>7d}" for m in Ms])
    F_at_grows = []
    for g in gammas[:8]:
        row = []
        for M in Ms:
            logn_lat, chi_lat = build_lattice(M, q, table)
            row.append(abs(F_lattice(g, 0.5, logn_lat, chi_lat)))
        F_at_grows.append(row)
        print(f"    {g:12.5f}", *[f"{v:9.4f}" for v in row])

    # midpoints with biggest M
    M = 200000
    logn_lat, chi_lat = build_lattice(M, q, table)
    print(f"\n  AT zero vs OFF (midpoint), M={M}:")
    on_vals, off_vals = [], []
    for i in range(7):
        g = gammas[i]
        mid = 0.5 * (gammas[i] + gammas[i + 1])
        fon = abs(F_lattice(g, 0.5, logn_lat, chi_lat))
        foff = abs(F_lattice(mid, 0.5, logn_lat, chi_lat))
        on_vals.append(fon); off_vals.append(foff)
        print(f"    gamma={g:10.5f}  |F(gamma)|={fon:8.4f}   "
              f"mid={mid:10.5f}  |F(mid)|={foff:8.4f}   ratio off/on={foff/max(fon,1e-12):7.2f}")

    # Honest verdict: partial sums of L's Dirichlet series do NOT converge on the critical line
    # (the series sum chi(n)/sqrt(n) is only conditionally/Abel summable). So |F| at gamma does
    # not go to literally 0 -- it goes to |L(gamma)|=0's slowly-fluctuating partial sum. The
    # discriminating signal is on/off CONTRAST, not |F|->0.  We report both.
    mean_on = np.mean(on_vals); mean_off = np.mean(off_vals)
    contrast = mean_off / max(mean_on, 1e-12)
    decreasing = all(F_at_grows[k][0] >= F_at_grows[k][-1] for k in range(len(F_at_grows)))
    print(f"\n  mean |F(gamma)|={mean_on:.4f}  mean |F(mid)|={mean_off:.4f}  "
          f"off/on contrast={contrast:.2f}")
    print(f"  NOTE: exact zero is the mpmath |L|<1e-12 check (PASS={all_exact}); the truncated "
          f"lattice/helix\n        partial sum only DIPS at gamma (conditional convergence), it "
          f"is not literally 0.")
    return all_exact, contrast


# ===========================================================================
# TEST 3: per-axis closure -- Euler product == lattice sum == L; vanishes only at gamma
# ===========================================================================
def test3(zeros):
    banner("TEST 3: per-axis closure (Euler product) vs lattice sum vs exact L")
    q, table = 3, CHARS["mod 3 quadratic"][1]
    # On the critical line sigma=1/2 the Euler product DIVERGES (it converges only for sigma>1).
    # So the honest test of the per-axis geometric-series CLAIM is done where it converges:
    #   (a) sigma=1.5: Euler product == lattice Dirichlet sum == exact L  (machine precision)
    #   (b) report that on sigma=1/2 the product does NOT converge -> cannot 'vanish at gamma'
    #       as a convergent object; the analytic continuation (the L we test) does.
    print("  (a) Convergent regime sigma=1.5: Euler product == lattice sum == exact L ?")
    M = 200000
    logn_lat, chi_lat = build_lattice(M, q, table)
    for w in [0.0, 8.03973715568, 25.0]:
        ep = euler_product(w, 1.5, q, table, P=200000)
        ls = F_lattice(w, 1.5, logn_lat, chi_lat)
        Lx = complex(Lval(q, table, mp.mpf(3)/2 + 1j * mp.mpf(w)))
        print(f"    w={w:14.8f}: |Euler-L|={abs(ep-Lx):.2e}  |lattice-L|={abs(ls-Lx):.2e}")

    print("\n  (b) Critical line sigma=1/2: does the per-axis Euler PRODUCT converge / vanish at gamma?")
    print("      Partial Euler products prod_{p<=P}(1-chi(p)p^{-1/2-iw})^{-1}  at gamma_1 vs growing P:")
    g = float(zeros[1])
    prev = None
    for P in [100, 1000, 10000, 100000]:
        ep = euler_product(g, 0.5, q, table, P)
        print(f"      P={P:7d}: Euler partial = {ep.real:+.4f}{ep.imag:+.4f}i  |.|={abs(ep):8.4f}")
        prev = ep
    Lg = complex(Lval(q, table, mp.mpf(1)/2 + 1j * mp.mpf(g)))
    print(f"      exact L(1/2+i gamma) = {Lg.real:+.2e}{Lg.imag:+.2e}i  |L|={abs(Lg):.2e}  (the true 0)")
    print("      HONEST READ: the Euler product is divergent at sigma=1/2 (it does NOT close to 0).")
    print("      The vanishing at gamma is a property of the ANALYTIC CONTINUATION of the product,")
    print("      not of the per-axis geometric series summed on the line. So 'per-axis closure")
    print("      vanishes only at gamma' is FALSE as a convergent statement on sigma=1/2.")
    # success of (a):
    ep0 = euler_product(0.0, 1.5, q, table, P=200000)
    L0 = complex(Lval(q, table, mp.mpf(3)/2))
    return abs(ep0 - L0) < 1e-6


# ===========================================================================
# TEST 4: VOLUME LAW -- does #lattice points <= log N_AFE between zeros track N(T)?
# ===========================================================================
def test4():
    banner("TEST 4: VOLUME law  V(gamma)=#{n : log n <= log sqrt(q gamma/2pi)}  vs  N(T)")
    q = 3
    # We need CONSECUTIVE zeros for the gap regression. The file is sparse (1-20, then every 50th),
    # so generate consecutive chi3 zeros directly with mpmath findroot for solid statistics.
    print("  Generating consecutive chi3 zeros via mpmath (this is exact: each refined by findroot).")
    table = CHARS["mod 3 quadratic"][1]
    f = lambda s: Lval(q, table, mp.mpf(1)/2 + 1j * s)
    # scan for sign-pattern minima then findroot
    import time
    t0 = time.time()
    gammas = []
    t = mp.mpf("0.5")
    step = mp.mpf("0.04")
    prevmag = abs(f(t))
    going_down = False
    NMAX = 200
    while len(gammas) < NMAX and t < 350:
        t2 = t + step
        mag = abs(f(t2))
        if mag < prevmag:
            going_down = True
        else:
            if going_down:
                # local min near t; refine
                try:
                    root = mp.findroot(f, mp.mpc(float(t), 0), tol=mp.mpf(10)**(-25))
                    tm = mp.re(root)
                    if abs(mp.im(root)) < 1e-8 and abs(f(tm)) < 1e-12 and tm > 0.5 and \
                            (not gammas or abs(tm - gammas[-1]) > 1e-3):
                        gammas.append(tm)
                except Exception:
                    pass
            going_down = False
        prevmag = mag
        t = t2
    print(f"  Found {len(gammas)} consecutive exact zeros up to gamma={float(gammas[-1]):.2f} "
          f"in {time.time()-t0:.1f}s.")
    # verify they are exact
    maxL = max(float(abs(f(g))) for g in gammas)
    print(f"  max |L(1/2+i gamma)| over generated zeros = {maxL:.2e}  (<1e-12 ? "
          f"{'YES' if maxL < 1e-12 else 'NO'})")

    g = np.array([float(x) for x in gammas])

    # AFE radius:  N_AFE = sqrt(q gamma / 2pi).  Volume = #integers n <= N_AFE = floor(N_AFE).
    # (#{n : log n <= log N_AFE} = #{n <= N_AFE} = floor(N_AFE) -- pure integer count.)
    N_AFE = np.sqrt(q * g / (2 * np.pi))
    V = np.floor(N_AFE)  # integer count of lattice points in the L1 shell <a,f> <= log N_AFE

    # Zero-counting law N(T) ~ (T/2pi) log(qT/2pi) - T/2pi.  This is what gamma 'should' track.
    def Ncount(T):
        return (T / (2 * np.pi)) * np.log(q * T / (2 * np.pi)) - T / (2 * np.pi)
    Npred = Ncount(g)
    idx = np.arange(1, len(g) + 1)

    print("\n  (a) Does the cumulative count of zeros up to gamma match V(gamma)=floor(sqrt(q gamma/2pi))?")
    print("      i.e. is the 'volume' = the zero index?  (the hypothesis: gamma set by integers consumed)")
    print(f"      {'idx':>4s} {'gamma':>10s} {'N_AFE':>9s} {'V=floor':>8s} {'N(T) law':>9s} "
          f"{'V/idx':>7s} {'V/N(T)':>7s}")
    for k in list(range(0, 10)) + list(range(len(g)-5, len(g))):
        print(f"      {idx[k]:>4d} {g[k]:>10.4f} {N_AFE[k]:>9.3f} {int(V[k]):>8d} "
              f"{Npred[k]:>9.3f} {V[k]/idx[k]:>7.3f} {V[k]/Npred[k]:>7.3f}")

    # Regression 1: gamma vs V (area law claim gamma = (2pi/q) V^2 ?). By construction V=floor(sqrt(q g/2pi))
    # so g ~ (2pi/q) V^2 is TRUE BY DEFINITION of N_AFE -- report it but flag it's tautological.
    g_from_V = (2 * np.pi / q) * V**2
    rel_area = np.abs(g_from_V - g) / g
    print(f"\n  (b) area law gamma =? (2pi/q) V^2  [TAUTOLOGICAL: V:=floor(sqrt(q g/2pi))]: "
          f"max rel.err {np.max(rel_area):.3e}  (just floor rounding)")

    # Regression 2 (the REAL test): does V (volume) predict the ZERO INDEX (count of cancellations)?
    # Fit idx ~ a*V + b and also compare to N(T) law. The hypothesis 'iy = volume of integers
    # between cancellations' means consecutive-zero GAPS in gamma <-> equal increments of count.
    # Check: is dV (volume consumed between consecutive zeros) ~ constant, or ~ the spacing law?
    dV = np.diff(V)
    dgamma = np.diff(g)
    dN = np.diff(Npred)  # predicted #zeros per unit -- but consecutive zeros => dN ~ 1 by definition
    print(f"\n  (c) Volume consumed between consecutive zeros  dV = V(g_{{k+1}})-V(g_k):")
    print(f"      mean dV={np.mean(dV):.2f}  std dV={np.std(dV):.2f}  min={int(np.min(dV))} "
          f"max={int(np.max(dV))}   (is it ~constant?  CV={np.std(dV)/np.mean(dV):.3f})")
    print(f"      Pearson corr(dV, dgamma) = {np.corrcoef(dV, dgamma)[0,1]:.4f}   "
          f"(dV ~ dgamma * dN_AFE/dgamma; N_AFE=sqrt-shaped so this is mechanical)")
    # The substantive claim 'iy = volume between cancellations' -> V(gamma_k) ~ linear in k?
    A = np.vstack([V, np.ones_like(V)]).T
    coef, res, *_ = np.linalg.lstsq(A, idx, rcond=None)
    pred_idx = A @ coef
    ss_res = np.sum((idx - pred_idx)**2)
    ss_tot = np.sum((idx - np.mean(idx))**2)
    r2_lin = 1 - ss_res / ss_tot
    print(f"\n  (d) Is the zero INDEX (cancellation count) a LINEAR function of volume V?")
    print(f"      fit idx = {coef[0]:.5f} * V + {coef[1]:.3f} ;  R^2 = {r2_lin:.5f}")
    print(f"      But N(T) is super-linear (T log T), and V=floor(sqrt(qT/2pi)) ~ sqrt(T).")
    print(f"      So idx ~ N(T) ~ (q/2pi) V^2 log(...) -- index is ~V^2 log, NOT linear in V.")
    # Fit idx vs V with the actual law shape:  idx ~ c * V^2 * log(V) ?
    Vp = V[V > 1]
    idxp = idx[V > 1]
    feat = np.vstack([Vp**2 * np.log(Vp), Vp**2, Vp, np.ones_like(Vp)]).T
    c2, *_ = np.linalg.lstsq(feat, idxp, rcond=None)
    pred2 = feat @ c2
    r2_quad = 1 - np.sum((idxp - pred2)**2) / np.sum((idxp - np.mean(idxp))**2)
    print(f"      fit idx ~ c1 V^2 logV + c2 V^2 + c3 V + c4 : R^2 = {r2_quad:.6f}  "
          f"(c1={c2[0]:.4f})")
    print(f"      Theory: N(T)=(T/2pi)log(qT/2pi)-T/2pi, T=(2pi/q)V^2 => N ~ (V^2)(log V + const).")
    print(f"      Predicted leading coeff c1 = 2  (since (2pi/q)/(2pi)*2 from d/dV of V^2 logV... )")

    return r2_quad, np.std(dV)/np.mean(dV)


# ===========================================================================
# TEST 5: universality (all 5 chars) + FALSIFICATION (wrong frequencies must NOT collapse)
# ===========================================================================
def test5():
    banner("TEST 5: universality (all 5 chars, ONE rule) + falsification of wrong axis frequencies")
    M = 200000
    print("  (a) ONE rule, all 5 chars: lattice F dips at each char's exact zero, mpmath |L|<1e-12.")
    all_ok = True
    for name, (q, table) in CHARS.items():
        # find a couple of exact zeros for this char (small scan)
        f = lambda s: Lval(q, table, mp.mpf(1)/2 + 1j * s)
        ts = np.arange(0.6, 22.0, 0.05)
        mag = np.array([float(abs(f(mp.mpf(t)))) for t in ts])
        cand = []
        for i in range(1, len(ts) - 1):
            if mag[i] < mag[i-1] and mag[i] < mag[i+1] and mag[i] < 0.45:
                try:
                    root = mp.findroot(f, mp.mpc(ts[i], 0), tol=mp.mpf(10)**(-20))
                    tm = float(mp.re(root))
                    if abs(float(mp.im(root))) < 1e-6 and abs(complex(f(mp.mpf(tm)))) < 1e-10 \
                            and tm > 0.5 and all(abs(tm - z) > 1e-3 for z in cand):
                        cand.append(tm)
                except Exception:
                    pass
            if len(cand) >= 3:
                break
        cand = sorted(cand)[:3]
        logn_lat, chi_lat = build_lattice(M, q, table)
        Lexact = [float(abs(f(mp.mpf(z)))) for z in cand]
        Fon = [abs(F_lattice(z, 0.5, logn_lat, chi_lat)) for z in cand]
        Foff = [abs(F_lattice(0.5*(cand[i]+cand[i+1]), 0.5, logn_lat, chi_lat))
                for i in range(len(cand)-1)]
        exact_ok = all(e < 1e-12 for e in Lexact)
        # dip: each on-zero |F| markedly below neighbouring off |F|
        dip_ok = (len(Foff) > 0 and np.mean(Fon) < np.mean(Foff))
        all_ok = all_ok and exact_ok
        print(f"    {name:26s}: zeros {[round(z,4) for z in cand]}")
        print(f"        mpmath |L|: {['%.1e'%e for e in Lexact]}  (exact<1e-12 ? {exact_ok})")
        print(f"        |F(gamma)| : {[round(v,3) for v in Fon]}   "
              f"|F(mid)|: {[round(v,3) for v in Foff]}   dip ? {dip_ok}")

    # (b) FALSIFICATION: replace per-axis frequencies f_i=log p_i with WRONG ones; must NOT dip at gamma.
    print("\n  (b) FALSIFICATION: wrong axis frequencies f_i must NOT reproduce the collapse at gamma.")
    q, table = 3, CHARS["mod 3 quadratic"][1]
    g = 8.0397371556814666817  # chi3 gamma_1
    spf = smallest_prime_factor(M)
    primes = sieve_primes(M)
    chi_p = {int(p): chi_of(table, q, int(p)) for p in primes}

    def F_with_freq(freq_of_prime):
        """Rebuild lattice with arbitrary per-prime frequency f_p; F(g)=sum chi(a) exp(-(1/2+ig)<a,f>)."""
        # <a,f> = sum a_p f_p  ; amplitude exp(-1/2 <a,f>), phase exp(-i g <a,f>)
        tot = 0.0 + 0.0j
        for n in range(1, M + 1):
            if n == 1:
                tot += 1.0
                continue
            fac = factor_exponents(n, spf)
            val = 0.0
            c = 1.0 + 0.0j
            ok = True
            for p, e in fac.items():
                val += e * freq_of_prime[p]
                cp = chi_p[p]
                c *= cp ** e
            tot += c * np.exp(-(0.5 + 1j * g) * val)
        return abs(tot)

    logp_freq = {int(p): float(mp.log(int(p))) for p in primes}
    p_freq = {int(p): float(p) for p in primes}           # f_p = p (NOT log p)  -- wrong
    sqrtp_freq = {int(p): float(p)**0.5 for p in primes}   # f_p = sqrt p          -- wrong
    pidx_freq = {int(p): float(i + 1) for i, p in enumerate(primes)}  # f_p = prime index -- wrong

    base = F_with_freq(logp_freq)
    print(f"    f_p = log p   (CORRECT bridge):  |F(gamma_1)| = {base:.4f}   <- should DIP (small)")
    for label, fr in [("f_p = p", p_freq), ("f_p = sqrt(p)", sqrtp_freq),
                      ("f_p = prime index", pidx_freq)]:
        v = F_with_freq(fr)
        print(f"    {label:22s}:  |F(gamma_1)| = {v:.4f}   "
              f"<- should NOT dip (>> {base:.3f} ?  {'OK' if v > 5*base else 'NO-DISTINCTION'})")
    # also scramble exponents->coordinates? skip; frequency test is the cleanest.
    return all_ok


# ===========================================================================
if __name__ == "__main__":
    print(__doc__)
    zeros = load_chi3_zeros(ZERO_FILE)

    r1 = test1(M=20000)
    exact_ok, contrast = test2(zeros)
    r3 = test3(zeros)
    r2_quad, cv_dV = test4()
    r5 = test5()

    banner("SUMMARY (brutally honest)")
    print(f"  T1 lattice==helix (FTA reorder, tautology) : {'PASS' if r1 else 'FAIL'}")
    print(f"  T2 exact zeros (mpmath |L|<1e-12)          : {'PASS' if exact_ok else 'FAIL'}; "
          f"on/off contrast {contrast:.2f} (partial sum DIPS, not ->0)")
    print(f"  T3 Euler product == L (sigma=1.5 conv.)    : {'PASS' if r3 else 'FAIL'}; "
          f"on sigma=1/2 product DIVERGES (no convergent vanishing)")
    print(f"  T4 volume law: idx ~ V^2 logV              : R^2={r2_quad:.5f}; dV CV={cv_dV:.3f} "
          f"(dV NOT constant => gamma NOT a constant-volume count)")
    print(f"  T5 universality (5 chars, exact)           : {'PASS' if r5 else 'FAIL'} + "
          f"frequency falsification reported above")
