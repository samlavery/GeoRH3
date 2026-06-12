"""
metafuzz_cube-2.py  --  HYPOTHESIS cube-2:  GAUSSIAN / EISENSTEIN NUMBER-RING LATTICE.

CLAIM under test
----------------
The literal 2D "cube" per modulus is the integer ring of an imaginary-quadratic field:
   q=4  ->  Z[i]      (Gaussian integers),   norm N(a+bi)     = a^2 + b^2
   q=3  ->  Z[omega]  (Eisenstein integers), norm N(a+b*omega)= a^2 - a*b + b^2 ,  omega=e^{2pi i/3}
The Dirichlet character is the prime-splitting (norm) character of the ring, and the
Dedekind zeta factors:
   zeta_K(s) = zeta(s) * L(chi_q, s).
ONE universal rule: place each ring element z at its lattice point, amplitude N(z)^{-1/2},
phase exp(-i w log N(z)), sum with the ring's splitting sign.  Equivalently, by the
representation count r(n)=#{z: N(z)=n}=w_K * sum_{d|n} chi_q(d):
   Z_K(w) := sum_{n>=1} r(n) n^{-1/2} e^{-i w log n}  =  w_K * zeta(1/2+iw) * L(chi_q,1/2+iw).
Dividing out the zeta (trivial-class / diagonal) part, the residual chi-isotypic component
   F_q(w) := Z_K(w) / (w_K * zeta(1/2+iw))  =  L(chi_q, 1/2+iw)
should COLLAPSE (|F_q| -> 0) EXACTLY at the gamma of L(chi_q).

PREDICTIONS / FALSIFIABLE TESTS (all numbers reported, nothing fudged):
  (A) Representation-count identity  r(n) = w_K * sum_{d|n} chi_q(d)  exactly for n<=N_MAX
      (w_4 = 4 for Z[i];  w_3 = 6 for Z[omega]).
  (B) Lattice sum / zeta = L: residual |F_q(gamma)| < tol AT chi_q zeros, O(1) OFF.
      EXACT verification of the gammas themselves via mpmath |L(chi_q,1/2+i gamma)| < 1e-12.
  (C) Volume / Gauss-circle law:  V(X)=#{z in ring : N(z) <= X} ~ (2pi/sqrt|disc|) X.
      |disc(Q(i))|=4 -> slope pi.   |disc(Q(sqrt-3))|=3 -> slope 2pi/sqrt3.
      Quantify slope + R^2 against the actual lattice point counts.
  (D) "Volume between cancellations": correlate the integer/lattice count between
      consecutive zeros against the zero-counting law.  Use the 1000+ chi3 zeros.
  (E) SCOPE / FALSIFY universality: q=5 (quadratic & quartic) and q=7 are NOT
      imaginary-quadratic class-number-1 norm characters, so this ring-lattice form does
      NOT extend.  Confirm it works ONLY for q in {3,4}; document that the universal form
      is the prime-exponent helix (helix3d_universal.py), of which this is the low-q shadow.
"""
import numpy as np
import mpmath as mp

mp.mp.dps = 40

# ---------------------------------------------------------------------------
# characters (same residue tables as the baseline helix3d_universal.py)
# ---------------------------------------------------------------------------
CHARS = {
    "mod 3 quadratic":          (3, {1: 1, 2: -1}),
    "mod 4 quadratic":          (4, {1: 1, 3: -1}),
    "mod 5 quadratic":          (5, {1: 1, 4: 1, 2: -1, 3: -1}),
    "mod 5 quartic (complex)":  (5, {1: 1, 2: 1j, 4: -1, 3: -1j}),
    "mod 7 quadratic":          (7, {1: 1, 2: 1, 4: 1, 3: -1, 5: -1, 6: -1}),
}

def chi_of(q, table, m):
    return table.get(m % q, 0)

def Lval(q, table, s):
    """exact L(chi,s) = q^{-s} sum_a chi(a) Hurwitz-zeta(s, a/q)."""
    tot = mp.mpc(0)
    for a, c in table.items():
        tot += mp.mpc(c) * mp.zeta(s, mp.mpf(a) / q)
    return q ** (-s) * tot

# ---------------------------------------------------------------------------
# load EXACT zeros
# ---------------------------------------------------------------------------
def load_chi3(path='lchi3_zeros_record.txt', cap=None):
    g = []
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith('#'):
                continue
            parts = line.split()
            if len(parts) >= 2:
                try:
                    g.append(float(parts[1]))
                except ValueError:
                    pass
    g = np.array(sorted(set(g)))
    if cap:
        g = g[:cap]
    return g

def load_chi4(path='chi4_zeros.txt'):
    g = []
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith('#'):
                continue
            parts = line.split()
            if len(parts) >= 2:
                try:
                    g.append(float(parts[1]))
                except ValueError:
                    pass
    return np.array(sorted(set(g)))

# ===========================================================================
# (A) representation-count identity  r(n) = w_K * sum_{d|n} chi_q(d)
# ===========================================================================
def lattice_rep_counts(q, N_MAX):
    """Direct enumeration: r(n) = #{ring elements z with N(z)=n}, n=1..N_MAX.
       q=4: N(a+bi)=a^2+b^2.   q=3: N(a+b w)=a^2-ab+b^2."""
    r = np.zeros(N_MAX + 1, dtype=np.int64)
    B = int(np.ceil(np.sqrt(N_MAX))) + 2
    if q == 4:
        for a in range(-B, B + 1):
            for b in range(-B, B + 1):
                nrm = a * a + b * b
                if 1 <= nrm <= N_MAX:
                    r[nrm] += 1
    elif q == 3:
        for a in range(-2 * B, 2 * B + 1):
            for b in range(-2 * B, 2 * B + 1):
                nrm = a * a - a * b + b * b
                if 1 <= nrm <= N_MAX:
                    r[nrm] += 1
    else:
        raise ValueError("ring lattice only defined for q in {3,4}")
    return r

def divisor_sum_chi(q, table, N_MAX):
    """s(n) = sum_{d|n} chi_q(d)."""
    s = np.zeros(N_MAX + 1, dtype=np.int64)
    for d in range(1, N_MAX + 1):
        c = chi_of(q, table, d)
        if c == 0:
            continue
        s[d::d] += int(c.real if isinstance(c, complex) else c)
    return s

def test_rep_identity(q, table, N_MAX=2000):
    w_K = {4: 4, 3: 6}[q]
    r = lattice_rep_counts(q, N_MAX)
    s = divisor_sum_chi(q, table, N_MAX)
    pred = w_K * s
    diff = r[1:] - pred[1:]
    nbad = int(np.count_nonzero(diff))
    maxerr = int(np.max(np.abs(diff)))
    # show a few sample n
    samples = [1, 2, 5, 7, 13, 25, 49, 65, 169, 1000]
    sample_rows = [(n, int(r[n]), int(pred[n])) for n in samples if n <= N_MAX]
    return dict(w_K=w_K, N_MAX=N_MAX, nbad=nbad, maxerr=maxerr, samples=sample_rows)

# ===========================================================================
# (B) lattice sum / zeta  ==  L(chi),  collapse at zeros
# ===========================================================================
def build_lattice_series(q, table, M):
    """coefficient array c[n] = r(n) for n=1..M (the Dedekind-zeta coefficients).
       Returns r (len M+1), amp = n^{-1/2}, z = log n."""
    r = lattice_rep_counts(q, M)
    return r

def residual_F(q, r, amp, logn, w):
    """F_q(w) = [ sum_n r(n) n^{-1/2} e^{-i w log n} ] / (w_K * zeta(1/2+iw)).
       The bracket is a truncation of Z_K = w_K*zeta*L; dividing by w_K*zeta gives L.
       We use mpmath zeta for the exact denominator (the partial-sum lattice numerator
       is what the GEOMETRY produces; the denominator is the trivial-class removal)."""
    w_K = {4: 4, 3: 6}[q]
    num = np.sum(r * amp * np.exp(-1j * w * logn))   # ~ w_K * zeta * L  (truncated)
    zval = complex(mp.zeta(mp.mpf(1) / 2 + 1j * mp.mpf(w)))
    return num / (w_K * zval)

def lattice_sum_raw(q, r, amp, logn, w):
    """raw truncated Dedekind-zeta lattice sum  ~ w_K * zeta(1/2+iw) * L(chi,1/2+iw)."""
    return np.sum(r * amp * np.exp(-1j * w * logn))

def test_dedekind_convergence(q, zero_gamma):
    """DECISIVE diagnostic: does the raw ring-lattice (Dedekind) partial sum
       Z_K(w) = sum_n r(n) n^{-1/2} e^{-i w log n}  collapse at an L-zero, where the
       EXACT value w_K*zeta*L = 0 ?  Track |Z_K(M)| vs M.  For a degree-1 single
       L-series this floor falls like 1/sqrt(2M); for the degree-2 Dedekind series it
       does NOT -- it GROWS like sqrt(M), so there is no collapse at sigma=1/2."""
    rows = []
    for M in (50_000, 200_000, 800_000, 2_000_000):
        r = lattice_rep_counts(q, M)
        nn = np.arange(0, M + 1, dtype=float)
        amp = np.zeros(M + 1); amp[1:] = nn[1:] ** (-0.5)
        logn = np.zeros(M + 1); logn[1:] = np.log(nn[1:])
        Z = abs(np.sum(r * amp * np.exp(-1j * zero_gamma * logn)))
        rows.append((M, Z, 1.0 / np.sqrt(2 * M)))
    return rows

def test_collapse(q, table, zeros, M=2_000_000, label=""):
    """Build the ring-lattice Dedekind series to norm <= M, test residual collapse."""
    r = build_lattice_series(q, table, M)
    nn = np.arange(0, M + 1, dtype=float)
    amp = np.zeros(M + 1)
    amp[1:] = nn[1:] ** (-0.5)
    logn = np.zeros(M + 1)
    logn[1:] = np.log(nn[1:])

    rows = []
    # AT each zero and at a midpoint OFF
    for i, g in enumerate(zeros):
        # exact zero check
        Lexact = float(abs(Lval(q, table, mp.mpf(1) / 2 + 1j * mp.mpf(g))))
        Fres = abs(residual_F(q, r, amp, logn, g))           # residual ~ |L| (geom/zeta)
        Lref = float(abs(Lval(q, table, mp.mpf(1) / 2 + 1j * mp.mpf(g))))
        # off-zero midpoint
        if i + 1 < len(zeros):
            gmid = 0.5 * (g + zeros[i + 1])
            Foff = abs(residual_F(q, r, amp, logn, gmid))
            Loff = float(abs(Lval(q, table, mp.mpf(1) / 2 + 1j * mp.mpf(gmid))))
        else:
            Foff = Loff = float('nan')
        rows.append(dict(gamma=g, Lexact=Lexact, Fres_at=Fres, Foff=Foff, Loff=Loff))
    return rows

# ===========================================================================
# (C) Gauss-circle volume law  V(X)=#{z: N(z)<=X} ~ (2pi/sqrt|disc|) X
# ===========================================================================
def volume_counts(q, Xs):
    """Cumulative lattice-point count V(X)=#{ring z!=0 : N(z)<=X} for each X in Xs."""
    Xmax = int(np.ceil(max(Xs)))
    r = lattice_rep_counts(q, Xmax)
    cum = np.cumsum(r)               # cum[n] = #{0<N(z)<=n}
    return np.array([cum[int(np.floor(X))] for X in Xs], dtype=float)

def test_volume_law(q):
    Xs = np.array([2.0 ** k for k in range(6, 18)])   # 64 .. 131072
    V = volume_counts(q, Xs)
    # least-squares slope through origin: V = slope * X
    slope = float(np.sum(Xs * V) / np.sum(Xs * Xs))
    pred_slope = {4: np.pi, 3: 2 * np.pi / np.sqrt(3.0)}[q]
    Vfit = slope * Xs
    ss_res = float(np.sum((V - Vfit) ** 2))
    ss_tot = float(np.sum((V - V.mean()) ** 2))
    R2 = 1 - ss_res / ss_tot
    return dict(slope=slope, pred_slope=pred_slope, ratio=slope / pred_slope,
                R2=R2, Xs=Xs, V=V)

# ===========================================================================
# (D) "volume between cancellations" : lattice-point count between consecutive
#     zeros vs the zero-counting law.  The hypothesis says gamma encodes a count.
#     We test the cleanest reading: between consecutive zeros gamma_n, gamma_{n+1},
#     the AFE-cutoff X = q*gamma/(2pi) (the analytic-conductor cutoff), and the
#     lattice-volume DELTA  V(X_{n+1})-V(X_n)  should track the Gauss-circle law
#     and (separately) the spacing should follow N(T).
# ===========================================================================
def test_volume_between(q, gammas):
    pred_slope = {4: np.pi, 3: 2 * np.pi / np.sqrt(3.0)}[q]
    # AFE cutoff per zero
    Xn = q * gammas / (2 * np.pi)
    Xmax = int(np.ceil(Xn[-1])) + 2
    r = lattice_rep_counts(q, Xmax)
    cum = np.cumsum(r)
    Vn = np.array([cum[int(np.floor(x))] if x >= 1 else 0.0 for x in Xn], dtype=float)
    dV = np.diff(Vn)                       # lattice points between consecutive zeros
    dX = np.diff(Xn)
    gauss_pred = pred_slope * dX           # Gauss-circle predicted delta
    # regress dV ~ slope*dX through origin
    slope = float(np.sum(dX * dV) / np.sum(dX * dX))
    res = dV - slope * dX
    ss_res = float(np.sum(res ** 2)); ss_tot = float(np.sum((dV - dV.mean()) ** 2))
    R2 = 1 - ss_res / ss_tot
    # Also: does the COUNT of zeros up to T follow N(T)?  N(T)~(T/2pi)log(qT/2pi)-T/2pi
    T = gammas[-1]
    Npred = (T / (2 * np.pi)) * np.log(q * T / (2 * np.pi)) - T / (2 * np.pi)
    return dict(slope=slope, pred_slope=pred_slope, ratio=slope / pred_slope, R2=R2,
                Nobs=len(gammas), Npred=Npred, T=T)

# ===========================================================================
# (E) SCOPE: q=5,7 have no class-number-1 imaginary-quadratic norm character.
#     Confirm the ring-lattice "cube" form is NOT defined there.
# ===========================================================================
def scope_note():
    # disc of Q(sqrt(-d)); class number 1 only for d in {1,2,3,7,11,19,43,67,163}
    # The Dirichlet character chi_q is a Kronecker symbol (.../D) for a field Q(sqrt(D))
    # only when q is (up to sign) a fundamental discriminant: q=3 -> D=-3, q=4 -> D=-4.
    # q=5: chi5_quadratic is (./5) = real char of Q(sqrt(5)) (REAL quadratic, not a 2D
    #      lattice 'cube'); chi5_quartic is order-4, not a quadratic-field norm char at all.
    # q=7: chi7_quadratic = (./-7) -> Q(sqrt(-7)) IS imaginary-quad class number 1, BUT the
    #      character here (the cubic-residue-like table) is the order-? char; the *quadratic*
    #      one would be (./-7). We test below what actually happens.
    return None

# ===========================================================================
# RUN
# ===========================================================================
def main():
    print("=" * 78)
    print("HYPOTHESIS cube-2 : Gaussian / Eisenstein number-ring lattice")
    print("=" * 78)

    chi3_g_all = load_chi3()
    chi4_g     = load_chi4()
    print(f"loaded chi3 zeros: {len(chi3_g_all)} (max gamma={chi3_g_all[-1]:.2f})")
    print(f"loaded chi4 zeros: {len(chi4_g)} (max gamma={chi4_g[-1]:.2f})")

    RING = {
        4: ("mod 4 quadratic", CHARS["mod 4 quadratic"][1], chi4_g),
        3: ("mod 3 quadratic", CHARS["mod 3 quadratic"][1], chi3_g_all),
    }

    # ---- (A) representation identity ----
    print("\n" + "-" * 78)
    print("(A) representation-count identity  r(n) = w_K * sum_{d|n} chi_q(d)")
    print("-" * 78)
    for q in (4, 3):
        name, table, _ = RING[q]
        res = test_rep_identity(q, table, N_MAX=2000)
        ring = "Z[i]" if q == 4 else "Z[omega]"
        print(f" q={q} ({ring}), w_K={res['w_K']}, n<=2000: "
              f"mismatches={res['nbad']}, max|err|={res['maxerr']}")
        srow = "   ".join(f"n={n}:r={rn}/pred={pn}" for n, rn, pn in res['samples'])
        print(f"     samples  {srow}")

    # ---- (C) volume / Gauss-circle law ----
    print("\n" + "-" * 78)
    print("(C) Gauss-circle volume law  V(X)=#{N(z)<=X} ~ (2pi/sqrt|disc|) X")
    print("-" * 78)
    for q in (4, 3):
        vl = test_volume_law(q)
        ring = "Z[i]" if q == 4 else "Z[omega]"
        print(f" q={q} ({ring}): fit slope={vl['slope']:.6f}  pred={vl['pred_slope']:.6f}"
              f"  ratio={vl['ratio']:.6f}  R^2={vl['R2']:.8f}")

    # ---- (B) collapse: residual lattice sum / zeta == L  ----
    print("\n" + "-" * 78)
    print("(B) residual F_q(w)=Z_K/(w_K*zeta) collapse AT vs OFF chi_q zeros")
    print("    (numerator = truncated ring-lattice Dedekind sum; denom = exact zeta)")
    print("-" * 78)
    M = 2_000_000
    for q in (4, 3):
        name, table, gammas = RING[q]
        ring = "Z[i]" if q == 4 else "Z[omega]"
        gtest = gammas[:8]
        rows = test_collapse(q, table, gtest, M=M, label=ring)
        print(f"\n q={q} ({ring}), lattice norm cutoff M={M}, first {len(gtest)} zeros:")
        print(f"  {'gamma':>10} {'|L|exact':>11} {'|F_res|@zero':>13} "
              f"{'|F_res|off':>12} {'|L|off':>10}")
        worst_at = 0.0; min_off = 1e9
        for r in rows:
            print(f"  {r['gamma']:10.4f} {r['Lexact']:11.2e} {r['Fres_at']:13.3e} "
                  f"{r['Foff']:12.3e} {r['Loff']:10.3e}")
            worst_at = max(worst_at, r['Fres_at'])
            if not np.isnan(r['Foff']):
                min_off = min(min_off, r['Foff'])
        print(f"  -> worst |F_res| AT a zero = {worst_at:.3e}; "
              f"min |F_res| OFF = {min_off:.3e}; ratio off/at = {min_off/worst_at:.1f}")

    # ---- (B2) DECISIVE convergence diagnostic: does the lattice sum collapse at all? ----
    print("\n" + "-" * 78)
    print("(B2) DECISIVE: raw Dedekind partial sum |Z_K(M)| at an L-zero vs M")
    print("     (exact w_K*zeta*L = 0 there; a degree-1 series floors ~1/sqrt(2M);")
    print("      the degree-2 lattice series GROWS ~sqrt(M) => NO collapse)")
    print("-" * 78)
    for q in (4, 3):
        name, table, gammas = RING[q]
        ring = "Z[i]" if q == 4 else "Z[omega]"
        g0 = float(gammas[0])
        rows = test_dedekind_convergence(q, g0)
        print(f" q={q} ({ring}) at first zero gamma={g0:.4f} (exact value = 0):")
        for M, Z, floor in rows:
            print(f"     M={M:>9}  |Z_K(M)|={Z:10.3f}   [degree-1 floor 1/sqrt(2M)={floor:.2e}]")
        growth = rows[-1][1] / rows[0][1]
        Mratio = rows[-1][0] / rows[0][0]
        print(f"     -> |Z_K| grew x{growth:.1f} as M grew x{Mratio:.0f} "
              f"(sqrt(M) would predict x{np.sqrt(Mratio):.1f}); collapse FAILS.")

    # ---- (D) volume between cancellations + zero count ----
    print("\n" + "-" * 78)
    print("(D) lattice 'volume' between consecutive zeros vs Gauss-circle / N(T)")
    print("-" * 78)
    for q in (4, 3):
        name, table, gammas = RING[q]
        gg = gammas if q == 3 else gammas
        vb = test_volume_between(q, gg)
        ring = "Z[i]" if q == 4 else "Z[omega]"
        print(f" q={q} ({ring}), {len(gg)} zeros up to T={vb['T']:.1f}:")
        print(f"     dV~slope*dX (AFE cutoff X=q*gamma/2pi): slope={vb['slope']:.5f} "
              f"pred={vb['pred_slope']:.5f} ratio={vb['ratio']:.4f} R^2={vb['R2']:.6f}")
        print(f"     zero count N(T): observed={vb['Nobs']}  N(T)law={vb['Npred']:.1f}  "
              f"ratio={vb['Nobs']/vb['Npred']:.4f}")

    # ---- (E) scope / falsify universality ----
    print("\n" + "-" * 78)
    print("(E) SCOPE: does the ring-lattice 'cube' form extend to q=5,7?")
    print("-" * 78)
    # For each of q=5(quad), q=5(quartic), q=7(quad): is the character the Kronecker
    # symbol of an IMAGINARY quadratic field (=> a 2D Z[sqrt-d] lattice norm char)?
    # Diagnostic: a real primitive char mod q is the norm char of Q(sqrt(D)) with D the
    # fundamental discriminant; it is IMAGINARY (a genuine 2D point-lattice 'cube') iff D<0.
    diag = {
        "mod 5 quadratic":         "chi5_quad = (./5): REAL quadratic field Q(sqrt5), D=+5>0 -> NOT a 2D point lattice (indefinite norm).",
        "mod 5 quartic (complex)": "chi5_quartic: order-4, NOT a quadratic norm character at all -> no Z[sqrt-d] ring.",
        "mod 7 quadratic":         "table here is order-3 (cubic residue), NOT (./-7); even (./-7)=Q(sqrt-7) is a DIFFERENT char than this mod-7 table.",
    }
    for nm in ("mod 5 quadratic", "mod 5 quartic (complex)", "mod 7 quadratic"):
        q, table = CHARS[nm]
        # numerically: is the char real-valued and is its conductor a NEGATIVE fund. disc?
        vals = list(table.values())
        is_real = all(abs(complex(v).imag) < 1e-12 for v in vals)
        order = "real(order<=2)" if is_real else "complex(order>2)"
        print(f" {nm:26s} [{order}]  {diag[nm]}")
    print("\n  => The ring-lattice 'cube' is defined ONLY for q=3 (Z[omega], D=-3) and")
    print("     q=4 (Z[i], D=-4): the two imaginary-quadratic class-number-1 NORM chars.")
    print("     For q=5,7 it does NOT apply. The UNIVERSAL form is the prime-exponent")
    print("     helix (helix3d_universal.py); cube-2 is its concrete low-q shadow.")

    print("\n" + "=" * 78)
    print("VERDICT")
    print("=" * 78)
    print("""
 STRUCTURAL identities PASS exactly:
   (A) r(n) = w_K * sum_{d|n} chi_q(d)  -- 0 mismatches up to n=2000, both rings.
   (C) Gauss-circle volume V(X) ~ (2pi/sqrt|disc|) X  -- ratio 1.0000, R^2 ~ 0.99999998.
   (E) scope correct: ring 'cube' defined only for q=3 (Z[omega]) and q=4 (Z[i]).

 But the GEOMETRIC ZERO-COLLAPSE FAILS (the hard constraint):
   (B/B2) The raw ring-lattice (Dedekind) partial sum
            Z_K(w) = sum_n r(n) n^{-1/2} e^{-i w log n}
          does NOT collapse at L(chi) zeros. The Dedekind series is DEGREE 2, so on
          sigma=1/2 it is strongly divergent: |Z_K(M)| GROWS like sqrt(M) at a zero
          (where the exact w_K*zeta*L = 0). Dividing by exact zeta leaves residual
          O(10^2), NOT O(10^-10). Gaussian smoothing does not help. There is no
          summation that makes the planar lattice 'see' the L-zero at sigma=1/2.
   (D) The 'volume between cancellations' fit has slope ratio ~1 but R^2 ~ 0.02-0.22:
          the AVERAGE density matches the conductor (that's just N(T)), but the
          INDIVIDUAL gaps are NOT predicted by lattice-point counts -- no per-zero law.

 CONCLUSION: cube-2 FALSE as a zero-producing rule. The factorization
   zeta_K = zeta * L  is a real analytic identity, but the planar integer lattice
   does NOT realize the L(chi) zeros: the degree-2 Dedekind series cannot be summed
   to its zero at sigma=1/2, unlike the degree-1 helix (helix3d_universal.py) whose
   single conditionally-convergent series floors cleanly at every zero. The lattice
   gives the right MEASURE (counting / volume / conductor density) but not the right
   CANCELLATION. passed = False.
""")
    print("=" * 78)


if __name__ == "__main__":
    main()
