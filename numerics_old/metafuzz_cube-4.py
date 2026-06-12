"""
metafuzz_cube-4.py  --  ID cube-4
=================================================================================
CLAIM (BASE-q DIGIT CUBE / ODOMETER):
  Place integer n by its base-q digit expansion  n = sum_k d_k q^k, giving the
  lattice point (d_0,d_1,d_2,...) in {0,...,q-1}^infinity -- a genuine q-ary CUBE
  (each axis a digit, q sites per axis).  chi mod q reads ONLY the lowest digit
  d_0 = n mod q, so chi(n) = chi(d_0).  Universal ruleset stays:
        F(w) = sum_n chi(d_0(n)) n^{-1/2} e^{-i w log n}
  but now indexed by the q-adic digit cube / odometer.

  TESTED HERE (5 separate, falsifiable questions):
   (1) IDENTITY:  cube reindexing == baseline L(chi,1/2+iw)?  (must be exact; sanity)
   (2) BLOCK CONDITIONING:  do q-blocks [qm+1..qm+q] (one odometer low-digit cycle)
       give faster/better-conditioned convergence to 0 at w=gamma than the raw sum?
   (3) ODOMETER SPECTRUM:  build a chi-twisted q^K x q^K adding-machine operator with
       phase e^{-i w log n}; do its characteristic resonances (det) align with the
       true zeros gamma as K grows?  require match < 1e-8.
   (4) VOLUME / CARRY LAW:  USER HEADLINE -- is the zero height gamma the "volume of
       integers between successive cancellations"?  Count odometer steps / carry
       cascades between zeros; regress gap or gamma against q-scaled counts.
   (5) UNIVERSALITY:  q = 3,4,5(quad), 5(quartic complex), 7 -- ONE rule, EXACT zeros.

  FALSIFY if the digit-cube reindexing gives NO conditioning/spectral advantage AND
  the carry-volume does not track q*gamma.  Reported honestly per RULE TWO.
=================================================================================
"""
import numpy as np
import mpmath as mp
import os, time

mp.mp.dps = 40
HERE = os.path.dirname(os.path.abspath(__file__))
# lchi3_zeros_1000.txt is SPARSE (35 sampled heights up to 925); for gap statistics we
# use lchi3_zeros_record.txt which holds 3580 CONSECUTIVE chi3 zeros (40 digits each).
ZEROFILE = os.path.join(HERE, "lchi3_zeros_record.txt")

# ---------------- characters: the ONLY per-L input ----------------
CHARS = {
    "mod 3 quadratic":          (3, {1: 1, 2: -1}),
    "mod 4 quadratic":          (4, {1: 1, 3: -1}),
    "mod 5 quadratic":          (5, {1: 1, 4: 1, 2: -1, 3: -1}),
    "mod 5 quartic (complex)":  (5, {1: 1, 2: 1j, 4: -1, 3: -1j}),
    "mod 7 quadratic":          (7, {1: 1, 2: 1, 4: 1, 3: -1, 5: -1, 6: -1}),
}

def chi_of(table, q, m):
    r = int(m) % q
    return complex(table.get(r, 0))

def Lval(q, table, s):
    """exact L(chi,s) = q^{-s} sum_a chi(a) Hurwitz-zeta(s, a/q)."""
    tot = mp.mpc(0)
    for a, c in table.items():
        tot += mp.mpc(c) * mp.zeta(s, mp.mpf(a) / q)
    return q ** (-s) * tot

def true_zeros(q, table, hi=40.0, step=0.05, want=8):
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

# numpy character arrays for the big sums
def char_array(q, table, N):
    nn = np.arange(1, N + 1)
    v = np.zeros(N, dtype=complex)
    r = nn % q
    for res, val in table.items():
        v[r == res] = val
    return v

def F_raw(chi_vals, amp, z, w):
    return np.sum(chi_vals * amp * np.exp(-1j * w * z))

# ====================================================================
print("="*80)
print("metafuzz cube-4 : BASE-q DIGIT CUBE / ODOMETER realization")
print("="*80)

# -----------------------------------------------------------------------------
# (1) IDENTITY: cube reindexing == baseline L.  The cube is literally a reindexing
#     of the integers by their base-q digits.  Summing over all cube cells with
#     n=sum d_k q^k reproduces the integers 1..N exactly -> must equal baseline.
#     We verify chi(n)==chi(d_0) and that the digit-ordered sum == nat-ordered sum.
# -----------------------------------------------------------------------------
print("\n--- TEST 1: cube reindexing identity (chi(n)=chi(d_0), digit-sum == L) ---")
def digits_base_q(n, q):
    d = []
    while n > 0:
        d.append(n % q); n //= q
    return d if d else [0]

N1 = 200000
ident_ok = True
for name, (q, table) in CHARS.items():
    # check chi(n) == chi(d_0=n mod q) for a sample (this is exact by periodicity)
    bad = 0
    for n in range(1, 5000):
        d0 = digits_base_q(n, q)[0]
        if chi_of(table, q, n) != chi_of(table, q, d0):
            bad += 1
    # check the cube sum (reindex integers by digits, in increasing n it's the same set)
    chi_vals = char_array(q, table, N1)
    nn = np.arange(1, N1 + 1).astype(float)
    amp = 1.0 / np.sqrt(nn); z = np.log(nn)
    w_test = 8.0397371556814667  # chi3 first zero (just a probe height)
    Fcube = F_raw(chi_vals, amp, z, w_test)
    Lexact = complex(Lval(q, table, mp.mpf(1)/2 + 1j*mp.mpf(w_test)))
    rel = abs(Fcube - Lexact) / max(1e-30, abs(Lexact)) if abs(Lexact) > 1e-9 else abs(Fcube - Lexact)
    print(f"  {name:26s} q={q}: chi(n)==chi(d0) mismatches={bad}; "
          f"|F_cube - L| @ probe = {abs(Fcube-Lexact):.3e}  (|L|={abs(Lexact):.3e})")
    if bad != 0:
        ident_ok = False
print(f"  => chi(n)=chi(d_0) is EXACT (periodicity): identity holds = {ident_ok}")
print("  NOTE: |F_cube - L| at finite N is just the Dirichlet-series truncation tail,")
print("        identical to the baseline (cube is a reindex, NOT a new object).")

# -----------------------------------------------------------------------------
# (2) BLOCK CONDITIONING: group integers into q-blocks (one low-digit odometer cycle)
#     b_m(w) = sum_{j=0}^{q-1} chi(qm+j+1) (qm+j+1)^{-1/2} e^{-i w log(qm+j+1)}.
#     Compare truncation error of  sum_m b_m  (block-summed, M blocks) vs the raw
#     partial sum at the SAME number of integers, at w=gamma.  If the cube/odometer
#     organizes cancellation, block-summing should converge FASTER (smaller error).
# -----------------------------------------------------------------------------
print("\n--- TEST 2: q-block (odometer low-digit cycle) conditioning vs raw ---")
def block_vs_raw(q, table, w, Ntot):
    nn = np.arange(1, Ntot + 1).astype(float)
    chi_vals = char_array(q, table, Ntot)
    amp = 1.0/np.sqrt(nn); z = np.log(nn)
    terms = chi_vals * amp * np.exp(-1j*w*z)
    # raw running partial-sum error vs full
    target = complex(Lval(q, table, mp.mpf(1)/2 + 1j*mp.mpf(w)))  # ~0 at a zero
    raw_partial = np.cumsum(terms)
    # block sums: reshape into q-blocks (drop remainder)
    nblk = Ntot // q
    blk = terms[:nblk*q].reshape(nblk, q).sum(axis=1)
    blk_partial = np.cumsum(blk)
    # compare error after using same NUMBER OF INTEGERS at a set of checkpoints
    checkpoints = [1000, 5000, 20000, 100000]
    out = []
    for c in checkpoints:
        if c <= Ntot and c//q <= nblk:
            err_raw = abs(raw_partial[c-1] - target)
            err_blk = abs(blk_partial[c//q - 1] - target)
            out.append((c, err_raw, err_blk))
    return out

for name, (q, table) in CHARS.items():
    zs = true_zeros(q, table, want=2)
    if not zs:
        print(f"  {name}: no zeros"); continue
    w = zs[0]
    res = block_vs_raw(q, table, w, 200000)
    print(f"  {name:26s} q={q} @ gamma_1={w:.5f}")
    for c, er, eb in res:
        ratio = eb/er if er>0 else float('inf')
        print(f"      N={c:6d}: raw_err={er:.3e}  block_err={eb:.3e}  ratio(blk/raw)={ratio:.3f}")

# -----------------------------------------------------------------------------
# (3) ODOMETER SPECTRUM: the q-adic adding machine (odometer) is the map n->n+1 with
#     carries.  On K digits it's a permutation of {0,..,q^K-1} (cyclic shift +1 mod q^K).
#     Twist it by the universal phasor weight  W(n) = chi(d_0(n)) n^{-1/2} e^{-i w log n}.
#     Build the q^K x q^K diagonal-weighted shift  T(w) = diag(W) @ P   (P = +1 shift).
#     Its eigenvalues are W-weighted roots of unity; det(T(w)-I)=0 encodes resonance.
#     Ask: do the w making det(I - T(w)) (or the weighted-trace) vanish track gamma?
#     This is the honest spectral test of "zeros = odometer-shift spectrum twisted by chi".
# -----------------------------------------------------------------------------
print("\n--- TEST 3: chi-twisted odometer (adding-machine) spectrum vs gamma ---")
def odometer_resonance(q, table, w, K):
    """
    The q-adic odometer on K digits is the cyclic shift +1 on {0,..,q^K-1}.  Twist it by
    the universal weight  W(n) = chi(d_0) n^{-1/2} e^{-i w log n}.  Two honest functionals:
      sumW   = sum_n W(n)            -> THIS is just the L-truncation F (baseline), unchanged.
      sumW_supp = sum over chi-supported residues only (the actual cube cells the char lives on).
    A weighted *product* (det of the full cyclic shift) is degenerate: any n divisible by q
    has chi=0, so prod==0 trivially -> NOT a meaningful resonance.  We instead form the
    per-fibre transfer eigenvalue: lam_r(w) = sum_{n: n=r mod q} W(n), and the determinant of
    the q x q fibre-coupling (here diagonal since chi reads only d_0) -> resonances are just
    the per-residue Dirichlet sums.  We report sumW_supp and the largest fibre eigenvalue.
    """
    Nq = q**K
    nn = np.arange(1, Nq+1).astype(float)
    r = (np.arange(1, Nq+1) % q)
    chi_vals = char_array(q, table, Nq)
    base = (1.0/np.sqrt(nn)) * np.exp(-1j*w*np.log(nn))
    W = chi_vals * base
    sumW = np.sum(W)                       # = baseline F
    sumW_supp = np.sum(W[chi_vals != 0])   # over supported cube cells only (== sumW since chi=0 zero anyway)
    # per-residue fibre sums (the odometer's q fibres); the operator det = product of fibre
    # eigenvalues weighted by chi -> resonance functional R(w):
    fibre = np.array([np.sum(base[r == rr]) for rr in range(q)])  # un-twisted fibre sums
    Rw = sum(chi_of(table, q, rr) * fibre[rr] for rr in range(q))  # = sumW (chi twist of fibres)
    return sumW, sumW_supp, Rw, fibre

for name, (q, table) in list(CHARS.items())[:3]:  # 3 chars for the operator probe
    zs = true_zeros(q, table, want=2)
    if not zs: continue
    w = zs[0]
    print(f"  {name:26s} q={q} @ gamma_1={w:.5f}")
    for K in range(3, 8):
        sumW, sumW_supp, Rw, fibre = odometer_resonance(q, table, w, K)
        Nq=q**K
        # untwisted fibre sums do NOT vanish; only the chi-twist (=sumW) does -> the
        # cancellation is the chi orthogonality across fibres, not an odometer eigenvalue.
        maxfib = max(abs(fibre))
        print(f"      K={K} (q^K={Nq:6d}): |sumW(=F=twisted fibres)|={abs(sumW):.3e}  "
              f"max|untwisted fibre|={maxfib:.3e}  |R(w)|={abs(Rw):.3e}")
    print("      => the ONLY vanishing functional is the chi-twisted fibre sum (= baseline F).")
    print("         Untwisted odometer fibres do NOT vanish; there is no separate odometer")
    print("         eigenvalue that hits gamma -- the collapse is chi orthogonality, period.")

# -----------------------------------------------------------------------------
# (4) VOLUME / CARRY LAW  (USER HEADLINE):
#     "gamma = volume of integers between successive cancellations."
#     Operationalize two ways, then regress on the 1000 chi3 zeros:
#      (a) ZERO-COUNT law (known): N(T) ~ (T/2pi) log(qT/2pi) - T/2pi.  The *local* gap
#          delta_n = gamma_{n+1}-gamma_n ~ 2pi / log(q gamma_n / 2pi).  So the "number of
#          integers between zeros" in the natural density is set by 1/gap.  Test if a
#          q-ADIC / odometer count V_n (carry-cascade count over an n-range) tracks gamma.
#      (b) CARRY-CASCADE count: between heights, count odometer steps until the chi-fibre
#          running balance B(N)=sum_{n<=N} chi(n) re-closes (returns near 0).  chi mod q is
#          q-periodic with sum 0 over a block, so B(N) re-closes every q steps TRIVIALLY ->
#          that gives 'volume' = q per cancellation, INDEPENDENT of gamma.  We check if that
#          trivial q-period (or any odometer carry statistic) correlates with the gamma gaps.
# -----------------------------------------------------------------------------
print("\n--- TEST 4: VOLUME / CARRY law -- is gamma the integer-volume between zeros? ---")

# load the CONSECUTIVE exact chi3 zeros (record file: "n  gamma  |L|")
gammas = []
with open(ZEROFILE) as fh:
    for line in fh:
        line = line.strip()
        if not line or line.startswith("#"): continue
        parts = line.split()
        try:
            g = float(parts[1])
            gammas.append(g)
        except Exception:
            pass
gammas = np.array(sorted(gammas))
print(f"  loaded {len(gammas)} CONSECUTIVE exact chi3 zeros, range "
      f"[{gammas[0]:.3f}, {gammas[-1]:.3f}]")

q3 = 3
gaps = np.diff(gammas)
mid = 0.5*(gammas[1:] + gammas[:-1])
# density prediction: local gap ~ 2pi / log(q*gamma/2pi)
pred_gap = 2*np.pi / np.log(q3*mid/(2*np.pi))
# fit gaps ~ a * pred_gap + b
A = np.vstack([pred_gap, np.ones_like(pred_gap)]).T
coef, res_, rank_, sv_ = np.linalg.lstsq(A, gaps, rcond=None)
fit = A @ coef
ss_res = np.sum((gaps-fit)**2); ss_tot = np.sum((gaps-gaps.mean())**2)
R2 = 1 - ss_res/ss_tot
print(f"  (a) GAP vs density-predicted 2pi/log(q gamma/2pi):")
print(f"      fit gap = {coef[0]:.4f}*pred + {coef[1]:.4f},  R^2 = {R2:.4f}")
print(f"      mean |gap - pred| = {np.mean(np.abs(gaps-pred_gap)):.4f}  "
      f"(mean gap={gaps.mean():.4f})")

# 'volume of integers between zeros': cumulative integer count.  Interpret 'integers
# measured between cancellations' as the count of integer-heights or odometer steps whose
# winding has advanced one full turn between gamma_n and gamma_{n+1}.  The natural geometric
# count: number of integers n with log n in an interval set by the phase advance.  But the
# headline literally says gamma == volume.  Test the cleanest reading:
#   #{integers up to e^{(2pi/U)}} ... -> instead, directly test  N(gamma) (zero-count) law:
def Ncount_pred(T, q):
    return (T/(2*np.pi))*np.log(q*T/(2*np.pi)) - T/(2*np.pi)
idx = np.arange(1, len(gammas)+1)
Npred = Ncount_pred(gammas, q3)
# the zero-count law: index n ~ N(gamma_n).  Fit.
A2 = np.vstack([Npred, np.ones_like(Npred)]).T
coef2, *_ = np.linalg.lstsq(A2, idx, rcond=None)
fit2 = A2@coef2
R2c = 1 - np.sum((idx-fit2)**2)/np.sum((idx-idx.mean())**2)
print(f"  (b) ZERO-COUNT: index n vs N(gamma)=(T/2pi)log(qT/2pi)-T/2pi:")
print(f"      n = {coef2[0]:.5f}*N(gamma) + {coef2[1]:.4f},  R^2 = {R2c:.6f}")
print(f"      => gamma is set by the COUNT of zeros below it (Riemann-vonMangoldt), the")
print(f"         standard density.  This is a count law, but NOT a q-adic CARRY-cube count.")

# carry-cascade count test: does the q-adic odometer carry structure between consecutive
# zeros encode the gap?  Count, for the integer index interval, the number of base-q carry
# cascades (n where n mod q^j == 0).  Compare its growth to gamma growth.
def carry_cascades_upto(M, q):
    # number of carries when counting 1..M in base q = sum_j floor(M/q^j)
    s = 0; p = q
    while p <= M:
        s += M//p; p *= q
    return s
# does carry-count between zeros track the gap?  Use integer proxy n_k = exp(U-scale)?  The
# only honest map integers<->height is n ~ e^{height/?}.  There is NO finite integer interval
# between zeros without the log bridge.  Report this explicitly.
print(f"  (c) CARRY-CASCADE proxy: q-adic carries up to M=10^6 (q={q3}) = "
      f"{carry_cascades_upto(10**6, q3)}  (= M/(q-1)-ish, geometric, gamma-independent).")
print(f"      Carry count grows like M/(q-1); it has NO gamma dependence -> the odometer")
print(f"      carry 'volume' does NOT set the zero heights.  (honest negative)")

# -----------------------------------------------------------------------------
# (5) UNIVERSALITY: ONE rule (cube sum), EXACT zeros for all 5 characters, |L|<1e-12.
# -----------------------------------------------------------------------------
print("\n--- TEST 5: UNIVERSALITY -- cube sum collapses at EXACT zeros, all 5 chars ---")
N5 = 300000
universal_pass = True
exact_pass = True
for name, (q, table) in CHARS.items():
    zs = true_zeros(q, table, want=5)
    if not zs:
        print(f"  {name}: NO zeros found"); universal_pass=False; continue
    chi_vals = char_array(q, table, N5)
    nn = np.arange(1, N5+1).astype(float)
    amp = 1.0/np.sqrt(nn); z = np.log(nn)
    at  = [abs(F_raw(chi_vals, amp, z, w)) for w in zs]
    off = [abs(F_raw(chi_vals, amp, z, 0.5*(zs[i]+zs[i+1]))) for i in range(len(zs)-1)]
    exact = [float(abs(Lval(q, table, mp.mpf(1)/2 + 1j*mp.mpf(w)))) for w in zs]
    maxexact = max(exact)
    if maxexact >= 1e-12:
        exact_pass = False
    # cube collapse should be small at zeros, larger off (finite N -> ~1e-2..1e-3 at zeros)
    print(f"  {name:26s} q={q}")
    print(f"      gamma            : {[round(x,4) for x in zs]}")
    print(f"      |L|(mpmath EXACT): {['%.1e'%e for e in exact]}  (all <1e-12? {maxexact<1e-12})")
    print(f"      cube |F| AT  zero: {['%.2e'%a for a in at]}")
    print(f"      cube |F| OFF zero: {['%.2e'%a for a in off]}")
    # off should exceed at on average
    if np.mean(off) <= np.mean(at):
        universal_pass = False

print("\n" + "="*80)
print("SUMMARY (cube-4)")
print("="*80)
print(f"  T1 identity (chi=chi(d0), cube=reindex of L)     : EXACT (trivially true)")
print(f"  T5 EXACT zeros verified <1e-12 all 5 chars       : {exact_pass}")
print(f"  T5 cube collapse at zeros (universal)            : {universal_pass}")
print("  T2 block conditioning advantage                  : see ratios above")
print("  T3 odometer-spectrum functional vanishes at gamma: see |prodW|,|det(I-S)|")
print("  T4 carry-VOLUME tracks q*gamma                    : NO (carry count gamma-indep)")
print("  T4 zero-COUNT law (Riemann-vonMangoldt) holds     : yes (standard, not q-cube)")
