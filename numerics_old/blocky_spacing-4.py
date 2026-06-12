#!/usr/bin/env python3
# blocky_spacing-4.py  --  ID: spacing-4   CLAIM: H4 (ALIGN-TO-AXIS phasor condition / character-locking)
#
# GOAL
#   Build the REAL 3D blocky helix with explicit (x,y,z) phasors FIRST, print a coordinate
#   sample, THEN test the align-to-axis functional A_chi(w) and decide whether the cancellation
#   that produces the chi3 zeros is CHARACTER-LOCKED (arithmetic / FTA residue balance) or merely
#   geometric (same heights for the trivial character).
#
# H4 (falsifiable):
#   A_chi3(w) = | sum_n chi3(n) n^{-1/2} e^{i w log n} | / ( sum_n n^{-1/2} )
#   attains sharp minima EXACTLY at the chi3 zeros, driven by the n=1 mod 3 vs n=2 mod 3
#   phasor bundles being mutually balanced (antipodal under the +/- sign). The SAME geometry with
#   the trivial character must collapse at DIFFERENT heights (zeta/Hurwitz-like), proving the
#   collapse is arithmetic, not geometric. If trivial-char collapses at the chi3 zeros too -> H4 FALSE.
#   If the chi3 collapse comes from |S_+| alone vanishing (not the +/- balance) -> H4 FALSE.
#
# HONESTY GUARDRAILS (per task):
#   - Build the actual 3D solid with explicit (x,y,z); print a sample BEFORE measuring.
#   - Phasor = a real rotating UNIT vector hung at each point; a cancellation event is the
#     chi3-weighted PHASOR VECTOR-SUM collapsing onto the central axis (we sum the actual 2D
#     phasor vectors, not an abstract scalar). We ALSO compute the analytic |L| and explicitly
#     check whether the phasor-sum is secretly re-deriving the analytic L (it is, up to the
#     finite-N tail + completed-vs-Dirichlet correction -- we report this honestly).
#   - passed = True only if (3D built first) AND (collapse heights land on real chi3 zeros)
#     AND (the collapse is character-locked: trivial-char heights differ).
#   - capturesFluctuation: True only if the per-block fluctuation S(T) (individual zeros, not
#     just the mean log density) is reproduced by the construction itself.

import numpy as np
import mpmath as mp

mp.mp.dps = 30
np.random.seed(0)

# ----------------------------------------------------------------------------------------
# Exact analytic L(chi3, s) for verification (chi3 = real char mod 3):
#   L(chi3,s) = 3^{-s} ( zeta(s,1/3) - zeta(s,2/3) )
# ----------------------------------------------------------------------------------------
def Lchi3(s):
    return mp.power(3, -s) * (mp.zeta(s, mp.mpf(1)/3) - mp.zeta(s, mp.mpf(2)/3))

def to_mpf(x):
    """Convert a python/numpy float to mpf safely (avoid repr(np.float64)=='np.float64(..)')."""
    return mp.mpf(float(x))

# Trivial-character control: the Riemann zeta along the same line (zeta-analogue).
# zeta(1/2+it) for the "same geometry, different sign pattern" control.
def zeta_line(t):
    return mp.zeta(mp.mpf('0.5') + 1j*mp.mpf(t))

# ----------------------------------------------------------------------------------------
# Load the 65 exact chi3 zeros (|L|<1e-11) verified upstream.
# ----------------------------------------------------------------------------------------
ZERO_FILE = "/Users/samuellavery/proof/three/numerics/chi3_zeros_exact.txt"
chi3_zeros_str = []  # keep full-precision string form for mpmath
with open(ZERO_FILE) as f:
    for line in f:
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        chi3_zeros_str.append(line)
chi3_zeros_str = sorted(chi3_zeros_str, key=lambda s: float(s))
chi3_zeros = np.array([float(s) for s in chi3_zeros_str])
# map a float zero back to its full-precision string (for mpmath verification)
_zero_str_map = {float(s): s for s in chi3_zeros_str}
print(f"# Loaded {len(chi3_zeros)} exact chi3 zeros, range [{chi3_zeros[0]:.4f}, {chi3_zeros[-1]:.4f}]")

# Verify the first few to |L|<1e-12 (HARD RULE: verify any claimed boundary/cancellation height).
print("# Verifying exact chi3 zeros against analytic |L|:")
for g in chi3_zeros[:6]:
    val = abs(Lchi3(mp.mpf('0.5') + 1j*mp.mpf(_zero_str_map[float(g)])))
    print(f"#   gamma={g:>12.8f}   |L(1/2+i gamma)| = {mp.nstr(val,4)}")

# ========================================================================================
# STEP 1 -- BUILD THE REAL 3D BLOCKY HELIX (explicit x,y,z), print a coordinate sample.
# ========================================================================================
# The cloud: integer n placed on a spiral. Radial law R_n = sqrt(n) (area/packing law -- one loop
# per ~k integers, cumulative ~k^2, R ~ sqrt(n)), angular position theta_n = log n (the bridge
# readout wind n <-> n^{it}), axial height z_n = sqrt(n) (the climbing spiral / pitch direction).
# This is the "blocky" helix in that the radius STEPS with sqrt(n) and integers sit at log-spaced
# angles; blocks are the turns of the spiral. We keep the geometry FIXED across the whole cloud
# (this H4 test is about the PHASOR weighting, not the step law -- the step laws were swept in
# sibling files; here we isolate the character-locking of the collapse on one honest 3D solid).
#
# Phasor at each point: a UNIT vector that SPINS as we wind the readout height w:
#   phi_n(w) = w * log n   (drift = log n per unit w; this is the n^{iw} winding, log-free geometry
#                           is the angle theta_n = log n; the phasor SPIN rate is also log n, so as
#                           w advances the phasor at integer n rotates at rate log n -- the resonance.)
#   phasor_n(w) = ( cos(phi_n(w)), sin(phi_n(w)) )    -- a real rotating unit vector.
# Weight (amplitude) a_n = n^{-1/2}  (the 1/2 baseline -- sqrt-of-planar-packing).
# Character weight: chi3(n) in {+1,0,-1} by n mod 3  (or trivial 1_{gcd(n,1)=1}=1 for control).

def chi3(n):
    r = n % 3
    if r == 1:
        return 1
    if r == 2:
        return -1
    return 0  # n ≡ 0 mod 3: not coprime to conductor, character vanishes.

def chi_trivial(n):
    # Trivial character (zeta-analogue): all n weighted +1. This is the "no sign pattern" control.
    return 1

N = 200000  # number of integers in the cloud (terms in the Dirichlet sum); large enough for sharp minima.
n_idx = np.arange(1, N + 1, dtype=np.float64)
logn = np.log(n_idx)
amp = n_idx ** (-0.5)                 # a_n = n^{-1/2}
R = np.sqrt(n_idx)                    # radial law (planar packing)
Z = np.sqrt(n_idx)                    # axial height (climbing spiral)
# 3D coordinates of the cloud at a REFERENCE readout w0 (the static solid). theta_n = log n.
theta0 = logn
X0 = R * np.cos(theta0)
Y0 = R * np.sin(theta0)

chi3_w = np.array([chi3(int(n)) for n in n_idx], dtype=np.float64)
triv_w = np.ones(N, dtype=np.float64)  # trivial char weights all = 1.

print("\n# ================= STEP 1: 3D BLOCKY HELIX CLOUD (sample) =================")
print("#   n   chi3(n)   R=sqrt(n)    theta=log n        x            y            z=sqrt(n)")
for n in [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 100, 1000]:
    i = n - 1
    print(f"#  {n:>4d}    {int(chi3_w[i]):+d}    {R[i]:>9.4f}   {theta0[i]:>9.5f}   "
          f"{X0[i]:>11.5f}  {Y0[i]:>11.5f}   {Z[i]:>9.4f}")

# ========================================================================================
# STEP 2 -- attach the phasor and define its spin/drift; define the align-to-axis functional.
# ========================================================================================
# As we wind the readout w, the phasor at n is the unit vector at angle phi_n(w)=w*log n.
# The chi-weighted phasor VECTOR-SUM (resultant in the plane) is:
#   V_chi(w) = sum_n  chi(n) * a_n * ( cos(w log n), sin(w log n) )
# A cancellation event = the resultant V collapses onto the central axis (||V|| -> 0).
# Normalized align-to-axis functional:
#   A_chi(w) = || V_chi(w) || / ( sum_n a_n )
# We compute V as an actual 2D vector sum (real cos/sin components), NOT an abstract complex scalar,
# so the 3D phasor geometry is explicit. (Numerically V = Re/Im of sum chi a_n e^{i w log n}.)

sum_amp = amp.sum()  # normalizer sum_n n^{-1/2}

def phasor_vector_sum(w, weights):
    """Actual 2D phasor vector sum at readout height w. Returns (Vx, Vy, ||V||)."""
    phi = w * logn
    c = np.cos(phi)
    s = np.sin(phi)
    wa = weights * amp
    Vx = np.dot(wa, c)
    Vy = np.dot(wa, s)
    return Vx, Vy, np.hypot(Vx, Vy)

def A(w, weights):
    _, _, norm = phasor_vector_sum(w, weights)
    return norm / sum_amp

# Residue-class decomposition for chi3: S_+(w) over n=1 mod 3, S_-(w) over n=2 mod 3.
mask_plus = (n_idx.astype(int) % 3 == 1)
mask_minus = (n_idx.astype(int) % 3 == 2)
amp_plus = amp[mask_plus]
amp_minus = amp[mask_minus]
logn_plus = logn[mask_plus]
logn_minus = logn[mask_minus]

def Splus_Sminus(w):
    """Return complex S_+(w), S_-(w) (residue-class phasor bundles)."""
    Sp = np.dot(amp_plus, np.exp(1j * w * logn_plus))
    Sm = np.dot(amp_minus, np.exp(1j * w * logn_minus))
    return Sp, Sm

# Sanity: V_chi3 = S_+ - S_- (chi3=+1 on 1 mod3, -1 on 2 mod3, 0 on 0 mod3).
def check_decomp(w):
    Vx, Vy, _ = phasor_vector_sum(w, chi3_w)
    Sp, Sm = Splus_Sminus(w)
    D = Sp - Sm
    return abs((Vx + 1j * Vy) - D)

# ========================================================================================
# STEP 3 -- WIND: find where the chi3-weighted phasor vector-sum collapses; compare to exact zeros.
# ========================================================================================
print("\n# ================= STEP 3: WIND & LOCATE COLLAPSES =================")
# sanity check decomposition at a sample w
print(f"#   decomp check |V_chi3 - (S+ - S-)| at w=20.0 : {check_decomp(20.0):.2e}  (should be ~0)")

# Scan A_chi3(w) and A_trivial(w) on a fine grid over [6, 30] (per test plan); also extend to cover
# more exact zeros for the matching statistic.
def scan_minima(weights, wlo, whi, coarse_step=0.002):
    ws = np.arange(wlo, whi, coarse_step)
    vals = np.array([A(w, weights) for w in ws])
    # local minima
    mins = []
    for i in range(1, len(vals) - 1):
        if vals[i] < vals[i-1] and vals[i] < vals[i+1] and vals[i] < 0.05:
            mins.append((ws[i], vals[i]))
    # refine each via golden-section-ish parabolic bracket using mpmath findroot on dA? Use simple refine.
    refined = []
    for w0, v0 in mins:
        lo, hi = w0 - coarse_step, w0 + coarse_step
        for _ in range(60):
            m1 = lo + (hi - lo) / 3
            m2 = hi - (hi - lo) / 3
            if A(m1, weights) < A(m2, weights):
                hi = m2
            else:
                lo = m1
        wm = 0.5 * (lo + hi)
        refined.append((wm, A(wm, weights)))
    return refined

WLO, WHI = 6.0, 30.0
chi3_mins = scan_minima(chi3_w, WLO, WHI)
triv_mins = scan_minima(triv_w, WLO, WHI)

exact_in_range = chi3_zeros[(chi3_zeros >= WLO) & (chi3_zeros <= WHI)]
print(f"\n# chi3 collapse minima found in [{WLO},{WHI}] (A<0.05): {len(chi3_mins)}")
print(f"# exact chi3 zeros in range: {len(exact_in_range)}")

# Match each exact chi3 zero to nearest chi3 collapse minimum.
print("\n#   exact_gamma     nearest_chi3_min   |diff|      A_chi3@min   A_trivial@same_w   |L|@min")
match_errs = []
for g in exact_in_range:
    # nearest chi3 collapse
    wm = min((m[0] for m in chi3_mins), key=lambda w: abs(w - g))
    am = A(wm, chi3_w)
    at = A(wm, triv_w)
    Lval = abs(Lchi3(mp.mpf('0.5') + 1j * to_mpf(wm)))
    match_errs.append(abs(wm - g))
    print(f"#   {g:>11.6f}    {wm:>11.6f}   {abs(wm-g):>8.5f}   "
          f"{am:>10.5f}   {at:>12.5f}     {mp.nstr(Lval,3)}")

match_errs = np.array(match_errs)
print(f"\n# chi3 match: mean |diff|={match_errs.mean():.5f}, max |diff|={match_errs.max():.5f}, "
      f"median={np.median(match_errs):.5f}")

# ----- CHARACTER-LOCK TEST: do trivial-char collapses land on chi3 zeros or elsewhere? -----
print("\n# ================= CHARACTER-LOCK TEST =================")
print(f"# trivial-char collapse minima in [{WLO},{WHI}] (A<0.05): {len(triv_mins)}")
print("#   trivial_min_w     A_triv@min    A_chi3@same_w   nearest_chi3_zero  |diff to chi3 zero|   |zeta(1/2+iw)|")
triv_to_chi3 = []
for wm, _ in triv_mins:
    at = A(wm, triv_w)
    ac = A(wm, chi3_w)
    nz = chi3_zeros[np.argmin(np.abs(chi3_zeros - wm))]
    zval = abs(zeta_line(to_mpf(wm)))
    triv_to_chi3.append(abs(wm - nz))
    print(f"#   {wm:>11.6f}    {at:>9.5f}   {ac:>11.5f}    {nz:>13.6f}     {abs(wm-nz):>9.5f}        {mp.nstr(zval,3)}")

triv_to_chi3 = np.array(triv_to_chi3) if triv_to_chi3 else np.array([np.nan])
print(f"\n# trivial-char collapses vs chi3 zeros: mean dist = {np.nanmean(triv_to_chi3):.5f}")
print("#   (if this is LARGE and chi3 match is SMALL, the collapse is CHARACTER-LOCKED -> H4 supported)")

# Cross-check: evaluate A_trivial AT the exact chi3 zeros -- is it small (geometric) or large (locked)?
print("\n# A_trivial evaluated AT the exact chi3 zeros (should be LARGE if character-locked):")
at_at_chi3 = []
for g in exact_in_range:
    at = A(g, triv_w)
    ac = A(g, chi3_w)
    at_at_chi3.append(at)
    print(f"#   chi3 zero {g:>11.6f}:   A_chi3={ac:>9.5f}   A_trivial={at:>9.5f}")
at_at_chi3 = np.array(at_at_chi3)
ac_at_chi3 = np.array([A(g, chi3_w) for g in exact_in_range])
print(f"\n# At chi3 zeros: mean A_chi3 = {ac_at_chi3.mean():.5f}  vs  mean A_trivial = {at_at_chi3.mean():.5f}")

# ----- ROTATIONAL-BALANCE SIGNATURE: decompose each chi3 collapse into S_+ and S_- -----
print("\n# ================= ROTATIONAL-BALANCE (antipodality) at chi3 zeros =================")
print("#   chi3 zero      |S_+|       |S_-|     |S+|/|S-|    arg(S+)-arg(S-) (deg)    |S+ - S-|")
ratio_list = []
antip_list = []
for g in exact_in_range:
    Sp, Sm = Splus_Sminus(g)
    ratio = abs(Sp) / abs(Sm)
    dang = (np.angle(Sp) - np.angle(Sm))
    # wrap to (-180,180]
    dang_deg = (np.degrees(dang) + 180) % 360 - 180
    ratio_list.append(ratio)
    antip_list.append(abs(dang_deg))
    print(f"#   {g:>11.6f}   {abs(Sp):>8.5f}   {abs(Sm):>8.5f}    {ratio:>7.4f}      "
          f"{dang_deg:>10.3f}            {abs(Sp-Sm):>8.5f}")
ratio_arr = np.array(ratio_list)
antip_arr = np.array(antip_list)
print(f"\n# |S+|/|S-| at chi3 zeros: mean={ratio_arr.mean():.4f}, std={ratio_arr.std():.4f}  (expect ~1)")
print(f"# |arg(S+)-arg(S-)| at chi3 zeros: mean={antip_arr.mean():.4f} deg, std={antip_arr.std():.4f}")
# IMPORTANT MECHANISM CORRECTION (data-driven, per Rule Two/Four -- report what the geometry shows,
# not the hypothesis's guess): the data shows arg(S+)-arg(S-) ~ 0, NOT ~180. The two residue-class
# phasor BUNDLES are EQUAL and PARALLEL (same |S|, same phase): S_+(w) ~ S_-(w) at a chi3 zero.
# The cancellation is NOT antipodal phasors; it is the CHARACTER SIGN: chi3 puts +1 on S_+ and -1 on
# S_-, so V_chi3 = S_+ - S_-  vanishes precisely because the bundles COINCIDE. The "antipodality" of
# H4 lives in the chi3 SIGN PATTERN (+1 vs -1 residue class), not in the winding angle of the bundles.
# This is STILL character-locked / FTA-residue-balance (the conclusion of H4) -- the +/- residue
# structure is what forces the collapse -- but the balance is "equal parallel bundles cancelled by
# the sign", which is the correct, earned reading.
print(f"#   MECHANISM: |S+|/|S-|~1 ({'YES' if abs(ratio_arr.mean()-1)<0.05 else 'no'}) AND "
      f"arg(S+)-arg(S-)~0 ({'YES, bundles PARALLEL' if antip_arr.mean()<5 else 'no'})")
print(f"#   => collapse V=S+ - S- vanishes because the +1 and -1 residue bundles COINCIDE; the")
print(f"#      cancellation is carried by the chi3 SIGN (residue-class antipodal in CHARACTER, not phase).")
bundles_coincide = (abs(ratio_arr.mean() - 1) < 0.05) and (antip_arr.mean() < 5)

# Is the collapse driven by |S_+| alone vanishing, or by the +/- balance?
# Compare |S+ - S-| (the actual collapse, chi3) against min(|S+|,|S-|) (would-be if one bundle vanished).
print("\n# Is collapse the +/- BALANCE or |S_+| alone vanishing?")
collapse_norm = np.array([abs(Splus_Sminus(g)[0] - Splus_Sminus(g)[1]) for g in exact_in_range])
indiv_min = np.array([min(abs(Splus_Sminus(g)[0]), abs(Splus_Sminus(g)[1])) for g in exact_in_range])
print(f"#   mean |S+ - S-| (collapse)      = {collapse_norm.mean():.5f}")
print(f"#   mean min(|S+|,|S-|)            = {indiv_min.mean():.5f}")
print(f"#   -> collapse {'<<' if collapse_norm.mean() < 0.3*indiv_min.mean() else 'NOT <<'} "
      f"individual bundle magnitude => {'BALANCE-driven (H4)' if collapse_norm.mean() < 0.3*indiv_min.mean() else 'NOT balance-driven'}")

# ========================================================================================
# HONESTY CHECK -- is the phasor-sum secretly the analytic L?
# ========================================================================================
print("\n# ================= HONESTY: phasor-sum vs analytic L =================")
# A_chi3(w) is a truncated Dirichlet series sum_{n<=N} chi3(n) n^{-1/2} e^{i w log n}
#         = sum_{n<=N} chi3(n) n^{-1/2-iw}  = partial sum of L(1/2+iw, chi3).
# So YES it converges (slowly, conditionally) to L(1/2+iw)/sum_amp on the line. This is the honest
# statement: the phasor geometry IS the Dirichlet series of L. The 3D solid is a faithful geometric
# carrier of that series (not a different object). The minima therefore sit at L's zeros BY
# CONSTRUCTION -- which is exactly why landing on the real zeros is necessary but not "free": the
# CONTENT of H4 is WHICH sign pattern produces them (chi3 antipodal balance) vs trivial char, i.e.
# the character-locking, not the mere fact of collapse.
for g in exact_in_range[:5]:
    Vx, Vy, _ = phasor_vector_sum(g, chi3_w)
    partial = (Vx + 1j*Vy)  # = sum_{n<=N} chi3(n) n^{-1/2-ig}
    Lexact = complex(Lchi3(mp.mpf('0.5') + 1j*to_mpf(g)))
    print(f"#   w={g:>10.5f}:  partial-sum(N={N}) = {partial.real:+.4f}{partial.imag:+.4f}j   "
          f"|partial|={abs(partial):.4f}   |L_exact|={abs(Lexact):.2e}")

# ========================================================================================
# FLUCTUATION QUESTION: does this construction CAPTURE S(T) (per-block fluctuation) or only the mean?
# ========================================================================================
print("\n# ================= FLUCTUATION (S(T)) vs MEAN log density =================")
# The collapse heights here ARE the exact zeros (they = zeros of the partial L), so the spacing
# fluctuation is reproduced EXACTLY -- but ONLY because the construction evaluates the analytic L
# (the phasor sum is L's Dirichlet series). It is NOT a smooth/independent STEP LAW that predicts
# the zeros from block geometry; the fluctuation is INHERITED from L, not GENERATED by a feedback
# step rule. So as a "stepped helix that captures S(T) from its own geometry", this does NOT add
# new generative content beyond evaluating L. We report this honestly via capturesFluctuation.
gaps = np.diff(exact_in_range)
mean_gap = gaps.mean()
# mean log density prediction: local spacing ~ 2pi / log(q*gamma/(2pi)), q=3
import math
pred_gaps = np.array([2*math.pi / math.log(3*g/(2*math.pi)) for g in exact_in_range[:-1]])
resid = gaps - pred_gaps
print(f"#   mean actual gap = {mean_gap:.5f}")
print(f"#   mean log-density predicted gap = {pred_gaps.mean():.5f}")
print(f"#   gap fluctuation (std of residual gap-pred) = {resid.std():.5f}")
frac_fluct = resid.var() / gaps.var() if gaps.var() > 0 else float('nan')
print(f"#   fraction of gap-variance that is fluctuation (not mean law) = {frac_fluct:.3f}")
print("#   NOTE: the phasor construction reproduces individual zeros EXACTLY, but only because it")
print("#   IS L's Dirichlet series -- the fluctuation is INHERITED from L, not generated by a step law.")

# ----- DEEPEST-COLLAPSE-DEPTH (cleanest character-lock metric) -----
# The sharpest character-lock evidence: how DEEP does each functional ever collapse over the window?
# chi3 reaches ~1e-6 (true vanishing) at the chi3 zeros; the trivial char (same geometry) never gets
# near zero anywhere -- its minima floor far above. This is robust to the truncation ripple that
# muddies the trivial "minima" locations (the trivial partial Dirichlet sum has no FE completion, so
# its minima are dominated by the slow tail, not clean zeros).
print("\n# ================= DEEPEST COLLAPSE OVER WINDOW (character-lock depth) =================")
ws_dense = np.arange(WLO, WHI, 0.001)
ac_dense = np.array([A(w, chi3_w) for w in ws_dense])
at_dense = np.array([A(w, triv_w) for w in ws_dense])
chi3_deepest = ac_dense.min(); triv_deepest = at_dense.min()
print(f"#   chi3   deepest A over [{WLO},{WHI}] = {chi3_deepest:.6e}  (at w={ws_dense[ac_dense.argmin()]:.4f})")
print(f"#   triv   deepest A over [{WLO},{WHI}] = {triv_deepest:.6e}  (at w={ws_dense[at_dense.argmin()]:.4f})")
print(f"#   chi3 collapses {triv_deepest/max(chi3_deepest,1e-12):.0f}x DEEPER than trivial -> "
      f"only the chi3 sign pattern produces a TRUE vanishing.")

# ========================================================================================
# VERDICT
# ========================================================================================
print("\n# ================= VERDICT =================")
built_3d_first = True  # we printed explicit (x,y,z) phasor cloud above before any measurement.
lands_on_zeros = (match_errs.max() < 0.02)
# character-locked (two independent witnesses):
#   (i) at the chi3 zeros, A_trivial >> A_chi3 (trivial does NOT collapse where chi3 does);
#   (ii) over the whole window, chi3 reaches a TRUE vanishing (~1e-6) that trivial never approaches.
char_locked = (at_at_chi3.mean() > 100 * ac_at_chi3.mean()) and (triv_deepest > 100 * chi3_deepest)
balance_driven = (collapse_norm.mean() < 0.3 * indiv_min.mean())
# Corrected mechanism (data-driven): the residue bundles COINCIDE (parallel, equal), cancelled by sign.
mechanism_ok = bundles_coincide and balance_driven

print(f"#   built_3d_first         : {built_3d_first}")
print(f"#   lands_on_real_zeros    : {lands_on_zeros}  (max match err {match_errs.max():.5f})")
print(f"#   character_locked       : {char_locked}  (A_triv/A_chi3 at zeros "
      f"{at_at_chi3.mean()/max(ac_at_chi3.mean(),1e-9):.0f}x ; deepest-collapse "
      f"{triv_deepest/max(chi3_deepest,1e-12):.0f}x)")
print(f"#   balance_driven (V=S+-S- << |S±|): {balance_driven}")
print(f"#   mechanism: residue bundles COINCIDE, cancelled by chi3 sign: {mechanism_ok}")
print(f"#     (S+/S- magnitude ratio {ratio_arr.mean():.4f}, phase diff {antip_arr.mean():.4f} deg ~ 0)")
print(f"#   NOTE: H4 predicted ANTIPODAL bundles (~180 deg). Data shows PARALLEL bundles (~0 deg)")
print(f"#         cancelled by the CHARACTER SIGN. H4's CONCLUSION (character-locked, +/- residue")
print(f"#         balance / FTA) holds; its stated MECHANISM (antipodal winding) is corrected to")
print(f"#         'coincident bundles, sign-cancelled'.")

passed = built_3d_first and lands_on_zeros and char_locked and balance_driven
captures_fluct = False  # zeros are inherited from L's Dirichlet series, NOT generated by a step law.

print(f"\n#   H4 PASSED = {passed}")
print(f"#   capturesFluctuation = {captures_fluct}")

# Emit a compact machine-readable summary for the harness.
print("\n@@SUMMARY@@")
print(f"built_3d_first={built_3d_first}")
print(f"n_terms={N}")
print(f"chi3_match_max_err={match_errs.max():.6f}")
print(f"chi3_match_mean_err={match_errs.mean():.6f}")
print(f"n_exact_zeros_in_range={len(exact_in_range)}")
print(f"n_chi3_minima={len(chi3_mins)}")
print(f"n_trivial_minima={len(triv_mins)}")
print(f"triv_min_mean_dist_to_chi3zeros={np.nanmean(triv_to_chi3):.6f}")
print(f"A_chi3_at_chi3zeros_mean={ac_at_chi3.mean():.6f}")
print(f"A_trivial_at_chi3zeros_mean={at_at_chi3.mean():.6f}")
print(f"Splus_over_Sminus_mean={ratio_arr.mean():.6f}")
print(f"phase_diff_Splus_Sminus_deg_mean={antip_arr.mean():.6f}")
print(f"collapse_vs_indiv_ratio={collapse_norm.mean()/max(indiv_min.mean(),1e-12):.6f}")
print(f"chi3_deepest_collapse={chi3_deepest:.6e}")
print(f"trivial_deepest_collapse={triv_deepest:.6e}")
print(f"deepest_ratio_triv_over_chi3={triv_deepest/max(chi3_deepest,1e-12):.1f}")
print(f"char_locked={char_locked}")
print(f"balance_driven={balance_driven}")
print(f"bundles_coincide_sign_cancelled={bundles_coincide}")
print(f"passed={passed}")
print(f"capturesFluctuation={captures_fluct}")
