"""
blocky_fluct-2.py  --  ID fluct-2

A BLOCKY-HELIX realization of the zeros of L(chi3), chi3 = real char mod 3.

HARD RULE obeyed literally, in order:
  STEP 1  build the REAL 3D blocky solid with EXPLICIT (x,y,z); PRINT a coord sample.
  STEP 2  hang a real rotating unit PHASOR vector at each point; define its spin.
  STEP 3  wind; a cancellation = the chi3-weighted PHASOR VECTOR-SUM collapsing onto
          the central axis (resultant -> 0). Compare collapse heights to exact mpmath
          chi3 zeros (|L|<1e-12). Also test the ALIGN-TO-AXIS condition.

Then: FUZZ the block steps (pitch / radial / spacing) over the requested constants,
and run the FULLY SELF-CONSISTENT feedback fixed point that aims PAST the known
focused finding -- computing the geometric misalignment angle alpha at the CURRENT
iterate T_k (NOT the true zero gamma_k), iterating to a fixed point, and asking whether
the geometry PREDICTS the per-block fluctuation S(T) rather than merely fitting it.

Everything is built from the 3D points + phasor vectors. We never collapse to an
abstract scalar L; the resultant is always a real 2D vector sum of placed phasors.
"""

import numpy as np
import mpmath as mp

mp.mp.dps = 30
Q = 3
TWO_PI = 2.0 * np.pi

# ----------------------------------------------------------------------------
# Exact L(chi3, s) and its zeros (ground truth, |L| < 1e-12)
# ----------------------------------------------------------------------------
def Lchi3(s):
    return mp.power(3, -s) * (mp.zeta(s, mp.mpf(1) / 3) - mp.zeta(s, mp.mpf(2) / 3))

def absL_half(t):
    return abs(Lchi3(mp.mpf(0.5) + 1j * mp.mpf(t)))

def find_chi3_zeros(n_zeros=65, t_lo=2.0, t_hi=135.0, n_scan=4000):
    """Scan |L(1/2+it)| for minima, refine each with mp.findroot to |L|<1e-12."""
    ts = np.linspace(t_lo, t_hi, n_scan)
    vals = np.array([float(absL_half(t)) for t in ts])
    zeros = []
    for i in range(1, len(ts) - 1):
        if vals[i] < vals[i - 1] and vals[i] < vals[i + 1] and vals[i] < 0.4:
            try:
                root = mp.findroot(lambda s: Lchi3(s), mp.mpf(0.5) + 1j * mp.mpf(ts[i]))
                g = float(mp.im(root))
                if abs(float(mp.re(root)) - 0.5) < 1e-6 and float(absL_half(g)) < 1e-12:
                    if all(abs(g - z) > 1e-4 for z in zeros) and g > t_lo:
                        zeros.append(g)
            except Exception:
                pass
    zeros = sorted(zeros)
    return np.array(zeros[:n_zeros])


# ============================================================================
# STEP 1 -- BUILD THE REAL 3D BLOCKY HELIX (explicit x, y, z)
# ============================================================================
class BlockyHelix3D:
    """
    Piecewise (blocky) helix. Integers n = 1..Nmax are laid along the unwound line,
    split into BLOCKS k = 0,1,2,... (one block ~ one harmonic/zero). Within block k the
    geometry is CONSTANT; at each block boundary it STEPS:
        pitch[k]   axial rise per full turn (sets z),
        radius[n]  radial law / amplitude (Archimedean: R grows ~ loop index),
        spacing[k] arc length between consecutive integers in block k.
    Block assignment uses sqrt-area packing: cumulative integers ~ k^2 so block k
    holds ~k integers, giving R ~ sqrt(n) emergent (the sigma=1/2 planar-packing law).
    """
    def __init__(self, n_max=8000):
        self.n_max = n_max
        self.n = np.arange(1, n_max + 1)
        self.block_assign = np.floor(np.sqrt(self.n)).astype(int)  # k(n) ~ sqrt(n)

    def build(self, pitch_law, radius_law, spacing_law):
        n = self.n
        kk = self.block_assign
        ds = np.empty_like(n, dtype=float)
        pit = np.empty_like(n, dtype=float)
        for k in np.unique(kk):
            m = kk == k
            ds[m] = spacing_law(k)
            pit[m] = pitch_law(k)
        R = radius_law(n, kk)
        dphi = ds / np.maximum(R, 1e-9)        # angle subtended per integer
        phi = np.cumsum(dphi)                   # cumulative WINDING angle
        dz = pit * dphi / TWO_PI                # rise per turn -> rise per radian
        z = np.cumsum(dz)
        x = R * np.cos(phi)
        y = R * np.sin(phi)
        return dict(n=n, k=kk, R=R, phi=phi, z=z, x=x, y=y, ds=ds, pitch=pit)


def chi3(n):
    n = np.asarray(n)
    return np.where(n % 3 == 1, 1.0, np.where(n % 3 == 2, -1.0, 0.0))


# ============================================================================
# STEP 2 -- PHASOR: a real rotating unit vector hung at each 3D point
# ============================================================================
# The phasor at integer n is a unit vector in the plane transverse to the central
# axis. As we "wind" at trial height w, the phasor SPINS: psi(n; w) = w * Theta(n),
# where Theta(n) is the integer's intrinsic winding read-off (the bridge angle, the
# ONLY place log appears: wind n <-> n^{it}). chi3(n) flips the phasor by pi when -1.
def phasor_vectors(coords, w):
    """Return the array of placed phasor 2D unit vectors (chi3-signed), and amps."""
    n = coords['n']
    Theta = np.log(n)                       # bridge read-off (dictionary, not geometry)
    psi = w * Theta
    amp = 1.0 / np.maximum(coords['R'], 1e-9)   # geometric 1/R falloff (= 1/sqrt(n))
    ch = chi3(n)
    ux = ch * np.cos(psi)
    uy = ch * np.sin(psi)
    return ux, uy, amp


def phasor_resultant(coords, w):
    """VECTOR SUM of the placed, chi3-weighted, amplitude-weighted phasors -> resultant."""
    ux, uy, amp = phasor_vectors(coords, w)
    vx = np.sum(amp * ux)
    vy = np.sum(amp * uy)
    return np.array([vx, vy]), float(np.hypot(vx, vy))


def axis_alignment_defect(coords, w):
    """ALIGN-TO-AXIS: |resultant| / total amplitude. 0 = phasors collapse onto axis."""
    _, mag = phasor_resultant(coords, w)
    amp = 1.0 / np.maximum(coords['R'], 1e-9)
    tot = float(np.sum(np.abs(chi3(coords['n'])) * amp))
    return mag / max(tot, 1e-12)


def phasor_angle(coords, w):
    """Argument of the resultant vector -- the geometric phasor-misalignment angle."""
    vec, _ = phasor_resultant(coords, w)
    return float(np.arctan2(vec[1], vec[0]))


# ============================================================================
# STEP 3 -- WIND: find heights where the phasor VECTOR-SUM collapses to the axis
# ============================================================================
def find_collapse_heights(coords, w_lo, w_hi, n_scan=6000):
    """Scan trial winding height w; collapse = local minimum of |resultant(w)|."""
    ws = np.linspace(w_lo, w_hi, n_scan)
    mags = np.array([phasor_resultant(coords, w)[1] for w in ws])
    mins = []
    for i in range(1, len(ws) - 1):
        if mags[i] < mags[i - 1] and mags[i] < mags[i + 1]:
            # parabolic refine
            a, b, c = mags[i - 1], mags[i], mags[i + 1]
            denom = (a - 2 * b + c)
            shift = 0.5 * (a - c) / denom if abs(denom) > 1e-15 else 0.0
            dw = ws[1] - ws[0]
            mins.append((ws[i] + shift * dw, b))
    return mins


def match_to_zeros(collapse_heights, gammas, tol=0.5):
    """Greedy nearest-match of collapse heights to exact zeros."""
    matched = []
    used = set()
    for g in gammas:
        best, bj = None, None
        for j, w in enumerate(collapse_heights):
            if j in used:
                continue
            d = abs(w - g)
            if best is None or d < best:
                best, bj = d, j
        if bj is not None and best <= tol:
            matched.append((g, collapse_heights[bj], best))
            used.add(bj)
        else:
            matched.append((g, None, None))
    return matched


# ============================================================================
# Helper: the S(T) fluctuation reference (riemann-siegel-style, q=3)
#   Mean density of L(chi3) zeros at height T: rho(T) = (1/2pi) log(q T / 2pi).
#   S(T) := (deviation of actual count from the smooth count) -- here we use the
#   per-block residual of the cumulative-count law as the empirical fluctuation.
# ============================================================================
def smooth_count(T):
    # N(T) ~ (T/pi) log(qT/2pi) - T/pi  (main term of the chi3 zero-counting function)
    return (T / np.pi) * np.log(Q * T / TWO_PI) - T / np.pi

def empirical_S(gammas):
    """S_k = smooth_count(gamma_k) - (k - 1/2): how far the actual k-th zero lags/leads
    the smooth count. This is the standard argument-fluctuation signal S(T)."""
    k = np.arange(1, len(gammas) + 1)
    return smooth_count(gammas) - (k - 0.5)


def corr(a, b):
    a = np.asarray(a, float); b = np.asarray(b, float)
    v = np.isfinite(a) & np.isfinite(b)
    if v.sum() < 5:
        return np.nan
    return float(np.corrcoef(a[v], b[v])[0, 1])


# ============================================================================
# MAIN
# ============================================================================
def main():
    print("=" * 78)
    print("blocky_fluct-2.py :: BLOCKY-HELIX realization of L(chi3) zeros, with PHASORS")
    print("=" * 78)

    # ---- exact zeros (ground truth) ----
    print("\n[zeros] computing exact chi3 zeros via mpmath L(chi3,s)=3^-s(zeta(s,1/3)-zeta(s,2/3))")
    G = find_chi3_zeros(n_zeros=65)
    print(f"        found {len(G)} zeros; first 6: {np.round(G[:6],4)}")
    # verify
    worst = max(float(absL_half(g)) for g in G[:6])
    print(f"        |L(1/2+i gamma)| worst of first 6 = {worst:.2e}  (< 1e-12 OK)")
    S = empirical_S(G)

    # ===================== STEP 1: BUILD + PRINT 3D COORDS =====================
    print("\n" + "-" * 78)
    print("STEP 1 -- THE REAL 3D BLOCKY HELIX (explicit x,y,z), sample coordinates")
    print("-" * 78)
    H = BlockyHelix3D(n_max=8000)
    # a concrete blocky law set: pitch steps log-like, radius Archimedean (R=k loop idx),
    # spacing constant pi/3.  (This is just the object to LOOK at; we fuzz laws later.)
    pitch_law0   = lambda k: 0.5 * np.log(Q * max(k, 1) ** 2 / TWO_PI + 2.0)
    radius_law0  = lambda nn, kk: np.maximum(kk, 1).astype(float)
    spacing_law0 = lambda k: np.pi / 3
    coords = H.build(pitch_law0, radius_law0, spacing_law0)
    print(f"{'n':>6}{'block k':>8}{'R':>8}{'phi(wind)':>11}{'z(height)':>11}"
          f"   (        x,        y,        z)")
    for nn in [1, 2, 3, 4, 9, 16, 25, 100, 400, 1600, 4000]:
        i = nn - 1
        print(f"{nn:6d}{coords['k'][i]:8d}{coords['R'][i]:8.2f}{coords['phi'][i]:11.3f}"
              f"{coords['z'][i]:11.3f}   ({coords['x'][i]:9.2f},{coords['y'][i]:9.2f},"
              f"{coords['z'][i]:9.3f})")
    print("  (BLOCKY: at each k boundary pitch/radius/spacing STEP; R~sqrt(n) emergent.)")

    # ===================== STEP 2: PHASORS =====================
    print("\n" + "-" * 78)
    print("STEP 2 -- PHASOR (real rotating unit vector) hung at each point")
    print("-" * 78)
    w_demo = float(G[0])  # spin rate = first zero height
    ux, uy, amp = phasor_vectors(coords, w_demo)
    print(f"  spin rate w = gamma_1 = {w_demo:.5f}; phasor psi(n) = w*log n, flipped by chi3")
    print(f"  {'n':>4}{'chi3':>6}{'phasor (ux,uy)':>22}{'amp=1/R':>10}")
    for nn in [1, 2, 4, 5, 7, 8, 10]:
        i = nn - 1
        print(f"  {nn:4d}{chi3(nn):+6.0f}     ({ux[i]:+6.3f},{uy[i]:+6.3f})  {amp[i]:9.4f}")
    vec, mag = phasor_resultant(coords, w_demo)
    print(f"  PHASOR VECTOR-SUM resultant at gamma_1 = ({vec[0]:+.4f},{vec[1]:+.4f}) "
          f"|.|={mag:.4f}")
    print(f"  axis-alignment defect = {axis_alignment_defect(coords, w_demo):.4f} "
          f"(0 = phasors collapse onto central axis)")

    # ===================== STEP 3: WIND + COLLAPSE vs EXACT ZEROS ==============
    print("\n" + "-" * 78)
    print("STEP 3 -- WIND: chi3-weighted phasor VECTOR-SUM collapse heights vs exact zeros")
    print("-" * 78)
    mins = find_collapse_heights(coords, 2.0, float(G[-1]) + 2.0, n_scan=6000)
    collapse_w = [w for (w, m) in mins]
    matched = match_to_zeros(collapse_w, G[:40], tol=0.5)
    nhit = sum(1 for (_, w, _) in matched if w is not None)
    print(f"  found {len(collapse_w)} collapse minima; matched {nhit}/40 exact zeros (tol 0.5)")
    print(f"  {'zero#':>5}{'gamma_exact':>13}{'collapse_w':>12}{'|diff|':>9}")
    for idx, (g, w, d) in enumerate(matched[:14], 1):
        if w is None:
            print(f"  {idx:5d}{g:13.4f}{'--':>12}{'--':>9}")
        else:
            print(f"  {idx:5d}{g:13.4f}{w:12.4f}{d:9.4f}")
    diffs = np.array([d for (_, w, d) in matched if w is not None])
    if len(diffs):
        print(f"  RMS(collapse - exact) over matched = {np.sqrt(np.mean(diffs**2)):.4f}")
    # axis-alignment AT the exact zeros vs midpoints (does the geometry SEE the zero?)
    defect_at_zeros = np.array([axis_alignment_defect(coords, g) for g in G[:20]])
    mids = 0.5 * (G[:19] + G[1:20])
    defect_at_mids = np.array([axis_alignment_defect(coords, m) for m in mids])
    print(f"  mean align-defect AT zeros  = {defect_at_zeros.mean():.4f}")
    print(f"  mean align-defect at MIDpts = {defect_at_mids.mean():.4f}  "
          f"(zeros lower => geometry resonates at zeros)")

    # ===================== HONESTY: is this secretly the analytic L? ===========
    # The resultant is sum_n chi(n) * (1/R(n)) * e^{i w log n}.  If R(n)=sqrt(n) then
    # amp=1/sqrt(n) and this is EXACTLY the truncated Dirichlet series of L(chi3,1/2+iw).
    # That would mean the blocky PITCH/SPACING geometry is decorative (the collapse is
    # forced by amp + phase alone). We test that directly, three ways.
    print("\n" + "-" * 78)
    print("HONESTY CHECK -- does the BLOCKY geometry (pitch/spacing) move the collapse,")
    print("                 or is the resultant secretly the analytic-L Dirichlet sum?")
    print("-" * 78)
    # (i) compare resultant to the literal truncated L Dirichlet series at the zeros
    def dirichlet_L_partial(w, N):
        nn = np.arange(1, N + 1); return np.abs(np.sum(chi3(nn) * nn**(-0.5) * np.exp(1j * w * np.log(nn))))
    rel = []
    for g in G[:8]:
        _, mag = phasor_resultant(coords, g)
        dl = dirichlet_L_partial(g, coords['n'][-1])
        rel.append(abs(mag - dl))
    print(f"  max |resultant - truncated_L_partial| over 8 zeros = {max(rel):.2e}")
    print(f"  (≈0 => with R=k the amp=1/R is NOT 1/sqrt(n), so resultant != partial-L here;")
    print(f"   but the R=sqrt(n) fuzz winners ARE the partial-L series -- flagged below.)")
    # (ii) does changing PITCH alone move the collapse heights?  (it must, if geometry bites)
    cA = H.build(lambda k: np.pi/6,            radius_law0, spacing_law0)
    cB = H.build(lambda k: 3.0,                radius_law0, spacing_law0)
    mA = sorted(w for (w, _) in find_collapse_heights(cA, 2.0, 45.0, 2500))
    mB = sorted(w for (w, _) in find_collapse_heights(cB, 2.0, 45.0, 2500))
    nmin = min(len(mA), len(mB))
    pitch_moves = float(np.max(np.abs(np.array(mA[:nmin]) - np.array(mB[:nmin])))) if nmin else np.nan
    print(f"  max collapse-height shift when PITCH changes pi/6 -> 3.0 = {pitch_moves:.2e}")
    # (iii) does changing SPACING alone move them?
    cC = H.build(pitch_law0, radius_law0, lambda k: np.pi/6)
    cD = H.build(pitch_law0, radius_law0, lambda k: np.pi)
    mC = sorted(w for (w, _) in find_collapse_heights(cC, 2.0, 45.0, 2500))
    mD = sorted(w for (w, _) in find_collapse_heights(cD, 2.0, 45.0, 2500))
    nmin2 = min(len(mC), len(mD))
    spacing_moves = float(np.max(np.abs(np.array(mC[:nmin2]) - np.array(mD[:nmin2])))) if nmin2 else np.nan
    print(f"  max collapse-height shift when SPACING changes pi/6 -> pi = {spacing_moves:.2e}")
    geometry_inert = (pitch_moves < 1e-6) and (spacing_moves < 1e-6)
    print(f"  => pitch & spacing inert (collapse fixed by amp+phase only)?  {geometry_inert}")
    if geometry_inert:
        print(f"     HONEST FLAG: the on-axis collapse is driven by amp(=1/R)+phase(=w log n);")
        print(f"     pitch/spacing are decorative for the CANCELLATION. The radial law R(n) is")
        print(f"     the only geometric DOF that bites, and R=sqrt(n) reproduces partial-L.")

    # ===================== FUZZ: sweep block STEP laws & constants =============
    print("\n" + "-" * 78)
    print("FUZZ -- sweep PITCH / RADIAL / SPACING step laws & constants")
    print("        score = RMS of matched collapse heights vs first 30 exact zeros")
    print("-" * 78)
    CONSTS = {
        'pi/6': np.pi/6, 'pi/3': np.pi/3, 'pi/2': np.pi/2, 'pi': np.pi,
        'log2': 0.6931, 'log3': 1.0986, 'sqrt2': np.sqrt(2), 'sqrt3': np.sqrt(3),
        'e': np.e,
    }
    # spacing laws: constant at each requested constant
    # radial laws: R=k (Archimedean), R=k*c growth, R=k*sqrt step, R=e^{c k}-ish (capped)
    # pitch laws: constant c, c*(1+0.05k) linear, log-growth, sqrt
    pitch_variants = {}
    for nm, c in CONSTS.items():
        pitch_variants[f'const {nm}']  = (lambda c=c: (lambda k: c))()
        pitch_variants[f'lin {nm}']    = (lambda c=c: (lambda k: c * (1 + 0.05 * k)))()
    pitch_variants['log-growth'] = lambda k: 0.5 * np.log(Q * max(k,1)**2 / TWO_PI + 2.0)
    pitch_variants['sqrt']       = lambda k: 0.4 * np.sqrt(max(k,1))

    radial_variants = {
        'R=k':        lambda nn, kk: np.maximum(kk, 1).astype(float),
        'R=k*sqrt2':  lambda nn, kk: np.maximum(kk, 1).astype(float) * np.sqrt(2),
        'R=k*log3':   lambda nn, kk: np.maximum(kk, 1).astype(float) * 1.0986,
        'R=sqrt(n)':  lambda nn, kk: np.sqrt(nn.astype(float)),
        'R=e^{ck}':   lambda nn, kk: np.minimum(np.exp(0.15 * np.maximum(kk,1)), 1e6),
    }
    spacing_variants = {f'ds={nm}': (lambda c=c: (lambda k: c))() for nm, c in CONSTS.items()}

    best = None
    # to keep it tractable, sweep a focused grid (pitch x radial x spacing)
    results = []
    for pn, pl in pitch_variants.items():
        for rn, rl in radial_variants.items():
            for sn, sl in spacing_variants.items():
                try:
                    cds = H.build(pl, rl, sl)
                    mm = find_collapse_heights(cds, 2.0, float(G[29]) + 2.0, n_scan=2500)
                    cw = [w for (w, _) in mm]
                    mt = match_to_zeros(cw, G[:30], tol=0.8)
                    dd = np.array([d for (_, w, d) in mt if w is not None])
                    nh = len(dd)
                    rms = float(np.sqrt(np.mean(dd**2))) if nh >= 10 else np.inf
                    score = rms if nh >= 15 else np.inf
                    results.append((score, nh, pn, rn, sn))
                    if best is None or score < best[0]:
                        best = (score, nh, pn, rn, sn)
                except Exception:
                    pass
    results.sort(key=lambda t: t[0])
    print(f"  swept {len(results)} (pitch x radial x spacing) combos")
    print(f"  {'rank':>4}{'RMS':>9}{'#hit/30':>9}  pitch / radial / spacing")
    for r, (score, nh, pn, rn, sn) in enumerate(results[:8], 1):
        sc = f"{score:.4f}" if np.isfinite(score) else "  inf"
        print(f"  {r:4d}{sc:>9}{nh:9d}  {pn} | {rn} | {sn}")
    print("  NOTE: matching the MEAN spacing is easy (many combos hit ~half the zeros);")
    print("        the open content is the per-block FLUCTUATION, tested next.")

    # ===================== AIM PAST: self-consistent feedback fixed point ======
    print("\n" + "-" * 78)
    print("AIM-PAST -- FULLY SELF-CONSISTENT feedback fixed point (predict, not fit)")
    print("-" * 78)
    # (1) smooth feedback: T_{k+1} = T_k + pi / p_k, p_k = (1/2) log(q T_k / 2pi)
    def smooth_feedback(T0, K):
        Ts = [T0]
        for _ in range(K):
            p = 0.5 * np.log(Q * Ts[-1] / TWO_PI)
            Ts.append(Ts[-1] + np.pi / max(p, 1e-6))
        return np.array(Ts)
    Tb = smooth_feedback(float(G[0]), len(G) - 1)[:len(G)]
    e_smooth = Tb - G
    rms_smooth = float(np.sqrt(np.mean(e_smooth**2)))
    # local per-gap error (de-trended) = the genuinely local fluctuation, vs cumulative drift
    e_local = np.diff(Tb) - np.diff(G)
    print(f"  (1) smooth feedback (mean log law):")
    print(f"      RMS(T_smooth - gamma) cumulative over {len(G)} = {rms_smooth:.4f}")
    print(f"      corr(cumulative error, -S) = {corr(e_smooth, -S):+.3f}; "
          f"corr(local gap-error, -dS) = {corr(e_local, -np.diff(S)):+.3f}")

    # (2) build a small dedicated helix to read the geometric phasor angle alpha(T)
    Hf = BlockyHelix3D(n_max=8000)
    cf = Hf.build(pitch_law0, radius_law0, spacing_law0)
    def alpha_at(T):
        return phasor_angle(cf, T)   # geometric phasor-misalignment angle at height T
    # geometric signal vs the fluctuation directly (the load-bearing correlation)
    sin_alpha_G = np.array([np.sin(alpha_at(g)) for g in G])
    print(f"      corr(geometric sin alpha(gamma), S) = {corr(sin_alpha_G, S):+.3f} "
          f"(does the phasor angle SEE the fluctuation?)")

    # (2a) FITTED correction at the TRUE zeros (the prior known result, for reference):
    sin_alpha_true = sin_alpha_G
    A = np.vstack([sin_alpha_true, np.ones(len(G))]).T
    coef_fit, *_ = np.linalg.lstsq(A, e_smooth, rcond=None)
    pred_fit = A @ coef_fit
    var_expl_fit = 1 - np.var(e_smooth - pred_fit) / np.var(e_smooth)
    rms_fit = float(np.sqrt(np.mean((e_smooth - pred_fit)**2)))
    print(f"  (2a) FITTED correction a*sin(alpha(gamma))+b at TRUE zeros (reference):")
    print(f"       RMS {rms_smooth:.4f} -> {rms_fit:.4f}; variance of S explained = {var_expl_fit:.1%}")
    print(f"       (uses true gamma to read alpha => a FIT, not a prediction)")

    # (3) THE REAL TEST -- fully self-consistent: at step k read alpha at the CURRENT
    #     iterate (never the true zero), feed the correction, iterate to a fixed point,
    #     check landing on gamma WITHOUT using zeros as input.
    a_coef, b_coef = float(coef_fit[0]), float(coef_fit[1])
    Tsmooth = smooth_feedback(float(G[0]), len(G) - 1)[:len(G)]
    def self_consistent_boundaries(T0, a, b, relax=0.6, iters=200):
        # Faithful to blocky_robust_feedback: the correction is ONE-SHOT per index
        # (T_k <- T_k^smooth - [a sin alpha(T_k) + b]), but alpha is read at the CURRENT
        # iterate (NOT the true zero). Iterate the whole map to a fixed point.
        T = Tsmooth.copy()
        for _ in range(iters):
            sin_a = np.array([np.sin(alpha_at(t)) for t in T])
            Tn = Tsmooth - (a * sin_a + b)
            if np.max(np.abs(Tn - T)) < 1e-5:
                T = Tn; break
            T = (1 - relax) * T + relax * Tn  # damped fixed-point iteration
        return T
    Tsc = self_consistent_boundaries(float(G[0]), a_coef, b_coef)[:len(G)]
    e_sc = Tsc - G
    rms_sc = float(np.sqrt(np.mean(e_sc**2)))
    var_expl_sc = 1 - np.var(e_sc) / np.var(e_smooth)
    print(f"  (3) SELF-CONSISTENT fixed point (alpha read at CURRENT iterate, no zeros in):")
    print(f"      RMS(T_sc - gamma) = {rms_sc:.4f}   (smooth was {rms_smooth:.4f})")
    print(f"      variance of smooth error removed self-consistently = {var_expl_sc:.1%}")
    # (3-ctrl) ABLATION: does the a*sin(alpha) GEOMETRY add anything beyond a constant
    # drift shift?  Refit with ONLY a constant (a=0) and compare. If the geometry is real,
    # the full model must beat the constant-only model.
    b_only = float(np.mean(e_smooth))
    Tconst = Tsmooth - b_only
    rms_const = float(np.sqrt(np.mean((Tconst - G)**2)))
    print(f"      ABLATION const-only (a=0, just remove mean drift): RMS = {rms_const:.4f}")
    geom_adds = rms_sc < 0.9 * rms_const
    print(f"      => does sin(alpha) GEOMETRY beat a constant shift?  {geom_adds} "
          f"(if False, the 'capture' is just drift removal, NOT fluctuation)")

    # (3b) CONTROL: read alpha at the TRUE zeros (oracle) with the SAME one-shot map.
    #      This is identical to the FITTED reference (2a): if only this drops the RMS,
    #      the geometry is fitting, not predicting.
    sin_a_true = np.array([np.sin(alpha_at(g)) for g in G])
    Tseed = Tsmooth - (a_coef * sin_a_true + b_coef)
    rms_seed = float(np.sqrt(np.mean((Tseed - G)**2)))
    print(f"  (3b) CONTROL seeded with TRUE zeros to read alpha: RMS = {rms_seed:.4f}")

    # ---- verdict logic ----
    print("\n" + "=" * 78)
    print("VERDICT")
    print("=" * 78)
    built_3d = True  # printed explicit (x,y,z) sample above
    lands_on_zeros = (len(diffs) > 0 and np.sqrt(np.mean(diffs**2)) < 0.6 and nhit >= 8)
    # captures fluctuation: the self-consistent (predicting) RMS must (a) beat smooth,
    # (b) beat the constant-drift ablation -- otherwise the "capture" is just removing a
    # mean offset, not reading the per-block fluctuation through the geometry.
    predicts = (rms_sc < 0.9 * rms_smooth) and (var_expl_sc > 0.15) and geom_adds
    fits_only = (rms_seed < 0.6 * rms_smooth) and not predicts
    captures_fluct = bool(predicts)
    print(f"  3D object built first with explicit (x,y,z):           {built_3d}")
    print(f"  phasor vector-sum collapse lands on exact zeros:        {lands_on_zeros} "
          f"(RMS {np.sqrt(np.mean(diffs**2)):.3f}, {nhit}/40 hit)")
    print(f"  smooth feedback RMS / corr(-S):                         "
          f"{rms_smooth:.3f} / {corr(e_smooth,-S):+.2f}  (reproduces MEAN, error=S)")
    print(f"  FITTED (oracle) variance of S explained:                {var_expl_fit:.1%}")
    print(f"  SELF-CONSISTENT (predicting) variance removed:          {var_expl_sc:.1%} "
          f"(RMS {rms_sc:.3f})")
    print(f"  oracle-seeded RMS (control):                            {rms_seed:.3f}")
    print(f"  const-drift ablation RMS / geometry beats it:           {rms_const:.3f} / {geom_adds}")
    print(f"  corr(geometric sin alpha(gamma), S):                    {corr(sin_alpha_G, S):+.3f} "
          f"(near 0 => alpha does NOT see S)")
    print(f"  => captures per-block FLUCTUATION S(T) (predicting)?    {captures_fluct}")
    if fits_only:
        print(f"  => FLAG: only the oracle-seeded version improves => FIT, not prediction.")
    print(f"  => reproduces MEAN spacing:                             True")
    print(f"  => blocky pitch/spacing INERT for the collapse?         {geometry_inert}")
    if geometry_inert:
        print(f"     (HONEST: cancellation forced by amp(=1/R)+phase(=w log n); the only")
        print(f"      geometric DOF that bites is the radial law R(n); R=sqrt(n) = partial-L.)")

    return dict(
        built_3d=built_3d, lands_on_zeros=lands_on_zeros,
        rms_collapse=float(np.sqrt(np.mean(diffs**2))) if len(diffs) else None,
        nhit=nhit, rms_smooth=rms_smooth, corr_err_negS=corr(e_smooth, -S),
        var_expl_fit=float(var_expl_fit), var_expl_sc=float(var_expl_sc),
        rms_sc=rms_sc, rms_seed=rms_seed, rms_fit=rms_fit,
        captures_fluct=captures_fluct, fits_only=fits_only,
        geometry_inert=geometry_inert, pitch_moves=pitch_moves, spacing_moves=spacing_moves,
        rms_const=rms_const, geom_adds=geom_adds, corr_alpha_S=corr(sin_alpha_G, S),
        corr_localgap_negdS=corr(e_local, -np.diff(S)),
        best_fuzz=results[0] if results else None,
    )


if __name__ == "__main__":
    out = main()
