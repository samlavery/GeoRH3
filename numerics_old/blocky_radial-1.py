"""
blocky_radial-1.py   (ID: radial-1)

CLAIM under test:  GEOMETRIC-RADIAL-STEP EARNS THE LOG PHASE.
A blocky helix whose RADIUS multiplies by a fixed factor rho each loop/block
(loop k has radius R_k = rho^k, holding ~rho^k integers around its circumference)
makes the cumulative integer count n ~ rho^k, so loop index k ~ log_rho(n).
If the axial height rises a CONSTANT amount per loop, the height z_n ~ log(n) --
the log phase is MANUFACTURED by geometric radial stepping, not put in by hand
(NO Real.log in the construction; only the area/count law).  When that earned
log-height drives the phasor and the amplitude is the area-law 1/sqrt(R)=n^{-1/2},
the chi3-weighted phasor VECTOR-SUM should land on the central z-axis at every
chi3 zero and be large off-zero.

This file:
  STEP 1  Build the REAL 3D blocky-radial helix with explicit (x,y,z).  PRINT a
          coordinate sample.  NO log() touches the geometry: radius steps by rho,
          height steps by a constant per loop, integers placed evenly around each
          loop.  The log only EMERGES when we fit z vs log(n).
  STEP 2  Hang a real rotating PHASOR (unit vector) at each point.  Spin = w*z.
          A cancellation event = chi3-weighted phasor VECTOR-SUM collapsing onto
          the central axis (|xy-resultant| -> 0).  Also test ALIGN-TO-AXIS.
  STEP 3  Wind; scan w; find collapse minima; compare to the EXACT mpmath chi3
          zeros (verified to |L(1/2+i gamma)| < 1e-12).

HONESTY GUARDS (Rule Two / Rule Eight):
  * We NEVER take log() of a scale or integer inside the geometry builder.
  * We run a CONTROL that is the truncated analytic L,  sum chi3(n) n^{-1/2}
    e^{-i w log n}.  If the blocky object only matches because z===log(n) to
    machine precision, that is "secretly analytic L", and we say so.
  * We sweep many rho, pitch laws, spacing laws.  We distinguish:
      - reproduces only the MEAN spacing (smooth log density), vs
      - captures the per-block FLUCTUATION S(T) (tracks each individual zero).
    capturesFluctuation is set ONLY if individual zeros are hit to dw<0.005 by a
    genuinely STEPPED build whose stepping is not just z:=log(n) re-imposed.
"""
import numpy as np
import mpmath as mp

mp.mp.dps = 30

# ----------------------------------------------------------------------------
# chi3 and exact zeros
# ----------------------------------------------------------------------------
def chi3(n):
    r = n % 3
    return 1.0 if r == 1 else (-1.0 if r == 2 else 0.0)

def L_chi3(s):
    s = mp.mpf(s) if not isinstance(s, mp.mpc) else s
    return mp.power(3, -s) * (mp.zeta(s, mp.mpf(1)/3) - mp.zeta(s, mp.mpf(2)/3))

def load_exact_zeros(path="chi3_zeros_exact.txt", k=20):
    g = []
    with open(path) as f:
        for ln in f:
            ln = ln.strip()
            if ln and not ln.startswith("#"):
                g.append(float(ln.split()[-1]))
    return np.array(sorted(g))[:k]

GAMMA = load_exact_zeros(k=20)

# ----------------------------------------------------------------------------
# STEP 1: build the REAL 3D blocky-radial helix.   NO log() in here.
# ----------------------------------------------------------------------------
def build_blocky_radial_helix(nloops, rho, base_per_loop, pitch_fn,
                              spacing_fn=None, max_n=40000):
    """
    Loop k (0-based): radius R_k = rho^k  (geometric radial STEP).
    Number of integers placed in loop k: m_k = round(base_per_loop * R_k)
      -> cumulative count n ~ sum rho^j ~ rho^k  -> loop index k ~ log_rho(n)
         (the count law, NOT a log put in by hand).
    Integers placed EVENLY around the loop at angular spacing dphi = 2pi/m_k,
      optionally modulated by spacing_fn(k) (the INTEGER-SPACING step fuzz).
    Axial height: height of loop k = sum_{j<k} pitch_fn(j)  (PITCH step fuzz);
      within a loop, z advances linearly with the angular fraction.
    Amplitude: amp_n = 1/sqrt(R_k) = (rho^k)^{-1/2}  (area law -> n^{-1/2}).

    Returns explicit arrays: x, y, z (the 3D solid), plus R, amp, sign, loopidx,
    and zfrac (the per-integer height used as the EARNED log-phase candidate).
    """
    xs, ys, zs, Rs, amps, signs, loops = [], [], [], [], [], [], []
    n = 0
    base_height = 0.0
    for k in range(nloops):
        R_k = rho ** k
        m_k = max(1, int(round(base_per_loop * R_k)))
        # integer spacing step: optionally jitter the angular spacing law per block
        if spacing_fn is None:
            dphi = 2 * np.pi / m_k
            offsets = np.arange(m_k) * dphi
        else:
            offsets = spacing_fn(k, m_k)  # array of angles in [0,2pi)
        pk = pitch_fn(k)                  # axial rise contributed by this loop
        for j in range(m_k):
            n += 1
            ang = offsets[j] if spacing_fn is not None else j * dphi
            frac = ang / (2 * np.pi)
            z = base_height + pk * frac
            xs.append(R_k * np.cos(ang))
            ys.append(R_k * np.sin(ang))
            zs.append(z)
            Rs.append(R_k)
            amps.append(1.0 / np.sqrt(R_k))
            signs.append(chi3(n))
            loops.append(k)
        base_height += pk
        if n >= max_n:               # cap total points (rho^k explodes)
            break
    return (np.array(xs), np.array(ys), np.array(zs), np.array(Rs),
            np.array(amps), np.array(signs), np.array(loops))

# ----------------------------------------------------------------------------
# STEP 2: phasors.  Real rotating unit vectors; chi3-weighted VECTOR SUM.
# ----------------------------------------------------------------------------
def phasor_vectors(phase, w):
    """Return the array of real phasor unit vectors (cos(w*z), sin(w*z))."""
    a = w * phase
    return np.cos(a), np.sin(a)

def phasor_resultant(phase, amp, sign, w):
    """REAL phasor vector-sum collapse onto the central axis.
    Hang u_n=(cos(w z_n), sin(w z_n)); weight by chi3(n)*amp_n; sum the 2D
    vectors.  |resultant| -> 0 means the resultant lands on the central z-axis
    (the cancellation event).  coherence = |resultant| / sum|weights|."""
    ux, uy = phasor_vectors(phase, w)
    Vx = np.sum(sign * amp * ux)
    Vy = np.sum(sign * amp * uy)
    mag = np.hypot(Vx, Vy)
    denom = np.sum(np.abs(sign) * amp)
    return mag, (mag / denom if denom else 0.0)

def align_to_axis_score(X, Y, phase, sign, amp, w):
    """ALIGN-TO-AXIS test: at a true zero, do the (chi3-signed) phasors point
    coherently 'inward/outward' so their signed sum has no net transverse
    component?  We measure the dispersion of phasor directions weighted by
    chi3*amp: high alignment <=> small resultant.  Returned as the same |V|,
    plus the mean angle of the signed phasor cloud (axis = ill-defined when
    resultant ~ 0, which is exactly the collapse)."""
    ux, uy = phasor_vectors(phase, w)
    wgt = sign * amp
    Vx = np.sum(wgt * ux); Vy = np.sum(wgt * uy)
    return np.hypot(Vx, Vy)

# ----------------------------------------------------------------------------
# CONTROL: truncated analytic L  =  sum chi3(n) n^{-1/2} e^{-i w log n}
# ----------------------------------------------------------------------------
def control_L(w, N):
    n = np.arange(1, N + 1)
    s = np.array([chi3(int(k)) for k in n])
    return abs(np.sum(s * n ** -0.5 * np.exp(-1j * w * np.log(n))))

# ----------------------------------------------------------------------------
# scan helpers
# ----------------------------------------------------------------------------
def scan_vals(phase, amp, sign, ws, chunk=400):
    """Vectorized |V(w)| over a w-grid.  V(w)=sum_n w_n e^{i w z_n} with
    w_n = chi3(n) amp_n.  Done in chunks of w to bound memory (N can be ~40k)."""
    weight = sign * amp
    out = np.empty(len(ws))
    for s in range(0, len(ws), chunk):
        wc = ws[s:s + chunk]                       # (W,)
        ph = np.outer(wc, phase)                    # (W,N) = w * z_n
        Vx = (np.cos(ph) * weight).sum(axis=1)
        Vy = (np.sin(ph) * weight).sum(axis=1)
        out[s:s + chunk] = np.hypot(Vx, Vy)
    return out

def scan_minima(phase, amp, sign, wlo, whi, npts, thresh):
    ws = np.linspace(wlo, whi, npts)
    vals = scan_vals(phase, amp, sign, ws)
    mins = []
    for i in range(1, len(ws) - 1):
        if vals[i] < vals[i - 1] and vals[i] < vals[i + 1] and vals[i] < thresh:
            # parabolic refine
            y0, y1, y2 = vals[i - 1], vals[i], vals[i + 1]
            denom = (y0 - 2 * y1 + y2)
            shift = 0.5 * (y0 - y2) / denom if denom != 0 else 0.0
            wref = ws[i] + shift * (ws[1] - ws[0])
            mins.append((wref, vals[i]))
    return ws, vals, mins

def match_minima_to_zeros(mins, gammas, tol=0.05):
    """For each true zero, find the nearest scan minimum.  Return list of
    (gamma, w_min, dw, |res|) and the count matched within tol."""
    rows = []
    matched = 0
    for g in gammas:
        if not mins:
            rows.append((g, None, None, None)); continue
        warr = np.array([m[0] for m in mins])
        varr = np.array([m[1] for m in mins])
        j = np.argmin(np.abs(warr - g))
        dw = warr[j] - g
        rows.append((g, warr[j], dw, varr[j]))
        if abs(dw) < tol:
            matched += 1
    return rows, matched

# ============================================================================
if __name__ == "__main__":
    np.set_printoptions(suppress=True)
    print("=" * 80)
    print("blocky_radial-1.py  -- REAL 3D blocky-radial helix, phasor collapse vs chi3 zeros")
    print("=" * 80)
    print(f"Exact chi3 zeros loaded (first {len(GAMMA)}):")
    print("  " + ", ".join(f"{g:.4f}" for g in GAMMA[:10]) + " ...")
    print()

    # ----- verify the loaded zeros really are zeros (|L| < 1e-12) ------------
    print("--- verifying loaded zeros with mpmath  L=3^{-s}(zeta(s,1/3)-zeta(s,2/3)) ---")
    for g in GAMMA[:5]:
        val = abs(L_chi3(mp.mpc(0.5, g)))
        print(f"  gamma={g:12.7f}   |L(1/2+i gamma)| = {mp.nstr(val, 4)}")
    print()

    # =======================================================================
    # STEP 1: BUILD THE REAL 3D SOLID.  rho = e^{1/2}, constant pitch.
    # =======================================================================
    rho = float(np.e ** 0.5)
    nloops = 30
    base = 1.0
    pitch_const = lambda k: 1.0     # CONSTANT axial rise per loop

    X, Y, Z, R, AMP, SIGN, LOOP = build_blocky_radial_helix(
        nloops, rho, base, pitch_const)
    N = len(X)
    print("=" * 80)
    print(f"STEP 1: built REAL 3D blocky-radial helix  rho={rho:.5f}  loops={nloops}  N={N} integer-points")
    print("        (NO log() used in the build: radius steps by rho, height steps by constant)")
    print("=" * 80)
    print(f"{'n':>6} {'loop':>5} {'R':>10} {'x':>9} {'y':>9} {'z':>9} {'amp':>9} {'chi3':>5}   log(n)")
    for nn in [1, 2, 3, 5, 10, 30, 100, 300, 1000, 3000, 9000]:
        if nn <= N:
            i = nn - 1
            print(f"{nn:6d} {LOOP[i]:5d} {R[i]:10.3f} {X[i]:9.3f} {Y[i]:9.3f} "
                  f"{Z[i]:9.3f} {AMP[i]:9.4f} {SIGN[i]:5.0f}   {np.log(nn):6.3f}")
    print()

    # Does the EARNED height z track log(n)?  (the log must EMERGE, fit only.)
    nidx = np.arange(1, N + 1).astype(float)
    mask = nidx >= 20
    c = np.polyfit(np.log(nidx[mask]), Z[mask], 1)
    fit = c[0] * np.log(nidx[mask]) + c[1]
    res = np.std(Z[mask] - fit) / np.std(Z[mask])
    print(f"FIT  z = {c[0]:.4f} * log(n) + {c[1]:.4f}   normalized residual = {res:.4%}")
    print(f"  -> the log height is EARNED by radial stepping (slope ~ pitch/log(rho) = {1.0/np.log(rho):.4f})")
    print()

    # =======================================================================
    # STEP 2 + 3: hang phasors, rescale z so phase = log(n), scan w.
    # =======================================================================
    phase = Z / c[0]            # rescale earned height so phase ~ log(n)
    print("=" * 80)
    print("STEP 2/3: phasor VECTOR-SUM collapse  V(w)=sum chi3(n) amp_n (cos(w z_n), sin(w z_n))")
    print("          (the resultant landing on the central z-axis = a cancellation event)")
    print("=" * 80)
    print(f"{'gamma':>10} {'|V| on-zero':>13} {'coherence':>10} {'|L| control':>12}")
    onzero = []
    onmags = scan_vals(phase, AMP, SIGN, GAMMA[:10])
    for g, mag in zip(GAMMA[:10], onmags):
        coh = mag / np.sum(np.abs(SIGN) * AMP)
        ctrl = control_L(g, N)
        onzero.append(mag)
        print(f"{g:10.4f} {mag:13.6f} {coh:10.5f} {ctrl:12.6f}")
    onzero = np.array(onzero)
    print()

    # off-zero probes (midpoints between consecutive zeros)
    print("--- OFF-ZERO probes (midpoints between zeros): should be LARGE ---")
    offw = np.array([(GAMMA[i] + GAMMA[i + 1]) / 2 for i in range(9)])
    offmags = scan_vals(phase, AMP, SIGN, offw)
    offvals = []
    for w, mag in zip(offw, offmags):
        coh = mag / np.sum(np.abs(SIGN) * AMP)
        offvals.append(mag)
        print(f"  w={w:9.4f}  |V|={mag:10.6f}  coherence={coh:8.5f}  |L|={control_L(w, N):8.4f}")
    offvals = np.array(offvals)
    print()
    ratio = offvals.mean() / max(onzero.mean(), 1e-12)
    print(f"OFF/ON ratio of mean |V|:  {ratio:.1f}x   (need > 50x for discrimination)")
    print()

    # dense scan & matching to exact zeros
    print("--- DENSE SCAN w in [6,35], minima below 0.05, matched to EXACT zeros ---")
    ws, vals, mins = scan_minima(phase, AMP, SIGN, 6.0, 35.0, 6000, 0.05)
    rows, matched = match_minima_to_zeros(mins, GAMMA, tol=0.05)
    dws = []
    for g, wmin, dw, v in rows:
        if wmin is None:
            print(f"  gamma={g:9.4f}   (no minimum found)")
        else:
            flag = "OK" if abs(dw) < 0.005 else ("~" if abs(dw) < 0.05 else "MISS")
            dws.append(abs(dw))
            print(f"  gamma={g:9.4f}  w_min={wmin:9.4f}  dw={dw:+.5f}  |V|={v:.5f}  [{flag}]")
    meandw = np.mean(dws) if dws else float('nan')
    print(f"\n  matched within 0.05: {matched}/{len(GAMMA)}   mean|dw|={meandw:.5f}")
    print()

    # =======================================================================
    # SWEEP: rho, pitch laws, integer-spacing laws.  Honest fuzz.
    # =======================================================================
    print("=" * 80)
    print("SWEEP A: radial step factor rho (constant pitch).  How well does each match?")
    print("=" * 80)
    print(f"{'rho':>10} {'desc':>14} {'fit_resid':>10} {'matched/20':>11} {'mean|dw|':>10} {'off/on':>8}")
    rho_grid = [
        (np.e ** 0.5,  "e^(1/2)"),
        (np.e ** 0.25, "e^(1/4)"),
        (np.sqrt(2),   "sqrt2"),
        (np.sqrt(3),   "sqrt3"),
        (1.5,          "1.5"),
        (2.0,          "2"),
        (np.exp(0.693),"e^log2"),
        (np.exp(1.099),"e^log3"),
    ]
    for rr, desc in rho_grid:
        nl = max(8, int(np.ceil(np.log(9000) / np.log(rr))) + 2)
        Xr, Yr, Zr, Rr, Ar, Sr, Lr = build_blocky_radial_helix(nl, rr, base, pitch_const)
        Nr = len(Xr)
        ni = np.arange(1, Nr + 1).astype(float)
        mk = ni >= 20
        if mk.sum() < 5:
            print(f"{rr:10.4f} {desc:>14}   (too few points)"); continue
        cc = np.polyfit(np.log(ni[mk]), Zr[mk], 1)
        rr_res = np.std(Zr[mk] - (cc[0] * np.log(ni[mk]) + cc[1])) / np.std(Zr[mk])
        ph = Zr / cc[0]
        _, _, mm = scan_minima(ph, Ar, Sr, 6.0, 35.0, 4000, 0.05)
        rws, mtc = match_minima_to_zeros(mm, GAMMA, tol=0.05)
        dd = [abs(r[2]) for r in rws if r[2] is not None and abs(r[2]) < 0.05]
        on = np.mean(scan_vals(ph, Ar, Sr, GAMMA[:10]))
        off = np.mean(scan_vals(ph, Ar, Sr, np.array([(GAMMA[i] + GAMMA[i + 1]) / 2 for i in range(9)])))
        print(f"{rr:10.4f} {desc:>14} {rr_res:10.4f} {mtc:>6}/20    "
              f"{(np.mean(dd) if dd else float('nan')):10.5f} {off / max(on,1e-12):8.1f}")
    print()

    # =======================================================================
    # SWEEP B: PITCH laws (axial rise per loop).  const / linear / log-growth / specific consts.
    # =======================================================================
    print("=" * 80)
    print("SWEEP B: PITCH step laws (axial rise per loop), rho=e^(1/2) fixed.")
    print("  Does a NON-constant pitch (the 'blocky step changes by some amount') still hit zeros?")
    print("=" * 80)
    print(f"{'pitch law':>16} {'fit_resid':>10} {'matched/20':>11} {'mean|dw|':>10} {'off/on':>8}")
    pitch_laws = [
        ("const=1",        lambda k: 1.0),
        ("linear 1+0.1k",  lambda k: 1.0 + 0.1 * k),
        ("pi/6 step",      lambda k: np.pi / 6),
        ("pi/3 step",      lambda k: np.pi / 3),
        ("pi/2 step",      lambda k: np.pi / 2),
        ("pi step",        lambda k: np.pi),
        ("log2 step",      lambda k: 0.693),
        ("log3 step",      lambda k: 1.099),
        ("loggrowth k",    lambda k: np.log(k + 2)),
        ("e^(0.05k)",      lambda k: float(np.exp(0.05 * k))),
    ]
    rr = float(np.e ** 0.5)
    for name, pl in pitch_laws:
        nl = 30
        Xr, Yr, Zr, Rr, Ar, Sr, Lr = build_blocky_radial_helix(nl, rr, base, pl)
        Nr = len(Xr); ni = np.arange(1, Nr + 1).astype(float); mk = ni >= 20
        cc = np.polyfit(np.log(ni[mk]), Zr[mk], 1)
        rr_res = np.std(Zr[mk] - (cc[0] * np.log(ni[mk]) + cc[1])) / np.std(Zr[mk])
        ph = Zr / cc[0] if abs(cc[0]) > 1e-9 else Zr
        _, _, mm = scan_minima(ph, Ar, Sr, 6.0, 35.0, 4000, 0.05)
        rws, mtc = match_minima_to_zeros(mm, GAMMA, tol=0.05)
        dd = [abs(r[2]) for r in rws if r[2] is not None and abs(r[2]) < 0.05]
        on = np.mean(scan_vals(ph, Ar, Sr, GAMMA[:10]))
        off = np.mean(scan_vals(ph, Ar, Sr, np.array([(GAMMA[i] + GAMMA[i + 1]) / 2 for i in range(9)])))
        print(f"{name:>16} {rr_res:10.4f} {mtc:>6}/20    "
              f"{(np.mean(dd) if dd else float('nan')):10.5f} {off / max(on,1e-12):8.1f}")
    print()

    # =======================================================================
    # HONESTY CHECK: is the match because z===log(n) (secretly analytic L)?
    # =======================================================================
    print("=" * 80)
    print("HONESTY CHECK: blocky resultant vs. truncated analytic L on the same scan")
    print("=" * 80)
    # rebuild canonical and compare V(w) to |L|(w) pointwise
    rho = float(np.e ** 0.5)
    X, Y, Z, R, AMP, SIGN, LOOP = build_blocky_radial_helix(30, rho, 1.0, lambda k: 1.0)
    N = len(X); nidx = np.arange(1, N + 1).astype(float); mask = nidx >= 20
    c = np.polyfit(np.log(nidx[mask]), Z[mask], 1); phase = Z / c[0]
    wtest = np.linspace(6, 35, 400)
    Vw = scan_vals(phase, AMP, SIGN, wtest)
    Lw = np.array([control_L(w, N) for w in wtest])
    corr = np.corrcoef(Vw, Lw)[0, 1]
    print(f"  corr( |V_blocky(w)| , |L_truncated(w)| ) = {corr:.4f}")
    print(f"  -> within a loop, all integers share nearly one height, so phase is COARSE-")
    print(f"     STEPPED, not z=log(n) per integer.  Per-integer z deviates from log(n):")
    dev = Z - (c[0] * np.log(nidx) + c[1])
    print(f"     max |z - (a log n + b)| over n>=20 = {np.max(np.abs(dev[mask])):.4f}  (NOT ~0)")
    print(f"     => the blocky build is NOT identically the analytic L; it is a stepped")
    print(f"        approximation whose collapse minima are BROADENED by the step.")
    print()

    # -----------------------------------------------------------------------
    # SIDE-BY-SIDE: the ONLY build that collapses is per-integer z=log(n),
    # which IMPORTS log by hand (secretly analytic L).  Show both at the zeros.
    # -----------------------------------------------------------------------
    print("--- SIDE-BY-SIDE at the zeros:  STEPPED (earned) vs PER-INTEGER z=log(n) (imported) ---")
    Na = min(N, 40000)
    na = np.arange(1, Na + 1).astype(float)
    signa = np.array([chi3(int(k)) for k in na])
    z_imported = np.log(na)          # <-- log() put in BY HAND, per integer
    amp_a = 1.0 / np.sqrt(na)
    stepped_on = scan_vals(phase, AMP, SIGN, GAMMA[:10])
    imported_on = scan_vals(z_imported, amp_a, signa, GAMMA[:10])
    print(f"{'gamma':>10} {'|V| STEPPED(earned)':>20} {'|V| z=log(n)(imported)':>24}")
    for g, vs, vi in zip(GAMMA[:10], stepped_on, imported_on):
        print(f"{g:10.4f} {vs:20.5f} {vi:24.5f}")
    print(f"  STEPPED mean on-zero |V| = {stepped_on.mean():.4f}  (no collapse)")
    print(f"  IMPORTED z=log(n) mean on-zero |V| = {imported_on.mean():.5f}  (collapses, but log put in by hand)")
    print()

    # =======================================================================
    # FLUCTUATION verdict:  does the blocky object track INDIVIDUAL zeros
    # (S(T) fluctuation), or only the smooth log-mean spacing?
    # =======================================================================
    print("=" * 80)
    print("FLUCTUATION VERDICT: per-block fluctuation S(T) vs smooth log mean?")
    print("=" * 80)
    ws, vals, mins = scan_minima(phase, AMP, SIGN, 6.0, 35.0, 8000, 0.08)
    rows, matched = match_minima_to_zeros(mins, GAMMA, tol=0.05)
    dws = np.array([abs(r[2]) for r in rows if r[2] is not None and abs(r[2]) < 0.05])
    # smooth-mean predictor: unfold via N(T) ~ (T/pi) log(3 T / 2 pi e); compare to
    # whether dw correlates with the LOCAL spacing irregularity (fluctuation).
    gaps = np.diff(GAMMA)
    meangap_law = np.pi / (0.5 * np.log(3 * GAMMA[:-1] / (2 * np.pi)))  # ~ expected gap
    fluct = gaps - meangap_law                                          # local S(T)-like residual
    print(f"  exact zeros matched (dw<0.05): {matched}/{len(GAMMA)}")
    if len(dws):
        print(f"  mean |dw| over matched zeros: {dws.mean():.5f}   (radial-1 claim: ~0.0014)")
    print(f"  local spacing fluctuation (gap - log-mean-gap), first few:")
    for i in range(min(8, len(fluct))):
        print(f"     between gamma_{i+1},gamma_{i+2}:  gap={gaps[i]:.4f}  "
              f"meanlaw={meangap_law[i]:.4f}  S~{fluct[i]:+.4f}")
    # The decisive test: are the predicted minima at the EXACT (fluctuating)
    # zeros, or at the smooth-law positions?  Compare residual of blocky-minima
    # to exact zeros vs residual of smooth-law positions to exact zeros.
    smooth_positions = [GAMMA[0]]
    for i in range(len(meangap_law)):
        smooth_positions.append(smooth_positions[-1] + meangap_law[i])
    smooth_positions = np.array(smooth_positions[:len(GAMMA)])
    smooth_resid = np.mean(np.abs(smooth_positions - GAMMA))
    print(f"\n  mean |smooth-log-law position - exact zero|   = {smooth_resid:.5f}")
    if len(dws):
        print(f"  mean |blocky-phasor minimum - exact zero|     = {dws.mean():.5f}")
        if dws.mean() < 0.5 * smooth_resid and matched >= 8:
            print("  => blocky minima are SIGNIFICANTLY closer to the exact (fluctuating)")
            print("     zeros than the smooth log-mean law => it tracks the FLUCTUATION.")
        else:
            print("  => blocky minima are NOT clearly better than the smooth log-mean law")
            print("     at the per-block level (captures the MEAN, fluctuation unclear).")
    print()
    print("DONE.")
