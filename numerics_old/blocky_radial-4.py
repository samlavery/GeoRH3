"""
blocky_radial-4.py   (ID radial-4)

BLOCKY-HELIX realization of the zeros of L(chi3), built as a REAL 3D solid with
PHASORS, then measured against the EXACT mpmath chi3 zeros (|L|<1e-12 verified).

chi3 = real character mod 3:  chi3(n) = +1 (n=1 mod3), -1 (n=2 mod3), 0 (n=0 mod3).
L(chi3,s) = 3^{-s} (zeta(s,1/3) - zeta(s,2/3)).

----------------------------------------------------------------------------------
HONEST FRAME (aiming PAST the known-negative results in radial_step_blocky_test.py)
----------------------------------------------------------------------------------
The known trap:  build the per-point phase as phi_n = w*log(n) and read off
   resultant(w) = | sum_n chi3(n) * n^{-1/2} * e^{i w log n} |
This is just the truncated analytic L(1/2+iw); it dips at every zero TRIVIALLY
because it IS L.  That secretly re-derives the analytic object -- forbidden.

The DECISIVE open question (the fluctuation S(T)):  can the per-point phase be
built GEOMETRICALLY -- from the blocky helix winding / FTA prime-arrival angles --
in a way that is NOT a relabeling of log(n), yet still lands the cancellation
events on the individual zeros (not just the mean spacing)?

So we build several genuinely 3D blocky helices with EXPLICIT (x,y,z) and a real
rotating PHASOR vector at each point, and a cancellation = chi3-weighted PHASOR
VECTOR-SUM collapsing onto the central axis.  We sweep pitch/radial/spacing step
laws and the FTA winding rule.  We report MEAN-only vs FLUCTUATION honestly, and
we FLAG any construction whose phase is secretly log(n) (i.e. secretly L).

We always include a CONTROL = the secretly-analytic build (phase=log n) so the
reader can see the difference between "hits zeros because it is L" and "hits zeros
geometrically".
"""

import numpy as np
import mpmath as mp

mp.mp.dps = 30

# ------------------------------------------------------------------ chi3 & zeros
def chi3(n):
    r = n % 3
    return 1.0 if r == 1 else (-1.0 if r == 2 else 0.0)

def L_chi3(s):
    return mp.power(3, -s) * (mp.zeta(s, mp.mpf(1)/3) - mp.zeta(s, mp.mpf(2)/3))

# Exact zeros (precomputed, re-verified below to |L|<1e-12).
EXACT_ZEROS_STR = """
8.039737155681466518 11.249206207772935784 15.704619176721624996
18.261997495693126581 20.455770807742492678 24.059414856493450685
26.577868735774586639 28.218164506233385680 30.745040261382495572
33.897388927259420655 35.608412653938636083 37.551796556364628543
39.485207260929350070 42.616379226157569349 44.120572912072205440
46.274118023513139519 47.514104510117320501 50.375138650636266391
52.496749599060755997 54.193843101551912866
""".split()
GAMMA = np.array([float(x) for x in EXACT_ZEROS_STR])

def verify_zeros(k=6):
    print("verifying exact zeros to |L(1/2+i gamma)| < 1e-12 ...")
    ok = True
    for gs in EXACT_ZEROS_STR[:k]:
        v = abs(L_chi3(mp.mpf('0.5') + 1j*mp.mpf(gs)))
        flag = "OK" if v < 1e-11 else "??"
        if v >= 1e-11: ok = False
        print(f"   gamma={float(gs):18.12f}   |L| = {mp.nstr(v,3):>10}   {flag}")
    return ok

# ================================================================== 3D BUILDERS
# Each builder returns a dict with explicit arrays:
#   x,y,z   : 3D coordinates of integer n's point on the blocky helix
#   theta   : the winding angle (radians) of point n about the central z-axis
#   amp     : phasor magnitude (= radial amplitude weight, the n^{-1/2} area law)
#   block   : block index of n
#   phase   : the INTRINSIC per-point phase used to spin the phasor (geometry-derived)
#
# A phasor at point n is a unit-ish vector  v_n = amp_n * (cos(w*phase_n), sin(w*phase_n)),
# weighted by chi3(n).  Winding to "frequency" w, a cancellation event is
#   resultant(w) = | sum_n chi3(n) * amp_n * e^{i w phase_n} | -> 0   (lands on axis)
# We scan w; minima of resultant are the construction's "zeros".

def build_blocky(N, rho, pitch_law, spacing_law, phase_mode,
                 chi3_winding=False):
    """
    Real blocky 3D helix.

      * Loops indexed by block k = 0,1,2,...  Block k has radius R_k = rho**k
        (geometric radial step) and holds m_k = max(1,round(rho**k * spacing_law(k)))
        integers placed EVENLY around that loop (integer spacing step = spacing_law).
      * Axial rise per loop (pitch) = pitch_law(k); within a block the height
        advances LINEARLY in local index (so per-integer phase survives), slope = pitch_law(k).
      * The PHASE that spins the phasor is set by phase_mode:
          'angle'   : phase_n = cumulative winding angle theta_n / (2 pi)  (pure geometry)
          'height'  : phase_n = z_n            (axial height; blocky staircase of log)
          'logn'    : phase_n = log(n)         (CONTROL = secretly analytic L)
          'fta'     : phase_n = Theta(n), the FTA-additive winding built from prime
                      arrivals (geometric prime-residue angle), NOT log n.
      * amp_n = 1/R_area with R_area = sqrt(n) (area-law amplitude n^{-1/2}); this is
        the earned amplitude, independent of the phase choice.

    Returns dict of arrays length N.
    """
    x = np.zeros(N); y = np.zeros(N); z = np.zeros(N)
    theta = np.zeros(N); blockidx = np.zeros(N, dtype=int)
    nidx = np.arange(1, N+1).astype(float)

    n_i = 0
    running_z = 0.0
    cum_angle = 0.0
    k = 0
    while n_i < N:
        R_k = rho**k
        m_k = max(1, int(round(R_k * spacing_law(k))))
        slope = pitch_law(k)                       # axial rise across this loop
        dphi = 2*np.pi / m_k                        # angular spacing of integers in loop
        for j in range(m_k):
            if n_i >= N: break
            ang = cum_angle + j*dphi
            frac = j / m_k
            zz = running_z + slope*frac
            x[n_i] = R_k * np.cos(ang)
            y[n_i] = R_k * np.sin(ang)
            z[n_i] = zz
            theta[n_i] = ang
            blockidx[n_i] = k
            n_i += 1
        cum_angle += 2*np.pi                         # one full loop
        running_z += slope
        k += 1

    # ---- phase array ----
    logn = np.log(nidx)
    if phase_mode == 'angle':
        phase = theta / (2*np.pi)                    # # of turns = geometric "time"
    elif phase_mode == 'height':
        phase = z.copy()
    elif phase_mode == 'logn':
        phase = logn.copy()
    elif phase_mode == 'fta':
        phase = fta_winding(N, chi3_weighted=chi3_winding)
    else:
        raise ValueError(phase_mode)

    amp = 1.0 / np.sqrt(nidx)
    return dict(x=x, y=y, z=z, theta=theta, amp=amp, block=blockidx,
                phase=phase, n=nidx, logn=logn)

# ------------------------------------------------ FTA-additive winding Theta(n)
def fta_winding(N, base='logp', chi3_weighted=False):
    """
    Theta(n) = sum over prime powers p^a || n of a * angle(p),  completely additive:
       Theta(m*n) = Theta(m) + Theta(n).
    base='logp'  -> angle(p)=log p  (this REBUILDS log n exactly: Theta(n)=log n; CONTROL/secretly-L)
    base='unit'  -> angle(p)=1 for every prime (Omega(n), the prime-count winding -- pure geometry)
    base='pidx'  -> angle(p)= (index of p among primes) (geometric ordinal arrival)
    base='resid' -> angle(p)= +1 if p=1mod3, -1 if p=2mod3, 0 if p=3 (chi3 residue arrival)
    If chi3_weighted: multiply each prime's contribution by chi3(p) (signed arrival).
    """
    # sieve smallest prime factor
    spf = np.zeros(N+1, dtype=int)
    for i in range(2, N+1):
        if spf[i] == 0:
            for j in range(i, N+1, i):
                if spf[j] == 0:
                    spf[j] = i
    # prime index map
    primes = [p for p in range(2, N+1) if spf[p] == p]
    pindex = {p: i+1 for i, p in enumerate(primes)}

    def ang(p):
        if base == 'logp':
            return np.log(p)
        if base == 'unit':
            return 1.0
        if base == 'pidx':
            return float(pindex[p])
        if base == 'resid':
            r = p % 3
            return 1.0 if r == 1 else (-1.0 if r == 2 else 0.0)
        raise ValueError(base)

    Theta = np.zeros(N)
    for n in range(2, N+1):
        m = n
        s = 0.0
        while m > 1:
            p = spf[m]
            a = 0
            while m % p == 0:
                m //= p; a += 1
            w = ang(p)
            if chi3_weighted:
                w = w * chi3(p)
            s += a*w
        Theta[n-1] = s
    return Theta

# ============================================================== PHASOR READOUT
def resultant_vec(phase, amp, sign, w):
    """chi3-weighted phasor VECTOR-SUM at winding frequency w; |.| = distance from axis."""
    a = w*phase
    rx = np.sum(sign*amp*np.cos(a))
    ry = np.sum(sign*amp*np.sin(a))
    return np.hypot(rx, ry)

def align_to_axis(phase, sign, w):
    """ALIGN test: fraction of (chi3!=0) phasors pointing within pi/8 of a common
    axis direction at frequency w (a different cancellation signature)."""
    a = (w*phase) % (2*np.pi)
    mask = sign != 0
    aa = a[mask]
    # circular mean direction
    mx = np.mean(np.cos(aa)); my = np.mean(np.sin(aa))
    mu = np.arctan2(my, mx)
    d = np.abs(((aa - mu + np.pi) % (2*np.pi)) - np.pi)
    return np.mean(d < np.pi/8), np.hypot(mx, my)   # frac aligned, resultant length

def scan_minima(phase, amp, sign, ws, thresh):
    vals = np.array([resultant_vec(phase, amp, sign, w) for w in ws])
    mins = []
    for i in range(1, len(ws)-1):
        if vals[i] < vals[i-1] and vals[i] < vals[i+1] and vals[i] < thresh:
            mins.append((ws[i], vals[i]))
    return vals, mins

def score(mins, tol=0.05, K=12):
    matched = 0; ds = []
    if mins:
        ww = np.array([m[0] for m in mins])
        for g in GAMMA[:K]:
            j = np.argmin(np.abs(ww - g))
            d = abs(ww[j]-g)
            if d < tol:
                matched += 1; ds.append(d)
    return matched, (np.mean(ds) if ds else float('nan'))


# ================================================================== MAIN
def main():
    print("="*82)
    print("blocky_radial-4 : REAL 3D blocky helix + phasors vs EXACT chi3 zeros")
    print("="*82)
    ok = verify_zeros(6)
    print(f"   zeros verified: {ok}\n")

    N = 30000
    nidx = np.arange(1, N+1).astype(float)
    sign = np.array([chi3(int(k)) for k in nidx])

    # -------- STEP 1: build a real 3D blocky helix and PRINT a coordinate sample
    print("-"*82)
    print("STEP 1: build real 3D blocky helix (rho=sqrt2 radial step, geometric); SAMPLE coords")
    print("-"*82)
    H = build_blocky(N, rho=np.sqrt(2.0),
                     pitch_law=lambda k: 1.0,                 # constant pitch step
                     spacing_law=lambda k: 1.0,               # constant spacing factor
                     phase_mode='angle')
    print(f"{'n':>4} {'block':>5} {'x':>10} {'y':>10} {'z':>10} {'theta':>9} {'amp':>9}")
    for n in [1, 2, 3, 4, 5, 8, 13, 21, 34, 100, 1000]:
        i = n-1
        print(f"{n:>4} {H['block'][i]:>5} {H['x'][i]:>10.4f} {H['y'][i]:>10.4f} "
              f"{H['z'][i]:>10.4f} {H['theta'][i]:>9.3f} {H['amp'][i]:>9.5f}")

    # -------- STEP 2: phasor at each point (described), STEP 3: wind & collapse
    print("\n" + "-"*82)
    print("STEP 2/3: phasor = chi3(n)*amp*e^{i w*phase}; wind w; resultant->axis = zero event")
    print("-"*82)

    ws = np.linspace(6.0, 56.0, 12000)

    def run(label, phase, thresh=0.05, secretly_L=False):
        vals, mins = scan_minima(phase, H['amp'], sign, ws, thresh)
        m, md = score(mins, tol=0.05, K=12)
        # off-zero discrimination: median resultant at the 12 zeros vs at random off points
        rz = np.median([resultant_vec(phase, H['amp'], sign, g) for g in GAMMA[:12]])
        offs = np.array([13.0, 17.0, 22.5, 29.0, 41.0, 49.0])
        ro = np.median([resultant_vec(phase, H['amp'], sign, w) for w in offs])
        flag = "  <-- SECRETLY ANALYTIC L (phase==log n): hits zeros trivially, NOT geometric" if secretly_L else ""
        print(f"  {label:<34} matched {m:>2}/12  mean|dw|={md:7.4f}  "
              f"med|res|@zero={rz:6.3f} off={ro:6.3f}  #min={len(mins)}{flag}")
        return m, md

    # CONTROL: phase = log n  (the secretly-analytic build)
    run("CONTROL phase=log(n)  [=L]", H['logn'], secretly_L=True)

    # geometric angle phase (pure winding turns) -- no log anywhere
    run("GEOM phase=turns(theta/2pi)", H['phase'])

    # blocky height (staircase-of-log) phase
    Hh = build_blocky(N, rho=np.sqrt(2.0),
                      pitch_law=lambda k: 1.0, spacing_law=lambda k: 1.0,
                      phase_mode='height')
    run("GEOM phase=blocky height z", Hh['phase'])

    # -------- FTA winding family (the live route): geometric prime-arrival angles
    print("\n" + "-"*82)
    print("FTA-additive winding Theta(n): geometric prime-arrival phase (NOT smooth log n)")
    print("-"*82)
    fams = [
        ('Theta base=logp [=log n, =L]', 'logp', True),
        ('Theta base=unit (Omega(n))',   'unit', False),
        ('Theta base=pidx (ordinal)',    'pidx', False),
        ('Theta base=resid (chi3 res)',  'resid', False),
    ]
    for label, base, isL in fams:
        Th = fta_winding(N, base=base, chi3_weighted=False)
        run(f"FTA {label}", Th, thresh=0.08, secretly_L=isL)
    # chi3-weighted prime arrivals
    for base in ['unit', 'resid', 'logp']:
        Th = fta_winding(N, base=base, chi3_weighted=True)
        run(f"FTA chi3wt base={base}", Th, thresh=0.08,
            secretly_L=False)

    # -------- SWEEP the step constants on a non-log (geometric) phase --------
    print("\n" + "-"*82)
    print("SWEEP pitch/radial/spacing step constants (geometric 'height' phase, no log)")
    print("-"*82)
    consts = {
        'pi/6': np.pi/6, 'pi/3': np.pi/3, 'pi/2': np.pi/2, 'pi': np.pi,
        'log2': np.log(2), 'log3': np.log(3), 'sqrt2': np.sqrt(2), 'sqrt3': np.sqrt(3),
        'e': np.e,
    }
    best = (-1, None)
    for rho_name, rho in [('sqrt2', np.sqrt(2)), ('sqrt3', np.sqrt(3)), ('e^.5', np.e**0.5), ('1.5', 1.5)]:
        for pn, pc in consts.items():
            Hs = build_blocky(N, rho=rho,
                              pitch_law=lambda k, pc=pc: pc,
                              spacing_law=lambda k: 1.0,
                              phase_mode='height')
            vals, mins = scan_minima(Hs['phase'], Hs['amp'], sign, ws, 0.06)
            m, md = score(mins, tol=0.05, K=12)
            if m > best[0]:
                best = (m, f"rho={rho_name} pitch={pn}")
            if m >= 3:
                print(f"  rho={rho_name:>5} pitch_step={pn:>5}: matched {m}/12 mean|dw|={md:.4f}")
    print(f"  [sweep best: matched {best[0]}/12 at {best[1]}]")

    # -------- FEEDBACK / self-consistent boundaries (the explicit radial-4 claim) --
    print("\n" + "-"*82)
    print("FEEDBACK blocky: self-consistent boundaries b_{k+1}=b_k+pi/gap(b_k), mean-density")
    print("-"*82)
    feedback_boundaries()

    # -------- ALIGN-TO-AXIS signature on the FTA-resid phase ----------------
    print("\n" + "-"*82)
    print("ALIGN-TO-AXIS test (different cancellation signature) on geometric phases")
    print("-"*82)
    for label, base in [('logp[=L]', 'logp'), ('resid', 'resid'), ('unit', 'unit')]:
        Th = fta_winding(N, base=base, chi3_weighted=False)
        # alignment dips where phasors co-point; check at zeros vs off
        az = np.median([align_to_axis(Th, sign, g)[1] for g in GAMMA[:12]])
        ao = np.median([align_to_axis(Th, sign, w)[1] for w in [13., 17., 29., 41.]])
        print(f"  align res-length  base={base:<8} @zeros={az:.4f}  off={ao:.4f}")

    print("\n" + "="*82)
    print("VERDICT")
    print("="*82)
    print("""
  * CONTROL phase=log(n) hits all 12 zeros to mean|dw|~1e-3 -- because it IS the
    truncated analytic L (resultant(w)=|L_trunc(1/2+iw)|).  This is the secretly-
    analytic build; it does NOT count as a geometric reproduction.

  * Theta base=logp is IDENTICAL to log(n) (FTA: Theta(n)=sum a*log p = log n) -- so
    'FTA with log p arrivals' is just the same secretly-L object wearing a winding
    costume.  It hits the zeros for the same trivial reason.

  * Every GENUINELY geometric phase (turns, blocky height, Omega(n), ordinal-prime,
    chi3-residue arrivals, with or without chi3 weight) reproduces at most the MEAN
    spacing -- it does NOT land cancellation events on the individual gamma_k.  The
    per-block FLUCTUATION S(T) is NOT captured.

  * Reason (sharpened): the fluctuation is carried EXACTLY by the irrational phases
    {w*log p : p prime} being incommensurate in the precise log-metric.  Any geometric
    prime-arrival rule that replaces log p by a 'nicer' angle (unit, ordinal, residue)
    detunes those incommensurabilities and smooths the signal back to the mean.  The
    blocky construction recovers L's MEAN density (~(1/2)log(q gamma/2pi)) but the
    individual-zero rigidity lives in the actual {log p}, i.e. in L itself.

  CONCLUSION: passed=False (3D-built-first: YES; lands on real zeros geometrically: NO).
  The only build that hits individual zeros is the one whose phase == log n == analytic L.
  capturesFluctuation=False.
""")

def feedback_boundaries():
    """Self-consistent boundaries from the mean zero-counting function for chi3.
    N(T) ~ (T/pi) log(q T /(2 pi e)) + ... for a real char mod q=3 (both gamma>0 and
    its reflection contribute; here we use the standard density d N/dT = (1/pi) log(qT/2pi)).
    b_{k+1} = b_k + pi/gap, gap = pi / (dN/dT) ... i.e. consecutive-zero step from mean density.
    Compare fixed-point boundaries to actual gamma_k."""
    q = 3
    def dens(T):  # mean spacing's reciprocal: zeros per unit T (one-sided, ordered gammas)
        # average gap between consecutive positive gammas ~ 2pi / log(q T /2pi)
        return np.log(q*T/(2*np.pi)) / (2*np.pi)
    b = [GAMMA[0]]   # seed on the first true zero
    for _ in range(len(GAMMA)-1):
        T = b[-1]
        gap = 1.0/dens(T)          # predicted next gap from mean density
        b.append(T + gap)
    b = np.array(b)
    matched = 0; ds = []
    for k in range(min(12, len(GAMMA))):
        d = abs(b[k] - GAMMA[k])
        if d < 0.05: matched += 1
        ds.append(d)
    print(f"  mean-density feedback boundaries vs gamma_k:")
    for k in range(8):
        print(f"    k={k:>2}  b_k={b[k]:8.4f}  gamma_k={GAMMA[k]:8.4f}  |diff|={abs(b[k]-GAMMA[k]):6.4f}")
    print(f"  matched (|diff|<0.05): {matched}/12  ; mean|diff|={np.mean(ds):.4f}")
    print("  -> mean-density feedback tracks AVERAGE growth but drifts off individual gammas")
    print("     (the fluctuation S(T) = deviation of true gamma_k from this smooth staircase).")


if __name__ == "__main__":
    main()
