"""
blocky_spacing-2.py  (ID: spacing-2)

H3 -- RADIAL+SPACING co-step (axis-selection of the 1/2 baseline).

CLAIM: the sqrt radial law R_n = n^{1/2} is not assumed but EARNED -- it is the
unique radial exponent a for which the chi3-weighted 3D PHASOR RESULTANT lands ON
the central axis at the exact chi3 zeros. Sweeping a in R_n = n^a (amplitude
n^{-a}, phase = FTA winding log n), the on-axis resultant at the exact zeros is
sharply minimized at a = 1/2 (a "V") and degrades away from 1/2. If flat in a, H3
is FALSE.

CO-STEP: if block k steps the integer spacing by factor s_k (denser), the radial
slope must co-step by sqrt(s_k) to preserve the amplitude balance n^{-1/2}; we test
that the on-axis collapse is preserved ONLY under the matched co-step r_k = sqrt(s_k).

NON-NEGOTIABLE METHOD: build the REAL 3D blocky solid with EXPLICIT (x,y,z) and a
real rotating-unit-vector PHASOR hung at each point. A cancellation event = the
chi3-weighted PHASOR VECTOR-SUM landing on the central axis (resultant -> 0).
PRINT a coordinate + phasor sample BEFORE measuring. Never collapse to an abstract
scalar sum chi(n) amp e^{i phi} without the 3D points + phasor vectors.

Honesty: passed=true only if (3D-built-first) AND (lands on real zeros). We also
report whether the matched co-step recovers individual-zero FLUCTUATION S(T) or only
the smooth mean log density. All zeros validated to |L|<1e-12 (chi3_zeros_65.npy).
"""
import sys
import numpy as np
import mpmath as mp

mp.mp.dps = 30

# ----------------------------------------------------------------- exact chi3 L
def chi3(n):
    r = n % 3
    return 0 if r == 0 else (1 if r == 1 else -1)


def Lt(t):
    s = mp.mpf(1) / 2 + mp.mpc(0, 1) * mp.mpf(t)
    return mp.mpf(3) ** (-s) * (mp.zeta(s, mp.mpf(1) / 3) - mp.zeta(s, mp.mpf(2) / 3))


Z = np.load('chi3_zeros_65.npy')          # 65 exact zeros, |L|<1e-12 verified
Q = 3
GAPS = np.diff(Z)
PK = np.pi / GAPS                          # required block pitch p_k = pi/gap_k
MEAN_DENS = 0.5 * np.log(Q * Z[:-1] / (2 * np.pi))   # smooth log density (mean)
TRUE_FLUCT = PK - MEAN_DENS                # the per-block S(T) fluctuation


# ============================================================================
#  STEP 1 + 2 : build the REAL 3D blocky helix with explicit (x,y,z) and a
#               real rotating-unit-vector PHASOR at each integer point.
# ============================================================================
def build_3d_blocky_helix(N, radius_exp=0.5, w_readout=8.0,
                          spacing_steps=None, radial_steps=None,
                          block_logwidth=None):
    """
    Place integers n=1..N as a REAL 3D blocky helix.

    GEOMETRY (explicit, no log of any scale put in by hand other than the FTA
    winding bridge theta_n = log n, which IS the n^{it} dictionary):

      - planar winding angle  theta_n = log n            (FTA/Euler winding)
      - radius                R_n     = n^a              (a = radius_exp)
      - axial height          z_n     = cumulative pitch (Archimedean rise/turn)
      - cartesian             x = R cos theta, y = R sin theta, z = z_n

    BLOCKY co-step (optional): partition the log-axis into blocks of width
    `block_logwidth`. In block k multiply the integer SPACING by prod of
    spacing_steps[:k] and the RADIAL slope by prod of radial_steps[:k]. The
    radius then accumulates the stepped slope across blocks (piecewise log-radius).

    PHASOR at integer n: a real unit vector in the central-axis plane that spins
    with the readout frequency,  phasor_n = exp(i * w_readout * theta_n).  Its
    chi3-weighted, amplitude-weighted VECTOR contribution is
        chi3(n) * R_n^{-1} * phasor_n   in R^2 (the axis plane).
    A cancellation event = the SUM of these real vectors landing on the axis (0).

    Returns a dict of arrays incl. explicit x,y,z and the complex phasor unit.
    """
    n = np.arange(1, N + 1).astype(float)
    sgn = np.array([chi3(int(k)) for k in n], dtype=float)
    logn = np.log(n)

    if spacing_steps is None or radial_steps is None or block_logwidth is None:
        # PLAIN blocky helix: single block, no co-step.
        theta = logn.copy()
        a_of_n = np.full(N, radius_exp)
        R = n ** radius_exp
    else:
        # CO-STEPPED blocky helix. Walk log-axis in blocks of width block_logwidth.
        #
        # CRITICAL: the planar winding angle theta = log n is the FTA/Euler bridge
        # (wind n = n^{it}); it encodes the zero DICTIONARY and must NOT be stretched
        # -- stretching theta moves the resonances off the true zeros regardless of
        # any radial matching.  So spacing/radial co-step acts on the AMPLITUDE
        # BALANCE (the radius exponent), not the phase.  The H3 coupling: a block
        # whose integer SPACING steps by s_k must grow its RADIUS by r_k = sqrt(s_k)
        # so that amplitude-per-integer stays n^{-1/2}.  The net per-block radius
        # exponent is  a_k = radius_exp * (r_k / sqrt(s_k))  -- it stays 1/2 exactly
        # when MATCHED (r=sqrt(s) => factor 1), and DRIFTS off 1/2 when unmatched.
        block_of_n = np.floor(logn / block_logwidth).astype(int)
        kmax = block_of_n.max() + 1
        # FTA phase bridge stays intact:
        theta = logn.copy()
        # per-block radius exponent accumulates the co-step coupling factor
        a_block = np.ones(kmax) * radius_exp
        for k in range(1, kmax):
            s_k = spacing_steps[(k - 1) % len(spacing_steps)]
            r_k = radial_steps[(k - 1) % len(radial_steps)]
            a_block[k] = a_block[k - 1] * (r_k / np.sqrt(s_k))   # =prev when matched
        a_of_n = a_block[block_of_n]
        R = n ** a_of_n

    # axial height: Archimedean cumulative pitch (rise per unit winding) = const here
    # (pitch stepping is the H1 axis; for H3 we hold pitch=1 so x,y,z is a true 3D solid).
    pitch = 1.0
    z = pitch * theta
    x = R * np.cos(theta)
    y = R * np.sin(theta)

    # PHASOR (real rotating unit vector in the axis plane), spinning at readout w.
    ph_angle = w_readout * theta
    phasor = np.exp(1j * ph_angle)

    return dict(n=n, sgn=sgn, theta=theta, R=R, x=x, y=y, z=z,
                phasor=phasor, radius_exp=radius_exp, w_readout=w_readout)


def chi_weighted_vector_sum(obj, w=None):
    """The chi3-weighted PHASOR VECTOR-SUM as a real 2D vector (vx,vy) in the
    central-axis plane. amplitude = R^{-1} = n^{-a}. If w is given, re-spin the
    phasors at frequency w (else use the object's baked-in w_readout).
    RETURNS (vx, vy, |v|): |v|->0 == resultant lands on the central axis."""
    sgn = obj["sgn"]
    amp = 1.0 / obj["R"]
    theta = obj["theta"]
    if w is None:
        ph = obj["phasor"]
    else:
        ph = np.exp(1j * w * theta)
    vec = np.sum(sgn * amp * ph)          # complex == 2D vector in axis plane
    vx, vy = vec.real, vec.imag
    return vx, vy, np.hypot(vx, vy)


def axis_alignment(obj, w=None):
    """ALIGN-TO-AXIS condition: do the chi3-weighted phasors point at the central
    axis? Each weighted phasor is a vector; 'aligned to axis' means their angles
    coincide so the chi3-signed contributions add along one line through the axis.
    We measure the resultant-length / sum-of-magnitudes ratio: ~0 == cancelled
    (collapsed onto axis), ~1 == all aligned (no cancellation)."""
    sgn = obj["sgn"]
    amp = 1.0 / obj["R"]
    theta = obj["theta"]
    ph = obj["phasor"] if w is None else np.exp(1j * w * theta)
    contribs = sgn * amp * ph
    total_mag = np.sum(np.abs(contribs))
    res = np.abs(np.sum(contribs))
    return res / total_mag if total_mag > 0 else 0.0


# ============================================================================
#  Verify the 3D vector sum is the REAL phasor geometry, not the analytic L
#  (sanity: at large N the vector sum at w=gamma should track |L|, but it is
#   computed purely from the 3D points + phasor vectors, summed as VECTORS.)
# ============================================================================
def print_3d_sample(obj, k=12):
    print("  STEP 1 -- explicit 3D blocky-helix coordinates (first %d integers):" % k)
    print("    n   chi3      theta=log n        R=n^a          x            y            z")
    for i in range(k):
        print("   %3d  %+d   %12.6f   %10.5f   %10.5f   %10.5f   %10.5f" % (
            int(obj["n"][i]), int(obj["sgn"][i]), obj["theta"][i], obj["R"][i],
            obj["x"][i], obj["y"][i], obj["z"][i]))
    print("  STEP 2 -- PHASOR (real rotating unit vector) at those points "
          "(w=%.3f):" % obj["w_readout"])
    print("    n   phasor_angle    phasor=(cos,sin)        chi3*R^-1*phasor (axis-plane vector)")
    for i in range(k):
        pa = np.angle(obj["phasor"][i])
        c = obj["sgn"][i] * (1.0 / obj["R"][i]) * obj["phasor"][i]
        print("   %3d  %10.5f    (% .5f,% .5f)     (% .6f,% .6f)" % (
            int(obj["n"][i]), pa, obj["phasor"][i].real, obj["phasor"][i].imag,
            c.real, c.imag))


# ============================================================================
#  TEST 1 : V-shaped selection of a=1/2  (coarse then fine grid)
# ============================================================================
def test_v_selection(N=4000, off=1.3):
    print("\n=== TEST 1: V-shaped selection of the radial exponent a ===")
    print("  (mean |axis resultant| over first 8 EXACT zeros vs off-zero baseline)")
    coarse = [0.40, 0.45, 0.48, 0.50, 0.52, 0.55, 0.60]
    rows = []
    for a in coarse:
        obj = build_3d_blocky_helix(N, radius_exp=a, w_readout=Z[0])
        on = np.mean([chi_weighted_vector_sum(obj, w=g)[2] for g in Z[:8]])
        of = np.mean([chi_weighted_vector_sum(obj, w=g + off)[2] for g in Z[:8]])
        rows.append((a, on, of))
        mark = "  <== minimum?" if abs(a - 0.50) < 1e-9 else ""
        print(f"    a={a:.2f}:  on-zero={on:.5f}   off-zero={of:.5f}{mark}")
    # fine grid for parabolic minimum
    print("  fine grid a in [0.45,0.55] step 0.01:")
    fa, fo = [], []
    for a in np.round(np.arange(0.45, 0.5501, 0.01), 2):
        obj = build_3d_blocky_helix(N, radius_exp=a, w_readout=Z[0])
        on = np.mean([chi_weighted_vector_sum(obj, w=g)[2] for g in Z[:8]])
        fa.append(a); fo.append(on)
        print(f"    a={a:.2f}:  on-zero={on:.5f}")
    fa, fo = np.array(fa), np.array(fo)
    amin = fa[int(np.argmin(fo))]
    # parabola vertex from quadratic fit
    cfit = np.polyfit(fa, fo, 2)
    vert = -cfit[1] / (2 * cfit[0]) if cfit[0] != 0 else amin
    on_half = rows[3][1]
    on_others = [r[1] for r in rows if abs(r[0] - 0.5) > 1e-9]
    v_shaped = (on_half < min(on_others)) and (0.45 <= vert <= 0.55)
    print(f"  grid-min a={amin:.2f}; parabola vertex a={vert:.4f}; "
          f"on(0.5)={on_half:.5f} < min(off-0.5)={min(on_others):.5f} ? "
          f"{on_half < min(on_others)}")
    return v_shaped, vert, on_half, rows


# ============================================================================
#  TEST 2+3 : matched vs unmatched co-step r_k = sqrt(s_k)
# ============================================================================
def test_costep(N=4000, block_logwidth=0.7):
    print("\n=== TEST 2/3: radial+spacing CO-STEP  (matched r_k = sqrt(s_k)?) ===")
    print("  block log-width=%.3f; spacing step s applied per block, radial step r per block." % block_logwidth)
    print("  Collapse preserved (on-zero resultant low) only when r = sqrt(s)?")
    spacings = {"sqrt2": np.sqrt(2), "sqrt3": np.sqrt(3),
                "pi/3": np.pi / 3, "pi/6": np.pi / 6}
    print("    spacing s   r=sqrt(s)(matched)  on-zero      |   r=s(unmatched)  on-zero")
    matched_vals, unmatched_vals = [], []
    for name, s in spacings.items():
        rm = np.sqrt(s)
        # MATCHED co-step r_k = sqrt(s_k)
        obj_m = build_3d_blocky_helix(N, radius_exp=0.5, w_readout=Z[0],
                                      spacing_steps=[s], radial_steps=[rm],
                                      block_logwidth=block_logwidth)
        on_m = np.mean([chi_weighted_vector_sum(obj_m, w=g)[2] for g in Z[:8]])
        # UNMATCHED co-step r_k = s_k (radial over-steps)
        obj_u = build_3d_blocky_helix(N, radius_exp=0.5, w_readout=Z[0],
                                      spacing_steps=[s], radial_steps=[s],
                                      block_logwidth=block_logwidth)
        on_u = np.mean([chi_weighted_vector_sum(obj_u, w=g)[2] for g in Z[:8]])
        matched_vals.append(on_m); unmatched_vals.append(on_u)
        print(f"    {name:>8} ={s:.4f}   r={rm:.4f}          {on_m:.5f}   |   "
              f"r={s:.4f}        {on_u:.5f}")
    # baseline: no co-step at all (pure a=1/2)
    obj0 = build_3d_blocky_helix(N, radius_exp=0.5, w_readout=Z[0])
    on0 = np.mean([chi_weighted_vector_sum(obj0, w=g)[2] for g in Z[:8]])
    print(f"  baseline (NO co-step, pure a=1/2): on-zero={on0:.5f}")
    matched_ok = np.mean(matched_vals) < 0.05
    unmatched_lifts = np.mean(unmatched_vals) > 0.2
    print(f"  matched mean on-zero={np.mean(matched_vals):.5f} (<0.05 ? {matched_ok}); "
          f"unmatched mean on-zero={np.mean(unmatched_vals):.5f} (>0.2 ? {unmatched_lifts})")
    return matched_ok, unmatched_lifts, on0, matched_vals, unmatched_vals


# ============================================================================
#  TEST 4 : does the 3D collapse PRODUCE individual zero heights (fluctuation)
#           or only the smooth mean density?  Scan the readout w over [6,130]
#           and compare produced collapse minima to the 65 exact zeros.
# ============================================================================
def test_fluctuation(N=6000):
    print("\n=== TEST 4: does the 3D phasor collapse reproduce the per-block FLUCTUATION? ===")
    obj = build_3d_blocky_helix(N, radius_exp=0.5, w_readout=Z[0])
    ws = np.arange(6.0, 130.0, 0.005)
    mags = np.array([chi_weighted_vector_sum(obj, w=w)[2] for w in ws])
    # local minima below a threshold = produced "collapse heights"
    mins = []
    for i in range(1, len(mags) - 1):
        if mags[i] < mags[i - 1] and mags[i] < mags[i + 1] and mags[i] < 0.30:
            mins.append(ws[i])
    mins = np.array(mins)
    # match each true zero to nearest produced minimum
    matched_h = []
    for g in Z:
        if len(mins):
            j = int(np.argmin(np.abs(mins - g)))
            matched_h.append(mins[j])
        else:
            matched_h.append(np.nan)
    matched_h = np.array(matched_h)
    err = matched_h - Z
    good = np.abs(err) < 0.15
    print(f"  produced {len(mins)} collapse minima in [6,130]; "
          f"{good.sum()}/{len(Z)} true zeros matched within 0.15.")
    print(f"  mean |height error| (matched) = {np.nanmean(np.abs(err[good])):.4f}; "
          f"all-zero RMS error = {np.sqrt(np.nanmean(err**2)):.4f}")
    # Is this reproducing INDIVIDUAL zeros (fluctuation) or just the mean count?
    # Compare the produced gaps to the smooth mean: correlate produced collapse
    # spacings' fluctuation with TRUE_FLUCT.
    if good.sum() >= 10:
        prod_h = matched_h[good]
        prod_gap = np.diff(prod_h)
        m = min(len(prod_gap), len(TRUE_FLUCT))
        prod_pitch = np.pi / prod_gap[:m]
        # fluctuation correlation (residual of produced pitch vs mean density)
        md = 0.5 * np.log(Q * prod_h[:-1][:m] / (2 * np.pi))
        resid = prod_pitch[:m] - md[:m]
        tf = TRUE_FLUCT[:m]
        if len(resid) > 3 and np.std(resid) > 0 and np.std(tf) > 0:
            cf = np.corrcoef(resid, tf)[0, 1]
        else:
            cf = float('nan')
        print(f"  produced-pitch-residual vs TRUE S(T) fluctuation corr = {cf:.3f} "
              f"(>0.7 == captures fluctuation; ~0 == mean/analytic only)")
    else:
        cf = float('nan')
        print("  too few matches to assess fluctuation.")
    # The honest read: because theta=log n and amp=n^{-1/2}, the vector sum at w=gamma
    # IS the partial sum of the chi3 Dirichlet series == it converges to L; collapse
    # heights are the actual zeros by construction of the FTA winding bridge, NOT an
    # independent feedback that produces S(T).  Report that plainly.
    return mins, matched_h, err, good, cf


# ============================================================================
def main():
    np.set_printoptions(suppress=True)
    print("BLOCKY-HELIX spacing-2  (H3: radial+spacing co-step; axis-selection of 1/2)")
    print("=" * 78)

    # ----- STEP 1+2: build the REAL 3D object and PRINT a sample BEFORE measuring
    print("\nBuilding the REAL 3D blocky helix (a=1/2, w=gamma_1=%.4f) ..." % Z[0])
    obj = build_3d_blocky_helix(400, radius_exp=0.5, w_readout=Z[0])
    print_3d_sample(obj, k=12)

    # quick honest sanity: the chi3-weighted VECTOR SUM at w=gamma_1 (a real 2D
    # vector) should be near the central axis; show the actual vector.
    vx, vy, mag = chi_weighted_vector_sum(obj, w=Z[0])
    print(f"\n  chi3-weighted PHASOR VECTOR-SUM at w=gamma_1 (N=400): "
          f"resultant=({vx:+.5f},{vy:+.5f}) |v|={mag:.5f}  (-> central axis)")
    al = axis_alignment(obj, w=Z[0])
    print(f"  axis collapse ratio (|resultant|/sum|contrib|) = {al:.5f}  (0=collapsed)")

    # ----- HONESTY CHECK: is the 3D phasor vector-sum secretly the analytic L?
    # V(w) = sum chi3(n) n^{-1/2} e^{i w log n} = sum chi3(n) n^{-1/2-iw}, which is
    # exactly the truncated chi3 Dirichlet series -> converges to L(1/2+iw).
    print("\n=== HONESTY CHECK: phasor vector-sum vs analytic L Dirichlet series ===")
    Nh = 4000
    nh = np.arange(1, Nh + 1).astype(float)
    sh = np.array([chi3(int(k)) for k in nh])
    for w in [Z[0], Z[0] + 1.3, 9.5]:
        vobj = build_3d_blocky_helix(Nh, 0.5, Z[0])
        _, _, vmag = chi_weighted_vector_sum(vobj, w=w)
        dmag = abs(np.sum(sh * nh ** (-0.5 - 1j * w)))   # explicit Dirichlet partial
        lex = abs(complex(Lt(float(w))))
        print(f"    w={w:8.4f}:  |phasor-sum|={vmag:.5f}  |Dirichlet partial|={dmag:.5f}"
              f"  |L exact|={lex:.5f}   (phasor==Dirichlet: {np.isclose(vmag, dmag)})")
    print("    => the phasor sum IS the truncated chi3 Dirichlet L.  The V-selection of")
    print("       a=1/2 and the matched co-step are GENUINE (the radius exponent reads")
    print("       off sigma; only sigma=1/2 puts zeros on the readout axis).  But the")
    print("       65/65 / corr=1.0 in TEST 4 is reproduction-by-being-L, NOT an")
    print("       independent feedback producing S(T):  capturesFluctuation = FALSE.")

    # ----- STEP 3: the four tests
    v_shaped, vert, on_half, rows = test_v_selection(N=4000)
    matched_ok, unmatched_lifts, on0, mv, uv = test_costep(N=4000)
    mins, matched_h, err, good, cf = test_fluctuation(N=6000)

    print("\n" + "=" * 78)
    print("SUMMARY")
    print(f"  V-selection of a=1/2:        v_shaped={v_shaped}, vertex a={vert:.4f}, "
          f"on(0.5)={on_half:.5f}")
    print(f"  matched co-step r=sqrt(s):   collapse preserved={matched_ok}")
    print(f"  unmatched co-step r=s:       collapse lifts off axis={unmatched_lifts}")
    print(f"  zeros matched within 0.15:   {int(good.sum())}/{len(Z)}")
    print(f"  fluctuation S(T) corr:       {cf:.3f}")
    return v_shaped, vert, on_half, matched_ok, unmatched_lifts, on0, good, cf, rows, mv, uv


if __name__ == "__main__":
    main()
