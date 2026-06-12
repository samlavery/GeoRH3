"""
blocky_helix_build.py
=====================
BUILD THE REAL 3D BLOCKY HELIX FIRST, WITH PHASORS, then measure.

The object: a 3D helix split into BLOCKS, one block per harmonic/zero of L(chi3).
Within a block the geometry is CONSTANT; at each block boundary (= each zero) the
parameters STEP: pitch p (axial rise per turn), radial growth R (amplitude law),
and integer spacing ds each change.

At every integer-point along the wound curve we hang a PHASOR: a real rotating unit
vector. A "cancellation event" is the chi3-weighted PHASOR VECTOR-SUM collapsing onto
the central axis (resultant -> 0). We compare the heights where the resultant collapses
to the EXACT mpmath chi3 zeros.

We NEVER skip the 3D points: amplitudes/phases come from explicit (x,y,z) + a unit
phasor vector at each point. The chi(n)-weighted resultant is a genuine 3D vector sum.
"""
import numpy as np
import mpmath as mp

mp.mp.dps = 30
Q = 3

# ----------------------------------------------------------------------------
# EXACT zeros of L(chi3) (ground truth), loaded from the verified file.
# ----------------------------------------------------------------------------
def L_mp(s):
    return mp.power(3, -s) * (mp.zeta(s, mp.mpf(1)/3) - mp.zeta(s, mp.mpf(2)/3))

def compute_exact_zeros(N=65, cache="chi3_zeros_exact.txt"):
    """Compute first N consecutive zeros to |L|<1e-12; cache to file."""
    import os
    cached = []
    if os.path.exists(cache):
        with open(cache) as f:
            for ln in f:
                ln = ln.strip()
                if ln and not ln.startswith("#"):
                    cached.append(float(ln.split()[0]))
    if len(cached) >= N:
        return np.array(sorted(cached))[:N]
    # scan |L(1/2+it)| for minima, refine with findroot
    f = lambda t: L_mp(mp.mpf(1)/2 + 1j*t)
    ts = np.arange(0.6, 0.6 + 6.0*N, 0.04)   # generous upper range
    mag = np.array([float(abs(f(mp.mpf(str(t))))) for t in ts])
    zs = []
    for i in range(1, len(ts)-1):
        if mag[i] < mag[i-1] and mag[i] < mag[i+1] and mag[i] < 0.5:
            try:
                r = mp.findroot(f, mp.mpc(ts[i], 0))
                tm = mp.re(r)
                if abs(float(mp.im(r))) < 1e-8 and abs(complex(f(tm))) < 1e-11 \
                        and float(tm) > 0.5 and all(abs(float(tm)-z) > 1e-4 for z in zs):
                    zs.append(float(tm))
            except Exception:
                pass
            if len(zs) >= N:
                break
    zs = sorted(zs)[:N]
    with open(cache, "w") as fp:
        fp.write("# chi3 zeros, gamma_n; |L(1/2+i gamma)|<1e-11\n")
        for z in zs:
            fp.write(f"{z:.18f}\n")
    return np.array(zs)

GAMMA = compute_exact_zeros(65)
print("="*78)
print("EXACT chi3 zeros (ground truth), first 12:")
print("  " + "  ".join(f"{g:.4f}" for g in GAMMA[:12]))
print(f"  total loaded: {len(GAMMA)}")
print("="*78)

# chi3 sign: chi(n)=+1 if n=1 mod 3, -1 if n=2 mod 3, 0 if n=0 mod 3
def chi3(n):
    r = n % 3
    return 1.0 if r == 1 else (-1.0 if r == 2 else 0.0)

# ----------------------------------------------------------------------------
# THE 3D BLOCKY HELIX BUILDER.
#
# We place "integers" (the arithmetic carriers) as points along a wound 3D curve.
# The curve is piecewise: block k covers a contiguous run of integers. Inside block k
# the three step-parameters are constant:
#     ds_k   : arc spacing between consecutive integers (INTEGER SPACING step)
#     p_k    : axial rise per radian = pitch / (2 pi)   (PITCH step)
#     rho_k  : radial growth rule (RADIAL/amplitude step) -> radius R as fn of arc s
# At each block boundary the parameters jump by the chosen step law.
#
# Construction (cone/spiral): integers sit at arc-length s_n = sum of ds over points.
# theta advances so arc length matches; radius R(s) given by radial law; z = p * theta.
# x = R cos theta, y = R sin theta, z = (axial). A phasor unit vector is attached at
# each point with phase = the WINDING ANGLE theta_n (this is the geometry's own phase,
# NOT an imposed log n).
# ----------------------------------------------------------------------------

def build_blocky_helix(block_pitches, ints_per_block=None, ds_law="const", ds0=None,
                       radial_law="archimedean", radial_c=1.0, N_int=None):
    """
    Build explicit (x,y,z) coords + phasor angle for integers along a blocky helix.

    block_pitches : array of pitch-per-radian values p_k for each block k.
                    The winding angle accrues; block k ends after a fixed angular
                    extent OR after ints_per_block[k] integers.
    Returns dict with arrays: n, theta, R, x, y, z, phasor_angle, block_id.
    """
    if ints_per_block is None:
        ints_per_block = [50]*len(block_pitches)
    n_list, theta_list, R_list, z_list, blk_list = [], [], [], [], []
    theta = 0.0
    z = 0.0
    s = 0.0  # cumulative arc length
    n = 0
    for k, p_k in enumerate(block_pitches):
        cnt = ints_per_block[k]
        # spacing law for this block
        if ds_law == "const":
            ds_k = ds0 if ds0 is not None else (np.pi/3)
        elif ds_law == "shrink":
            ds_k = (ds0 if ds0 else np.pi/3) / (1 + 0.0*k)
        else:
            ds_k = np.pi/3
        for _ in range(cnt):
            n += 1
            s += ds_k
            # radial law: R as function of arc length / index
            if radial_law == "archimedean":
                R = radial_c * np.sqrt(max(n, 1))     # sqrt(n): planar packing baseline
            elif radial_law == "linear":
                R = radial_c * theta + 1e-6
            elif radial_law == "log":
                R = radial_c * np.log(max(n, 2))
            else:
                R = radial_c * np.sqrt(max(n, 1))
            # advance winding angle by arc/radius (so arc length ~ R*dtheta)
            dtheta = ds_k / max(R, 1e-6)
            theta += dtheta
            z += p_k * dtheta
            n_list.append(n); theta_list.append(theta); R_list.append(R)
            z_list.append(z); blk_list.append(k)
            if N_int is not None and n >= N_int:
                break
        if N_int is not None and n >= N_int:
            break
    n_arr = np.array(n_list)
    theta_arr = np.array(theta_list)
    R_arr = np.array(R_list)
    z_arr = np.array(z_list)
    x_arr = R_arr * np.cos(theta_arr)
    y_arr = R_arr * np.sin(theta_arr)
    return dict(n=n_arr, theta=theta_arr, R=R_arr, x=x_arr, y=y_arr, z=z_arr,
                phasor_angle=theta_arr.copy(), block=np.array(blk_list))


# ----------------------------------------------------------------------------
# PHASOR VECTOR-SUM (the real cancellation test, NOT an abstract scalar).
# At winding "test frequency" w, each integer point carries a phasor unit vector
# rotated by w * (its winding-coordinate). Weight by chi3(n) and amplitude 1/R.
# Resultant = sum of the 2D phasor vectors. Collapse = |resultant| -> 0.
# We return BOTH the vector resultant and its magnitude.
# ----------------------------------------------------------------------------

def phasor_resultant(geo, w, use_phase="theta"):
    """Return (vx, vy, magnitude) of the chi3-weighted phasor vector-sum at freq w."""
    n = geo["n"]
    sign = np.array([chi3(int(nn)) for nn in n])
    amp = 1.0 / np.maximum(geo["R"], 1e-9)
    if use_phase == "theta":
        phase = w * geo["phasor_angle"]
    elif use_phase == "z":
        phase = w * geo["z"]
    else:
        phase = w * geo["phasor_angle"]
    vx = np.sum(sign * amp * np.cos(phase))
    vy = np.sum(sign * amp * np.sin(phase))
    return vx, vy, np.hypot(vx, vy)


# ----------------------------------------------------------------------------
# THE ANALYTIC CONTROL: the actual L(chi3) phasor sum with phase = -t log n,
# amplitude n^{-1/2}. This DOES collapse at the true zeros (it IS the truncated L).
# We keep it ONLY as a baseline to confirm our pipeline detects collapses.
# ----------------------------------------------------------------------------

def analytic_L_resultant(t, N=4000):
    nn = np.arange(1, N+1)
    sign = np.array([chi3(int(k)) for k in nn])
    amp = nn**-0.5
    phase = -t * np.log(nn)
    vx = np.sum(sign*amp*np.cos(phase)); vy = np.sum(sign*amp*np.sin(phase))
    return vx, vy, np.hypot(vx, vy)


if __name__ == "__main__":
    # ---- BUILD a concrete blocky helix and PRINT a real sample of (x,y,z) ----
    NB = 65
    # smooth log-mean pitch per block: p_k = pi / gap_k, gap_k ~ 2pi/log(q gamma/2pi)
    # use the EXACT zeros to set block boundaries in "winding height" but pitches from log law
    pitches = [0.5*np.log(Q*GAMMA[k]/(2*np.pi)) for k in range(NB)]
    geo = build_blocky_helix(pitches, ints_per_block=[60]*NB,
                             ds_law="const", ds0=np.pi/3,
                             radial_law="archimedean", radial_c=1.0,
                             N_int=3000)
    print("\n=== THE BUILT 3D BLOCKY HELIX (real coordinates) ===")
    print(f"{'n':>5} {'block':>5} {'theta':>9} {'R':>8} {'x':>9} {'y':>9} {'z':>9}  {'phasor_ang':>10}")
    for i in [0, 1, 2, 4, 9, 59, 60, 119, 600, 1500, 2999]:
        if i < len(geo["n"]):
            print(f"{geo['n'][i]:5d} {geo['block'][i]:5d} {geo['theta'][i]:9.3f} "
                  f"{geo['R'][i]:8.3f} {geo['x'][i]:9.3f} {geo['y'][i]:9.3f} "
                  f"{geo['z'][i]:9.3f}  {geo['phasor_angle'][i]:10.3f}")

    # ---- CONFIRM the pipeline: analytic L collapses at exact zeros ----
    print("\n=== PIPELINE CHECK: analytic-L phasor resultant at exact zeros (control) ===")
    print(f"  {'gamma':>9} {'|resultant L|':>14}  (should be small at a zero)")
    for g in GAMMA[:6]:
        _, _, m = analytic_L_resultant(g, N=6000)
        print(f"  {g:9.4f} {m:14.5f}")
    # off-zero control
    for t in [9.5, 13.0, 17.0]:
        _, _, m = analytic_L_resultant(t, N=6000)
        print(f"  {t:9.4f} {m:14.5f}   (off-zero, should be larger)")

    # ---- THE GEOMETRY'S OWN phasor collapse: does theta(n)-winding cancel chi3? ----
    print("\n=== GEOMETRY'S OWN PHASOR COLLAPSE (winding=theta, NO imposed log) ===")
    print(f"  {'gamma':>9} {'|geo resultant|':>16}")
    for g in GAMMA[:6]:
        vx, vy, m = phasor_resultant(geo, g, use_phase="theta")
        print(f"  {g:9.4f} {m:16.5f}")
    print("  (if these do NOT dip at the zeros, theta-winding != log n; expected per prior work)")
