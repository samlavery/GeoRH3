"""
blocky_core.py -- shared machinery for the BLOCKY-HELIX experiments.

Provides:
  - exact chi3 = real char mod 3 L-function and its zeros (mpmath, |L|<1e-12 verified),
  - the REAL 3D blocky-helix builder: explicit (x,y,z) coords + a PHASOR (unit vector)
    at every integer point, with PER-BLOCK stepped pitch / radial / spacing laws,
  - the phasor VECTOR-SUM collapse measurement (resultant -> central axis at a zero),
  - the ALIGN-TO-AXIS measurement (do all phasors point at the central axis?).

The blocks are delimited by candidate "zero heights"; within a block geometry is
constant, at each boundary pitch/radius/spacing STEP. This is the literal blocky helix.
"""
import numpy as np
import mpmath as mp

mp.mp.dps = 30


# ---------------------------------------------------------------- L(chi3, s)
def chi3(n):
    r = n % 3
    return 0 if r == 0 else (1 if r == 1 else -1)


def Lchi3(s):
    s = mp.mpc(s)
    return mp.mpf(3) ** (-s) * (mp.zeta(s, mp.mpf(1) / 3) - mp.zeta(s, mp.mpf(2) / 3))


def Lt(t):
    """L on the critical line as a function of the (real) height t, returned complex."""
    return Lchi3(mp.mpf(1) / 2 + mp.mpc(0, 1) * mp.mpf(t))


def find_zeros(n_zeros=65, t_hi=120.0, coarse=0.02):
    """Scan |L(1/2+it)| minima, refine with secant findroot on the real height t.
    Verifies |L| < 1e-12 at each accepted zero."""
    ts = np.arange(0.6, t_hi, coarse)
    mag = np.array([float(abs(Lt(float(t)))) for t in ts])
    cand = []
    for i in range(1, len(mag) - 1):
        if mag[i] < mag[i - 1] and mag[i] < mag[i + 1] and mag[i] < 0.6:
            cand.append(ts[i])
    zeros = []
    for t0 in cand:
        try:
            # 1-D real root of the modulus-squared via secant on Re/Im simultaneously:
            # use findroot on g(t)=Lt(t) treating t real by feeding mp.mpf each step.
            r = mp.findroot(lambda t: Lt(mp.re(t)), mp.mpf(t0))
            t = float(mp.re(r))
            if abs(float(abs(Lt(t)))) < 1e-12 and t > 0.5:
                if all(abs(t - z) > 1e-4 for z in zeros):
                    zeros.append(t)
        except Exception:
            pass
        if len(zeros) >= n_zeros:
            break
    return np.array(sorted(zeros))


# ---------------------------------------------------------- the BLOCKY 3D object
def build_blocky_helix(N, block_bounds, pitch_law, radial_law, spacing_law,
                       phasor_law):
    """
    Build the REAL 3D blocky helix with explicit coordinates and a phasor per point.

    N            : number of integer points to place (n = 1..N).
    block_bounds : array of arc-length (cumulative-spacing) boundaries delimiting blocks;
                   block index of integer n = how many boundaries it has passed.
    pitch_law    : k -> axial rise per unit winding angle in block k (z' = pitch_k).
    radial_law   : k -> radial growth coefficient in block k (dR/dtheta = radial_k).
    spacing_law  : k -> arc spacing between consecutive integers in block k.
    phasor_law   : (n, theta, k) -> phase angle of the unit phasor at integer n.

    Returns dict with arrays: n, block, theta, R, x, y, z, phasor (complex unit),
    plus the cumulative arc-length s of each integer.
    """
    n = np.arange(1, N + 1)
    # --- 1. lay integers on the unwound LINE with per-block stepped spacing ---
    # determine block of each integer by walking arc length and comparing to bounds.
    s = np.zeros(N)
    blk = np.zeros(N, dtype=int)
    acc = 0.0
    bidx = 0
    for i in range(N):
        # block index = number of bounds strictly below current arc length
        while bidx < len(block_bounds) and acc >= block_bounds[bidx]:
            bidx += 1
        blk[i] = bidx
        step = spacing_law(bidx)
        acc += step
        s[i] = acc
    # --- 2. integrate winding angle theta and radius R block-by-block ---
    # within a block, dR/dtheta = radial_k constant, and arc length ds = sqrt(R'^2 + R^2) dtheta
    # for an Archimedean-type spiral R = R0 + a*(theta-theta0).  We instead use the simpler,
    # explicit construction: the winding angle advances proportionally to arc length divided by
    # the *local* radius (so each loop of circumference ~2 pi R consumes ~2 pi R of arc), and R
    # grows linearly in theta with slope radial_k.  Solve incrementally.
    theta = np.zeros(N)
    R = np.zeros(N)
    z = np.zeros(N)
    th = 0.0
    r = radial_law(0) * 1.0 + 1.0   # seed radius (avoid 0)
    zc = 0.0
    prev_s = 0.0
    for i in range(N):
        k = blk[i]
        ds = s[i] - prev_s
        prev_s = s[i]
        a = radial_law(k)            # dR/dtheta slope this block
        p = pitch_law(k)             # dz/dtheta this block
        # advance angle so that arc consumed ~ ds along spiral of current radius r:
        # ds ~ sqrt(r^2 + a^2) * dtheta  =>  dtheta = ds / sqrt(r^2 + a^2)
        dth = ds / np.sqrt(r * r + a * a)
        th += dth
        r += a * dth
        zc += p * dth
        theta[i] = th
        R[i] = r
        z[i] = zc
    x = R * np.cos(theta)
    y = R * np.sin(theta)
    # --- 3. attach phasors (unit complex = 2D rotating vector in the plane) ---
    ph = np.array([phasor_law(n[i], theta[i], blk[i]) for i in range(N)])
    phasor = np.exp(1j * ph)
    return dict(n=n, block=blk, theta=theta, R=R, x=x, y=y, z=z,
                phasor=phasor, s=s)


def chi_weighted_resultant(obj, upto=None):
    """The chi3-weighted PHASOR VECTOR-SUM. Collapse to the central axis == |resultant|->0.
    Amplitude defaults to 1/sqrt(n) (the n^{-1/2} of the critical line) times 1/R weighting
    is NOT applied here -- pure phasor sum with chi3 sign and n^{-1/2}."""
    if upto is None:
        upto = len(obj["n"])
    n = obj["n"][:upto]
    sgn = np.array([chi3(int(k)) for k in n], dtype=float)
    amp = n.astype(float) ** -0.5
    res = np.sum(sgn * amp * obj["phasor"][:upto])
    return res


def axis_alignment(obj, upto=None):
    """ALIGN-TO-AXIS test: at a collapse, do the phasors point AT the central axis?
    The radial direction at point i is (cos theta_i, sin theta_i). The phasor is a unit
    vector with angle ph_i. 'Pointing at the axis' = phasor antiparallel to radial outward,
    i.e. ph_i ~ theta_i + pi. Return mean alignment <cos(ph - (theta+pi))> (1 = all inward)."""
    if upto is None:
        upto = len(obj["n"])
    th = obj["theta"][:upto]
    ph = np.angle(obj["phasor"][:upto])
    return np.mean(np.cos(ph - (th + np.pi)))


if __name__ == "__main__":
    Z = find_zeros(12, t_hi=30.0)
    print("first chi3 zeros (|L|<1e-12 verified):")
    for t in Z:
        print(f"   {t:.10f}   |L|={float(abs(Lt(t))):.2e}")
