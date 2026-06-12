"""
radial_step_blocky.py

RADIAL-STEP BLOCKY HELIX -- build the REAL 3D solid FIRST, with explicit (x,y,z)
coordinates and a real rotating PHASOR (unit vector) hung at every point.  Then
measure the chi3-weighted phasor VECTOR-SUM collapse against the exact mpmath
zeros of L(chi3).

THE OBJECT
----------
A 3D helix split into BLOCKS, one block per zero gamma_k.  Inside block k the
geometry is CONSTANT; at each block boundary the parameters STEP:
  - pitch p_k        : axial rise per turn (z grows by p_k * (turn fraction))
  - radial law r_k   : the radius / amplitude jumps each block (this file's focus)
  - spacing dphi_k   : angular spacing between consecutive integers in the block

Each integer n in block k is a POINT placed at:
    phi_n = (running azimuth, advanced by dphi_k per integer)
    R_n   = radial law r_k(local index)         <-- the RADIAL STEP we sweep
    z_n   = running height, rising by pitch p_k

At each point we hang a PHASOR: a real unit vector  u_n = (cos a_n, sin a_n)
whose angle a_n = w * phi_n  (w is the probe frequency; the winding angle is the
phase, log-free -- this is the FTA winding, NOT log n).  The chi3 weight
chi3(n) in {+1,-1,0} flips / kills the phasor.  A CANCELLATION EVENT is the
weighted phasor RESULTANT  V(w) = sum_n chi3(n) * amp_n * u_n  collapsing to ~0
(the vector lands on the central axis).  We ALSO test ALIGN-TO-AXIS: at a true
zero do the live phasors point coherently (resultant small *because* they cancel
in direction, measured by the ratio |resultant| / sum|amp|).

We never collapse to an abstract scalar sum chi(n) amp e^{i phi} without first
materializing the 3D points + phasor vectors; the resultant is the literal 2D
vector sum of the hung unit vectors (axis = z), so the "lands on the axis"
picture is the actual computation.

We sweep the RADIAL STEP law and the pitch/spacing constants, including the
specific constants pi/6, pi/3, pi/2, pi, log2, log3, sqrt2, sqrt3, e, e^{c k}.
"""
import numpy as np
import mpmath as mp

mp.mp.dps = 30

# ----------------------------------------------------------------------------
# Exact chi3 zeros (verified to |L|<1e-12 above; loaded from the record file).
# ----------------------------------------------------------------------------
def chi3(n):
    r = n % 3
    return 1.0 if r == 1 else (-1.0 if r == 2 else 0.0)

def L_chi3(s):
    s = mp.mpf(s) if not isinstance(s, mp.mpc) else s
    return mp.power(3, -s) * (mp.zeta(s, mp.mpf(1)/3) - mp.zeta(s, mp.mpf(2)/3))

def load_zeros(path="lchi3_zeros_1000.txt", k=20):
    g = []
    with open(path) as f:
        for ln in f:
            ln = ln.strip()
            if ln and not ln.startswith("#"):
                g.append(float(ln.split()[1]))
    return np.array(sorted(g))[:k]

GAMMA = load_zeros(k=20)

# ----------------------------------------------------------------------------
# THE BUILD: explicit 3D blocky helix with phasors.
#
# block_bounds : the integer index n at which block k ends (boundary = a zero).
#   We tie block k to gamma_k; the number of integers in block k is chosen by a
#   spacing rule.  Within block k: constant pitch p_k, spacing dphi_k, radial r_k.
# ----------------------------------------------------------------------------
def build_blocky_helix(Nint, radial_law, pitch_law, spacing_law,
                       block_sizes):
    """Return arrays x,y,z,phi,R,amp,sign for integers 1..Nint placed on the
    blocky helix, plus the phasor angle base = phi (winding).  Each block uses
    constant geometry; parameters step at boundaries.

    radial_law(k, j, R_prev) -> radius for the j-th integer (0-based) of block k,
        given the running radius at block start R_prev.
    pitch_law(k)   -> axial rise per turn in block k.
    spacing_law(k) -> angular spacing dphi between integers in block k.
    block_sizes    -> list of ints, how many integers in each block.
    """
    x = np.zeros(Nint); y = np.zeros(Nint); z = np.zeros(Nint)
    phi = np.zeros(Nint); R = np.zeros(Nint); amp = np.zeros(Nint)
    sign = np.zeros(Nint)
    running_phi = 0.0
    running_z = 0.0
    R_block_start = 1.0
    n = 0
    k = 0
    for bs in block_sizes:
        dphi = spacing_law(k)
        pitch = pitch_law(k)
        for j in range(bs):
            if n >= Nint:
                break
            running_phi += dphi
            Rn = radial_law(k, j, R_block_start)
            # height rises with pitch: pitch = axial rise per *turn* (2pi of phi)
            running_z += pitch * (dphi / (2*np.pi))
            phi[n] = running_phi
            R[n] = Rn
            z[n] = running_z
            x[n] = Rn * np.cos(running_phi)
            y[n] = Rn * np.sin(running_phi)
            amp[n] = 1.0 / Rn           # amplitude = 1/radius (cone collapse weight)
            sign[n] = chi3(n + 1)        # integer is n+1 (1-indexed)
            n += 1
        # next block starts where this one ended radially
        R_block_start = R[n-1] if n > 0 else R_block_start
        k += 1
        if n >= Nint:
            break
    return x[:n], y[:n], z[:n], phi[:n], R[:n], amp[:n], sign[:n]


def phasor_resultant(phi, amp, sign, w):
    """The REAL phasor vector sum: hang unit vector u_n=(cos w phi, sin w phi)
    at each point, weight by chi3(n)*amp_n, sum the VECTORS.  Returns the 2D
    resultant (Vx,Vy) and its magnitude, plus the coherence ratio
    |V| / sum|chi*amp| (0 = perfect cancellation / on-axis, 1 = fully aligned)."""
    a = w * phi
    Vx = np.sum(sign * amp * np.cos(a))
    Vy = np.sum(sign * amp * np.sin(a))
    mag = np.hypot(Vx, Vy)
    denom = np.sum(np.abs(sign) * amp)
    ratio = mag / denom if denom > 0 else 0.0
    return Vx, Vy, mag, ratio


def control_L(w, Nint):
    """The analytic L control: sum chi3(n) n^{-1/2} e^{-i w log n}, truncated."""
    n = np.arange(1, Nint + 1)
    s = np.array([chi3(k) for k in n])
    return abs(np.sum(s * n**-0.5 * np.exp(-1j * w * np.log(n))))


if __name__ == "__main__":
    np.set_printoptions(suppress=True)
    print("=" * 78)
    print("RADIAL-STEP BLOCKY HELIX -- the real 3D object with phasors")
    print("=" * 78)
    print(f"Exact chi3 zeros (gamma_k): {GAMMA[:8]}")
    print()

    # ----- a first concrete instance: radius jumps by sqrt of cumulative count,
    #       pitch = pi/gap_k (the LOG-mean density), spacing = pi/3 -----------
    Nint = 4000
    # block sizes: tie boundary k to gamma_k via the unfolded count.  Use the
    # naive "one block per zero" with sizes growing like the local density.
    nblocks = 18
    # spacing fixed pi/3; choose block sizes so cumulative integers ~ proportional
    # to gamma (density grows like log gamma).  Simple: equal blocks first.
    block_sizes = [Nint // nblocks] * nblocks

    def radial_sqrt_cumulative(k, j, R0):
        # radius = sqrt(global index): the area-law cone (R ~ sqrt n)
        return None  # placeholder; replaced below by direct global build

    # Direct global build is clearer for the sqrt(n) area law:
    n = np.arange(1, Nint + 1)
    phi = np.cumsum(np.full(Nint, np.pi/3))
    R = np.sqrt(n.astype(float))
    z = np.cumsum(np.full(Nint, (np.pi/3)/(2*np.pi)))  # constant pitch pi placeholder
    amp = 1.0 / R
    sign = np.array([chi3(k) for k in n])
    x = R * np.cos(phi); y = R * np.sin(phi)

    print("--- SAMPLE OF THE BUILT 3D SOLID (smooth baseline, R=sqrt n, dphi=pi/3) ---")
    print(f"{'n':>5} {'phi':>9} {'R':>8} {'z':>8}   (x, y, z)        phasor@w=1")
    for nn in [1, 2, 3, 5, 10, 100, 1000, 4000]:
        i = nn - 1
        a = 1.0 * phi[i]
        print(f"{nn:5d} {phi[i]:9.3f} {R[i]:8.3f} {z[i]:8.3f}  "
              f"({x[i]:8.2f},{y[i]:8.2f},{z[i]:7.2f})  "
              f"u=({np.cos(a):+.3f},{np.sin(a):+.3f}) chi={int(sign[i]):+d}")
    print()
    print("--- phasor resultant of THIS smooth helix at the chi3 zeros ---")
    print(f"{'gamma':>9} {'|resultant|':>12} {'coherence':>10} {'|L control|':>12}")
    for g in GAMMA[:8]:
        Vx, Vy, mag, ratio = phasor_resultant(phi, amp, sign, g)
        print(f"{g:9.3f} {mag:12.5f} {ratio:10.5f} {control_L(g, Nint):12.5f}")
    print("(smooth dphi=pi/3 winds at a fixed rate -> resonates at ONE w, not at the zeros)")
