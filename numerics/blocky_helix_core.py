"""
blocky_helix_core.py -- THE REAL 3D BLOCKY HELIX OBJECT with PHASORS.

Per the HARD RULE: build the actual 3D solid with explicit (x,y,z), hang a real
rotating unit PHASOR at each point, and detect a cancellation as the chi3-weighted
PHASOR VECTOR-SUM collapsing onto the central axis (resultant -> 0). No abstract
scalar Sum chi(n) amp e^{i phi} shortcut.

Geometry (BLOCKY / stepped):
  - The line of integers n=1,2,3,... is wound onto a vertical axis (z = height).
  - It is split into BLOCKS, one block per zero/harmonic. Within block k the geometry
    is CONSTANT; at each block boundary the params STEP: pitch p_k (axial rise per turn),
    radial law R_k, integer spacing ds_k.
  - integer n sits at cumulative WINDING ANGLE phi(n) = sum of per-integer angular steps
    (angular step in block k = ds_k converted to radians via the block's circumference),
    HEIGHT z(n) from pitch, RADIUS R(n) from the radial law.
  - PHASOR at integer n: a real unit vector u(n) = (cos psi(n), sin psi(n)) in the plane
    transverse to the axis, where psi(n) is the phasor's winding phase. chi3(n) weights it.

Cancellation test at frequency/height proxy w:
  resultant(w) = sum_n chi3(n) * amp(n) * phasor(n; w)    [a 2D VECTOR]
  |resultant| -> 0  <=>  phasors vector-cancel  <=>  candidate zero.
"""
import numpy as np

# ---- chi3 (real char mod 3): chi(n)=+1 if n%3==1, -1 if n%3==2, 0 if n%3==0 ----
def chi3(n):
    n = np.asarray(n)
    return np.where(n % 3 == 1, 1.0, np.where(n % 3 == 2, -1.0, 0.0))

class BlockyHelix:
    """
    A piecewise (blocky) helix. Blocks are indexed k=0,1,2,...; block k occupies a
    contiguous run of integers. Within block k:
        pitch[k]   : axial rise per full turn (controls z)
        radius_fn  : R as a function of (n, k, block-local data)
        dspacing[k]: arc spacing between consecutive integers in block k
    Boundaries between blocks are where the geometry STEPS.

    We allow the *number of integers per block* to be set externally (e.g. by a
    feedback/fixed-point rule) or by a fixed count. Default: 'integers per block'
    chosen so each block subtends a target angular span (one half-wave: pi).
    """
    def __init__(self, n_max=20000):
        self.n_max = n_max
        self.n = np.arange(1, n_max + 1)

    def build(self, pitch_law, radius_law, spacing_law, phasor_law, block_assign):
        """
        pitch_law(k, gamma_k) -> pitch for block k
        radius_law(n, k) -> radius at integer n in block k
        spacing_law(k, gamma_k) -> arc spacing in block k
        phasor_law(n, w) -> phasor phase psi at integer n given winding freq w
        block_assign -> array (len n_max) giving block index k for each integer n.
        Returns dict of explicit coordinates.
        """
        n = self.n
        kk = block_assign  # block index per integer
        # arc spacing per integer (from its block)
        # we precompute per-block scalars then broadcast
        uniqk = np.unique(kk)
        ds = np.empty_like(n, dtype=float)
        pit = np.empty_like(n, dtype=float)
        for k in uniqk:
            m = kk == k
            ds[m] = spacing_law(k)
            pit[m] = pitch_law(k)
        R = radius_law(n, kk)
        # cumulative arc length s(n)
        s = np.cumsum(ds)
        # winding angle: arc / radius (angle subtended). Use local radius.
        # dphi = ds / R  (radians)
        dphi = ds / np.maximum(R, 1e-9)
        phi = np.cumsum(dphi)
        # height: pitch is rise per turn (2pi rad); dz = pitch * dphi/(2pi)
        dz = pit * dphi / (2 * np.pi)
        z = np.cumsum(dz)
        x = R * np.cos(phi)
        y = R * np.sin(phi)
        return dict(n=n, k=kk, R=R, phi=phi, z=z, x=x, y=y, s=s, ds=ds, pitch=pit)

# ---- PHASOR vector-sum collapse (the REAL test, 2D vectors not scalar) ----
def phasor_resultant(coords, w, phase_field):
    """
    Hang a phasor at each integer: unit vector at angle psi(n) = w * phase_field(n).
    chi3-weight and amplitude-weight, then VECTOR SUM -> resultant in the plane.
    Returns (resultant_vec (2,), magnitude).
    """
    n = coords['n']
    amp = 1.0 / np.maximum(coords['R'], 1e-9)   # amplitude ~ 1/R (geometric falloff)
    ch = chi3(n)
    psi = w * phase_field
    vx = np.sum(ch * amp * np.cos(psi))
    vy = np.sum(ch * amp * np.sin(psi))
    return np.array([vx, vy]), np.hypot(vx, vy)

def axis_alignment_defect(coords, w, phase_field):
    """
    ALIGN-TO-AXIS test: at a true cancellation, the chi3-weighted phasors should
    point symmetrically so their resultant lands on the axis (resultant ~ 0).
    Defect = |resultant| normalized by total amplitude (1 = no cancellation, 0 = perfect).
    """
    n = coords['n']
    amp = 1.0 / np.maximum(coords['R'], 1e-9)
    ch = chi3(n)
    tot = np.sum(np.abs(ch) * amp)
    _, mag = phasor_resultant(coords, w, phase_field)
    return mag / max(tot, 1e-12)

if __name__ == "__main__":
    # ---- BUILD ONE CONCRETE BLOCKY HELIX AND PRINT A SAMPLE (per HARD RULE) ----
    G = np.load('/tmp/chi3_zeros65.npy')[:65]
    H = BlockyHelix(n_max=2000)
    n = H.n
    # block assignment: a simple sqrt-area packing -> block k holds ~k integers
    # cumulative integers up to block K ~ K^2, so k(n) ~ sqrt(n)
    block_assign = np.floor(np.sqrt(n)).astype(int)
    # laws: pitch steps with log (smooth mean), radius linear-in-k (Archimedean), spacing pi/3
    pitch_law   = lambda k: np.pi / 3 * (1 + 0.1 * k)      # blocky stepping pitch
    radius_law  = lambda nn, kk: np.maximum(kk, 1).astype(float)  # R = k (loop index)
    spacing_law = lambda k: np.pi / 3                      # constant integer arc spacing
    coords = H.build(pitch_law, radius_law, spacing_law, None, block_assign)
    print("=== THE BUILT 3D BLOCKY HELIX (explicit coordinates) ===")
    print(f"{'n':>5} {'block k':>7} {'R':>7} {'phi(wind)':>10} {'z(height)':>10}   (x, y, z)")
    for nn in [1, 2, 3, 4, 9, 16, 25, 100, 400, 1000]:
        i = nn - 1
        print(f"{nn:5d} {coords['k'][i]:7d} {coords['R'][i]:7.2f} {coords['phi'][i]:10.3f} "
              f"{coords['z'][i]:10.3f}   ({coords['x'][i]:8.2f},{coords['y'][i]:8.2f},{coords['z'][i]:7.3f})")
    print("\n=== PHASOR at each point (real unit vectors), sample ===")
    w = 8.0397371557  # first chi3 zero height as winding freq
    phase = np.log(coords['n'])  # bridge readout (the dictionary n^{it} <-> wind)
    psi = w * phase
    print(f"  using winding freq w = {w} (= gamma_1); phasor angle psi(n)=w*log n")
    for nn in [1, 2, 4, 5, 7, 8]:
        i = nn - 1
        u = (np.cos(psi[i]), np.sin(psi[i]))
        print(f"   n={nn}: chi3={chi3(nn):+.0f}  phasor u=({u[0]:+.3f},{u[1]:+.3f})  amp={1/coords['R'][i]:.3f}")
    vec, mag = phasor_resultant(coords, w, phase)
    print(f"\n  PHASOR VECTOR-SUM resultant at gamma_1: ({vec[0]:+.4f},{vec[1]:+.4f}) |.|={mag:.4f}")
    print(f"  axis-alignment defect = {axis_alignment_defect(coords, w, phase):.4f}  (0 = collapsed to axis)")
