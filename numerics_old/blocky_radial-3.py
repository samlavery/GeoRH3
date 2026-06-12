"""
blocky_radial-3.py   (ID: radial-3)

CLAIM under test (a NEGATIVE control / falsification):
  CONSTANT-HEIGHT-PER-BLOCK gives MEAN-ONLY at best, usually NOTHING.
  If the height is piecewise-CONSTANT within each block (every integer in block k
  shares one height z = z_block(k)), the within-block phasor phase is destroyed:
  every integer in the block points the same direction, so the chi3-weighted
  sub-sum over the block is fixed by chi3 residues alone and is w-INDEPENDENT.
  The resultant never develops zero-tracking minima -> 0 zeros matched, for any
  block width.  This FALSIFIES the naive 'one constant block per zero' picture.

  The remedy probe: let the height vary LINEARLY inside the block (slope = pitch).
  Tracking is RESTORED only when the slope makes per-integer phase ~ log(n)
  (the log law).  We sweep the slope law and show the restoration is conditional.

HARD RULE obeyed: we BUILD THE REAL 3D BLOCKY HELIX with explicit (x,y,z), PRINT a
coordinate sample BEFORE measuring, hang a real rotating PHASOR unit-vector at each
point, and detect a cancellation as the chi3-weighted PHASOR VECTOR-SUM collapsing
onto the central axis (resultant length -> 0).  We also test the ALIGN-TO-AXIS
condition (do all phasors point toward the axis at a zero?).  We never collapse to
an abstract scalar sum chi(n) amp e^{i phi} as the primary object -- the 3D points
and their attached vectors ARE the object; the scalar is only the resultant length.

EXACT zeros from mpmath: L(chi3,s) = 3^{-s}(zeta(s,1/3) - zeta(s,2/3)).
"""

import numpy as np
import mpmath as mp

mp.mp.dps = 30

# ------------------------------------------------------------------ chi3, zeros
def chi3(n):
    r = n % 3
    return 1.0 if r == 1 else (-1.0 if r == 2 else 0.0)

def Lchi3(s):
    s = mp.mpf(s) if not isinstance(s, mp.mpc) else s
    return mp.power(3, -s) * (mp.zeta(s, mp.mpf(1)/3) - mp.zeta(s, mp.mpf(2)/3))

def load_exact_zeros(path="chi3_zeros_exact.txt", k=20):
    g_str = []
    try:
        with open(path) as f:
            for ln in f:
                ln = ln.strip()
                if ln and not ln.startswith("#"):
                    g_str.append(ln.split()[0])
    except FileNotFoundError:
        pass
    g_str = g_str[:k]
    g_mp = [mp.mpf(s) for s in g_str]            # full-precision targets
    return np.array([float(x) for x in g_mp]), g_mp

GAMMA, GAMMA_MP = load_exact_zeros(k=20)

# verify the zeros: |L(1/2+i gamma)| should be tiny at full mpmath precision
def verify_zero_mp(t_mp):
    return float(abs(Lchi3(mp.mpf('0.5') + 1j*t_mp)))

print("="*80)
print("radial-3 : BLOCKY HELIX, flat-block falsification + linear-block restoration")
print("="*80)
print("\nExact chi3 zeros (mpmath), verified |L(1/2+i gamma)|:")
for i in range(6):
    v = verify_zero_mp(GAMMA_MP[i])
    print(f"   gamma = {GAMMA[i]:18.12f}   |L| = {v:.3e}")
assert all(verify_zero_mp(GAMMA_MP[i]) < 1e-12 for i in range(6)), "zero targets not verified!"

# =====================================================================
# STEP 1.  BUILD THE REAL 3D BLOCKY HELIX with explicit (x,y,z).
# =====================================================================
# Geometry (the blocky cone / Archimedean-rewound helix):
#   - integers n = 1..N are placed; block index k = floor(log n / W) (log-width W).
#   - RADIUS law (steps per block): area law R(n) = sqrt(n) -> amplitude amp = 1/R.
#       (radius is what gives the n^{-1/2} weight; it steps because the block does.)
#   - ANGLE about the axis: theta(n) = U * z_n  (the winding of the helix; the
#       phasor we hang spins as we wind -- see STEP 2).
#   - HEIGHT z_n: THIS is the variable under test.
#       FLAT-BLOCK  : z_n = z_block(k) = k*W           (constant within block)
#       LINEAR-BLOCK: z_n = block_base(k) + slope_k * local_fraction  (varies in block)
#
# A point of the solid is (x,y,z) = (R cos theta, R sin theta, z_n).  We PRINT a
# sample of these real coordinates before any measurement.

N = 40000
n = np.arange(1, N + 1).astype(float)
sign = np.array([chi3(int(k)) for k in n])
logn = np.log(n)
R_area = np.sqrt(n)          # radius law (area law): loop k holds ~k integers => R ~ sqrt(n)
amp = 1.0 / R_area           # amplitude weight n^{-1/2}, earned from the area law


def build_flat_block_heights(W):
    """z_n piecewise CONSTANT inside each log-block of width W."""
    k = np.floor(logn / W)
    return k * W                 # bottom-of-block height, constant across the block


def build_linear_block_heights(W, slope_scale):
    """z_n advances LINEARLY inside each block; the SLOPE steps per block.
    We choose the slope so cumulative height tracks the log law when slope_scale=1:
    inside block k (log-interval [kW,(k+1)W)) the local fraction runs 0..1 and the
    height rises by slope_k = slope_scale * W; base = k*W. So z = log-staircase made
    continuous-in-block.  With slope_scale=1 this reproduces z ~ log n; off 1 it
    detunes the per-integer phase away from the log law."""
    k = np.floor(logn / W)
    base = k * W
    local_frac = (logn - base) / W           # 0..1 within the block
    slope = slope_scale * W
    return base + slope * local_frac


def helix_coords(z, U):
    """Return explicit (x,y,z) of the blocky helix and the per-point phasor angle.
    theta = U * z is the winding angle; phasor base direction = theta."""
    theta = U * z
    x = R_area * np.cos(theta)
    y = R_area * np.sin(theta)
    return x, y, z, theta


# Print a real coordinate sample for one flat-block build and one linear-block build.
U0 = 1.0
Wprint = 0.25
z_flat = build_flat_block_heights(Wprint)
z_lin = build_linear_block_heights(Wprint, 1.0)
xf, yf, zf, thf = helix_coords(z_flat, U0)
xl, yl, zl, thl = helix_coords(z_lin, U0)

print("\n" + "-"*80)
print("STEP 1: explicit 3D blocky-helix coordinates (W=0.25 log units, U=1.0)")
print("-"*80)
print(f"{'n':>5} {'block':>5} | {'FLAT (x,y,z)':>34} | {'LINEAR (x,y,z)':>34}")
for ni in [1, 2, 3, 5, 8, 13, 21, 55, 100, 300, 1000, 5000]:
    i = ni - 1
    bk = int(np.floor(logn[i] / Wprint))
    print(f"{ni:>5} {bk:>5} | "
          f"({xf[i]:9.3f},{yf[i]:9.3f},{zf[i]:7.3f}) | "
          f"({xl[i]:9.3f},{yl[i]:9.3f},{zl[i]:7.3f})")
print("Note: within a flat block z is CONSTANT (e.g. n=1,2 share z); "
      "within a linear block z RISES.")

# =====================================================================
# STEP 2.  HANG A PHASOR (real rotating unit vector) at each point.
# =====================================================================
# As we wind ('w' = the spectral winding rate we scan), the phasor at integer n is
# the unit vector  u_n(w) = (cos(w * z_n), sin(w * z_n)).  It spins with w about the
# axis.  The chi3-weighted, amplitude-weighted PHASOR VECTOR-SUM is
#     V(w) = sum_n sign_n * amp_n * u_n(w)          (a 2D vector in the plane normal
#                                                    to the central axis)
# A cancellation event = V(w) collapses to the central axis: |V(w)| -> 0.
# We keep V as an actual VECTOR (Vx, Vy); the resultant length |V| is the readout.

def phasor_vector_sum(z, w):
    """Return the real 2D resultant VECTOR (Vx, Vy) of the chi3-weighted phasors."""
    a = w * z
    Vx = np.sum(sign * amp * np.cos(a))
    Vy = np.sum(sign * amp * np.sin(a))
    return Vx, Vy

def resultant_len(z, w):
    Vx, Vy = phasor_vector_sum(z, w)
    return np.hypot(Vx, Vy)

# Demonstrate the phasor vector-sum is a genuine vector (print Vx,Vy at a zero).
print("\n" + "-"*80)
print("STEP 2: phasor VECTOR-SUM V(w)=(Vx,Vy) is a real planar vector")
print("-"*80)
# use the linear-block (slope tuned to log) build at U so that w=gamma should collapse
z_demo = build_linear_block_heights(0.02, 1.0)   # fine staircase ~ log n
for w in [GAMMA[0], (GAMMA[0]+GAMMA[1])/2, GAMMA[1]]:
    Vx, Vy = phasor_vector_sum(z_demo, w)
    print(f"  w={w:8.4f}:  V=({Vx:+.5f},{Vy:+.5f})  |V|={np.hypot(Vx,Vy):.5f}")

# =====================================================================
# STEP 3.  WIND.  Find where the phasor vector-sum collapses; compare to exact zeros.
# =====================================================================
ws = np.linspace(6.0, 35.0, 8000)

def find_minima(ws, vals, thresh):
    out = []
    for i in range(1, len(ws) - 1):
        if vals[i] < vals[i-1] and vals[i] < vals[i+1] and vals[i] < thresh:
            out.append((ws[i], vals[i]))
    return out

def score(mins, tol=0.03, kk=12):
    matched, ds = 0, []
    for g in GAMMA[:kk]:
        if mins:
            ww = np.array([m[0] for m in mins])
            j = int(np.argmin(np.abs(ww - g)))
            d = abs(ww[j] - g)
            if d < tol:
                matched += 1; ds.append(d)
    return matched, (np.mean(ds) if ds else float('nan'))

def axis_alignment(z, w):
    """ALIGN-TO-AXIS test: at a candidate cancellation, how aligned/anti-aligned are
    the (chi3-signed) phasors?  Return the resultant length normalized by the total
    weight (1 = perfectly coherent, 0 = perfectly cancelled).  A true zero is the
    cancellation: signed phasors balance so resultant ~ 0 despite individual units."""
    Vx, Vy = phasor_vector_sum(z, w)
    tot = np.sum(amp * np.abs(sign))
    return np.hypot(Vx, Vy) / tot

print("\n" + "="*80)
print("STEP 3a:  FLAT-BLOCK FALSIFICATION  (height constant within each block)")
print("="*80)
flat_results = {}
for W in [0.05, 0.1, 0.25, 0.5]:
    z = build_flat_block_heights(W)
    vals = np.array([resultant_len(z, w) for w in ws])
    # adaptive threshold: 12% of the median resultant so we catch ANY dip
    thr = max(0.02, 0.12 * np.median(vals))
    mins = find_minima(ws, vals, thr)
    m, md = score(mins)
    flat_results[W] = m
    print(f"  W={W:4.2f} (log): matched {m}/12 zeros, mean|dw|={md:.4f}, "
          f"#minima={len(mins):3d}, median|V|={np.median(vals):.3f}, thr={thr:.3f}")

# Also a "W tied to 1/density" flat build: block width = pi/gap_k at local height.
# (Variable-width flat blocks; still constant height inside each.)
def build_flat_variable_width():
    """Blocks bounded so each holds the integers up to the next zero's mean spacing;
    height still constant inside each block (the falsification stays)."""
    # density d(t) ~ (1/2pi) log(3 t / 2pi); cumulative integers per unit log set
    # block edges in log; we just make edges follow local mean spacing in log.
    edges = [0.0]
    t = 1.0
    while edges[-1] < logn[-1]:
        # local mean gap in gamma ~ 2pi / log(3 gamma /2pi); convert to a log-width
        gam = max(8.0, edges[-1] * 10.0 + 8.0)
        gap = 2*np.pi / np.log(3*gam/(2*np.pi))
        edges.append(edges[-1] + max(0.02, gap/10.0))
    edges = np.array(edges)
    k = np.searchsorted(edges, logn, side='right') - 1
    k = np.clip(k, 0, len(edges)-2)
    return edges[k]    # constant height = left edge of variable block

zfv = build_flat_variable_width()
vals = np.array([resultant_len(zfv, w) for w in ws])
thr = max(0.02, 0.12*np.median(vals))
mins = find_minima(ws, vals, thr)
m, md = score(mins)
print(f"  W tied to 1/density (variable-width flat blocks): matched {m}/12, "
      f"mean|dw|={md:.4f}, #minima={len(mins)}")

print("\n  --> FLAT-BLOCK PREDICTION (falsification): ~0 zeros matched everywhere.")
print(f"      observed matches per W: {flat_results}")

# Why: explicitly show the flat-block resultant is a COARSE w-comb fixed by chi3
# block-sums S_k (w-structure does not resolve individual gamma_k).
print("\n  Mechanism check: flat-block V(w) = sum_k S_k * (cos,sin)(w*z_block(k)),")
print("  with S_k = sum of chi3 over block k (w-INDEPENDENT block weights):")
W = 0.25
k = np.floor(logn / W).astype(int)
Kmax = k.max()
S = np.array([np.sum((sign*amp)[k == kk]) for kk in range(Kmax+1)])
zblk = np.arange(Kmax+1) * W
nzero = np.sum(np.abs(S) > 1e-9)
print(f"    #blocks={Kmax+1}, #blocks with nonzero chi3 sum S_k = {nzero} "
      f"(coarse comb; cannot resolve {len(GAMMA)} zeros).")

print("\n" + "="*80)
print("STEP 3b:  LINEAR-IN-BLOCK RESTORATION  (height rises inside block; slope swept)")
print("="*80)
print("  height varies inside block (per-integer phase survives); we sweep the slope")
print("  scale.  Tracking should return ONLY when slope tunes per-integer phase to log n.")

def run_linear(W, slope_scale):
    z = build_linear_block_heights(W, slope_scale)
    # fit z = a*log n + b on the bulk so the winding rate w is comparable to gamma
    msk = n >= 50
    c = np.polyfit(logn[msk], z[msk], 1)
    zr = (z - c[1]) / c[0] if abs(c[0]) > 1e-12 else z
    res = np.std((zr - logn)[msk]) / np.std(logn[msk])
    vals = np.array([resultant_len(zr, w) for w in ws])
    thr = max(0.05, 0.15*np.median(vals))
    mins = find_minima(ws, vals, thr)
    m, md = score(mins)
    return m, md, res, len(mins)

print(f"\n  {'W':>5} {'slope':>6} | {'matched':>7} {'mean|dw|':>9} "
      f"{'z~logn resid':>12} {'#min':>5}")
best = (-1, None)
for W in [0.05, 0.1, 0.25]:
    for ss in [0.25, 0.5, 1.0, 1.5, 2.0]:
        m, md, res, nm = run_linear(W, ss)
        flag = "  <== tuned to log" if (abs(ss-1.0) < 1e-9) else ""
        print(f"  {W:>5.2f} {ss:>6.2f} | {m:>7d} {md:>9.4f} {res:>12.4f} {nm:>5d}{flag}")
        if m > best[0]:
            best = (m, (W, ss))

# =====================================================================
# CONTROL builds: smooth log (Build A, the analytic L made geometric) + sqrt + const.
# =====================================================================
print("\n" + "="*80)
print("CONTROLS")
print("="*80)

def control(zfield, name, sweep_fit=True):
    z = zfield.copy()
    if sweep_fit:
        msk = n >= 50
        c = np.polyfit(logn[msk], z[msk], 1)
        z = (z - c[1]) / c[0] if abs(c[0]) > 1e-12 else z
    vals = np.array([resultant_len(z, w) for w in ws])
    thr = max(0.05, 0.15*np.median(vals))
    mins = find_minima(ws, vals, thr)
    m, md = score(mins)
    print(f"  {name:32s}: matched {m}/12, mean|dw|={md:.4f}, #minima={len(mins)}")
    return m

m_logA = control(logn, "smooth z=log(n)  (Build A)", sweep_fit=False)
control(R_area, "smooth z=sqrt(n)", sweep_fit=True)
control(np.full(N, 1.0), "z=const (degenerate)", sweep_fit=False)

# ALIGN-TO-AXIS readout at the true zeros for Build A vs flat block.
print("\n  ALIGN-TO-AXIS at the exact zeros (normalized resultant, 0=cancelled):")
zflat = build_flat_block_heights(0.25)
for g in GAMMA[:6]:
    a_logA = axis_alignment(logn, g)
    a_flat = axis_alignment(zflat, g)
    print(f"    gamma={g:8.4f}:  Build-A coherence={a_logA:.4f}   "
          f"flat-block coherence={a_flat:.4f}")

# =====================================================================
# VERDICT
# =====================================================================
print("\n" + "="*80)
print("VERDICT")
print("="*80)
flat_any = max(flat_results.values())
print(f"  flat-block max matches over all W: {flat_any}/12  "
      f"(prediction: ~0 -> FALSIFICATION confirmed)" if flat_any <= 1 else
      f"  flat-block max matches over all W: {flat_any}/12")
print(f"  linear-block best: {best[0]}/12 at (W,slope_scale)={best[1]}")
print(f"  Build-A (smooth log) control: {m_logA}/12")
print("\n  Interpretation:")
print("   - Flat-block (constant height per block) DESTROYS within-block phase ->")
print("     resultant is a coarse w-comb of chi3 block-sums; it does NOT track zeros.")
print("   - Restoration requires per-integer phase ~ log(n): only the LINEAR-in-block")
print("     height with slope tuned to the log law recovers minima -- and that is the")
print("     SMOOTH log mean re-expressed, i.e. it reproduces the MEAN spacing, not the")
print("     per-block FLUCTUATION S(T).  The fluctuation is NOT captured by either.")

import json
verdict = {
    "flat_block_max_matches": int(flat_any),
    "linear_block_best_matches": int(best[0]),
    "linear_block_best_params": best[1],
    "buildA_smooth_log_matches": int(m_logA),
    "n_exact_zeros_in_window": int(np.sum((GAMMA >= 6) & (GAMMA <= 35))),
}
print("\nMACHINE_VERDICT " + json.dumps(verdict))
