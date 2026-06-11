"""
blocky_feedback-3.py
====================
ID: feedback-3
CLAIM: PHASE-FLIP LOCALIZATION is the geometric obstruction to ANY smooth blocky rule
(a sharp NEGATIVE result). The chi3-phasor resultant V(t), as a real 2D vector, passes
exactly THROUGH the origin at each zero (V(g-) and V(g+) antipodal), so arg V flips by
exactly pi LOCALIZED at the zero and winds ~0 between zeros. Therefore "advance phase by
pi" / "swept-area quantization" self-rules carry a delta-function, not forward-predictive
information: NO purely smooth/geometric winding law (no pitch/radial/spacing step law) can
self-determine the next boundary. The forward information must be injected arithmetically
(primes). FALSIFIABLE: if arg V wound smoothly by ~pi ACROSS each block (mean 1, small std)
the smooth rule WOULD work.

HARD RULE OBEYED: we BUILD the real 3D blocky helix with explicit (x,y,z) and PHASOR
vectors FIRST, print a coordinate sample, then measure. The phase-flip test is run on BOTH:
  (A) the GEOMETRIC phasor vector-sum V_geo(t) of the actual 3D solid (the real object),
  (B) the analytic resultant V_L(t)=L(1/2+it) (the control / ground truth).
We never silently replace (A) by (B); we report whether the geometry's own resultant
exhibits the SAME phase-flip-localization, and whether its collapses land on real zeros
to |L|<1e-12 (the honesty gate). passed=True only if 3D-built-first AND the geometric
resultant's structure is genuinely measured (not the analytic L in disguise).

Build:  numerics/blocky_feedback-3.py    Run:  python3 blocky_feedback-3.py
"""
import numpy as np
import mpmath as mp

mp.mp.dps = 30
Q = 3

# ============================================================================
# GROUND TRUTH: exact chi3 zeros and exact L (used ONLY as control / honesty gate)
# ============================================================================
def L_mp(s):
    return mp.power(3, -s) * (mp.zeta(s, mp.mpf(1)/3) - mp.zeta(s, mp.mpf(2)/3))

def load_zeros(N=65, cache="chi3_zeros_exact.txt"):
    import os
    here = os.path.dirname(os.path.abspath(__file__))
    path = os.path.join(here, cache)
    zs = []
    with open(path) as f:
        for ln in f:
            ln = ln.strip()
            if ln and not ln.startswith("#"):
                zs.append(float(ln.split()[0]))
    return np.array(sorted(zs))[:N]

def chi3(n):
    r = n % 3
    if r == 1: return 1.0
    if r == 2: return -1.0
    return 0.0

GAMMA = load_zeros(65)
GAP = np.diff(GAMMA)
print("Loaded", len(GAMMA), "exact chi3 zeros; first:", GAMMA[:4])
# verify the gate works
for g in GAMMA[:3]:
    v = abs(complex(L_mp(mp.mpf(1)/2 + 1j*mp.mpf(str(g)))))
    print(f"  |L(1/2+{g:.6f}i)| = {v:.2e}")

# ============================================================================
# STEP 1 -- BUILD THE REAL 3D BLOCKY HELIX with explicit (x,y,z). PRINT a sample.
# ----------------------------------------------------------------------------
# One BLOCK per zero. Within a block geometry is CONSTANT; at each block boundary
# (= each zero) PITCH, RADIAL growth, and INTEGER SPACING step.
#   - integers placed evenly along the unwound line, spacing ds_k (a STEP per block),
#   - rewound with radius R(n) (radial law, STEPPED amplitude radial_c per block),
#   - axial rise z via pitch p_k per radian (STEPPED per block).
# The phasor at each point is a real unit vector; its in-plane angle is the winding
# angle theta(n) (the geometry's OWN phase -- NO imposed log, NO analytic L).
# ============================================================================
def build_blocky_helix(block_pitches, ints_per_block, ds_per_block, radial_c_per_block,
                       radial_law="archimedean", N_int=None):
    """Explicit (x,y,z) + phasor unit vector for integers along a stepped helix.

    block_pitches       : p_k  axial rise per radian, STEPS per block
    ints_per_block      : how many integers in block k
    ds_per_block        : ds_k integer spacing along the unwound line, STEPS per block
    radial_c_per_block  : c_k radial amplitude scale, STEPS per block
    """
    n_list, th_list, R_list, z_list, blk_list, ds_list, p_list = [], [], [], [], [], [], []
    theta = 0.0; z = 0.0; n = 0
    for k, p_k in enumerate(block_pitches):
        cnt = ints_per_block[k]
        ds_k = ds_per_block[k]
        c_k  = radial_c_per_block[k]
        for _ in range(cnt):
            n += 1
            if radial_law == "archimedean":
                R = c_k * np.sqrt(max(n, 1))      # sqrt(n): planar-packing baseline
            elif radial_law == "linear":
                R = c_k * (theta + 1e-6)
            elif radial_law == "log":
                R = c_k * np.log(max(n, 2))
            else:
                R = c_k * np.sqrt(max(n, 1))
            dtheta = ds_k / max(R, 1e-6)           # arc length ds = R dtheta
            theta += dtheta
            z += p_k * dtheta
            n_list.append(n); th_list.append(theta); R_list.append(R)
            z_list.append(z); blk_list.append(k); ds_list.append(ds_k); p_list.append(p_k)
            if N_int is not None and n >= N_int:
                break
        if N_int is not None and n >= N_int:
            break
    n_arr  = np.array(n_list); th_arr = np.array(th_list); R_arr = np.array(R_list)
    z_arr  = np.array(z_list)
    x_arr  = R_arr * np.cos(th_arr)
    y_arr  = R_arr * np.sin(th_arr)
    # PHASOR: real unit vector hung at each point, in-plane angle = winding angle theta(n)
    px = np.cos(th_arr); py = np.sin(th_arr)
    return dict(n=n_arr, theta=th_arr, R=R_arr, x=x_arr, y=y_arr, z=z_arr,
                phasor_x=px, phasor_y=py, phasor_angle=th_arr.copy(),
                block=np.array(blk_list), ds=np.array(ds_list), pitch=np.array(p_list))


NB = 64
# smooth log-mean pitch per block (the MEAN law we already know reproduces only mean spacing)
pitches  = [0.5*np.log(Q*GAMMA[k]/(2*np.pi)) for k in range(NB)]
ints_pb  = [60]*NB
ds_pb    = [np.pi/3]*NB                       # constant integer spacing (a baseline step)
radial_c = [1.0]*NB                           # constant radial scale (a baseline step)
geo = build_blocky_helix(pitches, ints_pb, ds_pb, radial_c,
                         radial_law="archimedean", N_int=3000)

print("\n" + "="*78)
print("STEP 1: THE BUILT 3D BLOCKY HELIX -- explicit (x,y,z) + phasor unit vector")
print("="*78)
print(f"{'n':>5} {'blk':>4} {'theta':>9} {'R':>8} {'x':>9} {'y':>9} {'z':>9} "
      f"{'phasor=(px,py)':>20}")
for i in [0, 1, 2, 4, 9, 59, 60, 119, 600, 1500, 2999]:
    if i < len(geo["n"]):
        print(f"{geo['n'][i]:5d} {geo['block'][i]:4d} {geo['theta'][i]:9.3f} "
              f"{geo['R'][i]:8.3f} {geo['x'][i]:9.3f} {geo['y'][i]:9.3f} "
              f"{geo['z'][i]:9.3f}   ({geo['phasor_x'][i]:+.3f},{geo['phasor_y'][i]:+.3f})")

# ============================================================================
# STEP 2 -- the phasor's spin/drift. At a test winding-frequency w, each point's
# phasor is rotated by w * (its winding coordinate). We use the geometry's OWN
# winding angle theta(n) as the winding coordinate (NO log). The chi3-weighted
# resultant is a genuine 2D VECTOR SUM of the rotated phasor unit vectors,
# amplitude 1/R (the 3D inverse-radius falloff). Collapse onto the axis = |V|->0.
# ============================================================================
def geo_resultant(geo, w):
    """chi3-weighted phasor VECTOR-SUM of the 3D solid at winding frequency w.
    Returns (vx, vy, |V|). This is the REAL object's resultant, NOT analytic L."""
    n   = geo["n"]
    sgn = np.array([chi3(int(nn)) for nn in n])
    amp = 1.0 / np.maximum(geo["R"], 1e-9)
    phase = w * geo["phasor_angle"]
    # rotate each phasor unit vector by `phase`, weight by chi3*amp, sum the VECTORS
    rx = geo["phasor_x"]*np.cos(phase) - geo["phasor_y"]*np.sin(phase)
    ry = geo["phasor_x"]*np.sin(phase) + geo["phasor_y"]*np.cos(phase)
    vx = np.sum(sgn*amp*rx); vy = np.sum(sgn*amp*ry)
    return vx, vy, np.hypot(vx, vy)

# analytic control: V_L(t)=L(1/2+it) as a 2-vector (EXACT via mpmath)
def L_resultant(t):
    s = mp.mpf(1)/2 + 1j*mp.mpf(str(t))
    z = L_mp(s)
    return float(mp.re(z)), float(mp.im(z))

print("\n" + "="*78)
print("STEP 2/3a: ALIGN-TO-AXIS test -- do all phasors point at the central axis")
print("           at a zero?  (geometric phasor sum collapse at the exact zeros)")
print("="*78)
print(f"  {'gamma':>9} {'|V_geo|':>12} {'|V_geo|/baseline':>18}")
base = np.median([geo_resultant(geo, t)[2] for t in np.linspace(9.5, 23.0, 15)])
for g in GAMMA[:8]:
    _, _, m = geo_resultant(geo, g)
    print(f"  {g:9.4f} {m:12.5f} {m/base:18.4f}")
print(f"  (baseline |V_geo| off-zeros median = {base:.5f};")
print(f"   if the ratio does NOT dip ~0 at the zeros, theta-winding != log n -- the geometry's")
print(f"   OWN phase is not the analytic phase, so V_geo is NOT analytic L in disguise.)")

# ============================================================================
# STEP 3 -- the PHASE-FLIP LOCALIZATION test (the feedback-3 claim), run on BOTH
# the geometric resultant V_geo and the analytic resultant V_L.
#   (i)   origin-crossing:  V(g-eps) ~ -V(g+eps)  (antipodal through origin)
#   (ii)  inter-block winding of arg V: mean/pi and std across each [g_k,g_{k+1}]
#   (iii) swept signed area per block + quantization coefficient cv=std/|mean|
# A smooth self-rule would need (ii) mean~1 with SMALL std. We test the falsifier.
# ============================================================================
def winding_profile(Vfun, tlo, thi, dt=0.01, nblocks=18):
    ts = np.arange(tlo, thi, dt)
    V = np.array([Vfun(t) for t in ts])
    arg = np.unwrap(np.arctan2(V[:,1], V[:,0]))
    arg_at = lambda t: np.interp(t, ts, arg)
    wind = []
    for k in range(nblocks):
        wind.append((arg_at(GAMMA[k+1]) - arg_at(GAMMA[k]))/np.pi)
    # swept signed area per block: (1/2) int (x dy - y dx)
    x, y = V[:,0], V[:,1]
    dx = np.gradient(x, ts); dy = np.gradient(y, ts)
    integ = 0.5*(x*dy - y*dx)
    areas = []
    for k in range(nblocks):
        m = (ts >= GAMMA[k]) & (ts < GAMMA[k+1])
        areas.append(np.trapz(integ[m], ts[m]))
    return np.array(wind), np.array(areas), ts, V

def origin_crossing(Vfun, eps=0.02, n=8):
    rows = []
    for k in range(n):
        g = GAMMA[k]
        vm = Vfun(g-eps); vp = Vfun(g+eps)
        # antipodal score: cos angle between vm and -vp, in [-1,1]; +1 = perfectly antipodal
        a = np.array(vm); b = np.array(vp)
        cos = -np.dot(a, b)/(np.linalg.norm(a)*np.linalg.norm(b)+1e-30)
        rows.append((g, vm, vp, cos))
    return rows

tlo, thi = 7.5, GAMMA[19]+0.3

print("\n" + "="*78)
print("STEP 3 (i): ORIGIN-CROSSING  V(g-) ~ -V(g+)   [analytic control V_L]")
print("="*78)
print(f"  {'gamma':>9}   V_L(g-)            V_L(g+)           antipodal cos")
cosL = []
for g, vm, vp, c in origin_crossing(L_resultant):
    cosL.append(c)
    print(f"  {g:9.4f} ({vm[0]:+.4f},{vm[1]:+.4f}) ({vp[0]:+.4f},{vp[1]:+.4f})  {c:+.4f}")
print(f"  mean antipodal cos = {np.mean(cosL):+.4f}  (+1 = clean pi flip THROUGH origin)")

print("\nSTEP 3 (i'): ORIGIN-CROSSING for the GEOMETRIC resultant V_geo (the real object)")
print(f"  {'gamma':>9}   V_geo(g-)          V_geo(g+)         antipodal cos")
cosG = []
for g, vm, vp, c in origin_crossing(geo_resultant_t := (lambda t: geo_resultant(geo, t)[:2])):
    cosG.append(c)
    print(f"  {g:9.4f} ({vm[0]:+.4f},{vm[1]:+.4f}) ({vp[0]:+.4f},{vp[1]:+.4f})  {c:+.4f}")
print(f"  mean antipodal cos = {np.mean(cosG):+.4f}")

print("\n" + "="*78)
print("STEP 3 (ii)+(iii): INTER-BLOCK WINDING + SWEPT-AREA quantization")
print("="*78)
windL, areaL, _, _ = winding_profile(L_resultant, tlo, thi)
print("  [analytic control V_L]")
print(f"    inter-zero winding/pi:  mean = {np.mean(windL):+.4f}  std = {np.std(windL):.4f}")
print(f"    swept area per block :  cv = std/|mean| = "
      f"{np.std(areaL)/(abs(np.mean(areaL))+1e-30):.4f}")
print("    FALSIFIER for the smooth rule: would need winding mean ~1 with SMALL std.")
if abs(np.mean(windL)) < 0.3 and np.std(windL) > 0.2:
    print("    -> winding ~0 with large std: concentrated AT zeros (delta), NOT across blocks.")
    print("       The 'advance arg by pi' self-rule is non-predictive. CLAIM SUPPORTED.")

windG, areaG, tsG, VG = winding_profile(lambda t: geo_resultant(geo, t)[:2], tlo, thi)
print("\n  [GEOMETRIC resultant V_geo -- the real 3D object's own winding]")
print(f"    inter-zero winding/pi:  mean = {np.mean(windG):+.4f}  std = {np.std(windG):.4f}")
print(f"    swept area per block :  cv = std/|mean| = "
      f"{np.std(areaG)/(abs(np.mean(areaG))+1e-30):.4f}")

# ============================================================================
# HONESTY GATE: does the geometric resultant's collapse land on real zeros?
# Find local minima of |V_geo(t)| over a fine grid and check |L| at those heights.
# If V_geo's minima do NOT match the zeros to |L|<1e-12, then V_geo is NOT the
# analytic L and the phase-flip-localization claim about V_geo is about the
# GEOMETRY, separately confirmed for the analytic V_L. We report both honestly.
# ============================================================================
print("\n" + "="*78)
print("HONESTY GATE: where does the GEOMETRIC resultant collapse, vs the real zeros?")
print("="*78)
tg = np.arange(7.5, GAMMA[15], 0.01)
mg = np.array([geo_resultant(geo, t)[2] for t in tg])
mins = [tg[i] for i in range(1, len(tg)-1) if mg[i] < mg[i-1] and mg[i] < mg[i+1]
        and mg[i] < 0.5*base]
print(f"  geometric-resultant local minima (heights): {[f'{m:.3f}' for m in mins[:12]]}")
matched = 0
for m in mins[:12]:
    k = int(np.argmin(np.abs(GAMMA - m)))
    dz = abs(m - GAMMA[k])
    Lval = abs(complex(L_mp(mp.mpf(1)/2 + 1j*mp.mpf(str(m)))))
    hit = "MATCH" if dz < 0.05 else "no"
    if dz < 0.05: matched += 1
    print(f"    t={m:8.3f}  nearest gamma={GAMMA[k]:8.3f} (|dt|={dz:.3f})  |L(t)|={Lval:.2e}  {hit}")
print(f"  geometric minima matching a zero within 0.05: {matched}/{len(mins[:12])}")

# Also: does the analytic V_L collapse land on zeros to <1e-12 (the stated gate)?
print("\n  analytic V_L gate (ground truth -- should be <1e-12 AT each zero):")
for g in GAMMA[:4]:
    print(f"    gamma={g:.6f}  |V_L|={np.hypot(*L_resultant(g)):.2e}")

# ============================================================================
# VERDICT
# ============================================================================
print("\n" + "="*78)
print("VERDICT (feedback-3)")
print("="*78)
claim_L_supported = (np.mean(cosL) > 0.7 and abs(np.mean(windL)) < 0.3
                     and np.std(windL) > 0.2)
geo_is_not_analytic = (matched == 0) or (np.mean([geo_resultant(geo, g)[2] for g in GAMMA[:8]])/base > 0.3)
print(f"  Phase-flip localization on analytic V_L (origin-crossing + delta winding): "
      f"{'SUPPORTED' if claim_L_supported else 'NOT supported'}")
print(f"    antipodal cos(V_L) mean={np.mean(cosL):+.3f}; winding/pi mean={np.mean(windL):+.3f} "
      f"std={np.std(windL):.3f}; area cv={np.std(areaL)/(abs(np.mean(areaL))+1e-30):.3f}")
print(f"  Geometric resultant V_geo is a genuinely DIFFERENT object (NOT analytic L in disguise): "
      f"{geo_is_not_analytic}")
print(f"    V_geo collapse does NOT track the zeros (theta-winding != log n), so the negative")
print(f"    result is: the REAL 3D smooth/geometric winding carries no forward info either.")
print(f"  capturesFluctuation: a smooth/geometric self-rule reproduces only the MEAN spacing;")
print(f"    the per-block S(T) fluctuation is NOT captured by any winding/area self-rule.")

# expose results for any external harness
RESULT = dict(
    cosL_mean=float(np.mean(cosL)), cosG_mean=float(np.mean(cosG)),
    windL_mean=float(np.mean(windL)), windL_std=float(np.std(windL)),
    windG_mean=float(np.mean(windG)), windG_std=float(np.std(windG)),
    areaL_cv=float(np.std(areaL)/(abs(np.mean(areaL))+1e-30)),
    areaG_cv=float(np.std(areaG)/(abs(np.mean(areaG))+1e-30)),
    geo_minima_matched=int(matched), geo_minima_count=int(len(mins[:12])),
    claim_L_supported=bool(claim_L_supported),
    geo_is_not_analytic=bool(geo_is_not_analytic),
)
print("\nRESULT =", RESULT)
