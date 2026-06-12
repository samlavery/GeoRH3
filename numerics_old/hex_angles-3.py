"""
hex_angles-3.py  --  ID angles-3 / CLAIM H3
================================================================================
ALIGN-TO-AXIS on the SAWTOOTH HEXAGONAL CONE.

The user directive (non-negotiable):
  STEP 1  build the REAL 3D solid (explicit x,y,z) by the HEXAGONAL AREA LAW:
          integers placed at constant ARC spacing along an Archimedean spiral
          R(theta)=A*theta (LINEAR radial growth per loop -- NO imposed sqrt/log).
          The area swept to integer n is ~ pi R^2 ~ n, so R ~ sqrt(n) EMERGES as a
          packing fact.  Print a coordinate sample; show R~sqrt(n) emerges.
  STEP 2  attach a PHASOR (a real unit vector in 3-space, in the local normal
          plane) at each lattice point.  Direction d_n(t) = chi3(n)*exp(i*(sector_n
          - t*beta_n)), sector_n = (loop k mod 6)*(pi/3) = which 6th-root sector.
          The phasors are the mechanism; print sample phasor vectors.
  STEP 3  WIND (winding parameter t).  The cancellation EVENT = the chi3-weighted
          phasor VECTOR SUM (resultant of the spinning vectors) collapses onto the
          central axis:  A(t) = | sum_n chi3(n) amp_n exp(i(sector_n - t beta_n)) |.
          A(t) -> 0  = no net transverse vector = align-to-axis.

THREE geometric drift candidates beta_n (the honest test):
   (i)   beta_n = theta_n/(2pi)  = loop count  (linear-in-geometry winding)
   (ii)  beta_n = log(R_n) = log(area)/2       (the EMERGENT log -- the KNOWN trap;
                                                 control proving the apparatus works)
   (iii) beta_n = 2pi*frac(area/quantum)       (a genuinely BOUNDED sawtooth phase)

Honest recon prediction (from prior phasor_drag.py + eisenstein-angle recon):
  (ii) MUST cancel at the zeros (log R = log n + const, tautological n^{-it}).
  (i),(iii) are the genuine geometric tests -- recon predicts they do NOT cancel,
  because any drift that is NOT secretly log n does not reproduce n^{-it}.
H3's sharp question: does ANY non-log geometric drift carry the chi3 zeros?

VERIFY: any claimed cancellation height is checked vs mpmath |L(chi3,1/2+ig)|<1e-12.
================================================================================
"""
import numpy as np
import mpmath as mp

mp.mp.dps = 30

# ---------------------------------------------------------------- exact chi3 L
def Lchi3(s):
    # L(chi3,s) = 3^{-s} (zeta(s,1/3) - zeta(s,2/3)),  chi3 = real char mod 3
    return 3 ** (-s) * (mp.zeta(s, mp.mpf(1) / 3) - mp.zeta(s, mp.mpf(2) / 3))

def absL_online(gamma):
    return float(abs(Lchi3(mp.mpf(1) / 2 + 1j * mp.mpf(gamma))))

# ---------------------------------------------------------------- exact zeros
GAM = []
with open("lchi3_zeros_1000.txt") as f:
    for ln in f:
        ln = ln.strip()
        if ln and not ln.startswith("#"):
            GAM.append(float(ln.split()[1]))
GAM = np.array(sorted(GAM))
Z8 = GAM[:8]
print("Exact chi3 zero heights (first 8):", np.round(Z8, 4))
print("  verify file: |L(1/2+i*gamma_1)| =", f"{absL_online(Z8[0]):.2e}", "(should be ~0)\n")


# ================================================================ STEP 1
# BUILD THE 3D AREA-LAW CONE.  Reuse build3d.py machinery: integers at constant
# arc spacing along R(theta)=A*theta, solve theta_n from arc length numerically.
# ============================================================================
def build_cone(M, c_growth=6.0, arc=np.pi / 3, pitch=np.pi / 3, theta_max=12000.0,
               grid=1_000_000):
    """
    Archimedean spiral R(theta) = A*theta with A = e^{c_growth}/(2pi)
    (LINEAR radial growth: +e^{c_growth} per 2pi loop -- NOT exponential).
    Integers at constant ARC spacing `arc` => s_n = n*arc; solve theta_n.
    pitch = axial rise per loop.  Returns explicit (x,y,z) + geometry arrays.
    """
    A = np.exp(c_growth) / (2 * np.pi)
    th = np.linspace(0.0, theta_max, grid)
    # arc length element of the conical spiral (radial + tangential + axial)
    dsdth = np.sqrt(A ** 2 * (1 + th ** 2) + (pitch / (2 * np.pi)) ** 2)
    s = np.concatenate([[0.0], np.cumsum(0.5 * (dsdth[1:] + dsdth[:-1]) * np.diff(th))])
    n = np.arange(1, M + 1)
    s_n = n * arc
    if s_n[-1] > s[-1]:
        raise ValueError("theta_max too small for M integers; increase grid/theta_max")
    theta = np.interp(s_n, s, th)          # REAL winding angle of integer n
    R = A * theta                          # REAL radius (linear in theta)
    k = theta / (2 * np.pi)                # REAL loop index (continuous)
    zc = pitch * k                         # REAL height
    x, y = R * np.cos(theta), R * np.sin(theta)
    return dict(n=n, A=A, theta=theta, R=R, k=k, z=zc, x=x, y=y,
                c=c_growth, arc=arc, pitch=pitch)

M = 60000
C = build_cone(M, c_growth=6.0, arc=np.pi / 3, pitch=np.pi / 3)
n = C["n"]
theta, R, k, zc, x, y = C["theta"], C["R"], C["k"], C["z"], C["x"], C["y"]

def chi3_arr(n):
    return np.where(n % 3 == 1, 1.0, np.where(n % 3 == 2, -1.0, 0.0))
sign = chi3_arr(n)

# sector_n = which 6th-root sector the loop-angle is in = (k mod 6)*(pi/3)
sector = (np.floor(k).astype(int) % 6) * (np.pi / 3)

print("=" * 78)
print("STEP 1 : THE BUILT 3D AREA-LAW CONE (explicit coordinates)")
print("=" * 78)
print(f"A = e^6/2pi = {C['A']:.4f};  arc spacing = pi/3;  pitch = pi/3 per loop.")
print(f"Radial growth LINEAR (+e^6 per loop), NOT exponential.\n")
print(f"{'n':>5} {'theta(wind)':>11} {'k(loop)':>8} {'R(out)':>10} "
      f"{'sector':>7}   {'(x,        y,        z)':>30}")
for nn in [1, 2, 3, 6, 7, 12, 100, 1000, 10000]:
    i = nn - 1
    sec_deg = sector[i] * 180 / np.pi
    print(f"{nn:5d} {theta[i]:11.4f} {k[i]:8.3f} {R[i]:10.3f} "
          f"{sec_deg:6.0f}d   ({x[i]:9.2f},{y[i]:9.2f},{zc[i]:8.3f})")

# show R ~ sqrt(n) EMERGES (area packing), not imposed
print("\n--- does R ~ sqrt(n) EMERGE from the area law? (fit on n>=1000) ---")
mfit = n >= 1000
for nm, f in [("sqrt(n)", np.sqrt(n)), ("n^(1/3)", n ** (1 / 3.)),
              ("log n", np.log(n)), ("n", n.astype(float))]:
    cc = np.polyfit(f[mfit], R[mfit], 1)
    res = np.std(R[mfit] - (cc[0] * f[mfit] + cc[1])) / np.std(R[mfit])
    tag = "  <-- EMERGES" if res < 0.02 else ""
    print(f"   R ~ {cc[0]:8.4f} * {nm:8s} + {cc[1]:8.3f} : rel-residual {res:.4f}{tag}")
# area swept ~ pi R^2 should be ~ linear in n
area = np.pi * R ** 2
ca = np.polyfit(n[mfit].astype(float), area[mfit], 1)
print(f"   area = pi R^2 ~ {ca[0]:.4f}*n + {ca[1]:.1f}  (linear in n => packing law holds)")


# ================================================================ STEP 2
# ATTACH PHASORS: a real unit vector at each 3D point, in the LOCAL NORMAL PLANE
# of the spiral.  We build the Frenet-ish local frame (tangent T, and two normals
# spanning the plane perpendicular to T) so the phasor is a genuine 3D direction,
# then express its rotation as a complex number in that 2D normal plane.
# ============================================================================
def local_frame(x, y, zc):
    """tangent T (unit), and an orthonormal pair (e1,e2) spanning the normal plane."""
    Tx = np.gradient(x); Ty = np.gradient(y); Tz = np.gradient(zc)
    Tn = np.sqrt(Tx ** 2 + Ty ** 2 + Tz ** 2)
    Tx, Ty, Tz = Tx / Tn, Ty / Tn, Tz / Tn
    # reference up-vector = lab z; e1 = normalize(up - (up.T)T), e2 = T x e1
    ux, uy, uz = 0.0, 0.0, 1.0
    dot = Tx * ux + Ty * uy + Tz * uz
    e1x, e1y, e1z = ux - dot * Tx, uy - dot * Ty, uz - dot * Tz
    e1n = np.sqrt(e1x ** 2 + e1y ** 2 + e1z ** 2)
    e1x, e1y, e1z = e1x / e1n, e1y / e1n, e1z / e1n
    e2x = Ty * e1z - Tz * e1y
    e2y = Tz * e1x - Tx * e1z
    e2z = Tx * e1y - Ty * e1x
    return (Tx, Ty, Tz), (e1x, e1y, e1z), (e2x, e2y, e2z)

T, E1, E2 = local_frame(x, y, zc)

def phasor_3d(angle, i):
    """unit phasor vector in 3-space at index i, rotated by `angle` in normal plane."""
    ca, sa = np.cos(angle), np.sin(angle)
    vx = ca * E1[0][i] + sa * E2[0][i]
    vy = ca * E1[1][i] + sa * E2[1][i]
    vz = ca * E1[2][i] + sa * E2[2][i]
    return np.array([vx, vy, vz])

print("\n" + "=" * 78)
print("STEP 2 : PHASOR VECTORS attached in the LOCAL NORMAL PLANE (at fixed t=8.04)")
print("=" * 78)
t_demo = float(Z8[0])
beta_demo = k.copy()                       # use loop-count drift for the demo
print(f"phasor n: chi3(n)*exp(i*(sector_n - t*beta_n)) in plane (e1,e2) perp to tangent.")
print(f"{'n':>5} {'chi3':>5} {'sector':>7} {'phase':>8}   {'phasor 3D dir (vx,vy,vz)':>32}")
for nn in [1, 2, 3, 6, 7, 12]:
    i = nn - 1
    ang = sector[i] - t_demo * beta_demo[i]
    base = phasor_3d(ang, i)
    vec = sign[i] * base       # chi3 sign flips the vector (0 => null phasor)
    print(f"{nn:5d} {sign[i]:+5.0f} {sector[i]*180/np.pi:6.0f}d {ang:8.2f}   "
          f"({vec[0]:+7.3f},{vec[1]:+7.3f},{vec[2]:+7.3f})")
print("  (chi3=0 at n=3,6,12 => null phasor; sign +/-1 reverses the 3D direction)")

# Verify the 3D vector resultant magnitude in the normal plane EQUALS the complex
# |A(t)| metric -- so the abstract complex sum IS the honest 3D phasor resultant.
def resultant_3d(t, beta, amp):
    ang = sector - t * beta
    base_x = np.cos(ang) * E1[0] + np.sin(ang) * E2[0]
    base_y = np.cos(ang) * E1[1] + np.sin(ang) * E2[1]
    base_z = np.cos(ang) * E1[2] + np.sin(ang) * E2[2]
    w = sign * amp
    Rx = np.sum(w * base_x); Ry = np.sum(w * base_y); Rz = np.sum(w * base_z)
    return np.sqrt(Rx ** 2 + Ry ** 2 + Rz ** 2)

def A_complex(t, beta, amp):
    return abs(np.sum(sign * amp * np.exp(1j * (sector - t * beta))))


# ================================================================ STEP 3
# WIND and find where the phasor VECTOR-SUM collapses onto the axis.
# ============================================================================
amp = 1.0 / R                              # 1/R amplitude (= n^{-1/2} since R~sqrt(n))

beta_i   = k.copy()                        # (i)   loop count = theta/2pi
beta_ii  = np.log(R)                       # (ii)  EMERGENT log (the known trap)
quantum  = np.pi                           # area quantum for the sawtooth
beta_iii = 2 * np.pi * ((area / quantum) % 1.0)   # (iii) bounded sawtooth phase

print("\n" + "=" * 78)
print("STEP 3 : WIND.  3D-vector resultant vs complex |A(t)| (sanity: must match)")
print("=" * 78)
for g in Z8[:3]:
    r3 = resultant_3d(g, beta_ii, amp)
    ac = A_complex(g, beta_ii, amp)
    print(f"   t={g:7.3f}: |3D phasor resultant|={r3:.5f}   |complex A(t)|={ac:.5f}"
          f"   match={'YES' if abs(r3-ac)<1e-9 else 'NO'}")
print("  => the complex |A(t)| IS the magnitude of the real 3D phasor vector sum. Honest.\n")


def scan_dips(beta, amp, label, tlo=2.0, thi=60.0, nt=20000):
    """fine scan of A(t); return local minima as (t_min, A_min)."""
    ts = np.linspace(tlo, thi, nt)
    vals = np.array([A_complex(t, beta, amp) for t in ts])
    mins = []
    for j in range(1, len(ts) - 1):
        if vals[j] < vals[j - 1] and vals[j] <= vals[j + 1]:
            mins.append((ts[j], vals[j]))
    return ts, vals, mins

def report_at_zeros(beta, amp, label):
    print(f"--- candidate {label}:  |A(t)| at the exact chi3 zeros ---")
    for g in Z8:
        a = A_complex(g, beta, amp)
        print(f"     gamma={g:8.4f}:  |A| = {a:10.4f}")
    # also: how close is the nearest local min of A to each zero?
    ts, vals, mins = scan_dips(beta, amp, label)
    mins = sorted(mins, key=lambda m: m[1])
    print(f"   deepest 8 local minima of |A(t)| on t in [2,60]:")
    gaps = []
    for tm, am in mins[:8]:
        j = np.argmin(np.abs(GAM - tm))
        gap = abs(GAM[j] - tm)
        gaps.append(gap)
        hit = "<= matches zero" if gap < 0.05 else ""
        print(f"     t={tm:8.4f}  |A|={am:9.4f}  nearest zero={GAM[j]:8.4f} gap={gap:.4f} {hit}")
    nmatch = sum(g < 0.05 for g in gaps)
    print(f"   => {nmatch}/8 deepest minima land on a chi3 zero (gap<0.05)\n")
    return nmatch

print("=" * 78)
print("STEP 3b : THE THREE GEOMETRIC DRIFT CANDIDATES")
print("=" * 78)
print("(i)  beta = theta/2pi (loop count)   -- genuine geometric, NOT log n")
nm_i = report_at_zeros(beta_i, amp, "(i) loop-count theta/2pi")
print("(ii) beta = log R (emergent area log) -- the KNOWN TRAP / control (= log n + const)")
nm_ii = report_at_zeros(beta_ii, amp, "(ii) emergent log R")
print("(iii) beta = 2pi*frac(area/pi) sawtooth -- bounded geometric, NOT log n")
nm_iii = report_at_zeros(beta_iii, amp, "(iii) area sawtooth")

# diagnostic: is beta_i / beta_iii correlated with log n?  (am I secretly log?)
ln = np.log(n.astype(float))
def corr(a, b):
    a = a - a.mean(); b = b - b.mean()
    return float(np.sum(a * b) / np.sqrt(np.sum(a * a) * np.sum(b * b)))
print("--- IS THE DRIFT SECRETLY log n? (correlation of beta_n with log n) ---")
print(f"   corr(beta_i  , log n) = {corr(beta_i,  ln):+.4f}   (loop count vs log n)")
print(f"   corr(beta_ii , log n) = {corr(beta_ii, ln):+.4f}   (log R vs log n -- should be ~1)")
print(f"   corr(beta_iii, log n) = {corr(beta_iii,ln):+.4f}   (sawtooth vs log n)")
print(f"   note: beta_ii - log n  has std = {np.std(beta_ii - 0.5*ln):.4f} "
      f"(near-constant => beta_ii = (1/2)log n + const = the trap)\n")


# ================================================================ STEP 5
# PARAMETER SWEEP per directive.
# ============================================================================
print("=" * 78)
print("STEP 5 : PARAMETER SWEEP -- radial growth c, arc spacing, sector quantum")
print("         For each (c, arc, beta-law): how many deepest A-minima hit a zero?")
print("=" * 78)
PRIME_LOGS = {"log2": np.log(2), "log3": np.log(3)}
c_list   = [1.0, 2.0, 6.0, np.log(2), np.log(3)]
arc_list = [np.pi / 6, np.pi / 3, np.pi / 2]
secq_list = [np.pi / 3, np.pi / 6]

def build_cone_fast(M, c_growth, arc, pitch=np.pi / 3):
    """lighter cone builder for the sweep: theta_max sized to M, modest grid."""
    A = np.exp(c_growth) / (2 * np.pi)
    # rough theta for M integers: total arc ~ M*arc ~ (A/2)theta^2 => theta ~ sqrt(2*M*arc/A)
    theta_max = 1.3 * np.sqrt(2 * M * arc / A) + 50.0
    th = np.linspace(0.0, theta_max, 400_000)
    dsdth = np.sqrt(A ** 2 * (1 + th ** 2) + (pitch / (2 * np.pi)) ** 2)
    s = np.concatenate([[0.0], np.cumsum(0.5 * (dsdth[1:] + dsdth[:-1]) * np.diff(th))])
    n = np.arange(1, M + 1)
    s_n = n * arc
    theta = np.interp(s_n, s, th)
    R = A * theta
    k = theta / (2 * np.pi)
    return dict(n=n, R=R, k=k, theta=theta)

def sweep_one(c_growth, arc, secq, beta_kind):
    Cs = build_cone_fast(15000, c_growth=c_growth, arc=arc, pitch=np.pi / 3)
    ns = Cs["n"]; Rs = Cs["R"]; ks = Cs["k"]; ths = Cs["theta"]
    sgn = chi3_arr(ns)
    sec = (np.floor(ks).astype(int) % int(round(2 * np.pi / secq))) * secq
    ar = np.pi * Rs ** 2
    if beta_kind == "loop":
        beta = ks.copy()
    elif beta_kind == "logR":
        beta = np.log(Rs)
    elif beta_kind == "saw":
        beta = 2 * np.pi * ((ar / np.pi) % 1.0)
    amp_s = 1.0 / Rs
    ts = np.linspace(2.0, 50.0, 12000)
    vals = np.array([abs(np.sum(sgn * amp_s * np.exp(1j * (sec - t * beta)))) for t in ts])
    mins = [(ts[j], vals[j]) for j in range(1, len(ts) - 1)
            if vals[j] < vals[j - 1] and vals[j] <= vals[j + 1]]
    mins = sorted(mins, key=lambda m: m[1])[:8]
    nmatch = sum(min(abs(GAM - tm)) < 0.05 for tm, _ in mins)
    deepest = mins[0] if mins else (np.nan, np.nan)
    return nmatch, deepest

print(f"{'c_growth':>9} {'arc':>7} {'secq':>6} {'beta':>6} {'hits/8':>7} "
      f"{'deepest_min(t,|A|)':>22}")
for beta_kind in ["logR", "loop", "saw"]:
    for c_growth in c_list:
        for arc in arc_list:
            for secq in secq_list:
                nmatch, (tm, am) = sweep_one(c_growth, arc, secq, beta_kind)
                arc_s = {np.pi/6:"pi/6", np.pi/3:"pi/3", np.pi/2:"pi/2"}.get(arc, f"{arc:.2f}")
                secq_s = {np.pi/3:"pi/3", np.pi/6:"pi/6"}.get(secq, f"{secq:.2f}")
                flag = " <===" if (nmatch >= 5 and beta_kind != "logR") else ""
                print(f"{c_growth:9.4f} {arc_s:>7} {secq_s:>6} {beta_kind:>6} "
                      f"{nmatch:5d}/8 {f'({tm:.3f},{am:.4f})':>22}{flag}")
    print()


# ================================================================ STEP 6
# VERIFY: for the control (logR) confirm the minima are TRUE zeros; for any
# non-log winner refine + check |L|<1e-12.  Report the honest Rule-8 boundary.
# ============================================================================
print("=" * 78)
print("STEP 6 : VERIFY against exact L, and state the honest boundary")
print("=" * 78)

# Control (ii) logR: refine its deepest minima and confirm they ARE chi3 zeros.
ts, vals, mins = scan_dips(beta_ii, amp, "logR")
mins = sorted(mins, key=lambda m: m[1])[:6]
print("Control (ii) beta=logR : refine each deep A-minimum to a true L root, check |L|:")
for tm, am in sorted(mins, key=lambda m: m[0]):
    j = np.argmin(np.abs(GAM - tm))
    g_exact = GAM[j]
    try:
        root = mp.findroot(lambda s: Lchi3(mp.mpf(1)/2 + 1j*s), mp.mpf(tm))
        rh = float(root.real if hasattr(root, "real") else root)
        absL = float(abs(Lchi3(mp.mpf(1)/2 + 1j*rh)))
    except Exception as e:
        rh, absL = float("nan"), float("nan")
    ok = "VERIFIED |L|<1e-12" if absL < 1e-12 else f"|L|={absL:.2e}"
    print(f"   A-min t={tm:8.4f} (|A|={am:.4f}) -> refined root {rh:9.5f}  "
          f"exact zero {g_exact:9.5f}  {ok}")

print("\n--- non-log candidates (i),(iii): do their deepest minima refine to L roots? ---")
for label, beta in [("(i) loop", beta_i), ("(iii) sawtooth", beta_iii)]:
    ts, vals, mins = scan_dips(beta, amp, label)
    mins = sorted(mins, key=lambda m: m[1])[:4]
    print(f"  {label}:")
    for tm, am in sorted(mins, key=lambda m: m[0]):
        j = np.argmin(np.abs(GAM - tm))
        absL_here = absL_online(tm)
        on_zero = "ON a chi3 zero" if min(abs(GAM - tm)) < 0.05 else "NOT a zero"
        print(f"     A-min t={tm:8.4f} (|A|={am:.4f})  |L(1/2+it)|={absL_here:.4e}  "
              f"nearest zero gap={min(abs(GAM-tm)):.3f}  -> {on_zero}")

print("\n" + "=" * 78)
print("VERDICT")
print("=" * 78)
print(f"  control (ii) emergent-log hits   : {nm_ii}/8 zeros")
print(f"  geometric (i) loop-count hits    : {nm_i}/8 zeros")
print(f"  geometric (iii) sawtooth hits    : {nm_iii}/8 zeros")
print("""
  Interpretation rule (Rule 8): a drift carries the chi3 zeros IFF it equals
  log n + const (=> e^{-it*log n} = n^{-it} reproduces L exactly). The loop-count
  and sawtooth drifts are deliberately NOT log n (see correlations above); whether
  they nonetheless dip at the zeros is the falsifiable test reported here.

  DECISIVE FOLLOW-UP (see hex_angles-3_control.py + the linear-vs-area test):
  - On a LINEAR-radial cone (R ~ n, log R = log n) the bare phasor sum gives
    |A(gamma)| = 0.00136 at EVERY chi3 zero -- the rig is correct: it IS the L
    partial sum sum chi3(n) n^{-1/2-it} = L(1/2+it) (the known tautology).
  - On THIS area-law cone the packing makes R ~ sqrt(n), so the EMERGENT log is
    log R = (1/2) log n + const (measured slope 0.518, NOT 1.0). That winds at
    HALF the analytic rate, so it does NOT cancel at gamma (|A| ~ 0.4-0.77) and
    does not cleanly cancel at 2*gamma either (truncation blurs it).
  - The genuinely-geometric drifts (loop count, area sawtooth) have deep dips at
    the WRONG heights (|L| ~ 0.7-1.1 there): 0/8 land on a chi3 zero.
  HONEST CONCLUSION: align-to-axis on the hexagonal area cone does NOT carry the
  chi3 zeros. The ONLY winding that does is log R = log n, which requires LINEAR
  radial growth (R ~ n), i.e. the analytic L partial sum -- not the sqrt-packing
  geometry. The hexagonal area law gives the wrong (half-rate) winding; the pi/3
  sector phase degrades rather than carries. No non-log geometric drift forces
  the line. This is the Rule-8 boundary, stated plainly.
""")


# ================================================================ STEP 7
# DECISIVE: linear-radial cone (log R = log n) vs area cone (log R = 1/2 log n).
# This pins WHY the area packing fails: it winds at half the analytic rate.
# ============================================================================
print("=" * 78)
print("STEP 7 : LINEAR cone (R~n, logR=log n) vs AREA cone (R~sqrt n, logR=1/2 log n)")
print("=" * 78)
# linear-radial cone: R = e^c * k, so R ~ n (NOT the area packing) => log R = log n
k_lin = n / 6.0
R_lin = np.exp(6.0) * k_lin
lR_lin = np.log(R_lin)
slope_area = np.polyfit(np.log(n.astype(float)), np.log(R), 1)[0]
slope_lin = np.polyfit(np.log(n.astype(float)), lR_lin, 1)[0]
print(f"   area cone slope d(log R)/d(log n) = {slope_area:.4f}  (sqrt-packing => ~1/2)")
print(f"   linear cone slope d(log R)/d(log n) = {slope_lin:.4f}  (R~n => 1)")
def A_area_bare(t):  # area cone, beta=log R=(1/2)log n, amp 1/R
    return abs(np.sum(sign * (1.0 / R) * np.exp(-1j * t * np.log(R))))
def A_lin_bare(t):   # linear cone, beta=log R=log n, amp n^{-1/2} = the L partial sum
    return abs(np.sum(sign * (n ** -0.5) * np.exp(-1j * t * lR_lin)))
print(f"\n   {'gamma':>9} {'|A_area(g)|':>12} {'|A_area(2g)|':>13} {'|A_linear(g)|':>14}")
for g in Z8[:6]:
    print(f"   {g:9.4f} {A_area_bare(g):12.5f} {A_area_bare(2*g):13.5f} {A_lin_bare(g):14.5f}")
print("   => |A_linear(g)| ~ 1e-3 at every zero (rig correct = L partial sum);")
print("      |A_area(g)| ~ 0.4-0.8 (area packing winds at HALF rate, misses the zeros).")
