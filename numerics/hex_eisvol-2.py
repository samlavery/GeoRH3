"""
hex_eisvol-2.py  --  ID eisvol-2: ALIGN-TO-AXIS COLLAPSE on a real 3D integer helix
with chi3 (Eisenstein split/inert/ramify) phasors dragged by the EARNED radial log.

Directive compliance:
  STEP 1  build the real 3D solid (explicit x,y,z), PRINT a coordinate sample.
  STEP 2  attach a phasor (a real rotating 3D unit vector) at each lattice point;
          define exactly how it spins with the winding parameter y.
  STEP 3  wind; find where the chi3-weighted phasor VECTOR-SUM (resultant) collapses.

Then -- and this is the load-bearing part per Rules 2/4 and the directive's
"flag if it is secretly the analytic L" -- a battery of BRUTAL HONESTY tests to
decide whether this collapse is genuinely new hexagonal/6th-root structure, or
whether it is just |L(chi3, 1/2+iy)| wearing a 3D costume.

Run:  python3 hex_eisvol-2.py
"""
import numpy as np
import mpmath as mp

mp.mp.dps = 30

# ----------------------------------------------------------------------------
# exact chi3 L and its zeros (ground truth)
# ----------------------------------------------------------------------------
def Lchi3(s):
    s = mp.mpf(s) if not isinstance(s, mp.mpc) else s
    return mp.mpf(3)**(-s) * (mp.zeta(s, mp.mpf(1)/3) - mp.zeta(s, mp.mpf(2)/3))

def absL_online(y):
    return abs(Lchi3(mp.mpf(1)/2 + 1j*mp.mpf(y)))

gammas = []
with open("/Users/samuellavery/proof/three/numerics/lchi3_zeros_1000.txt") as f:
    for line in f:
        line = line.strip()
        if line and not line.startswith("#"):
            gammas.append(float(line.split()[1]))
gammas.sort()
Z = gammas[:8]
print("chi3 zeros (first 8):", [round(g, 4) for g in Z])
print("verify exact |L(chi3,1/2+i gamma)| at the zeros:")
for g in Z[:5]:
    print(f"   gamma={g:9.4f}  |L|={float(absL_online(g)):.2e}")

def chi3(n):
    r = n % 3
    return 1 if r == 1 else (-1 if r == 2 else 0)

# ============================================================================
# STEP 1 -- BUILD THE REAL 3D OBJECT (explicit coordinates)
# ============================================================================
# Integer helix: place integer n on an Archimedean spiral R(theta)=A*theta,
# arc-spacing pi/3 between consecutive integers => 6 integers per loop (the six
# 6th-root / Eisenstein-unit directions), pitch pi/3 per loop in z.
#   A = e^6 / (2 pi)   (so radius grows e^6 per loop -- the "eisvol" scale)
# theta_n solves arc-length s(theta_n) = n*pi/3 on R=A*theta.
print("\n" + "=" * 76)
print("STEP 1: build the real 3D integer helix (Archimedean R=A*theta, spacing pi/3).")
print("=" * 76)
N = 200000
Asc = np.exp(6.0) / (2 * np.pi)
n = np.arange(1, N + 1)

# arc-length inversion on a fine grid (ds = sqrt((dR)^2 + (R dtheta)^2 + (dz)^2))
th_grid = np.linspace(0, 6000, 2_000_000)
dz_dth = 1.0 / 6.0  # z = theta/6  (pitch pi/3 per 2pi loop -> dz/dtheta = (pi/3)/(2pi)=1/6)
ds = np.sqrt(Asc**2 * (1 + th_grid**2) + dz_dth**2)
sarc = np.concatenate([[0.0], np.cumsum(0.5 * (ds[1:] + ds[:-1]) * np.diff(th_grid))])
theta = np.interp(n * (np.pi / 3), sarc, th_grid)

R = Asc * theta
zc = theta / 6.0
x = R * np.cos(theta)
yy = R * np.sin(theta)

print(f"  A = e^6/(2pi) = {Asc:.6f};  spacing pi/3 = {np.pi/3:.4f}; 6 integers per loop.")
print(f"  {'n':>6}{'theta':>10}{'R':>11}{'z':>9}     (x, y, z)")
for nn in [1, 2, 3, 6, 12, 36, 100, 1000, 10000]:
    i = nn - 1
    print(f"  {nn:6d}{theta[i]:10.4f}{R[i]:11.3f}{zc[i]:9.4f}"
          f"     ({x[i]:10.2f}, {yy[i]:10.2f}, {zc[i]:7.4f})")

# integers per loop should be 6 (hexagonal!) -- count integers with theta in [2pi k, 2pi(k+1))
loops = (theta / (2 * np.pi)).astype(int)
print("  integers per loop (should be 6 = six Eisenstein unit directions):",
      [int(np.sum(loops == k)) for k in range(1, 8)])

# ============================================================================
# STEP 2 -- ATTACH A PHASOR at each point + define its spin
# ============================================================================
# The phasor at integer n is a real unit vector lying in the lab xy-plane,
# pointing at lab angle  alpha_n(y) = theta_n - y * Phi_n,  where the DRAG
#   Phi_n = log R_n  is EARNED from the linear radial growth (Phi_n = log n + const,
# const = 6 - log 6, verified below) -- NOT placed at log positions.
# chi3 weights the phasor by the Eisenstein splitting sign; amplitude = 1/R_n
# (geometric: inverse radius, the inward pull falls off with distance from axis).
Phi = np.log(R)
sign = np.where(n % 3 == 1, 1.0, np.where(n % 3 == 2, -1.0, 0.0))
amp_geo = 1.0 / R            # geometric amplitude (inverse radius)
const_check = Phi - np.log(n)
print("\n" + "=" * 76)
print("STEP 2: attach chi3 phasors; drag Phi_n = log R_n (EARNED from radial growth).")
print("=" * 76)
print(f"  Phi_n - log n at n=10,1e2,1e3,1e4,1e5 = "
      f"{const_check[9]:.4f},{const_check[99]:.4f},{const_check[999]:.4f},"
      f"{const_check[9999]:.4f},{const_check[99999]:.4f}  (const 6-log6={6-np.log(6):.4f})")
print(f"  amplitude = 1/R_n  (geometric inward falloff). NOTE: 1/R != n^(-1/2); R~n linear here.")
print(f"  sample phasor unit vectors at y=8.0397 (lab xy components cos,sin of theta-y*Phi):")
for nn in [1, 2, 4, 5, 7]:
    i = nn - 1
    a = theta[i] - Z[0] * Phi[i]
    print(f"    n={nn} chi3={chi3(nn):+d}  dir=({np.cos(a):+.3f},{np.sin(a):+.3f},0)  amp={amp_geo[i]:.4f}")

# ============================================================================
# STEP 3 -- WIND and measure the chi3-weighted phasor VECTOR-SUM (resultant)
# ============================================================================
def resultant(yv, Nc, amp):
    cut = np.exp(-(n / Nc) ** 2)            # smooth cutoff: truncation can't fake it
    ang = theta - yv * Phi
    vx = np.sum(sign * amp * cut * np.cos(ang))
    vy = np.sum(sign * amp * cut * np.sin(ang))
    return np.hypot(vx, vy)

print("\n" + "=" * 76)
print("STEP 3: wind; resultant phasor-vector magnitude at chi3 zeros vs off-zero controls.")
print("=" * 76)
Nc = 60000.0
print(f"  (geometric amp=1/R, smooth cutoff Nc={Nc:.0f})")
print(f"  {'y':>9}{'|resultant|':>14}   tag")
for g in Z[:5]:
    print(f"  {g:9.4f}{resultant(g, Nc, amp_geo):14.5f}   chi3 zero")
for g0 in [6.0, 10.0, 13.0, 22.0]:
    print(f"  {g0:9.4f}{resultant(g0, Nc, amp_geo):14.5f}   off-zero control")

# ============================================================================
# BRUTAL HONESTY BATTERY  -- is this secretly |L(chi3, 1/2+iy)| ?
# ============================================================================
print("\n" + "#" * 76)
print("# HONESTY BATTERY: is the collapse genuinely geometric, or a costume for L?")
print("#" * 76)

# --- H1: direct algebra. With amp = n^{-1/2} EXACTLY, R_n=A*theta_n, Phi_n=log R_n,
#         the resultant magnitude is |sum sign_n n^{-1/2} e^{i(theta_n - y log R_n)}|.
#         theta_n is a fixed per-n rotation; e^{-iy*const} is a global phase.
#         If we DROP theta_n (set the per-point geometric offset to 0) and use n^{-1/2},
#         the magnitude becomes EXACTLY |sum chi3(n) n^{-1/2} e^{-iy log n}| = |partial L|.
amp_L = n ** (-0.5)

def resultant_noTheta(yv, Nc, amp):
    cut = np.exp(-(n / Nc) ** 2)
    ang = - yv * np.log(n)                  # drop theta_n; pure log n drag; amp chosen
    vx = np.sum(sign * amp * cut * np.cos(ang))
    vy = np.sum(sign * amp * cut * np.sin(ang))
    return np.hypot(vx, vy)

print("\nH1: drop the geometric theta_n offset, use amp=n^{-1/2}: this is the RAW Dirichlet")
print("    partial sum |sum chi3(n) n^{-1/2} e^{-iy log n}| (smoothed). Compare to exact |L|.")
print(f"  {'y':>9}{'|raw partial L|':>17}{'exact |L|':>14}   tag")
for g in list(Z[:4]) + [6.0, 10.0, 13.0]:
    rp = resultant_noTheta(g, 200000.0, amp_L)
    print(f"  {g:9.4f}{rp:17.6f}{float(absL_online(g)):14.6f}   "
          f"{'ZERO' if g in Z else 'ctrl'}")
print("  => if raw-partial-L tracks exact |L| (small at zeros, O(1) off), the *Dirichlet*")
print("     content alone already cancels at the zeros: theta_n adds nothing essential.")

# --- H2: does the geometric theta_n offset matter? Compare collapse WITH vs WITHOUT
#         theta_n, both at amp=n^{-1/2}, to isolate any genuine geometric contribution.
def resultant_withTheta(yv, Nc, amp):
    cut = np.exp(-(n / Nc) ** 2)
    ang = theta - yv * Phi
    vx = np.sum(sign * amp * cut * np.cos(ang))
    vy = np.sum(sign * amp * cut * np.sin(ang))
    return np.hypot(vx, vy)

print("\nH2: WITH theta_n vs WITHOUT (both amp=n^{-1/2}, same drag log R). Does the 3D")
print("    geometric rotation theta_n change WHERE it collapses, or only rescale?")
print(f"  {'y':>9}{'with theta':>13}{'no theta':>12}{'exact|L|':>12}   tag")
for g in list(Z[:4]) + [6.0, 10.0, 13.0]:
    w_ = resultant_withTheta(g, 200000.0, amp_L)
    wo = resultant_noTheta(g, 200000.0, amp_L)
    print(f"  {g:9.4f}{w_:13.6f}{wo:12.6f}{float(absL_online(g)):12.6f}   "
          f"{'ZERO' if g in Z else 'ctrl'}")

# --- H3: does the amplitude choice (1/R geometric vs n^{-1/2} analytic) move the zeros?
#         If both collapse at the SAME y (the chi3 zeros), the cancellation is governed by
#         the PHASE (the log-n drag = Dirichlet phase), not the geometry. That is the
#         diagnosis: it's the analytic L's phase, dressed in different amplitudes.
print("\nH3: amplitude 1/R (geometric) vs n^{-1/2} (analytic), WITH theta_n. Same zeros?")
print(f"  {'y':>9}{'amp=1/R':>12}{'amp=n^-1/2':>13}   tag")
for g in list(Z[:5]) + [6.0, 10.0, 13.0]:
    a1 = resultant_withTheta(g, 60000.0, amp_geo)
    a2 = resultant_withTheta(g, 60000.0, amp_L)
    print(f"  {g:9.4f}{a1:12.5f}{a2:13.6f}   {'ZERO' if g in Z else 'ctrl'}")

# --- H4: the dispositive test. SCAN y across a window and CORRELATE the geometric
#         collapse curve with exact |L(chi3,1/2+iy)|. High correlation + collapse minima
#         AT the L-zeros => the curve IS (a smoothed reparam of) |L|. Also locate the
#         actual minima of the geometric curve and check they sit on the chi3 zeros.
print("\nH4: scan y in [5,30]; correlate geometric collapse vs exact |L|; do minima = zeros?")
ys = np.linspace(5.0, 30.0, 501)
geo = np.array([resultant_withTheta(yv, 60000.0, amp_geo) for yv in ys])
exL = np.array([float(absL_online(yv)) for yv in ys])
# normalize both to unit mean for shape comparison
gn = geo / geo.mean(); en = exL / exL.mean()
corr = np.corrcoef(gn, en)[0, 1]
print(f"  Pearson correlation (geometric collapse shape vs exact |L| shape) = {corr:.4f}")
# find local minima of the geometric curve
mins = [ys[i] for i in range(1, len(ys) - 1) if geo[i] < geo[i-1] and geo[i] < geo[i+1]]
zeros_in_window = [g for g in gammas if 5.0 <= g <= 30.0]
print(f"  geometric-curve local minima in [5,30]: {[round(m,3) for m in mins]}")
print(f"  exact chi3 zeros        in [5,30]: {[round(g,3) for g in zeros_in_window]}")
matched = []
for g in zeros_in_window:
    if mins:
        nearest = min(mins, key=lambda m: abs(m - g))
        matched.append((round(g, 3), round(nearest, 3), round(abs(nearest - g), 3)))
print(f"  (zero, nearest geo-min, |diff|): {matched}")

# --- H5: hexagonal leverage check. The spacing pi/3 = 6/loop is the only place the
#         hexagon enters the GEOMETRY. Does CHANGING the spacing (breaking the hexagon)
#         move the collapse off the zeros? If the zeros are unchanged by spacing, the
#         "6th-root leverage" is decorative and the cancellation is purely the chi3 phase.
print("\nH5: hexagonal leverage probe -- change arc-spacing (break 6/loop), recheck zeros.")
def resultant_spacing(yv, spacing_factor, amp):
    # rebuild theta with a different arc-spacing; everything else identical
    theta2 = np.interp(n * (np.pi / 3) * spacing_factor, sarc, th_grid)
    R2 = Asc * theta2
    Phi2 = np.log(R2)
    cut = np.exp(-(n / 60000.0) ** 2)
    ang = theta2 - yv * Phi2
    vx = np.sum(sign * amp * cut * np.cos(ang))
    vy = np.sum(sign * amp * cut * np.sin(ang))
    return np.hypot(vx, vy)

print(f"  {'y':>9}{'pi/3 (hex)':>12}{'pi/2.5':>11}{'pi/4':>10}   tag")
for g in list(Z[:4]) + [10.0]:
    h0 = resultant_spacing(g, 1.0, amp_geo)
    h1 = resultant_spacing(g, (np.pi/2.5)/(np.pi/3), amp_geo)
    h2 = resultant_spacing(g, (np.pi/4)/(np.pi/3), amp_geo)
    print(f"  {g:9.4f}{h0:12.5f}{h1:11.5f}{h2:10.5f}   {'ZERO' if g in Z else 'ctrl'}")
print("  => if it still collapses at the SAME chi3 zeros after breaking 6/loop, the hexagon")
print("     spacing is NOT what sets the zeros; the chi3 SIGN (Eisenstein splitting) + log-n")
print("     phase are. That would localize the real leverage to chi3(n)=Eisenstein splitting,")
print("     not to the pi/3 geometry.")

print("\nDONE hex_eisvol-2.")
