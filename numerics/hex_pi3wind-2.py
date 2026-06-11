"""
hex_pi3wind-2.py  --  ID pi3wind-2
ALIGN-TO-AXIS COLLAPSE on the hexagonal integer helix.

CLAIM under test: the chi3 zero gamma is the winding height where the chi3-weighted
phasor resultant on the hexagonal helix has NO net radial (inward/outward) component
-- the phasors balance with their resultant lying ALONG the axis, not pointing in/out.
Both the inward-radial AND tangential normalized components of the resultant vanish at
gamma = chi3 zero, while at non-zero control heights they are O(1).

We BUILD the real 3D object first (explicit (x,y,z) per integer), ATTACH a real 3D
phasor vector at each point, WIND it, and measure the VECTOR resultant -- never a bare
scalar sum.

Leverage of the 6th root: azimuth step = pi/3 = the Eisenstein unit angle (6 units per
loop = the six 6th-roots), radius R(n)=sqrt(n) from the hexagonal area law n ~ R^2,
pitch pi/3 per loop = the axial dimension the 2D iy-projection loses.

VERDICT (after running, see bottom): FALSIFIED.  The per-n hexagonal twist theta_n=n*pi/3
DESTROYS the cancellation.  The twisted |C| at the exact zeros (mean ~0.003 at N=80000) is
statistically indistinguishable from |C| at control / random heights (~0.003), and BOTH
shrink ~1/sqrt(N) with N (a truncation residue of a NON-cancelling sum), at zeros and
controls alike.  Only the PLAIN fibre sum |sum chi3(n) n^{-1/2} e^{-i gamma log n}| actually
vanishes at zeros -- and that is exactly the tautological L(1/2+i gamma), which the brief
forbade re-deriving.  Align-to-axis adds NO new zero-detecting geometry.

HONESTY NOTE we will keep checking: the height still enters as gamma*log n.  Align-to-axis
reframes WHERE the cancellation lives (radial vs tangential geometry); it does NOT remove
the log.  We must verify whether the radial/tangential split is GENUINELY new geometric
information, or whether |C_rad| and |C_tan| are just the real/imag parts of the same
analytic fibre sum sum_n chi3(n) n^{-1/2} e^{-i gamma log n} = L(1/2+i gamma) up to a
per-n phase twist (n*pi/3+pi).  That distinction is the whole scientific question.
"""
import numpy as np, mpmath as mp

mp.mp.dps = 30
def chi3(n): return [0, 1, -1][n % 3]
def Lchi3(s): return 3**(-s) * (mp.zeta(s, mp.mpf(1)/3) - mp.zeta(s, mp.mpf(2)/3))

# exact zeros (col 2 of the landmark file)
ZEROS = [8.0397371556814666817, 11.2492062077729352497, 15.7046191767216255651,
         18.2619974956931275689, 20.4557708077424928534, 24.0594148564934507745,
         26.5778687357745853145, 28.2181645062333860931, 30.7450402613824957378,
         33.8973889272594190176]

# ---------------------------------------------------------------------------
# STEP 1 -- BUILD THE REAL 3D OBJECT.  Explicit (x,y,z) per integer n.
#   x = sqrt(n) cos(n*pi/3),  y = sqrt(n) sin(n*pi/3),  z = (pi/3)*(n/6)
#   radius   R(n) = sqrt(n)              (hexagonal area law n ~ R^2)
#   azimuth  theta(n) = n*pi/3           (6 integers per loop = 6th-root sectors)
#   pitch    z grows pi/3 per loop       (axial dim lost by the 2D projection)
# ---------------------------------------------------------------------------
def build_helix(N):
    n = np.arange(1, N + 1, dtype=np.float64)
    theta = n * (np.pi / 3.0)
    R = np.sqrt(n)
    x = R * np.cos(theta)
    y = R * np.sin(theta)
    z = (np.pi / 3.0) * (n / 6.0)
    return n, x, y, z, theta, R

N = 80000
n, x, y, z, theta, R = build_helix(N)

print("=" * 78)
print("STEP 1 -- the 3D hexagonal integer helix (explicit coordinates).")
print("  R(n)=sqrt(n)  azimuth n*pi/3 (6 ints/loop)  pitch pi/3 per loop")
print(f"  built N={N} points.  sample (n : x, y, z : chi3):")
for i in [1, 2, 3, 4, 5, 6, 7, 12, 100, 1000]:
    j = i - 1
    print(f"    n={i:5d}: ({x[j]:+9.4f}, {y[j]:+9.4f}, {z[j]:+9.4f})   chi3={chi3(i):+d}")
# show that 6 consecutive integers = the 6 azimuthal sectors (6th-root directions)
print("  azimuths of n=1..6 (mod 2pi), in units of pi/3 -- the six 6th-root sectors:")
print("   ", [round((theta[i] % (2*np.pi)) / (np.pi/3)) for i in range(6)])

# ---------------------------------------------------------------------------
# STEP 2 -- ATTACH A PHASOR at each 3D point.  A real unit 3-vector living in the
# LOCAL plane spanned by the inward-radial direction r_hat and the tangential
# direction t_hat (the two in-plane lab directions at that point).  As we wind by
# height gamma, the phasor SPINS by angle phi(n) = -gamma*log n (the bridge readout).
#
#   inward-radial unit dir:  r_in = (cos(theta+pi), sin(theta+pi), 0) = -(cos th, sin th,0)
#   tangential   unit dir:   t_hat = (-sin theta, cos theta, 0)
#   phasor vector at n:      P(n) = cos(phi) * r_in + sin(phi) * t_hat   (a real 3-vector)
#   weight:                  w(n) = chi3(n) * n^{-1/2}
#
# The chi3-weighted phasor RESULTANT is the vector  V = sum_n w(n) P(n)  (a real 3-vector).
# We decompose V into:
#   radial component  C_rad = (sum_n w(n) P(n)) . (mean inward dir)  -- but inward dir
#       varies per point, so the physically meaningful scalar is the per-point inward
#       projection averaged: C_rad = sum_n w(n) [P(n).r_in(n)] = sum_n w(n) cos(phi(n)),
#   tangential        C_tan = sum_n w(n) [P(n).t_hat(n)] = sum_n w(n) sin(phi(n)),
#   ... BUT that collapses the geometry.  The HYPOTHESIS (per the FORMULA block) puts the
#   per-point hexagonal twist (n*pi/3+pi) INTO the phase:
#       phi_geo(n) = -gamma*log n - (theta(n) + pi)
#   and reads C_rad = sum w(n) cos(phi_geo), C_tan = sum w(n) sin(phi_geo).
# We implement EXACTLY the FORMULA-block definition (with the hexagonal twist), and also
# the lab-frame resultant vector, so we can see whether the twist matters.
# ---------------------------------------------------------------------------
w = np.array([chi3(int(k)) for k in n], dtype=np.float64) * n ** (-0.5)
norm = np.sum(n ** (-0.5))          # normalizer (sum_n n^{-1/2}), all-positive

def components_formula(gamma):
    """EXACT FORMULA-block definition: phase = -gamma*log n - (n*pi/3 + pi)."""
    phi = -gamma * np.log(n) - (theta + np.pi)
    C_rad = np.sum(w * np.cos(phi)) / norm
    C_tan = np.sum(w * np.sin(phi)) / norm
    return C_rad, C_tan

def resultant_vector(gamma):
    """The actual 3D phasor VECTOR resultant V = sum_n w(n) P(n), P in the local r_in/t_hat plane,
    spun by phi_bridge = -gamma*log n.  Returns (Vx,Vy,Vz) and its decomposition."""
    phi = -gamma * np.log(n)                       # bridge spin only
    # local inward-radial and tangential unit vectors (z-component 0; this is a planar phasor)
    r_in_x, r_in_y = -np.cos(theta), -np.sin(theta)
    t_x, t_y = -np.sin(theta), np.cos(theta)
    Px = np.cos(phi) * r_in_x + np.sin(phi) * t_x
    Py = np.cos(phi) * r_in_y + np.sin(phi) * t_y
    Vx = np.sum(w * Px) / norm
    Vy = np.sum(w * Py) / norm
    Vz = 0.0
    mag = np.hypot(Vx, Vy)
    return Vx, Vy, Vz, mag

def fibre_scalar(gamma):
    """The bare analytic fibre sum |sum chi3(n) n^{-1/2} e^{-i gamma log n}| / norm (the standard collapse)."""
    s = np.sum(w * np.exp(-1j * gamma * np.log(n)))
    return abs(s) / norm

print()
print("STEP 2 -- phasor attached: P(n) = cos(phi) r_in(n) + sin(phi) t_hat(n), a real 3-vector.")
print("  sample phasor vectors at gamma=8.0397 (the first zero), spin phi=-gamma*log n:")
gtest = ZEROS[0]
phi0 = -gtest * np.log(n)
for i in [1, 2, 3, 6, 100]:
    j = i - 1
    r_in = np.array([-np.cos(theta[j]), -np.sin(theta[j]), 0.0])
    t_h = np.array([-np.sin(theta[j]), np.cos(theta[j]), 0.0])
    P = np.cos(phi0[j]) * r_in + np.sin(phi0[j]) * t_h
    print(f"    n={i:4d}: P=({P[0]:+.4f},{P[1]:+.4f},{P[2]:+.4f})  |P|={np.linalg.norm(P):.4f}  w={w[j]:+.4f}")

# ---------------------------------------------------------------------------
# STEP 3 -- WIND and look for the vector collapse.
# ---------------------------------------------------------------------------
print()
print("=" * 78)
print("STEP 3 -- wind & measure the chi3-weighted phasor VECTOR resultant.")
print()
print("Per the FORMULA block: C_rad = sum w cos(-g log n -(n pi/3+pi)),  C_tan = sum w sin(...).")
print(f"{'gamma':>14} {'type':>9} | {'C_rad':>11} {'C_tan':>11} {'|C|':>10} | {'|V|lab':>9} | {'fibre|sum|':>10} | {'|L|*|zeta|':>11}")
print("-" * 110)

def report(gamma, label):
    cr, ct = components_formula(gamma)
    Vx, Vy, Vz, mag = resultant_vector(gamma)
    fib = fibre_scalar(gamma)
    s = mp.mpf(1)/2 + 1j*mp.mpf(str(gamma))
    Lz = abs(Lchi3(s)) * abs(mp.zeta(s))
    print(f"{gamma:>14.6f} {label:>9} | {cr:>+11.6f} {ct:>+11.6f} {np.hypot(cr,ct):>10.6f} | {mag:>9.6f} | {fib:>10.6f} | {float(Lz):>11.6f}")
    return cr, ct, mag, fib

# the exact zeros
zero_results = []
for g in ZEROS:
    zero_results.append(report(g, "ZERO"))

print("-" * 110)
# control midpoints (halfway between consecutive zeros) -- should be O(1)
controls = [(ZEROS[i] + ZEROS[i+1]) / 2 for i in range(len(ZEROS) - 1)]
ctrl_results = []
for g in controls:
    ctrl_results.append(report(g, "control"))

print("-" * 110)
# random non-zero heights as an extra honest control
rng = np.random.default_rng(0)
rand_heights = sorted(rng.uniform(6.0, 34.0, 6))
for g in rand_heights:
    report(g, "random")

# ---------------------------------------------------------------------------
# THE DECISIVE HONESTY TEST: is C_rad,C_tan genuinely new, or just Re/Im of the
# analytic fibre sum with a fixed per-n twist?  If |C| == fibre|sum| (up to the
# normalizer) for EVERY gamma, then align-to-axis is NOT new geometry -- it is the
# same analytic L, merely rotated coordinate-by-coordinate.  Test the identity
#   C_rad + i C_tan  ?=  e^{-i pi} * sum_n w(n) e^{-i gamma log n - i theta_n}
# i.e. |C| should equal | sum_n w(n) e^{-i(gamma log n + theta_n)} | / norm,
# which is a DIFFERENT scalar sum than the plain fibre sum (it has the extra theta_n).
# So the real question: does adding theta_n = n*pi/3 to each term still vanish at zeros?
# ---------------------------------------------------------------------------
print()
print("=" * 78)
print("HONESTY / DECISIVE TEST -- is align-to-axis NEW geometry, or the analytic L re-dressed?")
print()
print(" (A) |C| (twisted by theta_n=n*pi/3) vs plain fibre |sum| at each zero & control.")
print("     If |C| ~ 0 at zeros, the per-n hexagonal twist still cancels -> claim's 'radial'")
print("     vanishing holds.  If |C| ~ 0 == fibre|sum| ~ 0 BOTH, they may be the same content.")
print()
print(f"{'gamma':>12} {'type':>8} | {'|C|(twisted)':>13} | {'fibre|sum|(plain)':>18} | {'ratio |C|/fibre':>16}")
print("-" * 78)
for g, lab in [(z, "ZERO") for z in ZEROS] + [(c, "control") for c in controls]:
    cr, ct = components_formula(g)
    Cmag = np.hypot(cr, ct)
    fib = fibre_scalar(g)
    ratio = Cmag / fib if fib > 1e-15 else float('nan')
    print(f"{g:>12.5f} {lab:>8} | {Cmag:>13.6f} | {fib:>18.6f} | {ratio:>16.4f}")

# Direct algebraic check: C_rad + i*C_tan  ==  -e^{-i*0} * (1/norm) sum_n w e^{-i(g log n + theta_n)} ?
print()
print(" (B) algebraic identity check at gamma=8.0397:")
g = ZEROS[0]
cr, ct = components_formula(g)
C = cr + 1j*ct
# components_formula uses cos/sin of (-g log n - theta - pi); cos(a)=Re e^{i a}?
# C = sum w [cos(psi) + i sin(psi)]/norm with psi = -g log n - theta - pi = sum w e^{i psi}/norm
twisted = np.sum(w * np.exp(1j*(-g*np.log(n) - theta - np.pi))) / norm
print(f"     C_rad+iC_tan          = {C:.8f}")
print(f"     (1/norm) sum w e^(i psi) = {twisted:.8f}   (psi=-g log n - theta - pi)")
print(f"     => |C| is the magnitude of a TWISTED fibre sum (extra per-n phase theta_n=n*pi/3).")
print(f"     plain fibre |sum|/norm = {fibre_scalar(g):.8f}")

# ---------------------------------------------------------------------------
# ROBUSTNESS SWEEP -- vary radial law R(n) and azimuth step; does the collapse survive?
# (If the collapse is the fibre identity it survives any geometry; that is the honest read.)
# ---------------------------------------------------------------------------
print()
print("=" * 78)
print("ROBUSTNESS SWEEP -- C_rad,C_tan at the first 3 zeros under different geometry.")
print(" (radial law only changes theta via nothing; theta = azstep*n.  We vary azstep & whether")
print("  the per-n twist uses theta.  The fibre spin -g log n is unchanged -> collapse should persist.)")
def comps_general(gamma, azstep):
    th = n * azstep
    phi = -gamma * np.log(n) - (th + np.pi)
    cr = np.sum(w * np.cos(phi)) / norm
    ct = np.sum(w * np.sin(phi)) / norm
    return cr, ct
for azstep, name in [(np.pi/6, "pi/6"), (np.pi/3, "pi/3"), (np.pi/2, "pi/2")]:
    print(f"  azimuth step = {name}:")
    for g in ZEROS[:3]:
        cr, ct = comps_general(g, azstep)
        print(f"      gamma={g:.5f}: C_rad={cr:+.6f} C_tan={ct:+.6f} |C|={np.hypot(cr,ct):.6f}")

# ---------------------------------------------------------------------------
# SUMMARY scoring -- automated pass/fail
# ---------------------------------------------------------------------------
print()
print("=" * 78)
print("SUMMARY")
zero_Cmags = [np.hypot(cr, ct) for cr, ct, mag, fib in zero_results]
ctrl_Cmags = [np.hypot(cr, ct) for cr, ct, mag, fib in ctrl_results]
print(f"  max |C| over {len(zero_results)} ZEROS    = {max(zero_Cmags):.6f}")
print(f"  min |C| over {len(ctrl_results)} controls = {min(ctrl_Cmags):.6f}")
print(f"  separation (min control / max zero) = {min(ctrl_Cmags)/max(zero_Cmags):.1f}x")
# verify the zeros really are zeros
print("  mpmath verification |L(1/2+i gamma)| at each claimed zero:")
for g in ZEROS[:4]:
    s = mp.mpf(1)/2 + 1j*mp.mpf(str(g))
    print(f"      gamma={g:.6f}: |L|={float(abs(Lchi3(s))):.3e}")
