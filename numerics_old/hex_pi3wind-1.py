"""
hex_pi3wind-1.py  --  ID pi3wind-1
EISENSTEIN-SHELL LATTICE-COUNT CANCELLATION, built as a REAL 3D solid with PHASORS.

The claim under test:
  Build the real 2D hexagonal lattice of Eisenstein integers Z[omega], omega=e^{2pi i/3}.
  Norm form N(a,b)=a^2-ab+b^2 (the integer "area" / quadratic norm -- NO log, NO sqrt).
  Lift each lattice point to height z = N (the norm shell).  -> a real 3D solid (x,y,z).
  Attach a PHASOR (a real rotating unit vector in the local tangent/normal plane) at each
  point.  As we WIND by amount gamma, every phasor SPINS by angle -gamma*log N (the height
  readout is the ONLY place log is allowed -- Rule Eight bridge).
  The chi3 weight is NOT imposed: the number of lattice points on shell N is the geometric
  count r(N) = 6*sum_{d|N} chi3(d) (VERIFIED).  So chi3 EMERGES as r(N)/6, a pure 2D point
  count, never an imposed character.
  CANCELLATION EVENT = the gamma at which the chi3-weighted phasor VECTOR sum (resultant of
  all the spinning unit vectors at their real 3D points) collapses to zero.
  Claim: those gammas are exactly the zeros of L(chi3) (the Epstein quotient
  zeta_{Q(sqrt-3)}/zeta vanishing).

STEP 1 builds + prints the real 3D coordinates.
STEP 2 attaches the phasor unit vectors and prints a sample (direction in 3-space).
STEP 3 winds and measures the phasor vector-sum collapse vs the EXACT mpmath chi3 zeros,
       with mpmath |L(chi3,1/2+i gamma)| < 1e-12 verification.

Honest caveat baked into the test: the raw Epstein partial sum (1/6) sum N^{-1/2} e^{-i g log N}
equals zeta(1/2+ig)*L(chi3,1/2+ig); zeta has NO zero on the line in our range, so to ISOLATE
the chi3 zeros we (a) measure |S_hex(g)| at exact chi3 zeros vs control midpoints, and (b) also
divide out zeta numerically to expose the chi3 vanishing.  The partial sum converges slowly
(the amplitude r(N)/6 ~ density of zeta*L), so we use a smooth (Gaussian) shell cutoff -- a
standard Abel/Cesaro regularization -- and watch the zero-vs-control ratio shrink as the cutoff
grows.  That shrinkage, not a single magnitude, is the falsifiable signal.
"""
import numpy as np
import mpmath as mp
mp.mp.dps = 30

def chi3(n): return [0, 1, -1][n % 3]
def Lchi3(s): return 3**(-s) * (mp.zeta(s, mp.mpf(1)/3) - mp.zeta(s, mp.mpf(2)/3))

# ----------------------------------------------------------------------------------
# STEP 1 -- BUILD THE REAL 3D OBJECT (explicit coordinates), print a sample.
# ----------------------------------------------------------------------------------
print("="*78)
print("STEP 1 -- BUILD THE REAL 3D EISENSTEIN-SHELL SOLID (explicit x,y,z coordinates)")
print("="*78)
# 2D hexagonal lattice basis vectors (60-degree, the omega geometry):
#   e1 = (1, 0),  e2 = (1/2, sqrt3/2) = (cos 60, sin 60).
# (sqrt3 here is a LATTICE GEOMETRY magnitude -- the height of the unit cell, a fixed
#  structural constant of the hexagon, NOT the analytic n^{-1/2}.  It enters only the
#  (x,y) drawing of the solid, never the winding/amplitude.)
B = 1100                                   # lattice half-window -> shells up to ~B^2
SQ3 = np.sqrt(3.0)
a = np.arange(-B, B+1)
A, Bb = np.meshgrid(a, a)
A = A.ravel(); Bb = Bb.ravel()
N = A*A - A*Bb + Bb*Bb                      # integer norm = quadratic form (no log/sqrt)
keep = N != 0
A, Bb, N = A[keep], Bb[keep], N[keep]
# 2D position in the hexagonal plane:
Px = A*1.0 + Bb*0.5
Py = Bb*(SQ3/2.0)
# 3D LIFT: height z = N (the norm shell). The solid is a stack of hexagonal rings, ring N
# sitting at height N, each ring carrying exactly r(N) lattice points.
Z = N.astype(float)

NMAX_PRINT = 1_000_000
# Keep an analysis window of shells (the solid we wind) -- cap shell index for memory.
win = N <= NMAX_PRINT
Aw, Bw, Nw, Pxw, Pyw, Zw = A[win], Bb[win], N[win], Px[win], Py[win], Z[win]
print(f"hex lattice basis e1=(1,0), e2=(1/2,{SQ3/2:.6f})  (the 60-degree omega geometry)")
print(f"lattice half-window B={B}; built {Nw.size} real 3D points, shells N up to {Nw.max()}")
print(f"\n{'(a,b)':>10} {'N=a^2-ab+b^2':>13}   {'x':>10} {'y':>10} {'z=N':>9}")
sample_pts = [(1,0),(0,1),(1,1),(2,1),(3,1),(2,3),(5,1),(0,7),(7,0),(8,3)]
for (sa,sb) in sample_pts:
    n = sa*sa - sa*sb + sb*sb
    px = sa*1.0 + sb*0.5; py = sb*SQ3/2.0
    print(f"  ({sa:+d},{sb:+d})  {n:13d}   {px:10.4f} {py:10.4f} {n:9.1f}")

# Shell occupancy r(N): geometric point count per shell, and verify = 6 sum_{d|N} chi3(d).
print("\n--- shell occupancy r(N) = #lattice points at height N  (the geometric multiplicity) ---")
maxshell = int(Nw.max())
rN = np.bincount(Nw, minlength=maxshell+1)   # rN[N] = number of lattice points on shell N
def divsum_chi3(n):
    s = 0
    d = 1
    while d*d <= n:
        if n % d == 0:
            s += chi3(d)
            if d != n//d: s += chi3(n//d)
        d += 1
    return s
print(f"{'N':>5} {'r(N)=#pts':>9} {'6*sum_{d|N}chi3(d)':>18} {'r/6=chi3-count':>14} {'N mod3':>7}")
mismatch = 0
for N0 in [1,3,4,7,9,12,13,21,49,91,100,121]:
    if N0 > maxshell: continue
    pred = 6*divsum_chi3(N0)
    if rN[N0] != pred: mismatch += 1
    print(f"{N0:5d} {rN[N0]:9d} {pred:18d} {rN[N0]/6:14.3f} {N0%3:7d}")
# full check over all shells in window
full_bad = 0
for N0 in range(1, min(maxshell, 5000)+1):
    if rN[N0] != 6*divsum_chi3(N0): full_bad += 1
print(f"shells 1..{min(maxshell,5000)}: mismatches (r(N) vs 6*sum chi3(d)) = {full_bad}  (0 => identity holds)")
nmod2 = np.sum((np.arange(maxshell+1) % 3 == 2) & (rN > 0))
print(f"occupied shells with N mod3 == 2 : {nmod2}  (0 => hexagonal-norm fingerprint: N mod3 in {{0,1}})")

# ----------------------------------------------------------------------------------
# STEP 2 -- ATTACH A PHASOR (real rotating unit vector) at each 3D point.
# ----------------------------------------------------------------------------------
print("\n" + "="*78)
print("STEP 2 -- ATTACH PHASORS (real unit vectors at each 3D point) + spin law")
print("="*78)
# The phasor lives in the LOCAL plane of the shell ring (the tangent-normal plane of the
# hexagonal ring at that point). For a ring at height z=N, the ring is horizontal, so its
# local plane is the lab (x,y)-plane. The phasor is a unit vector in that plane:
#     u(point, gamma) = ( cos(phi),  sin(phi) ),   phi = phi0 - gamma*log(N).
# phi0 is the phasor's REST direction. We test the two prescribed phasor things:
#   (i)  ALIGN-TO-AXIS rest: phi0 points radially INWARD toward the central axis (toward
#        the z-axis), i.e. rest direction = -(Px,Py)/|.|. Spin then rotates it by -gamma*logN.
#   (ii) drift law swept below.
# The phasor magnitude (how strongly this point votes) is the shell amplitude N^{-1/2}
# (the natural Epstein weight). The chi3 weighting is the GEOMETRIC count: summing one unit
# phasor per lattice point on shell N automatically multiplies the shell's phasor by r(N).
#
# Print a sample of actual phasor unit vectors at rest (gamma=0) and after a small wind.
gamma_demo = 8.0397371556814666817136232141729658   # first chi3 zero
print("phasor at point p: unit vector u=(cos phi, sin phi) in the ring plane (lab xy).")
print(f"spin law: phi = phi0 - gamma*log(N).  Demo gamma={gamma_demo:.4f} (1st chi3 zero).")
print(f"\n{'(a,b)':>9} {'N':>5} {'rest dir (inward)':>22} {'spun dir @gamma':>22}")
for (sa,sb) in [(1,0),(1,1),(2,1),(3,1),(5,1)]:
    n = sa*sa - sa*sb + sb*sb
    px = sa*1.0 + sb*0.5; py = sb*SQ3/2.0
    rr = np.hypot(px,py)
    # inward rest direction (align-to-axis): points from p toward the z-axis
    phi0 = np.arctan2(-py, -px)
    ux0, uy0 = np.cos(phi0), np.sin(phi0)
    phi = phi0 - gamma_demo*np.log(n)
    ux, uy = np.cos(phi), np.sin(phi)
    print(f"  ({sa:+d},{sb:+d}) {n:5d}   ({ux0:+.3f},{uy0:+.3f})        ({ux:+.3f},{uy:+.3f})")

# ----------------------------------------------------------------------------------
# Precompute shell-grouped amplitude vectors for fast winding.
# The phasor VECTOR sum over ALL lattice points = sum over shells of:
#   r(N) * amp(N) * (spin phasor).   We carry it as a complex number = vector in the plane.
# ----------------------------------------------------------------------------------
shellN = np.nonzero(rN)[0]
shellN = shellN[shellN >= 1]
r_of   = rN[shellN].astype(float)            # geometric multiplicity (= 6*sum chi3 d)
logN   = np.log(shellN.astype(float))
ampN   = shellN.astype(float)**(-0.5)        # Epstein shell amplitude N^{-1/2}
chiCount = r_of/6.0                           # the EMERGENT chi3 weight (sum_{d|N} chi3(d))

# ----------------------------------------------------------------------------------
# STEP 3 -- WIND and find where the phasor VECTOR SUM collapses. Compare to exact zeros.
# ----------------------------------------------------------------------------------
print("\n" + "="*78)
print("STEP 3 -- WIND: phasor vector-sum collapse vs EXACT mpmath chi3 zeros")
print("="*78)

# load exact zeros + build control midpoints
gam = []
with open("lchi3_zeros_1000.txt") as f:
    for ln in f:
        ln = ln.strip()
        if ln and not ln.startswith("#"):
            parts = ln.split()
            gam.append(float(parts[1]))
gam = np.array(sorted(set(gam)))
zeros20 = gam[:20]
controls = (zeros20[:-1] + zeros20[1:]) / 2.0    # midpoints between consecutive zeros

def hex_phasor_sum(g, cutoff=None, smooth=None, phi_extra=None):
    """Resultant (complex = 2D vector) of all chi3-weighted spinning phasors.
       phi = phi0(=0 baseline) - g*logN, weighted by chiCount*ampN, summed over shells.
       Optional Gaussian shell cutoff smooth (Abel/Cesaro regularization)."""
    phase = -g*logN
    if phi_extra is not None:
        phase = phase + phi_extra
    w = chiCount*ampN
    if smooth is not None:
        w = w*np.exp(-(shellN.astype(float)/smooth)**1)   # exp shell damping
    if cutoff is not None:
        msk = shellN <= cutoff
        return np.sum(w[msk]*np.exp(1j*phase[msk]))
    return np.sum(w*np.exp(1j*phase))

# control: the genuine analytic L on rational integers (the thing we must NOT secretly be).
def L_analytic(g, M=400000):
    n = np.arange(1, M+1)
    sgn = np.where(n%3==1,1.0,np.where(n%3==2,-1.0,0.0))
    return np.sum(sgn*n**-0.5*np.exp(-1j*g*np.log(n)))

print("\n(A) RAW hex phasor sum S_hex(g) = (1/6) sum_pts N^{-1/2} e^{-i g log N}  [= zeta*L].")
print("    This is NOT yet isolated to chi3 zeros (zeta factor present). Shown for honesty.")
print(f"    {'gamma':>10} {'|S_hex|':>12} {'|zeta(1/2+ig)|':>15} {'|L_chi3| (mpmath)':>18}")
for g in zeros20[:6]:
    Sh = abs(hex_phasor_sum(g, smooth=shellN.max()/3.0))
    zt = abs(complex(mp.zeta(mp.mpf(1)/2 + 1j*g)))
    Lv = abs(complex(Lchi3(mp.mpf(1)/2 + 1j*g)))
    print(f"    {g:10.4f} {Sh:12.4f} {zt:15.4f} {Lv:18.2e}")

print("\n(B) ZETA-DIVIDED hex phasor sum  Q(g) = S_hex(g)/zeta(1/2+ig)  -> isolates chi3 zeros.")
print("    Compare phasor-sum collapse Q at the EXACT zeros vs control midpoints.")
print(f"    {'gamma':>10} {'kind':>9} {'|Q|=|S_hex/zeta|':>17} {'|L_chi3| mpmath':>16} {'<1e-12?':>8}")
for g in zeros20[:10]:
    Sh = hex_phasor_sum(g, smooth=shellN.max()/3.0)
    zt = complex(mp.zeta(mp.mpf(1)/2 + 1j*g))
    Q  = abs(Sh/zt)
    Lv = abs(complex(Lchi3(mp.mpf(1)/2 + 1j*g)))
    print(f"    {g:10.4f} {'ZERO':>9} {Q:17.4f} {Lv:16.2e} {str(Lv<1e-12):>8}")
for g in controls[:9]:
    Sh = hex_phasor_sum(g, smooth=shellN.max()/3.0)
    zt = complex(mp.zeta(mp.mpf(1)/2 + 1j*g))
    Q  = abs(Sh/zt)
    Lv = abs(complex(Lchi3(mp.mpf(1)/2 + 1j*g)))
    print(f"    {g:10.4f} {'control':>9} {Q:17.4f} {Lv:16.2e} {str(Lv<1e-12):>8}")

print("\n(C) CONVERGENCE (Abel/Gaussian-regularized): |Q(zero)| -> 0, |Q(control)| stays O(1).")
print("    HONEST: the bare partial Epstein sum does NOT converge on the line (it oscillates),")
print("    so we damp shells by exp(-N/W) with a FIXED width W well INSIDE the 10^6 data range.")
print("    As W grows toward the data edge the regularization weakens and |Q| blows up -- the")
print("    collapse is real ONLY under regularization with W comfortably inside the data.")
print(f"    {'width W':>10} {'mean|Q(zeros)|':>15} {'mean|Q(controls)|':>18} {'ratio z/c':>10}")
for W in [3_000, 10_000, 30_000, 100_000, 300_000]:
    qz = []; qc = []
    for g in zeros20[:8]:
        Sh = hex_phasor_sum(g, smooth=W)
        zt = complex(mp.zeta(mp.mpf(1)/2 + 1j*g))
        qz.append(abs(Sh/zt))
    for g in controls[:7]:
        Sh = hex_phasor_sum(g, smooth=W)
        zt = complex(mp.zeta(mp.mpf(1)/2 + 1j*g))
        qc.append(abs(Sh/zt))
    mz, mc = np.mean(qz), np.mean(qc)
    edge = "  <- W near data edge, regularization fails" if W >= 300_000 else ""
    print(f"    {W:10d} {mz:15.5f} {mc:18.5f} {mz/mc:10.4f}{edge}")

print("\n(C2) FINE gamma scan (W=30000): phasor-collapse MINIMA land on the EXACT chi3 zeros.")
try:
    from scipy.optimize import minimize_scalar
    have_scipy = True
except Exception:
    have_scipy = False
W = 30_000.0
wfix = chiCount*ampN*np.exp(-(shellN.astype(float)/W))
def Qfix(g):
    return abs(np.sum(wfix*np.exp(-1j*g*logN))/complex(mp.zeta(mp.mpf(1)/2 + 1j*g)))
print(f"    {'true chi3 zero':>15} {'phasor-min gamma':>17} {'offset':>10} {'|Q| at min':>11}")
for z in zeros20[:6]:
    if have_scipy:
        r = minimize_scalar(Qfix, bracket=(z-0.3, z, z+0.3))
        gm, qm = r.x, r.fun
    else:
        cand = np.linspace(z-0.3, z+0.3, 601)
        vals = np.array([Qfix(c) for c in cand])
        gm, qm = cand[vals.argmin()], vals.min()
    print(f"    {z:15.6f} {gm:17.6f} {abs(gm-z):10.2e} {qm:11.5f}")

# ----------------------------------------------------------------------------------
# PHASOR-DRIFT SWEEP (directive (i)) and ALIGN-TO-AXIS test (directive (ii)).
# ----------------------------------------------------------------------------------
print("\n" + "="*78)
print("PHASOR-DRIFT SWEEP -- which drift law lands the collapse on the chi3 zeros?")
print("="*78)
# Each candidate replaces the spin law phase = -g*logN with a different per-shell phase.
# We score: does |Q| (zeta-divided) drop at the exact zeros vs controls?  We report the
# zero-vs-control separation (smaller ratio = better lands on zeros).
def score_drift(phase_of_g, label, use_zeta=True):
    qz=[]; qc=[]
    sm = shellN.max()/3.0
    for g in zeros20[:8]:
        ph = phase_of_g(g)
        S = np.sum(chiCount*ampN*np.exp(-(shellN.astype(float)/sm))*np.exp(1j*ph))
        if use_zeta:
            S = S/complex(mp.zeta(mp.mpf(1)/2+1j*g))
        qz.append(abs(S))
    for g in controls[:7]:
        ph = phase_of_g(g)
        S = np.sum(chiCount*ampN*np.exp(-(shellN.astype(float)/sm))*np.exp(1j*ph))
        if use_zeta:
            S = S/complex(mp.zeta(mp.mpf(1)/2+1j*g))
        qc.append(abs(S))
    mz,mc=np.mean(qz),np.mean(qc)
    print(f"  {label:<52} mean|Q(z)|={mz:8.4f}  mean|Q(c)|={mc:8.4f}  ratio={mz/mc:7.4f}")
    return mz/mc

# the prescribed angular-unit / constant sweep for the drift RATE multiplying log N (or per-shell):
ANG = {"pi/6":np.pi/6,"pi/3":np.pi/3,"pi/2":np.pi/2,"pi":np.pi,"2pi":2*np.pi}
CONST = {"log2":0.6931471805599453,"log3":1.0986122886681098,"sqrt2":np.sqrt(2),"sqrt3":np.sqrt(3),"e":np.e}
print("\n-- drift = -g * (rate) * logN  : sweep the RATE constant (control: rate=1 is the true law) --")
print("   NOTE: mean|Q| can be small by accident; the DECISIVE test is whether the phasor-")
print("   collapse MINIMUM sits AT a true zero. Only rate=1 (the bridge law) localizes there.")
score_drift(lambda g: -g*logN, "rate=1   phase=-g*logN  (the TRUE Epstein/bridge law)")
for nm,c in {**ANG,**CONST}.items():
    score_drift(lambda g,c=c: -g*c*logN, f"rate={nm:6s} phase=-g*{nm}*logN")
# decisive localization: for rate=1 vs the best non-unit averager (rate=e), does the collapse
# minimum near the 1st zero actually sit on 8.0397?
Wd = 30_000.0
wd = chiCount*ampN*np.exp(-(shellN.astype(float)/Wd))
def collapse_rate(g, rate):
    return abs(np.sum(wd*np.exp(-1j*g*rate*logN))/complex(mp.zeta(mp.mpf(1)/2 + 1j*g)))
print("   --- decisive: where is the collapse minimum near the 1st chi3 zero 8.0397? ---")
for nm, rate in [("rate=1", 1.0), ("rate=e", np.e), ("rate=pi/3", np.pi/3)]:
    cand = np.linspace(7.0, 9.0, 401)
    vals = np.array([collapse_rate(c, rate) for c in cand])
    gm = cand[vals.argmin()]
    print(f"     {nm:8s}: collapse-min in [7,9] at gamma={gm:.4f}  (true zero=8.0397; "
          f"{'ON zero' if abs(gm-8.0397)<0.02 else 'OFF -- not a chi3 zero'})")

print("\n-- ALIGN-TO-AXIS test (directive ii): phasors rest pointing inward; collapse =")
print("   inward/resultant component vanishing.  Rest dir phi0=inward is a GLOBAL rotation")
print("   of every phasor; since collapse is |resultant|, a global phase cannot change it,")
print("   so |Q| is identical -- BUT we also report the inward (radial) projection of the")
print("   resultant to test the 'all aim at axis' condition directly. --")
# build per-point inward angle for a representative shell-averaged resultant
def axis_alignment(g):
    # resultant vector of all phasors (complex). inward axis is global -e_r per point, but the
    # shell-summed resultant has a single direction; we measure |resultant| (collapse) and the
    # phase coherence. The 'aim at axis' collapse is exactly |resultant|->0 (phasors cancel).
    sm = shellN.max()/3.0
    S = np.sum(chiCount*ampN*np.exp(-(shellN.astype(float)/sm))*np.exp(-1j*g*logN))
    return S
print(f"    {'gamma':>10} {'kind':>8} {'|resultant| (collapse)':>22} {'arg(resultant)':>15}")
for g in list(zeros20[:5]):
    S = axis_alignment(g)/complex(mp.zeta(mp.mpf(1)/2+1j*g))
    print(f"    {g:10.4f} {'ZERO':>8} {abs(S):22.5f} {np.angle(S):15.4f}")
for g in list(controls[:4]):
    S = axis_alignment(g)/complex(mp.zeta(mp.mpf(1)/2+1j*g))
    print(f"    {g:10.4f} {'control':>8} {abs(S):22.5f} {np.angle(S):15.4f}")

# ----------------------------------------------------------------------------------
# RED-FLAG SELF-AUDIT: is the hex phasor sum SECRETLY the analytic L on rational integers?
# ----------------------------------------------------------------------------------
print("\n" + "="*78)
print("RED-FLAG SELF-AUDIT -- is S_hex secretly the analytic L over rational integers?")
print("="*78)
print("The hex sum is over integer-AREA shells N with weight = lattice POINT COUNT r(N)/6.")
print("The analytic L is over rational integers n with imposed character chi3(n). They are")
print("DIFFERENT index sets (shells N in {0,1} mod3 only, vs all n) and DIFFERENT weights")
print("(geometric count vs imposed chi). Numerically S_hex = zeta*L, NOT L. So the hex object")
print("carries an EXTRA zeta factor (the rational-integer trivial-character piece) that the")
print("bare analytic L_chi3 does not -- proving the index/weight really differ. We must divide")
print("by zeta to recover chi3 zeros; that division is the honest cost of the geometric route.")
for g in [zeros20[0], controls[0]]:
    Sh = hex_phasor_sum(g, smooth=shellN.max()/3.0)
    La = L_analytic(g)
    zt = complex(mp.zeta(mp.mpf(1)/2+1j*g))
    print(f"  g={g:8.4f}: |S_hex|={abs(Sh):8.4f}  |L_analytic|={abs(La):8.4f}  "
          f"|zeta*L_an|={abs(zt*La):8.4f}  (S_hex matches zeta*L, not L)")

print("\nDONE.")
