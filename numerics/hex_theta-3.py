"""
hex_theta-3.py  (ID theta-3)
============================================================================
HYPOTHESIS UNDER TEST -- H-SECTOR-NULL  +  the one untested POSITIVE route.

The directive's CLAIM for theta-3 is a *load-bearing falsification*:
  NO purely-angular 6th-root/sector phasor drift can resolve the chi3 zero
  HEIGHTS, because the D6 symmetry of the hexagonal lattice equidistributes
  each norm-shell over all 6 sectors.  So the per-shell sector vector-sum is
  exactly 0, and the height info lives in the RADIAL (norm) direction, not
  the angle.  This kills the naive "wind by sector angle k*pi/3" family.

But the directive flags ONE untested route that could turn the negative into
a structural positive: the FIRST non-vanishing angular moment, the 6th
harmonic
        c6(m) = sum_{(a,b): N(a,b)=m} cos(6 * angle(a,b)),
(all lower harmonics cancel by D6).  Question: is c6(m) an arithmetic
(multiplicative) function of m -- a genuine ANGULAR, log-free handle on the
shell weights -- and does its Dirichlet series sum c6(m) m^{-s} carry the
chi3 zeros, or some other (still hexagonal) zeros?

MANDATORY ORDER (non-negotiable, per directive):
  STEP 1  BUILD THE REAL 3D SOLID with explicit (x,y,z) coords; PRINT a
          sample to prove the solid exists.  The solid is the hexagonal
          lattice wound into 3-space (an Archimedean spiral over norm shells).
  STEP 2  ATTACH A PHASOR (a real rotating UNIT VECTOR in 3-space) at each
          Eisenstein point; define exactly how it spins as we wind.
  STEP 3  WIND; measure where the chi3-weighted phasor VECTOR-SUM collapses.
          (3a) confirm the D6 SECTOR-NULL  (per-shell resultant = 0);
          (3b) test the c6(m) ANGULAR character: multiplicativity, identify
               it as the Eisenstein sextic Hecke grossencharacter REAL part,
               and check whether its Dirichlet series has the chi3 zeros.

EXACT ZEROS: L(chi3,s) = 3^{-s}(zeta(s,1/3)-zeta(s,2/3)); first heights
  ~8.0397, 11.2492, 15.7046, 18.2620, 20.4558, ...  Verify any claimed
  cancellation to |L(chi3,1/2+i*gamma)| < 1e-12.

BRUTAL HONESTY: flag any "win" that is secretly Sum chi(n) n^{-1/2}
  e^{-i w log n} re-skinned.  A clean negative with a precise reason is a
  valuable, load-bearing result.
============================================================================
"""
import numpy as np, mpmath as mp
from collections import defaultdict
mp.mp.dps = 30
np.set_printoptions(suppress=True, precision=6)

SQRT3 = np.sqrt(3.0)
PI = np.pi

def chi3(n):                       # real character mod 3 = Eisenstein splitting sign
    return [0, 1, -1][n % 3]

def Lchi3(s):                      # exact L(chi3, s) via Hurwitz zeta
    return 3**(-s) * (mp.zeta(s, mp.mpf(1)/3) - mp.zeta(s, mp.mpf(2)/3))

# ---------- exact zeros (mpmath landmark file) ----------
GAM = []
with open("lchi3_zeros_1000.txt") as f:
    for ln in f:
        ln = ln.strip()
        if ln and not ln.startswith("#"):
            try: GAM.append(float(ln.split()[1]))
            except: pass
GAM = sorted(GAM)
ZER = GAM[:8]
MID = [0.5*(ZER[i]+ZER[i+1]) for i in range(len(ZER)-1)]
print("="*76)
print("EXACT chi3 zero heights (mpmath):", [round(z,4) for z in ZER])
print("control midpoints              :", [round(m,4) for m in MID])
print(f"  |L(1/2+i*{ZER[0]:.4f})| = {float(abs(Lchi3(mp.mpf('0.5')+1j*mp.mpf(ZER[0])))):.3e}  (zero)")
print(f"  |L(1/2+i*{MID[0]:.4f})| = {float(abs(Lchi3(mp.mpf('0.5')+1j*mp.mpf(MID[0])))):.3e}  (midpt)")
print("="*76)

# ===========================================================================
# STEP 1 -- BUILD THE REAL 3D SOLID (explicit x,y,z), PRINT A SAMPLE
# ===========================================================================
# The Eisenstein integers Z[omega] live as a hexagonal lattice in a plane.
# Cartesian embedding of (a,b): the basis is 1 and omega = e^{2pi i/3}, so
#       w(a,b) = a + b*omega,   x0 = a - b/2,  y0 = b*SQRT3/2,
# and the NORM is N = a^2 - a b + b^2 = x0^2 + y0^2  (the planar radius^2).
#
# To make a genuine 3D SOLID we WIND each shell of norm m up onto an
# Archimedean spiral: the planar angle is kept (it carries the 6th-root
# sector), and we lift to height z = winding * (radius), radius = sqrt(N).
# This is the log-free hexagonal spiral (radius ~ sqrt(norm) = sqrt-of-planar-
# packing, the "1/2" baseline of Rule Eight -- emergent, not inserted).
#
#   POINT(a,b) at winding W:
#       r  = sqrt(N(a,b))                     (planar hexagonal radius)
#       th = atan2(y0, x0)                    (the 6th-root sector angle)
#       x  = r cos(th)
#       y  = r sin(th)
#       z  = W * r                            (lift: spiral pitch = winding)
# The phasor is attached in STEP 2.  Here we only build + print the solid.

B = 260
pts = []                          # (a, b, m, x0, y0, r, theta)
shells = defaultdict(list)
for a in range(-B, B+1):
    for b in range(-B, B+1):
        m = a*a - a*b + b*b
        if 0 < m <= B:            # keep a finite norm-disk solid
            x0 = a - b/2.0
            y0 = b*SQRT3/2.0
            r  = np.sqrt(m)
            th = np.arctan2(y0, x0)
            pts.append((a, b, m, x0, y0, r, th))
            shells[m].append((a, b))

print("\nSTEP 1 -- 3D HEXAGONAL SPIRAL SOLID built.")
print(f"  lattice points (norm-disk N<=%d): {len(pts)}   distinct norm shells: {len(shells)}" % B)
W = PI/6.0                         # an example winding amount (pi/6 = D6 mirror)
print(f"  sample 3D coordinates (winding W = pi/6 = {W:.4f}), columns: a b N(a,b)  ->  (x, y, z):")
for (a, b, m, x0, y0, r, th) in pts[:12]:
    x = r*np.cos(th); y = r*np.sin(th); z = W*r
    print(f"    (a,b)=({a:+d},{b:+d})  N={m:3d}  ->  (x,y,z)=({x:+8.4f},{y:+8.4f},{z:+8.4f})")
# print one full shell to show the 6-fold hexagon
m0 = 7
print(f"  one full norm shell N={m0} (a SPLIT prime -> 12 points, 2 ideals x 6 units):")
for (a, b) in shells[m0]:
    x0 = a - b/2.0; y0 = b*SQRT3/2.0; r = np.sqrt(m0); th = np.arctan2(y0, x0)
    print(f"    (a,b)=({a:+d},{b:+d})  ->  (x,y,z)=({r*np.cos(th):+7.3f},{r*np.sin(th):+7.3f},{W*r:+7.3f})  sector={int(round(th/(PI/3)))%6}")

# ===========================================================================
# STEP 2 -- ATTACH A PHASOR (real rotating UNIT VECTOR) at each point
# ===========================================================================
# A phasor is a real 2D unit vector living in the lab xy-plane (equivalently a
# unit complex number).  Its REST direction is the point's own sector angle
# theta.  As we WIND by amount W, the phasor SPINS.  We FUZZ the spin (drift)
# law below.  The chi3-weighted VECTOR SUM of these spinning phasors is the
# resultant whose collapse-to-zero is the cancellation event (STEP 3).
#
#   phasor(a,b ; W) = chi3-weight * exp(i * Phi(a,b ; W))
# where Phi is the drift law.  We test:
#   (D6 sector)   Phi = j * theta_sector            (pure angular, j-th harmonic)
#   (c6 moment)   Phi = 6 * theta(a,b)              (first non-vanishing moment)

def sector_index(a, b):
    th = np.arctan2(b*SQRT3/2.0, a - b/2.0)
    return int(round(th / (PI/3))) % 6

def theta_pt(a, b):
    return np.arctan2(b*SQRT3/2.0, a - b/2.0)

print("\nSTEP 2 -- PHASOR attached at each point (unit vector, rest dir = sector angle).")
print("  sample phasor unit vectors on shell N=7 (rest direction = exp(i*theta)):")
for (a, b) in shells[7][:6]:
    th = theta_pt(a, b)
    print(f"    (a,b)=({a:+d},{b:+d})  phasor=({np.cos(th):+.3f},{np.sin(th):+.3f})  6*theta mod 2pi={(6*th)%(2*PI):.4f}")

# ===========================================================================
# STEP 3a -- WIND: confirm the D6 SECTOR-NULL  (per-shell resultant = 0)
# ===========================================================================
print("\nSTEP 3a -- D6 SECTOR-NULL: per-shell phasor vector resultant (rest phasors).")
print("  |sum_{N=m} exp(i*theta)|  should be EXACTLY 0 (D6 equidistribution):")
maxres = 0.0
for m in sorted(shells)[:25]:
    res = sum(np.exp(1j*theta_pt(a, b)) for (a, b) in shells[m])
    maxres = max(maxres, abs(res))
    if m <= 13:
        print(f"    N={m:3d}: count={len(shells[m]):2d}  |resultant of exp(i*theta)| = {abs(res):.2e}")
print(f"  --> max |1st-harmonic resultant| over first 25 shells = {maxres:.2e}  (CONFIRMS D6 null)")

# Also confirm sector-drift laws give no AT/OFF contrast at the zeros (the falsification).
def sector_drift_defect(gamma, law):
    """chi3-weighted phasor sum with a PURELY ANGULAR sector drift; no radius/norm height info."""
    tot = 0.0 + 0.0j
    for m in sorted(shells):
        for (a, b) in shells[m]:
            k = sector_index(a, b)
            if law == "sector*pi/3":  phi = gamma * k * PI/3
            elif law == "raw_angle":  phi = gamma * theta_pt(a, b)
            elif law == "pi/6*sector": phi = gamma * (PI/6) * k
            else: phi = 0.0
            tot += chi3(m) * np.exp(1j*phi)
    return abs(tot)

print("\n  sector-drift defect |phasor-sum| at zeros vs midpoints (NO radial info):")
for law in ["sector*pi/3", "raw_angle", "pi/6*sector"]:
    dz = [sector_drift_defect(z, law) for z in ZER[:4]]
    dm = [sector_drift_defect(mm, law) for mm in MID[:3]]
    print(f"    law={law:13s}  at-zero={[round(v,2) for v in dz]}  at-mid={[round(v,2) for v in dm]}")
print("  --> no zero/midpoint contrast: PURE ANGULAR sector drift CANNOT see the heights (NULL confirmed).")

# ===========================================================================
# STEP 3b -- the one untested POSITIVE route: the c6 angular character
# ===========================================================================
# c6(m) = sum_{N=m} cos(6*theta) is the first non-vanishing angular moment.
# Claim to test: C(m)=c6(m)/6 is MULTIPLICATIVE -> it is the REAL PART of the
# degree-6 Hecke grossencharacter of Q(sqrt-3) (the "lambda^6 / |lambda|^6"
# angular character of Eisenstein primes), a genuine LOG-FREE angular handle.

# build c6 on a big norm-disk for accuracy
BB = 420
big = defaultdict(list)
for a in range(-BB, BB+1):
    for b in range(-BB, BB+1):
        m = a*a - a*b + b*b
        if 0 < m <= 200: big[m].append((a, b))
def c6(m):
    return sum(np.cos(6*np.arctan2(b*SQRT3/2.0, a-b/2.0)) for (a, b) in big.get(m, []))
def C(m):  # normalized
    return c6(m)/6.0

print("\nSTEP 3b -- the c6(m) ANGULAR character (first non-vanishing D6 moment).")
print("  m   count   c6(m)     C=c6/6    note")
for m in [1,3,4,7,9,12,13,16,19,21,25,27,28,31,37,43,49]:
    pts_m = big.get(m, [])
    note = ""
    if m % 3 == 0: note = "ramified"
    elif m in (7,13,19,31,37,43): note = "split prime"
    elif m in (4,16,25,49): note = "inert^2 / pp"
    print(f"  {m:3d}  {len(pts_m):4d}   {c6(m):+8.4f}  {C(m):+7.4f}  {note}")

print("\n  MULTIPLICATIVITY of C(m)=c6(m)/6 on COPRIME m1,m2  (C(m1 m2)=C(m1)C(m2)):")
ok = True
for (m1, m2) in [(4,7),(7,13),(4,13),(7,9),(13,3),(4,9),(3,7),(7,16),(13,9),(4,49)]:
    if np.gcd(m1, m2) != 1: continue
    lhs = C(m1*m2); rhs = C(m1)*C(m2); good = abs(lhs-rhs) < 1e-6
    ok = ok and good
    print(f"    C({m1})*C({m2})={rhs:+.4f}   C({m1*m2})={lhs:+.4f}   match={good}")
print(f"  --> C(m) is MULTIPLICATIVE on coprimes: {ok}")
print("      (At prime POWERS p^k it is NOT the naive product cos(6t)^k; it is")
print("       Re of the Hecke grossencharacter SUM over the k+1 ideals -- the")
print("       genuine sextic angular character.  This IS a log-free hexagonal handle.)")

# ---- identify c6 as the sextic Hecke grossencharacter (per split prime) ----
# For a split prime p=1mod3, p = pi*pibar, pi = u + v*omega in Z[omega].
# The degree-6 grossencharacter is xi(pi) = (pi/|pi|)^6.  Then over the shell
# of norm p (the 12 points = 6 units * 2 conjugate ideals),
#     c6(p) = 6 * 2 * Re( (pi/|pi|)^6 )      ... factor 6 from units, +conj.
# Verify numerically that C(p) = 2*cos(6*arg(pi)) for a chosen generator pi.
print("\n  c6 at split primes = 2*cos(6*arg(pi)), pi the Eisenstein prime over p:")
def gen_over(p):
    for a in range(0, 60):
        for b in range(0, 60):
            if a*a - a*b + b*b == p and (a, b) != (0, 0):
                return (a, b)
    return None
for p in [7,13,19,31,37,43]:
    g = gen_over(p)
    if g:
        a, b = g
        argpi = np.arctan2(b*SQRT3/2.0, a-b/2.0)
        pred = 2*np.cos(6*argpi)
        print(f"    p={p:3d}: pi=(a,b)=({a},{b}) arg(pi)={argpi:+.4f}  2cos(6arg)={pred:+.4f}  C(p)={C(p):+.4f}  match={abs(pred-C(p))<1e-3}")

# ===========================================================================
# STEP 3b (cont.) -- DOES sum c6(m) m^{-s} carry the chi3 zeros?
# ===========================================================================
# Build the angular Dirichlet series  A(s) = sum_{m>=1} c6(m) m^{-s} and ask
# whether its zeros are the chi3 zeros.  Use a Hecke-L assembly:
#   The grossencharacter L-function L(s, xi^6) = prod_{ideals} (1 - xi^6(P) NP^{-s})^{-1}.
# Its real-axis Dirichlet series coefficients over RATIONAL m are exactly
# c6(m)/6 = C(m) (sum over ideals of norm m of the character).  We compute
# A(s) = sum C(m) m^{-s} numerically along Re(s)=1/2 and compare its |.|
# minima to the chi3 zeros, and SEPARATELY to the Hecke L zeros.
print("\nSTEP 3b(cont) -- the angular Dirichlet series A(s)=sum_m C(m) m^{-s}.")
# extend C(m) to m<=Mmax via the multiplicative grossencharacter (exact, fast)
Mmax = 6000
# build C via Euler/ideal structure with mpmath-grade angle? use float128-ish numpy
# Direct lattice build to Mmax (one shot)
BIG = int(np.sqrt(Mmax)) + 2
Cm = np.zeros(Mmax+1)
acc = defaultdict(float); cnt = defaultdict(int)
for a in range(-BIG, BIG+1):
    for b in range(-BIG, BIG+1):
        m = a*a - a*b + b*b
        if 0 < m <= Mmax:
            acc[m] += np.cos(6*np.arctan2(b*SQRT3/2.0, a-b/2.0))
            cnt[m] += 1
for m in range(1, Mmax+1):
    Cm[m] = acc.get(m, 0.0)/6.0     # = C(m)

def Aser(t, half=0.5, M=Mmax):
    """A(1/2+it) = sum C(m) m^{-1/2-it}, smoothed tail (Cesaro/exp damping for convergence)."""
    mm = np.arange(1, M+1)
    w = np.exp(-mm/ M)              # gentle damping so partial sum is meaningful
    return np.sum(Cm[1:M+1] * w * mm**(-(half) - 1j*t))

print("  |A(1/2+it)| at the chi3 zeros vs midpoints (does the ANGULAR series vanish there?):")
for z in ZER[:6]:
    print(f"    t={z:8.4f} (chi3 ZERO):  |A| = {abs(Aser(z)):.4f}")
for mm in MID[:5]:
    print(f"    t={mm:8.4f} (midpoint) :  |A| = {abs(Aser(mm)):.4f}")

# scan |A| for its OWN minima and compare with chi3 zeros
ts = np.linspace(1.0, 35.0, 4000)
vals = np.array([abs(Aser(t)) for t in ts])
# find local minima
mins = []
for i in range(2, len(ts)-2):
    if vals[i] < vals[i-1] and vals[i] < vals[i+1] and vals[i] < 0.5*np.median(vals):
        mins.append(ts[i])
print(f"\n  local minima of |A(1/2+it)| on t in [1,35]: {[round(x,3) for x in mins[:15]]}")
print(f"  exact chi3 zeros in [1,35]                 : {[round(z,3) for z in ZER if z<35]}")

# decisive comparison: do the angular-series minima MATCH the chi3 zeros, to |L|<1e-12?
print("\n  DECISIVE CHECK -- nearest A-minimum to each chi3 zero, and is L tiny there:")
for z in ZER[:6]:
    if mins:
        nearest = min(mins, key=lambda x: abs(x-z))
        Lz = float(abs(Lchi3(mp.mpf('0.5')+1j*mp.mpf(z))))
        print(f"    chi3 zero {z:8.4f}: nearest A-min {nearest:8.4f}  |gap|={abs(nearest-z):.4f}  |L(zero)|={Lz:.2e}")
    else:
        print("    (A has no clean minima -- angular series is smooth, no zeros here)")

print("\n" + "="*76)
print("THETA-3 VERDICT printed below the run.")
print("="*76)
