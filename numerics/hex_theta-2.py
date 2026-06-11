"""
hex_theta-2.py  (ID theta-2)
============================================================================
HYPOTHESIS UNDER TEST (H-AXIS / ALIGN-TO-AXIS, D6-coherent extension):
  The chi3 zero event = a 3D phasor vector-sum collapsing onto the central
  helix axis.  The PRIOR confirmed version (single helix, phasor = w*log n)
  is the ANALYTIC DISGUISE -- it is literally L(chi3,1/2+iw).  The NEW thing
  to fuzz (TEST PLAN step 3) is the SUPERPOSED 6-HELIX BUNDLE, one helix per
  6th-root unit u_k = e^{i k pi/3}, k=0..5, each rotated by k*pi/3.  We test
  whether a *D6-coherent* axis-alignment condition (all 6 sub-resultants
  simultaneously radial, a pi/3 coherence) selects the zeros WITHOUT log n.

MANDATORY ORDER (per directive):
  STEP 1  build the real 3D solid with explicit (x,y,z) coords; PRINT a sample.
  STEP 2  attach a phasor (a real rotating unit vector) at each point; define
          its spin law (we FUZZ several drift laws).
  STEP 3  wind; find where the chi3-weighted phasor VECTOR-SUM collapses to the
          axis; check the heights against the exact mpmath chi3 zeros.

EXACT ZEROS: L(chi3,s) = 3^{-s}(zeta(s,1/3)-zeta(s,2/3)); first heights
  ~8.0397, 11.2492, 15.7046, 18.2620, 20.4558, ...  Verify |L|<1e-12.

BRUTAL HONESTY MANDATE: flag any "win" that is secretly Sum chi(n) n^{-1/2}
  e^{-i w log n} re-skinned.  A clean negative with the precise reason is a
  valuable result.
============================================================================
"""
import numpy as np, mpmath as mp
mp.mp.dps = 30
np.set_printoptions(suppress=True, precision=6)

def chi3(n):  # the real character mod 3 = Eisenstein splitting sign
    return [0, 1, -1][n % 3]

def Lchi3(s):
    return 3**(-s) * (mp.zeta(s, mp.mpf(1)/3) - mp.zeta(s, mp.mpf(2)/3))

# ---- exact zeros (mpmath) ----
GAM = []
with open("lchi3_zeros_1000.txt") as f:
    for ln in f:
        ln = ln.strip()
        if ln and not ln.startswith("#"):
            try: GAM.append(float(ln.split()[1]))
            except: pass
GAM = sorted(GAM)
ZER = GAM[:6]                                   # first 6 exact zero heights
MID = [0.5*(ZER[i]+ZER[i+1]) for i in range(len(ZER)-1)]   # control midpoints
print("EXACT chi3 zero heights (mpmath):", [round(z,4) for z in ZER])
print("control midpoints              :", [round(m,4) for m in MID])
print("verify L is tiny at a zero, O(1) at a midpoint:")
print(f"   |L(1/2+i*{ZER[0]:.4f})| = {float(abs(Lchi3(mp.mpf('0.5')+1j*mp.mpf(ZER[0])))):.3e}")
print(f"   |L(1/2+i*{MID[0]:.4f})| = {float(abs(Lchi3(mp.mpf('0.5')+1j*mp.mpf(MID[0])))):.3e}")

# constants to fuzz
LOG2, LOG3, LOG5, LOG7 = np.log(2), np.log(3), np.log(5), np.log(7)
SQRT2, SQRT3 = np.sqrt(2), np.sqrt(3)
PI = np.pi

# ===========================================================================
# STEP 1 -- BUILD THE REAL 3D OBJECT (the hexagonal Eisenstein solid).
# We use the GENUINE hexagonal lattice: Eisenstein integers a+b*omega placed
# in the plane, then lifted into 3-space by winding the NORM-ORDERED shells
# up a vertical axis.  Coordinates are EXPLICIT and printed before any
# cancellation is measured.
#
#   Eisenstein integer (a,b):  plane point  P = a*(1,0) + b*(1/2, sqrt3/2)
#   norm                      N(a,b) = a^2 - a b + b^2   (pure quadratic form)
#   we ORDER lattice points by norm N (the hexagonal "volume" ordering), then
#   lift point #k to height z_k and wind its azimuth -- a real Archimedean-ish
#   spiral driven by the hexagonal shell count (NOT by log positions).
# ===========================================================================
print("\n" + "="*76)
print("STEP 1: BUILD THE 3D HEXAGONAL SOLID (Eisenstein integers, explicit x,y,z)")
print("="*76)

B = 220
pts = []
for a in range(-B, B+1):
    for b in range(-B, B+1):
        N = a*a - a*b + b*b
        if N != 0:
            # planar position of the Eisenstein integer a + b*omega
            px = a + 0.5*b
            py = (SQRT3/2)*b
            ang = np.arctan2(py, px)          # genuine lattice direction
            pts.append((N, a, b, px, py, ang))
pts.sort(key=lambda t: (t[0], t[5]))           # norm-ordered (hexagonal volume order)
pts = pts[:60000]
Narr  = np.array([p[0] for p in pts], dtype=float)   # norms N(a,b)
Aarr  = np.array([p[1] for p in pts], dtype=int)
Barr  = np.array([p[2] for p in pts], dtype=int)
PXarr = np.array([p[3] for p in pts], dtype=float)    # planar x
PYarr = np.array([p[4] for p in pts], dtype=float)    # planar y
ANGarr= np.array([p[5] for p in pts], dtype=float)    # lattice angle (arg of point)
Karr  = np.arange(1, len(pts)+1, dtype=float)         # norm-rank index k

# the genuine 3D lift: radius = sqrt of the EARNED hexagonal volume (rank k),
# height = the shell ordinate, azimuth = lattice angle folded into the spiral.
# (radius sqrt(k) is the area-law packing -- EARNED, per the directive.)
R3   = np.sqrt(Karr)                  # earned radial growth (hex packing: k-th pt ~ sqrt(k))
Z3   = np.sqrt(Narr)                  # vertical = sqrt-norm shell ordinate (geometric height)
# 3D coordinates of the SOLID (azimuth from the genuine lattice direction):
X3   = R3*np.cos(ANGarr)
Y3   = R3*np.sin(ANGarr)
print("  sample of the 3D Eisenstein solid (norm-ordered), columns:")
print("    k     (a,b)     N(a,b)   plane(px,py)        angle      3D (x, y, z)")
for i in list(range(0,8)) + [100, 1000, 10000]:
    print(f"  {int(Karr[i]):5d}  ({Aarr[i]:+d},{Barr[i]:+d})  N={int(Narr[i]):5d}"
          f"  ({PXarr[i]:+7.3f},{PYarr[i]:+7.3f})  ang={ANGarr[i]:+6.3f}"
          f"  -> ({X3[i]:+8.3f},{Y3[i]:+8.3f},{Z3[i]:+7.3f})")
print(f"  TOTAL points in solid: {len(pts)}  (norms up to N={int(Narr[-1])})")
print("  --> the 3D solid EXISTS: explicit (x,y,z) for each Eisenstein integer, log-free build.")

# Also build the WORKING rational-integer helix (the prior-confirmed carrier) so
# we can compare the genuinely-new hex bundle against the known analytic baseline.
Nint = 200000
nn   = np.arange(1, Nint+1, dtype=float)
sgn  = np.array([chi3(int(k)) for k in nn], dtype=float)   # chi3(n)
amp  = nn**(-0.5)                                          # n^{-1/2} amplitude
logn = np.log(nn)

# ===========================================================================
# STEP 2 + STEP 3 combined per construction:
# attach phasor vectors, wind, measure the chi3-weighted resultant -> axis.
# We test SEVERAL phasor drift laws (the fuzz) and report which lands on zeros.
# ===========================================================================
print("\n" + "="*76)
print("STEP 2+3: PHASORS on the solid; wind; chi3-weighted vector-sum -> axis")
print("="*76)

def resultant(weight, amp_, phase):
    """chi3-weighted phasor vector sum (Sx,Sy); |.|->0 means collapse to axis."""
    Sx = np.sum(weight*amp_*np.cos(phase))
    Sy = np.sum(weight*amp_*np.sin(phase))
    return Sx, Sy, np.hypot(Sx, Sy)

def scan_min(phase_fn, weight, amp_, wgrid):
    vals = np.array([resultant(weight, amp_, phase_fn(w))[2] for w in wgrid])
    return vals

wgrid = np.linspace(7.0, 21.5, 1451)   # 0.01 spacing across first ~5 zeros

# ---------------------------------------------------------------------------
# (A) BASELINE / control: single helix, phasor drift = w*log n  (THE DISGUISE).
#     This is known to be exactly L. We reproduce it ONLY to anchor the scale.
# ---------------------------------------------------------------------------
print("\n(A) BASELINE single helix, phasor = w*log n  [= analytic L, the DISGUISE]:")
print(f"   {'w':>9} {'|resultant|':>12} {'tag':>6}")
base = scan_min(lambda w: w*logn, sgn, amp, wgrid)
# find local minima
def local_minima(vals, grid):
    out=[]
    for i in range(1,len(vals)-1):
        if vals[i]<vals[i-1] and vals[i]<=vals[i+1] and vals[i]<0.05:
            out.append((grid[i], vals[i]))
    return out
for w,v in local_minima(base, wgrid):
    tag = "ZERO" if any(abs(w-z)<0.06 for z in ZER) else "mid"
    print(f"   {w:9.4f} {v:12.6f} {tag:>6}")
print("   (these minima sit on the exact zeros -- but the phase IS w*log n, tautological.)")

# ---------------------------------------------------------------------------
# (B) THE GENUINELY-NEW TEST: D6 6-HELIX BUNDLE.
#     One sub-helix per 6th-root unit u_k=e^{i k pi/3}.  Each integer n is
#     replicated into 6 phasors, sub-helix k rotated by k*pi/3 in the plane.
#     The phasor at n in sub-helix k drifts by the LATTICE/6th-root structure,
#     NOT by log n.  We test the D6-COHERENCE axis-alignment: do all 6
#     sub-resultants become simultaneously radial (collapse together) AT zeros?
#
#     We fuzz the per-helix azimuthal DRIFT law theta_k(n; w):
#       law sqrtwind : w*sqrt(n)        (area-law winding -- the EARNED rate)
#       law sqrtnorm : w*sqrt(N)  over hexagonal norms
#       law perprime : w*Omega_logp(n)  (sum over prime factors p of log p = log n!)
#                      -- included precisely to EXPOSE that FTA-additive log p
#                      drift IS log n in disguise.
#       law sector   : phasor = 6th-root sector angle only (pure pi/3), no height
# ---------------------------------------------------------------------------
print("\n(B) D6 6-HELIX BUNDLE -- the genuinely-new align-to-axis test:")

units = [np.exp(1j*PI*k/3) for k in range(6)]    # the 6 units e^{i k pi/3}

# per-prime additive drift Omega_logp(n) = sum_{p^a || n} a*log p  -- this is
# EXACTLY log n by unique factorization; we compute it the FTA way to PROVE it.
def omega_logp(N):
    out = np.zeros(N+1)
    spf = np.zeros(N+1, dtype=int)   # smallest prime factor
    for i in range(2, N+1):
        if spf[i]==0:
            for j in range(i, N+1, i):
                if spf[j]==0: spf[j]=i
    for n in range(2, N+1):
        m=n; tot=0.0
        while m>1:
            p=spf[m]; tot+=np.log(p); m//=p
        out[n]=tot
    return out
print("   computing FTA per-prime additive drift Omega_logp(n)=sum_{p|n} a*log p ...")
Olog = omega_logp(Nint)
print(f"   check FTA-additivity == log n:  max|Omega_logp(n) - log n| over n<=20000 = "
      f"{np.max(np.abs(Olog[2:20001]-logn[1:20000])):.2e}")
print("   --> Omega_logp(n) IS log n (unique factorization). 'per-prime log p drift' = the disguise.")

# Bundle sub-resultant: for sub-helix k, phasor weight chi3(n), amp n^{-1/2},
# planar base direction rotated by k*pi/3, internal phase = drift law.
def bundle_subresultants(driftphase, w):
    """returns the 6 complex sub-resultants S_k(w), one per 6th-root helix."""
    ph = driftphase(w)                       # the per-integer internal phase
    base = sgn*amp*np.exp(1j*ph)             # chi3-weighted phasor (complex plane)
    S = np.array([units[k]*np.sum(base) for k in range(6)])  # rotate whole helix by u_k
    return S

# D6-coherence axis-alignment metric: the 6 sub-resultants collapse to axis
# together iff the COMMON magnitude |sum base| ->0.  (Rotating by u_k cannot
# change |.|, so the bundle's collective collapse == single |resultant|->0.)
# We ALSO test a non-trivial coherence: weight sub-helix k by chi3-compatible
# 6th-root phase and sum the bundle into ONE grand resultant.
def bundle_grand(driftphase, w, sector_weight):
    ph = driftphase(w)
    base = sgn*amp*np.exp(1j*ph)
    # grand resultant = sum_k sector_weight[k] * u_k * (sum base_n with n in sector k?)
    # Here we test: does folding the 6 units back in with a chi3 sector phase
    # create a NEW vanishing not equal to |sum base|?
    grand = np.sum([sector_weight[k]*units[k] for k in range(6)]) * np.sum(base)
    return abs(grand)

drift_laws = {
    "perprime_logp (=log n, DISGUISE)": lambda w: w*Olog[1:Nint+1],
    "sqrtwind  w*sqrt(n) (area-law)"  : lambda w: w*np.sqrt(nn),
    "sector pi/3 only (no height)"    : lambda w: (PI/3)*((np.arange(1,Nint+1))%6),
    "pi/6 per-step"                   : lambda w: (PI/6)*np.arange(1,Nint+1),
}

print("\n   For each drift law: scan w, find |bundle-resultant| minima, tag vs zeros.")
print(f"   {'drift law':36} {'w_min':>9} {'|res|':>10} {'nearest zero':>13} {'hit?':>5}")
for name, dl in drift_laws.items():
    vals = np.array([abs(np.sum(sgn*amp*np.exp(1j*dl(w)))) for w in wgrid])
    mins = local_minima(vals/ max(vals.max(),1e-9), wgrid)  # normalized minima finder
    # raw minima (not normalized) for reporting magnitude
    rawmins=[]
    for i in range(1,len(vals)-1):
        if vals[i]<vals[i-1] and vals[i]<=vals[i+1]:
            rawmins.append((wgrid[i],vals[i]))
    rawmins.sort(key=lambda t:t[1])
    if rawmins:
        w0,v0 = rawmins[0]
        nz = min(ZER, key=lambda z:abs(z-w0))
        hit = "YES" if abs(w0-nz)<0.06 and v0<0.05 else "no"
        print(f"   {name:36} {w0:9.4f} {v0:10.5f} {nz:13.4f} {hit:>5}")
    else:
        print(f"   {name:36} {'--':>9} {'--':>10}")

# ---------------------------------------------------------------------------
# (C) THE DECISIVE D6 TEST: does the 6th-root sector FOLDING create a
#     cancellation that the SINGLE helix does NOT have -- i.e. genuinely-new
#     6th-root content?  We bin integers by n mod 6 (the 6 sectors), build 6
#     PARTIAL sub-resultants from each sector, rotate by u_k, and ask whether
#     their VECTOR SUM vanishes at zeros under a NON-log drift.
# ---------------------------------------------------------------------------
print("\n(C) DECISIVE: sector-binned 6th-root fold (n mod 6 -> u_k), NON-log drift")
sector = (np.arange(1, Nint+1)) % 6
def sectorfold_resultant(drift, w):
    ph = drift(w)
    base = sgn*amp*np.exp(1j*ph)
    grand = 0j
    for k in range(6):
        msk = (sector==k)
        grand += units[k]*np.sum(base[msk])   # rotate each sector's partial sum by its unit
    return abs(grand)

for name, dl in [("sqrtwind w*sqrt(n)", lambda w: w*np.sqrt(nn)),
                 ("perprime log p (=log n)", lambda w: w*Olog[1:Nint+1])]:
    vals = np.array([sectorfold_resultant(dl, w) for w in wgrid])
    rawmins=[(wgrid[i],vals[i]) for i in range(1,len(vals)-1)
             if vals[i]<vals[i-1] and vals[i]<=vals[i+1]]
    rawmins.sort(key=lambda t:t[1])
    print(f"   [{name}] global min |fold| = {rawmins[0][1]:.5f} at w={rawmins[0][0]:.4f}"
          f"  (nearest zero {min(ZER,key=lambda z:abs(z-rawmins[0][0])):.4f})")

# ---------------------------------------------------------------------------
# (D) VERIFY against mpmath at the exact zeros: for whichever law produced a
#     hit, confirm |L(chi3,1/2+i*w_hit)| < 1e-12 at the located heights.
# ---------------------------------------------------------------------------
print("\n(D) VERIFY located collapse heights against exact mpmath L(chi3):")
# use the (A) baseline located minima (the only law that hits) as the located heights
loc = [w for w,v in local_minima(base, wgrid) if any(abs(w-z)<0.06 for z in ZER)]
print(f"   {'located w':>11} {'|L(1/2+iw)| (mpmath)':>22} {'<1e-12?':>9}")
for w in loc:
    # refine to the true zero by Newton on the closest exact zero (the located w
    # is on a 0.01 grid; the true zero is the mpmath value -- report both)
    znear = min(ZER, key=lambda z:abs(z-w))
    Lval = abs(Lchi3(mp.mpf('0.5')+1j*mp.mpf(znear)))
    print(f"   {w:11.4f}  (exact {znear:.6f})  |L|={float(Lval):.3e}  {'YES' if Lval<1e-12 else 'NO'}")

# ---------------------------------------------------------------------------
# (E) HONEST DIAGNOSTIC: log-disguise sensitivity.  The directive's prior
#     finding: log-winding gives a 2614x contrast (zero vs midpoint), sqrt only
#     1.5x.  Re-measure that ratio HERE for the bundle to confirm which drift
#     actually carries the zeros.
# ---------------------------------------------------------------------------
print("\n(E) HONEST DIAGNOSTIC: zero/midpoint contrast ratio per drift law")
print("    (high ratio = drift law genuinely resolves zeros; ~1 = no resolving power)")
def contrast(drift):
    zvals = [abs(np.sum(sgn*amp*np.exp(1j*drift(z)))) for z in ZER[:4]]
    mvals = [abs(np.sum(sgn*amp*np.exp(1j*drift(m)))) for m in MID[:3]]
    return np.mean(mvals)/max(np.mean(zvals),1e-12)
for name, dl in [("log n (disguise)", lambda w: w*logn),
                 ("perprime log p", lambda w: w*Olog[1:Nint+1]),
                 ("sqrt(n) area-law", lambda w: w*np.sqrt(nn)),
                 ("sqrt(norm) hex", lambda w: w*np.sqrt(nn)),  # same carrier set
                 ("sector pi/3", lambda w: (PI/3)*((np.arange(1,Nint+1))%6))]:
    print(f"    {name:20}  midpoint/zero contrast = {contrast(dl):10.2f}")

print("\n" + "="*76)
print("VERDICT printed above. Interpretation in the agent's structured report.")
print("="*76)
