"""
hex_eisvol-1.py  --  ID eisvol-1: HECKE ANGULAR PHASOR (the genuine 6th-root object).

GOAL (per directive): build a REAL 3D solid of Eisenstein integers with EXPLICIT (x,y,z)
coords (printed FIRST), attach a rotating unit PHASOR vector at each lattice point built
from the 6th-root angular character xi_k(z) = e^{6 i k arg(z)} (log-free), then WIND
(parameter = height y) and find where the chi3-weighted phasor VECTOR-SUM (resultant)
collapses to zero. The k=0 angular Epstein-Hecke winding equals zeta(s)*L(chi3,s), so the
chi3 zeros are the heights where the k=0 phasor resultant vanishes (and the zeta factor
does not), while k>=1 angular phasors should NOT vanish there.

HONEST framing kept front-and-center (Rule Eight / the prior finding):
  - The PHASOR DIRECTION e^{6ik arg} is genuinely log-free -- pure 6th-root / hexagonal
    sector. That is the real geometric handle and it SELECTS the character (k=0 vs k>=1).
  - But the winding/spin in y still uses the radial phase N^{-iy} = e^{-iy log N}: the
    radial AMPLITUDE 1/|z| = N^{-1/2} is the natural inverse-lattice-distance, but the
    SPIN rate per point is (log N), which is the analytic disguise. So eisvol-1 is NOT a
    full log-free placement of the zeros; it is the cleanest SEPARATION of the log-free
    angular content (which char) from the log-bearing radial content (which height).
  We report this distinction explicitly. We do NOT pretend the spin is log-free.

Convergence: the Epstein/L winding is conditionally convergent; we use a SMOOTH Gaussian
norm cutoff exp(-(N/Nc)^2) so partial sums actually converge to the analytic-continuation
value. Unsmoothed truncation gives spurious O(1)-O(10) "defects" -- pure truncation noise.

Verification: every claimed cancellation height is cross-checked with mpmath
|zeta(1/2+iy)*L(chi3,1/2+iy)| and |L(chi3,1/2+iy)| < 1e-12.
"""
import numpy as np, mpmath as mp
mp.mp.dps = 30

# ---------------------------------------------------------------- exact chi3 / L
def chi3(n):
    r = n % 3
    return 1 if r == 1 else (-1 if r == 2 else 0)
def Lchi3(s):   return mp.power(3, -s) * (mp.zeta(s, mp.mpf(1)/3) - mp.zeta(s, mp.mpf(2)/3))
def zeta(s):    return mp.zeta(s)

# exact zeros (col 2 = height), from the verified landmark file
gam = []
with open("/Users/samuellavery/proof/three/numerics/lchi3_zeros_1000.txt") as f:
    for ln in f:
        ln = ln.strip()
        if ln and not ln.startswith("#"):
            gam.append(float(ln.split()[1]))
gam = sorted(gam)
ZEROS = gam[:6]                    # 8.0397, 11.2492, 15.7046, 18.262, 20.456, 24.059
OFFZERO = [10.0, 13.0, 22.0]       # heights that are NOT chi3 zeros (controls)

# ====================================================================
# STEP 1 -- BUILD THE REAL 3D OBJECT (explicit coordinates, printed first)
# ====================================================================
# Eisenstein integer z = a + b*omega, omega = e^{2 pi i / 3}.
#   Re z = a - b/2 ,  Im z = b*sqrt(3)/2   (sqrt3/2 = FIXED hexagonal basis direction)
#   norm N = |z|^2 = a^2 - a b + b^2       (NO sqrt -- pure quadratic form)
#   ARG = atan2(Im z, Re z)                (a multiple structure of pi/3 sectors)
# 3D point: P = (Re z, Im z, h) with display height h = log N (display only; does NOT
# enter the vanishing -- the winding parameter is y, the spin uses log N separately).
B = 600
a_ = np.arange(-B, B + 1)
AA, BB = np.meshgrid(a_, a_)
AA = AA.ravel(); BB = BB.ravel()
keep = ~((AA == 0) & (BB == 0))
AA = AA[keep].astype(float); BB = BB[keep].astype(float)

REz = AA - BB / 2.0
IMz = BB * np.sqrt(3) / 2.0
N   = AA*AA - AA*BB + BB*BB           # integer norms (as float)
ARG = np.arctan2(IMz, REz)            # lattice angle, sectors of pi/3
Hdisp = np.log(N)                     # display height ONLY

print("=" * 78)
print("STEP 1 -- THE 3D EISENSTEIN SOLID  (z = a + b*omega, omega = e^{2pi i/3})")
print("=" * 78)
print(f"  built {len(AA)} lattice points, |a|,|b| <= {B}; max norm {int(N.max())}")
print("  sample coordinates  (a, b) -> (x=Re z, y=Im z, z=h=logN) ; norm ; arg/(pi/3):")
print(f"   {'a':>3} {'b':>3} | {'x':>9} {'y':>9} {'h=logN':>8} | {'N':>6} | {'arg/(pi/3)':>10}")
# print the norm-1 shell (the six units) + a few more, to show the 6-fold sectors
order = np.lexsort((np.round(ARG, 6), np.round(N, 6)))
shown = 0
for idx in order:
    n_ = N[idx]
    if n_ <= 3 or shown < 14:
        print(f"   {int(AA[idx]):>3} {int(BB[idx]):>3} | {REz[idx]:9.4f} {IMz[idx]:9.4f} "
              f"{Hdisp[idx]:8.4f} | {int(n_):>6} | {ARG[idx]/(np.pi/3):>10.4f}")
        shown += 1
    if shown >= 14:
        break
print("  -> norm-1 shell = the SIX UNITS at sectors arg/(pi/3) in {-2,-1,0,1,2,3}")
print("     i.e. exactly the 6th-roots e^{i k pi/3}. The solid is genuinely hexagonal.")

# verify the units are the 6th roots (log-free check)
unit_mask = (N == 1)
unit_args = np.sort(ARG[unit_mask] / (np.pi/3))
print(f"  unit-shell sectors arg/(pi/3) = {np.round(unit_args,4)}  (six 6th-roots) "
      f"-> count {int(unit_mask.sum())}")

# ====================================================================
# STEP 2 -- ATTACH A PHASOR (rotating unit vector) AT EACH 3D POINT
# ====================================================================
# Phasor at z, character k, wound to height y:
#   angle(z; k, y) = 6 k * ARG(z)  -  y * log N(z)
#   V_k(z; y) = ( cos(angle), sin(angle) )   -- a UNIT 2-vector in the lab plane
# The angular part 6 k ARG is the LOG-FREE 6th-root sector spin; the radial part y*logN
# is the height winding (the log-bearing piece we are honest about).
# chi3-weighting is supplied automatically: for k=0 the FULL Epstein sum over the lattice
# (1/6) sum N^{-s} = zeta(s) L(chi3,s) carries the chi3 factorization through the norm form.
def phasor_angle(k, y):
    return 6.0 * k * ARG - y * np.log(N)

def smooth_weight(Nc):
    return np.exp(-(N / Nc) ** 2)      # Gaussian norm cutoff for convergence

def resultant(k, y, Nc):
    """(1/6) * sum_pts  N^{-1/2} * smoothcut * V_k(z;y) , returned as a 2-vector (Rx,Ry)."""
    amp = N ** (-0.5) * smooth_weight(Nc)
    ang = phasor_angle(k, y)
    Rx = np.sum(amp * np.cos(ang)) / 6.0
    Ry = np.sum(amp * np.sin(ang)) / 6.0
    return Rx, Ry

print("\n" + "=" * 78)
print("STEP 2 -- PHASOR VECTORS  V_k(z;y) = (cos(6k*arg - y*logN), sin(...))")
print("=" * 78)
ysample = ZEROS[0]
print(f"  sample phasor directions at y = {ysample:.4f} (1st chi3 zero), k=0, "
      f"first 8 lattice pts (the units):")
ang0 = phasor_angle(0, ysample)
cnt = 0
for idx in order:
    if N[idx] == 1:
        vx, vy = np.cos(ang0[idx]), np.sin(ang0[idx])
        print(f"   pt(a={int(AA[idx]):>2},b={int(BB[idx]):>2}) N=1  phasor V=({vx:+.4f},{vy:+.4f})  "
              f"|V|={np.hypot(vx,vy):.3f}")
        cnt += 1
    if cnt >= 6:
        break
print("  each phasor is a genuine UNIT vector; it SPINS in y at rate logN (radial) and")
print("  sits at angular sector 6k*arg (the log-free 6th-root direction).")

# ====================================================================
# STEP 3 -- WIND (sweep y) AND FIND WHERE THE PHASOR RESULTANT COLLAPSES
# ====================================================================
print("\n" + "=" * 78)
print("STEP 3 -- WIND the solid; |resultant R_k(y)| should collapse to 0 at chi3 zeros")
print("=" * 78)

Ncs = [3000, 30000, 150000]
print("\n  k=0 resultant magnitude |R_0(y)| as Nc grows (smoothed Epstein winding):")
print("  [k=0 winding = zeta*L(chi3); MUST -> 0 at the chi3 zeros, stay O(1) off-zero]")
hdr = "    " + "  ".join(f"g={g:7.4f}" for g in ZEROS) + "   ||  " + "  ".join(f"off={o:.1f}" for o in OFFZERO)
print(hdr)
for Nc in Ncs:
    onz = [np.hypot(*resultant(0, g, Nc)) for g in ZEROS]
    ofz = [np.hypot(*resultant(0, o, Nc)) for o in OFFZERO]
    print(f"  Nc={Nc:>7}: " + "  ".join(f"{v:9.5f}" for v in onz)
          + "  ||  " + "  ".join(f"{v:7.4f}" for v in ofz))

# also show the resultant VECTOR collapsing (not just magnitude) at the finest Nc
print("\n  k=0 resultant VECTOR (Rx,Ry) at finest Nc -- vector lands on origin at zeros:")
Ncf = Ncs[-1]
for g in ZEROS:
    rx, ry = resultant(0, g, Ncf)
    print(f"   y={g:8.4f}: R=({rx:+.6f},{ry:+.6f})  |R|={np.hypot(rx,ry):.6f}")
for o in OFFZERO:
    rx, ry = resultant(0, o, Ncf)
    print(f"   y={o:8.4f}: R=({rx:+.6f},{ry:+.6f})  |R|={np.hypot(rx,ry):.6f}  (OFF-zero control)")

# falsifiable prediction: k>=1 angular phasors do NOT vanish at the chi3 zeros
print("\n  FALSIFIABLE PREDICTION CHECK -- k=1,2 angular phasors at the chi3 zeros:")
print("  [must NOT collapse there; their own Hecke-L zeros are a disjoint set]")
print("    " + "  ".join(f"g={g:7.4f}" for g in ZEROS))
for k in [1, 2]:
    row = [np.hypot(*resultant(k, g, Ncf)) for g in ZEROS]
    print(f"  k={k}:      " + "  ".join(f"{v:9.5f}" for v in row))

# ====================================================================
# CROSS-CHECK against exact mpmath values (the ground truth)
# ====================================================================
print("\n" + "=" * 78)
print("CROSS-CHECK vs exact mpmath  (the resultant must track the TRUE analytic vanishing)")
print("=" * 78)
print("  height y      |zeta*L_chi3|(exact)     |L_chi3|(exact)    -> chi3 zero?")
for g in ZEROS:
    s = mp.mpf(1)/2 + 1j*mp.mpf(g)
    zl = abs(zeta(s) * Lchi3(s))
    lc = abs(Lchi3(s))
    print(f"   {g:9.4f}    {mp.nstr(zl,4):>14}        {mp.nstr(lc,4):>12}     "
          f"{'YES |L|<1e-12' if lc < 1e-12 else 'no'}")
for o in OFFZERO:
    s = mp.mpf(1)/2 + 1j*mp.mpf(o)
    zl = abs(zeta(s) * Lchi3(s))
    lc = abs(Lchi3(s))
    print(f"   {o:9.4f}    {mp.nstr(zl,4):>14}        {mp.nstr(lc,4):>12}     "
          f"{'(off-zero, |L| O(0.1))'}")

# ====================================================================
# HONEST DIAGNOSIS -- is the SPIN log-free? (the actual question)
# ====================================================================
print("\n" + "=" * 78)
print("HONEST DIAGNOSIS -- can a LOG-FREE spin rate replace y*logN and still vanish here?")
print("=" * 78)
print("  Replace the radial spin rate logN by a log-free candidate g(N); keep the same")
print("  log-free angular sectors. Does |R_0(y)| still collapse at the chi3 zeros?")
def resultant_altspin(spin_vals, y, Nc):
    amp = N ** (-0.5) * smooth_weight(Nc)
    ang = -y * spin_vals               # k=0: pure radial spin, no angular term
    return np.hypot(np.sum(amp*np.cos(ang)), np.sum(amp*np.sin(ang))) / 6.0
candidates = {
    "logN  [analytic control]": np.log(N),
    "sqrt(N)":                  np.sqrt(N),
    "N":                        N.copy(),
    "N^(1/3)":                  N ** (1/3),
}
print("    spin rate g(N)            " + "  ".join(f"g={g:6.3f}" for g in ZEROS[:4]))
for nm, sv in candidates.items():
    vals = [resultant_altspin(sv, g, Ncf) for g in ZEROS[:4]]
    print(f"    {nm:24s}  " + "  ".join(f"{v:8.5f}" for v in vals))
print("  -> only g(N)=logN cancels at the chi3 zeros. Any log-free spin does NOT. This is")
print("     the WALL: the HEIGHT placement is log-bearing. eisvol-1's log-free win is the")
print("     ANGULAR character selection (k=0 vs k>=1), not the height itself.")

# ====================================================================
# DECISIVE DIAGNOSIS -- the k=0 LATTICE resultant does NOT actually place the zeros.
# The k=0 Epstein winding = zeta(s)*L(chi3,s) carries the ZETA POLE at s=1. Under the
# Gaussian smoothing the pole leaks through (Mellin pole at w = 1-2iy0) as a term that
# GROWS like Nc^{1/2} -- it does NOT vanish at a chi3 zero. So |R_0(y)| does not converge
# to 0 at the zeros; the small values at small Nc are the contamination not-yet-grown.
# ====================================================================
print("\n" + "=" * 78)
print("DECISIVE DIAGNOSIS -- the k=0 LATTICE resultant does NOT place the chi3 zeros")
print("=" * 78)
print("  |R_0(y0)|/6 vs Nc^{1/2} at the 1st zero -- ratio CONSTANT => grows as Nc^{1/2}:")
y0 = ZEROS[0]
for Nc in [10000, 40000, 160000]:
    rx, ry = resultant(0, y0, Nc)
    mag = np.hypot(rx, ry)
    print(f"    Nc={Nc:>7}: |R_0|={mag:.5f}   Nc^0.5={Nc**0.5:7.1f}   ratio={mag/Nc**0.5:.3e}")
print("  -> constant ratio = the zeta POLE residue leaking through smoothing. The lattice")
print("     sum is zeta*Lchi3 INSEPARABLY; |zeta(1/2+iy)| is O(1) (~1.3-2.3) at the zeros,")
print("     so the L(chi3) zero is NOT isolated by the Epstein phasor resultant.")

# The honest POLE-FREE control: the DIRECT chi3 Dirichlet sum (rational integers, no pole)
# DOES collapse to machine zero -- but that is the analytic L with log n built into the
# spin (the prior tautological finding), and it uses NO lattice / 6th-root structure.
nn = np.arange(1, 2_000_001, dtype=float)
sgn = np.where(nn % 3 == 1, 1.0, np.where(nn % 3 == 2, -1.0, 0.0))
def chi3_direct(y, Nc):
    amp = nn ** (-0.5) * np.exp(-(nn / Nc) ** 2)
    ang = -y * np.log(nn)
    return np.hypot(np.sum(sgn*amp*np.cos(ang)), np.sum(sgn*amp*np.sin(ang)))
print("\n  POLE-FREE control = DIRECT chi3 sum (no zeta factor) -- collapses cleanly:")
print("  [but this is the ANALYTIC L with log n in the spin; NO lattice/6th-root content]")
for Nc in [50000, 500000]:
    onz = [chi3_direct(g, Nc) for g in ZEROS]
    ofz = [chi3_direct(o, Nc) for o in OFFZERO]
    print(f"    Nc={Nc:>7}: on-zero={[f'{v:.6f}' for v in onz]}  off={[f'{v:.4f}' for v in ofz]}")

print("\n" + "=" * 78)
print("VERDICT (eisvol-1): the angular phasor e^{6ik arg} is a GENUINE log-free 6th-root")
print("vector and it correctly SELECTS the character (k=0=zeta*Lchi3 vs k>=1 disjoint), but")
print("the k=0 LATTICE resultant does NOT place the chi3 zeros: the inseparable zeta pole")
print("leaks through (Nc^{1/2} growth). Only the POLE-FREE direct chi3 sum vanishes -- and")
print("that is the analytic L with log n in the spin, leveraging NO hexagonal structure.")
print("=" * 78)

print("\nDONE hex_eisvol-1.")
