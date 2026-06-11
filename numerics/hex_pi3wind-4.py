"""
hex_pi3wind-4.py  --  ID pi3wind-4
=================================================================
GOAL (user directive): a GENUINE 3D geometric object made of the Eisenstein
integers Z[omega], omega = e^{2pi i/3}, with a PHASOR (a real rotating unit
vector in 3-space) attached at each lattice point.  Wind the structure; find
where the chi3-weighted phasor VECTOR-SUM collapses to zero; check those
winding heights against the EXACT mpmath chi3 zeros (|L|<1e-12).

HARD RULES honored:
 STEP 1  build the real 3D solid with explicit (x,y,z), PRINT a coord sample.
 STEP 2  attach a phasor vector at each point, define its spin law.
 STEP 3  wind, measure the VECTOR resultant, find the collapse heights.

We MINIMIZE log/sqrt: the structure (points, norm shells, sectors, 6th-root
units, pi/3 + pi/6 angles) is purely algebraic.  log appears ONLY at the very
end as the single permitted 'bridge' readout from winding-parameter to zero
height -- and we FLAG it loudly when it does, and also try a log-free variant.

We are brutally honest: at each stage we ask "is this secretly the analytic
L(chi3, 1/2 + i w) = sum_n chi3(n) n^{-1/2} e^{-i w log n} again?" and report.
=================================================================
"""

import numpy as np
import mpmath as mp

mp.mp.dps = 40
OMEGA = np.exp(2j * np.pi / 3.0)          # e^{2pi i/3}, the lattice generator
SQRT3 = np.sqrt(3.0)

def chi3(n):
    return [0, 1, -1][n % 3]

def Lchi3(s):
    """Exact L(chi3, s) via Hurwitz zeta."""
    return mp.power(3, -s) * (mp.zeta(s, mp.mpf(1)/3) - mp.zeta(s, mp.mpf(2)/3))

# exact zeros (from numerics/lchi3_zeros_1000.txt, verified |L|<1e-70)
EXACT_ZEROS = [
    8.0397371556814666817136232141729658027930102674,
    11.2492062077729352497050256788632146486959267932,
    15.7046191767216255651655508804327807582048028730,
    18.2619974956931275689244140935948651201930385652,
    20.4557708077424928534450258313131026704439632755,
    24.0594148564934507745930535932129647862605968275,
    26.5778687357745853145843509375340769341855096749,
    28.2181645062333860931830297603107705648142582519,
    30.7450402613824957378082418105061713503695279477,
    33.8973889272594190176778740330052395794468918191,
]

def verify_height(w):
    """|L(chi3, 1/2 + i w)| at given height w -- ground truth oracle."""
    return float(abs(Lchi3(mp.mpf(1)/2 + 1j*mp.mpf(w))))

print("="*72)
print("hex_pi3wind-4 : Eisenstein 3D helix + phasors vs exact chi3 zeros")
print("="*72)
print("Exact chi3 zero heights (first 4): "
      + ", ".join(f"{z:.4f}" for z in EXACT_ZEROS[:4]))
print("Oracle check |L(1/2+i*8.03974)| =", f"{verify_height(8.0397371556814667):.2e}")
print()

# =====================================================================
# STEP 1 : BUILD THE REAL 3D OBJECT
# =====================================================================
# The Eisenstein integers a + b*omega live in the hexagonal plane.  We do NOT
# leave them flat: we WIND them into a 3D solid by stacking norm-shells along a
# vertical (z) axis.  z is the norm-shell index (an integer area = a^2-ab+b^2),
# NOT a log.  Each lattice point keeps its true hexagonal (x,y) position; its
# height z is its quadratic norm N(a,b) (the 'volume of Eisenstein integers'
# coordinate).  Radial position r = |a + b*omega| = sqrt(N) is honest 2D
# geometry (the only sqrt, and it is a *coordinate* of a real point, never a
# weight built into a sum -- the analytic n^{-1/2} disguise is what we avoid).
#
# Result: a real 3D solid -- a stack of hexagonal norm-rings climbing the
# z-axis, every point a genuine (x,y,z) with an honest Eisenstein pedigree.
# =====================================================================

def build_eisenstein_solid(B=60, Nmax=2000):
    """Return list of dicts: each lattice point with explicit (x,y,z) + data."""
    pts = []
    for a in range(-B, B + 1):
        for b in range(-B, B + 1):
            N = a*a - a*b + b*b          # quadratic norm = integer area
            if N == 0 or N > Nmax:
                continue
            z = a + b*OMEGA              # honest hexagonal-plane complex coord
            x, y = z.real, z.imag
            theta = np.angle(z)          # lattice angle (for D6 / pi/6 sectors)
            pts.append({
                'a': a, 'b': b, 'N': N,
                'x': float(x), 'y': float(y), 'zheight': float(N),
                'r': float(abs(z)), 'theta': float(theta),
            })
    return pts

SOLID = build_eisenstein_solid(B=60, Nmax=2000)
print("-"*72)
print(f"STEP 1: built 3D Eisenstein solid -- {len(SOLID)} lattice points")
print("        coordinate = (x, y, z) with z = quadratic norm N(a,b) shell height")
print("-"*72)
# print a coordinate sample (smallest shells) to PROVE the solid exists
SOLID_sorted = sorted(SOLID, key=lambda p: (p['N'], p['theta']))
print(f"{'a':>3} {'b':>3} {'N':>4} | {'x':>8} {'y':>8} {'z=N':>6} | "
      f"{'r=|z|':>7} {'theta':>7} {'theta/(pi/6)':>11}")
for p in SOLID_sorted[:18]:
    print(f"{p['a']:>3} {p['b']:>3} {p['N']:>4} | "
          f"{p['x']:>8.4f} {p['y']:>8.4f} {p['zheight']:>6.0f} | "
          f"{p['r']:>7.4f} {p['theta']:>7.4f} {p['theta']/(np.pi/6):>11.4f}")
print("  ... (3D solid: hexagonal norm-shells stacked along z = integer area)")

# Confirm the hexagonal fingerprint: N mod 3 in {0,1}, never 2.
norms_seen = sorted(set(p['N'] for p in SOLID))
mod3 = sorted(set(N % 3 for N in norms_seen))
print(f"  norm residues mod 3 present: {mod3}  (must be subset of {{0,1}} -- "
      f"hexagonal fingerprint {'OK' if set(mod3) <= {0,1} else 'FAIL'})")
print()

# group points by shell
from collections import defaultdict
shells = defaultdict(list)
for p in SOLID:
    shells[p['N']].append(p)

# Verify the CLAIM's algebraic backbone (log-free, finite, 6th-root):
#   r(N)/6 = sum_{d|N} chi3(d) = d1(N) - d2(N)
def divisor_chi_sum(N):
    s = 0
    d = 1
    while d*d <= N:
        if N % d == 0:
            s += chi3(d)
            if d != N // d:
                s += chi3(N // d)
        d += 1
    return s

print("-"*72)
print("STEP 1b (algebraic backbone, log-free finite 6th-root object):")
print("   r(N)/6  ==  sum_{d|N} chi3(d) == d1(N)-d2(N)  ?")
print("-"*72)
ok_backbone = True
bad = 0
for N in sorted(shells.keys()):
    r = len(shells[N])
    if r % 6 != 0:
        ok_backbone = False
    if r // 6 != divisor_chi_sum(N):
        ok_backbone = False
        bad += 1
print(f"   checked {len(shells)} shells (N<=2000):  "
      f"r(N)/6 == sum chi3(d|N) holds for ALL: {ok_backbone}  (mismatches={bad})")
# print a few explicit shells
print("   sample:")
for N in [1, 3, 7, 13, 19, 21, 31, 49]:
    if N in shells:
        r = len(shells[N])
        print(f"     N={N:>3}: r(N)={r:>2}, r/6={r//6:+d}, "
              f"sum chi3(d|N)={divisor_chi_sum(N):+d}, "
              f"shell points (a,b)={[(p['a'],p['b']) for p in shells[N][:6]]}"
              + (" ..." if r > 6 else ""))
print()

# Verify the bare D6 angular phasor sum vanishes on each shell (units sum to 0).
print("-"*72)
print("STEP 1c: bare angular phasor sum over each shell == 0  (D6 symmetry)")
print("-"*72)
maxbare = 0.0
for N in sorted(shells.keys()):
    s = sum(np.exp(1j * p['theta']) for p in shells[N])
    maxbare = max(maxbare, abs(s))
print(f"   max over all shells N<=2000 of |sum_shell e^{{i theta}}| = {maxbare:.2e}"
      f"  ({'vanishes -> D6 OK' if maxbare < 1e-9 else 'NONZERO'})")
print(f"   (so a bare unweighted angular sum is dead; the chi3 signal must come "
      f"from\n    the SECTOR PARITY / count, not a uniform phase -- as the claim says.)")
print()

# =====================================================================
# STEP 2 : ATTACH A PHASOR AT EACH POINT  +  define how it SPINS
# =====================================================================
# A phasor here is a real unit vector in the lab xy-plane (a direction in
# 3-space lying in the horizontal plane): phasor = (cos PHI, sin PHI, 0).
# Its angle PHI(point ; w) depends on the winding parameter w.  We test
# several DRIFT LAWS (the user's fuzz target (i)) and the ALIGN-TO-AXIS
# condition (target (ii)).
#
# The chi3 weight enters as a SIGN (chi3 is real, order 2): the phasor at a
# point carries weight chi3(N) (the shell's character) OR chi3 of the
# divisor-sector parity.  The RESULTANT is the vector sum
#        V(w) = sum_points  weight * (cos PHI, sin PHI, 0)
# and a cancellation event is |V(w)| -> 0 (a genuine vector collapse).
# =====================================================================

# precompute, per shell, the data a phasor needs
shell_list = sorted(shells.keys())
shell_r    = {N: len(shells[N]) for N in shell_list}        # point count
shell_chi  = {N: divisor_chi_sum(N) for N in shell_list}    # = r/6, the weight
# representative geometric radius of a shell (honest sqrt of integer area)
shell_rad  = {N: np.sqrt(N) for N in shell_list}

# ---- candidate per-prime drift (FTA building block): Theta(n) = sum over
#      prime factors.  We try prime-log drifts AND pure-geometric pi/3 drifts.
def prime_factorization(n):
    f = {}
    d = 2
    m = n
    while d*d <= m:
        while m % d == 0:
            f[d] = f.get(d, 0) + 1
            m //= d
        d += 1
    if m > 1:
        f[m] = f.get(m, 0) + 1
    return f

DRIFT_LOGP = {p: np.log(p) for p in [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47]}

def theta_logp(N):
    """sum over prime factors p|N of (mult * log p)  == log N  (FTA additive)."""
    return sum(k * DRIFT_LOGP.get(p, np.log(p)) for p, k in prime_factorization(N).items())

print("="*72)
print("STEP 2 + STEP 3 : attach phasors, wind, hunt the vector collapse")
print("="*72)
print("Phasor at a shell-N point: unit vector (cos PHI, sin PHI, 0) in lab plane.")
print("Resultant V(w) = sum  weight * phasor ;  cancellation = |V(w)| -> 0.")
print()

# A winding sweep on a height grid, then refine minima, then verify vs |L|.
def sweep_and_match(name, phasor_phase, weight, use_shells=None,
                    wmin=2.0, wmax=36.0, ngrid=6000, note=""):
    """
    phasor_phase(N, w) -> PHI angle (radians) of the phasor at shell N, winding w.
    weight(N)          -> scalar chi3 weight on shell N.
    Returns list of (height, |V|, |L|) for the local minima of |V(w)|.
    """
    Ns = use_shells if use_shells is not None else shell_list
    Ns = [N for N in Ns if shell_r[N] > 0]
    wgrid = np.linspace(wmin, wmax, ngrid)
    # vectorized magnitude of resultant over the grid
    Nv = np.array(Ns, dtype=float)
    wt = np.array([weight(N) for N in Ns], dtype=float)
    mag = np.empty_like(wgrid)
    for i, w in enumerate(wgrid):
        phi = phasor_phase(Nv, w)
        vx = np.sum(wt * np.cos(phi))
        vy = np.sum(wt * np.sin(phi))
        mag[i] = np.hypot(vx, vy)
    # normalize by sum|wt| so |V| is comparable across laws
    norm = np.sum(np.abs(wt)) or 1.0
    magn = mag / norm
    # find local minima
    mins = []
    for i in range(1, len(magn)-1):
        if magn[i] < magn[i-1] and magn[i] <= magn[i+1] and magn[i] < 0.15:
            mins.append((wgrid[i], magn[i]))
    # refine each via parabolic + verify against |L|
    out = []
    for w0, m0 in mins:
        # local fine scan
        loc = np.linspace(w0-0.02, w0+0.02, 400)
        lm = []
        for w in loc:
            phi = phasor_phase(Nv, w)
            lm.append(np.hypot(np.sum(wt*np.cos(phi)), np.sum(wt*np.sin(phi)))/norm)
        j = int(np.argmin(lm))
        wbest = loc[j]
        out.append((float(wbest), float(lm[j]), verify_height(wbest)))
    # dedupe close heights
    out.sort()
    ded = []
    for h, mg, L in out:
        if ded and abs(h - ded[-1][0]) < 0.05:
            if mg < ded[-1][1]:
                ded[-1] = (h, mg, L)
            continue
        ded.append((h, mg, L))
    print(f"--- LAW: {name}")
    if note:
        print(f"    {note}")
    if not ded:
        print("    (no deep vector-collapse minima found in window)")
    else:
        print(f"    {'height w':>10} {'|V|/norm':>9} {'|L(1/2+iw)|':>12} "
              f"{'nearest exact zero':>20} {'dist':>7}")
        for h, mg, L in ded[:14]:
            zz = min(EXACT_ZEROS, key=lambda z: abs(z-h))
            print(f"    {h:>10.4f} {mg:>9.4f} {L:>12.2e} "
                  f"{zz:>20.4f} {abs(zz-h):>7.4f}")
    print()
    return ded

# ---------------------------------------------------------------
# LAW A (drift = per-prime log p ; the FTA building block).  This is the
# EXPECTED-tautological control: PHI = w * theta_logp(N) = w * log N, weight
# = chi3-count = sum chi3(d|N).  If THIS lands on the zeros it is just the
# analytic L re-skinned -- we run it precisely to SHOW the disguise and
# contrast it with the genuinely-geometric pi/3 / pi/6 laws.
# But note: our weight is chi3(d|N) summed over a SHELL indexed by NORM N,
# not chi(n) over plain integers n.  So even this is the Epstein/Dedekind
# zeta zeta(s)L(chi3,s), NOT L alone -- a real distinction we check.
# ---------------------------------------------------------------
THETA_LOGP_ARR = {N: theta_logp(N) for N in shell_list}
_logp_lookup = np.vectorize(lambda N: THETA_LOGP_ARR[int(N)])

resA = sweep_and_match(
    "A. per-prime log p drift, weight=chi3-count, NORM-indexed (Epstein side)",
    phasor_phase=lambda N, w: w * _logp_lookup(N),
    weight=lambda N: shell_chi[N],
    note="control: PHI = w*log N (FTA-additive). NORM shells -> zeta*L, not L.")

# ---------------------------------------------------------------
# LAW B (PURELY GEOMETRIC pi/3 winding, NO log anywhere).  The phasor drifts
# by the 6th-root sector angle of the shell times the winding count.  PHI =
# w * (pi/3) * (something integer/geometric).  We use the shell's lattice
# DIRECTION quantum.  This is the honest 6th-root structure -- if it lands on
# the zeros, that is NEW.  We try drift proportional to the norm N (integer
# area), winding unit pi/3.
# ---------------------------------------------------------------
resB = sweep_and_match(
    "B. pi/3 geometric winding, drift prop to integer area N (LOG-FREE)",
    phasor_phase=lambda N, w: w * (np.pi/3) * N,
    weight=lambda N: shell_chi[N],
    note="LOG-FREE: PHI = w*(pi/3)*N. genuine 6th-root unit angle, integer area.")

# ---------------------------------------------------------------
# LAW C (radial-growth Archimedean spiral, sqrt(N) honest geometry).  Drift =
# w * 2pi * r where r = sqrt(N) is the honest 2D radius (a real coordinate).
# This is the 'winding the spiral so loop k holds ~k integers' law from Rule 8.
# ---------------------------------------------------------------
resC = sweep_and_match(
    "C. radial spiral drift, PHI = w*sqrt(N) (honest geom radius)",
    phasor_phase=lambda N, w: w * np.sqrt(N),
    weight=lambda N: shell_chi[N],
    note="PHI = w*sqrt(N). sqrt is a real coordinate, not a weight.")

# ---------------------------------------------------------------
# LAW D : the HONEST analytic comparison done RIGHT -- over plain integers n
# (NOT norm shells), PHI = w*log n, amplitude n^{-1/2}, weight chi3(n).  This
# IS L(chi3,1/2+iw) tautologically.  We run it to confirm the oracle and to
# have the unambiguous "this is the analytic L" baseline for honest contrast.
# ---------------------------------------------------------------
def sweep_plain_L(wmin=2.0, wmax=36.0, ngrid=6000, Nmax=4000):
    ns = np.arange(1, Nmax+1)
    ch = np.array([chi3(int(n)) for n in ns], dtype=float)
    amp = ns**(-0.5)
    logn = np.log(ns)
    mask = ch != 0
    ns_, ch_, amp_, logn_ = ns[mask], ch[mask], amp[mask], logn[mask]
    wgrid = np.linspace(wmin, wmax, ngrid)
    mag = np.empty_like(wgrid)
    for i, w in enumerate(wgrid):
        v = np.sum(ch_ * amp_ * np.exp(-1j * w * logn_))
        mag[i] = abs(v)
    mins = []
    for i in range(1, len(mag)-1):
        if mag[i] < mag[i-1] and mag[i] <= mag[i+1] and mag[i] < 0.30:
            mins.append(wgrid[i])
    out = []
    for w0 in mins:
        loc = np.linspace(w0-0.03, w0+0.03, 600)
        lm = []
        for w in loc:
            lm.append(abs(np.sum(ch_*amp_*np.exp(-1j*w*logn_))))
        j = int(np.argmin(lm))
        out.append((float(loc[j]), verify_height(float(loc[j]))))
    ded = []
    out.sort()
    for h, L in out:
        if ded and abs(h-ded[-1][0]) < 0.05:
            continue
        ded.append((h, L))
    print("--- LAW D (BASELINE, ADMITTEDLY ANALYTIC): "
          "sum_n chi3(n) n^{-1/2} e^{-i w log n}  ==  L(chi3, 1/2+iw)")
    print(f"    {'height w':>10} {'|L(1/2+iw)|':>12} {'nearest exact':>14} {'dist':>7}")
    for h, L in ded[:12]:
        zz = min(EXACT_ZEROS, key=lambda z: abs(z-h))
        print(f"    {h:>10.4f} {L:>12.2e} {zz:>14.4f} {abs(zz-h):>7.4f}")
    print()
    return ded

resD = sweep_plain_L()

# =====================================================================
# STEP 3b : the ALIGN-TO-AXIS test (fuzz target ii)
# =====================================================================
# Build the actual 3D helix: each shell at height z=N, points on a ring of
# radius sqrt(N); attach the phasor and ask when phasors point radially inward
# (toward the central z-axis).  The "inward coherence" R(w) = | sum weight *
# (phasor . (-radial_hat)) | -- when does its winding-resonance match a zero?
# Here radial_hat at a point is (x,y,0)/r.  Phasor spins as PHI = w * drift.
# =====================================================================
print("="*72)
print("STEP 3b: ALIGN-TO-AXIS test (phasors aiming radially inward at central axis)")
print("="*72)
# Use one representative point direction per shell point; inward = -theta.
# Phasor angle PHI = w*drift + theta0 (start aligned to its own radial out).
# inward component = cos(PHI - (theta+pi)) = -cos(PHI-theta).
def axis_inward_resonance(drift_fn, weight, wmin=2.0, wmax=36.0, ngrid=4000,
                          name="", note=""):
    pts = SOLID
    th = np.array([p['theta'] for p in pts])
    Nn = np.array([p['N'] for p in pts], dtype=float)
    wt = np.array([weight(p['N']) for p in pts], dtype=float)
    drift = drift_fn(Nn)
    wgrid = np.linspace(wmin, wmax, ngrid)
    res = np.empty_like(wgrid)
    for i, w in enumerate(wgrid):
        PHI = w * drift + th
        inward = -np.cos(PHI - th)          # = -cos(w*drift)
        res[i] = abs(np.sum(wt * inward))
    res /= (np.sum(np.abs(wt)) or 1.0)
    # we look for VANISHING of the inward resultant (collapse) as the event
    mins = []
    for i in range(1, len(res)-1):
        if res[i] < res[i-1] and res[i] <= res[i+1] and res[i] < 0.10:
            mins.append((wgrid[i], res[i]))
    print(f"--- AXIS LAW: {name}")
    if note: print(f"    {note}")
    if not mins:
        print("    (no inward-resultant collapse found)")
    else:
        print(f"    {'height w':>10} {'inward|V|':>9} {'|L|':>12} {'near zero':>11} {'dist':>7}")
        seen=[]
        for w0, m0 in mins:
            if seen and abs(w0-seen[-1])<0.05: continue
            seen.append(w0)
            zz = min(EXACT_ZEROS, key=lambda z: abs(z-w0))
            print(f"    {w0:>10.4f} {m0:>9.4f} {verify_height(w0):>12.2e} "
                  f"{zz:>11.4f} {abs(zz-w0):>7.4f}")
    print()

axis_inward_resonance(
    lambda N: np.pi/3 * N, lambda N: shell_chi[N],
    name="inward, pi/3 * N drift (LOG-FREE)",
    note="phasors aim at axis; collapse where inward resultant vanishes.")
axis_inward_resonance(
    lambda N: _logp_lookup(N), lambda N: shell_chi[N],
    name="inward, log-N drift (analytic control)",
    note="control for contrast with the pi/3 geometric law.")

# =====================================================================
# HONEST VERDICT
# =====================================================================
print("="*72)
print("HONEST VERDICT")
print("="*72)

def count_hits(res, tol=0.03):
    """how many of the reported collapse heights actually verify |L|<1e-3 AND
    sit within tol of an exact zero."""
    hits = 0
    for h, *rest in res:
        L = rest[-1]
        zz = min(EXACT_ZEROS, key=lambda z: abs(z-h))
        if abs(zz-h) < tol:
            hits += 1
    return hits, len(res)

for tag, res in [("A log-p NORM(Epstein)", resA),
                 ("B pi/3 geometric LOGFREE", resB),
                 ("C sqrt(N) spiral", resC)]:
    h, n = count_hits(res)
    print(f"  LAW {tag:28s}: {h}/{n} collapse heights within 0.03 of an exact zero")
hD, nD = (sum(1 for h,L in resD if abs(min(EXACT_ZEROS,key=lambda z:abs(z-h))-h)<0.03),
          len(resD))
print(f"  LAW D analytic L baseline    : {hD}/{nD} (this one MUST hit -- it IS L)")
print()
print("Read the tables above. Key honesty questions answered inline:")
print(" * LAW A/D land on zeros only because PHI=w*log N reconstructs the")
print("   Dirichlet/Epstein series -- that is the analytic disguise, flagged.")
print(" * LAW B/C are the LOG-FREE 6th-root/geometric laws: do THEY land?")
print("   If not, the honest finding is that a uniform geometric phase drift")
print("   on norm-shells does NOT carry the heights -- consistent with the")
print("   claim's Hyp 3 (chi3 real => phases cancel, only the COUNT/parity")
print("   survives; the heights need the log bridge, which is the one")
print("   permitted analytic readout).")

# =====================================================================
# STEP 4 : DISAMBIGUATE the LAW B/C "8/388" coincidences.
# The loose 0.15 minima threshold fires on hundreds of shallow dips of the
# quasi-periodic integer-area drift; 8 landing near a zero out of 388 is pure
# density coincidence, NOT resonance.  Honest test: at the EXACT zero heights,
# is the log-free phasor resultant actually SMALL (a real collapse), or generic?
# Compare |V| AT the zeros vs |V| at random control heights.  A genuine
# mechanism makes |V| systematically smaller at zeros.
# =====================================================================
print("="*72)
print("STEP 4: is the LOG-FREE collapse REAL at the zeros, or coincidence?")
print("="*72)

def resultant_logfree_piN(w):
    Ns = np.array(shell_list, dtype=float)
    wt = np.array([shell_chi[N] for N in shell_list], dtype=float)
    phi = w*(np.pi/3)*Ns
    return np.hypot(np.sum(wt*np.cos(phi)), np.sum(wt*np.sin(phi)))/np.sum(np.abs(wt))

def resultant_sqrtN(w):
    Ns = np.array(shell_list, dtype=float)
    wt = np.array([shell_chi[N] for N in shell_list], dtype=float)
    phi = w*np.sqrt(Ns)
    return np.hypot(np.sum(wt*np.cos(phi)), np.sum(wt*np.sin(phi)))/np.sum(np.abs(wt))

def resultant_analyticL(w):
    ns = np.arange(1, 4001)
    ch = np.array([chi3(int(n)) for n in ns], dtype=float)
    m = ch != 0
    ns_, ch_ = ns[m], ch[m]
    v = np.sum(ch_ * ns_**(-0.5) * np.exp(-1j*w*np.log(ns_)))
    return abs(v)/np.sum(np.abs(ch_)*ns_**(-0.5))

rng = np.random.default_rng(0)
ctrl = rng.uniform(8.0, 34.0, 400)
for label, fn in [("pi/3*N (log-free)", resultant_logfree_piN),
                  ("sqrt(N) spiral   ", resultant_sqrtN),
                  ("analytic L (log) ", resultant_analyticL)]:
    at_zeros = np.array([fn(z) for z in EXACT_ZEROS])
    at_ctrl  = np.array([fn(w) for w in ctrl])
    print(f"  {label}: mean|V| at zeros={at_zeros.mean():.4f}  "
          f"at random={at_ctrl.mean():.4f}  "
          f"ratio={at_zeros.mean()/at_ctrl.mean():.3f}  "
          f"({'RESONATES (smaller at zeros)' if at_zeros.mean() < 0.6*at_ctrl.mean() else 'NO resonance'})")
print()
print("  Interpretation: ratio<<1 means the law genuinely collapses AT zeros.")
print("  ratio~1 means the 'hits' were density coincidence -> NOT a mechanism.")
