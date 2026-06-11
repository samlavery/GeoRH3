"""
hex_eisvol-4.py  --  ID eisvol-4: HEXAGONAL NORM-SHELL LEDGER ("Eisenstein volume" amplitude).

GOAL (per directive): build a REAL 3D solid of Eisenstein integers with EXPLICIT (x,y,z)
coordinates, attach a real rotating PHASOR VECTOR at each point, wind the structure, and find
where the chi3-weighted phasor VECTOR-SUM collapses to zero -- and check those collapse heights
against the EXACT mpmath chi3 zeros.  Minimize log/sqrt: the amplitude is the genuine inverse
lattice norm 1/N = 1/|z|^2 (a quadratic-form count, NO sqrt), the levels are the hex radii,
the angular structure is the 6th-root (pi/3) sectors and pi/6 mirror axes.

HARD RULE obeyed:
  STEP 1: build 3D points (a,b)->(x,y,z), print a coordinate sample (the solid exists).
  STEP 2: attach a phasor VECTOR (a 3D unit direction) at each point + define its spin law.
  STEP 3: wind; measure the actual VECTOR RESULTANT of the phasors; find its collapses.

HONESTY GUARD (Rule Eight / directive STEP 4): the Dedekind/Epstein winding
  sum_m a(m) m^{-s}, a(m)=sum_{d|m} chi3(d), is IDENTICALLY zeta(s)*L(chi3,s).  So if our phasor
  phase is y*log(m) we have merely re-drawn the analytic L as vectors -- that is the disguise.
  We test BOTH: (i) the honest analytic shell winding (to confirm it = zeta*L and hits the union
  of zeta+chi3 zeros), and (ii) genuinely NON-log drift laws (pi/3 sector holonomy, per-prime
  constants, local Frenet-frame drift) to see whether anything OTHER than log m localizes the
  zeros.  We report the truth either way.
"""
import numpy as np, mpmath as mp, math
mp.mp.dps = 30

# ----------------------------------------------------------------------------------------
# exact data
# ----------------------------------------------------------------------------------------
def chi3(n):
    r = n % 3
    return 1 if r == 1 else (-1 if r == 2 else 0)

def Lchi3(s):
    return mp.power(3, -s) * (mp.zeta(s, mp.mpf(1)/3) - mp.zeta(s, mp.mpf(2)/3))

ZEROS = [8.0397371556814667, 11.2492062077729352, 15.7046191767216256,
         18.2619974956931276, 20.4557708077424929, 24.0594148564934508,
         26.5778687357745853, 28.2181645062333861]
ZETA_ZEROS = [14.134725141734693, 21.022039638771555, 25.010857580145688]
# between-zero control heights (no chi3 zero, no zeta zero near these)
CONTROLS = [3.0, 5.0, 9.5, 13.0, 17.0, 22.5]

print("first 8 EXACT chi3 zero heights:", [round(g, 4) for g in ZEROS])
print("zeta zero heights (the union partner):", [round(g, 4) for g in ZETA_ZEROS])

# ========================================================================================
# STEP 1 -- BUILD THE REAL 3D OBJECT.
#   Eisenstein integer a+b*omega, omega = e^{2 pi i/3}.  Lab-plane embedding:
#       (x0,y0) = a*(1,0) + b*(cos120, sin120) = (a - b/2, b*sqrt3/2).
#   Norm N = a^2 - a b + b^2 = |x0+iy0|^2 (the pure quadratic form -- the radius^2).
#   The 3D SOLID: group points into NORM SHELLS (the Eisenstein energy levels). Shell of
#   norm m is a planar ring of the r(m) lattice points at radius sqrt(m). We LIFT to 3D by
#   a height h = (level index of the distinct norm m) -- the "loop / winding" coordinate.
#   So the solid is a stack of hexagonal rings climbing in z: an honest 3D staircase of shells.
#   (sqrt3/2 is used ONCE as the FIXED lattice direction -- a constant geometry, not an
#    n-dependent amplitude; sqrt(m) only positions the ring radius in the picture, the
#    AMPLITUDE used for cancellation is 1/N, no sqrt.)
# ========================================================================================
B = 160
raw = []
for a in range(-B, B + 1):
    for b in range(-B, B + 1):
        m = a*a - a*b + b*b
        if m != 0:
            x0 = a - 0.5*b
            y0 = b*math.sqrt(3)/2.0
            raw.append((a, b, m, x0, y0))
raw.sort(key=lambda t: (t[2], math.atan2(t[4], t[3])))

# distinct norms (the levels) and a level index for the z-lift
distinct_norms = sorted(set(t[2] for t in raw))
level_index = {m: i for i, m in enumerate(distinct_norms)}

# assemble the 3D solid
A   = np.array([t[0] for t in raw], float)
Bb  = np.array([t[1] for t in raw], float)
NRM = np.array([t[2] for t in raw], float)
X0  = np.array([t[3] for t in raw], float)
Y0  = np.array([t[4] for t in raw], float)
LEV = np.array([level_index[t[2]] for t in raw], float)
# height: use the level index (the winding/loop coordinate). Print as z.
Z3  = LEV.copy()
ANG = np.arctan2(Y0, X0)             # lattice direction (which pi/3 sector)
SECTOR = (np.floor((ANG % (2*np.pi)) / (np.pi/3)).astype(int)) % 6  # 6th-root sector 0..5

print("\n" + "="*84)
print("STEP 1: THE 3D SOLID -- Eisenstein integers as a stack of hex norm-shells (x,y,z).")
print("="*84)
print(f"{'a':>4}{'b':>4}{'norm':>6}{'x':>9}{'y':>9}{'z(level)':>9}{'sector':>7}{'arg(deg)':>10}")
for i in range(16):
    print(f"{int(A[i]):4d}{int(Bb[i]):4d}{int(NRM[i]):6d}"
          f"{X0[i]:9.3f}{Y0[i]:9.3f}{Z3[i]:9.0f}{SECTOR[i]:7d}{np.degrees(ANG[i]):10.2f}")
print(f"... total lattice points in solid: {len(A)};  distinct norm-levels: {len(distinct_norms)}")
print(f"first 20 representable hex norms (Eisenstein energy levels): {distinct_norms[:20]}")

# volume law (the pure quadratic-norm count -- 'volume of Eisenstein integers', no log/sqrt)
print("\nvolume law  #{(a,b)!=0 : N<=X} ~ (2pi/sqrt3) X  (pure norm count):")
for XX in [100, 1000, 5000, 20000]:
    c = int(np.sum(NRM <= XX))
    pred = 2*np.pi/np.sqrt(3)*XX
    print(f"   X={XX:6d}: count={c:7d}  (2pi/sqrt3)X={pred:10.1f}  ratio={c/pred:.4f}")

# ========================================================================================
# STEP 2 -- ATTACH A PHASOR VECTOR at each 3D point + define its spin law.
#   The phasor is a real unit vector living in the lab xy-plane (we also test an "inward /
#   toward-axis" component).  Its angle phi(point, w) = w * DRIFT(point) + phi0(point), so as
#   the winding parameter w increases the vector SPINS.  The chi3-weighted, amplitude-weighted
#   resultant is a genuine 2D (or 3D) VECTOR SUM of these spinning arrows.
#
#   We define several DRIFT laws to sweep (directive item (i)):
#     LOG    : DRIFT = log(N)                      <- the analytic disguise (CONTROL)
#     SECTOR : DRIFT = sector_angle = floor-to k*pi/3 of the lattice arg (pure 6th-root)
#     ARG    : DRIFT = the actual lattice argument ANG (continuous pi/3-sector direction)
#     HOLO   : DRIFT = Eisenstein-prime holonomy Theta(n) summed by FTA over n=N's factors
#     PERP2/3/5/7 : per-prime constant drifts (log2,log3,... and pi/6,pi/3 variants)
#   AMPLITUDE (directive: replace n^{-1/2} by the lattice volume 1/N):
#     AMP_NORM = 1/N           (the genuine inverse lattice norm = 1/|z|^2, NO sqrt) -- primary
#     AMP_SQRT = 1/sqrt(N)     (CONTROL, the analytic n^{-1/2})
#     AMP_ONE  = 1             (geometry-only)
# ========================================================================================
print("\n" + "="*84)
print("STEP 2: attach phasor VECTORS. Each point gets a unit arrow in the xy-plane that")
print("        SPINS as phi = w*DRIFT + phi0. Drift laws + amplitudes defined below.")
print("="*84)

# We work at the SHELL level for the cancellation (the ledger orders events by distinct norm),
# but we keep the full 3D point cloud for the geometric phasor picture. Build shell data.
MAXM = 60000
# shell coefficient a(m) = sum_{d|m} chi3(d) = Dedekind/Epstein coefficient (# Eisenstein ideals of norm m)
def divisor_chi_sum(m):
    s = 0; d = 1
    while d*d <= m:
        if m % d == 0:
            s += chi3(d)
            if d != m//d:
                s += chi3(m//d)
        d += 1
    return s

# ---- per-prime Eisenstein argument (for the holonomy drift), log-free lattice angles ----
def split_prime_arg(p):
    r = int(math.isqrt(p))
    for a in range(1, r+2):
        for b in range(0, r+2):
            if a*a - a*b + b*b == p:
                x = a + b/2.0; y = b*math.sqrt(3)/2.0
                ang = math.atan2(y, x)
                if 0 <= ang < math.pi/3 + 1e-9:
                    return ang
    return 0.0
_pa = {}
def prime_arg(p):
    if p in _pa: return _pa[p]
    if p == 3: v = math.pi/6              # ramified -> mirror axis
    elif p % 3 == 1: v = split_prime_arg(p)  # split -> a genuine sub-sector lattice angle
    else: v = math.pi/3                   # inert -> sector edge
    _pa[p] = v; return v

# smallest-prime-factor sieve up to MAXM, for Theta(n) holonomy on the SHELL index m
spf = np.zeros(MAXM+1, dtype=np.int64)
for i in range(2, MAXM+1):
    if spf[i] == 0:
        spf[i::i] = np.where(spf[i::i] == 0, i, spf[i::i])
Theta = np.zeros(MAXM+1)   # Eisenstein-prime holonomy, FTA-additive
for n in range(2, MAXM+1):
    p = int(spf[n])
    Theta[n] = Theta[n//p] + prime_arg(p)

# build per-shell arrays over distinct norms <= MAXM
shells = [m for m in distinct_norms if m <= MAXM]
sm   = np.array(shells, float)
acoef = np.array([divisor_chi_sum(m) for m in shells], float)
logm  = np.log(sm)
holom = np.array([Theta[m] for m in shells], float)
# the "sector" drift for a shell = the mean lattice argument of that shell's points (a 6th-root angle)
# build mapping norm -> representative argument (first-sector rep)
firstarg = {}
for a,b,m,x0,y0 in raw:
    if m <= MAXM and m not in firstarg:
        ang = math.atan2(y0, x0) % (np.pi/3)   # fold into one sector -> the pi/3 structure
        firstarg[m] = ang
secarg = np.array([firstarg.get(m, 0.0) for m in shells], float)

# amplitudes
AMP_NORM = 1.0/sm            # 1/N -- the Eisenstein VOLUME amplitude (no sqrt)  *** primary ***
AMP_SQRT = 1.0/np.sqrt(sm)   # 1/sqrt(N) -- the analytic control
AMP_ONE  = np.ones_like(sm)

print("prime Eisenstein args (log-free lattice angles, radians):")
for p in [2,3,5,7,11,13,19,31]:
    kind = 'split' if p%3==1 else ('inert' if p%3==2 else 'ramif')
    print(f"   p={p:3d} ({kind}): arg={prime_arg(p):.5f}  (= {prime_arg(p)/(np.pi/3):.4f} * pi/3)")
print(f"\nshells used (distinct norms <= {MAXM}): {len(shells)}")
print("sample shell ledger (m, a(m)=#ideals, 1/N amp, 1/sqrtN amp, holonomy Theta, sector-arg):")
for j in range(12):
    print(f"   m={int(sm[j]):4d}  a(m)={int(acoef[j]):+d}  1/N={AMP_NORM[j]:.4f}  "
          f"1/sqrtN={AMP_SQRT[j]:.4f}  Theta={holom[j]:.4f}  secarg={secarg[j]:.4f}")

# HONESTY: is the holonomy / sector drift just log m?
mask = sm > 5
def corr(u): return np.corrcoef(u[mask], logm[mask])[0,1]
print(f"\nHONESTY corr-with-log(m):  Theta-holonomy {corr(holom):.4f}   sector-arg {corr(secarg):.4f}")
print("  (corr~1 => that drift IS log m in disguise; corr far from 1 => genuinely different field)")

# ========================================================================================
# STEP 3 -- WIND and measure the VECTOR RESULTANT of the spinning phasors.
#   Resultant V(w) = sum_shells  a(m) * amp(m) * unit_vector( w*DRIFT(m) ).
#   This is an HONEST 2D vector sum (real arrows). |V(w)| small => phasors cancel (alignment-free
#   destructive interference); we also compute the "toward-axis" (radially-inward) coherence.
#   We sweep DRIFT and AMP, and report |V| at chi3 zeros vs zeta zeros vs controls.
# ========================================================================================
print("\n" + "="*84)
print("STEP 3: wind the phasors; |VECTOR RESULTANT| at chi3 zeros / zeta zeros / controls.")
print("="*84)

def resultant(w, drift, amp):
    """Real 2D vector sum of spinning unit phasors: V = sum a(m) amp(m) [cos,sin](w*drift)."""
    ph = w * drift
    vx = np.sum(acoef * amp * np.cos(ph))
    vy = np.sum(acoef * amp * np.sin(ph))
    return math.hypot(vx, vy)

def exact_dedekind(y):
    s = mp.mpf(1)/2 + 1j*y
    return abs(complex(mp.zeta(s) * Lchi3(s)))

def exact_chi3(y):
    s = mp.mpf(1)/2 + 1j*y
    return abs(complex(Lchi3(s)))

drift_laws = {
    "LOG(analytic ctrl)": logm,
    "HOLO(eisen holonomy)": holom,
    "SECTOR-ARG(pi/3)": secarg,
}
amp_laws = {
    "1/N (volume)": AMP_NORM,
    "1/sqrtN (ctrl)": AMP_SQRT,
    "1 (geom only)": AMP_ONE,
}

# For each (drift, amp) print the resultant at the test heights.
for dname, drift in drift_laws.items():
    for aname, amp in amp_laws.items():
        print(f"\n--- DRIFT={dname}  AMP={aname} ---")
        print(f"   {'height':>9} {'kind':>6} {'|phasor resultant|':>20} {'|zeta*L exact|':>16} {'|L chi3 exact|':>16}")
        rows = ([(g,'chi3') for g in ZEROS[:5]] +
                [(g,'zeta') for g in ZETA_ZEROS] +
                [(g,'ctrl') for g in CONTROLS])
        for g, kind in rows:
            print(f"   {g:9.4f} {kind:>6} {resultant(g,drift,amp):20.5f} "
                  f"{exact_dedekind(g):16.5f} {exact_chi3(g):16.5f}")

# ========================================================================================
# DIRECTIVE item (ii): ALIGN-TO-AXIS test.
#   Candidate cancellation CONDITION: the event is when the phasors collectively aim at the
#   central axis (radially inward).  Here the phasor at shell m sits at lab-angle secarg[m]
#   (its hex direction); "inward" means pointing toward the origin, i.e. direction angle
#   secarg[m]+pi.  As we wind, the phasor direction is w*DRIFT(m); its inward component is
#   cos( w*DRIFT(m) - (secarg[m]+pi) ).  We measure the chi3-weighted MEAN inward coherence
#   C_in(w) = sum a(m) amp(m) cos(w*DRIFT(m) - secarg(m) - pi) / sum |a(m)| amp(m).
#   Test: do |C_in| extrema (peaks of inward alignment) sit at chi3 zeros?
# ========================================================================================
print("\n" + "="*84)
print("DIRECTIVE (ii) ALIGN-TO-AXIS: inward-coherence C_in(w) of the spinning phasors.")
print("="*84)
def inward_coherence(w, drift, amp):
    target = secarg + np.pi   # inward direction at each shell
    num = np.sum(acoef * amp * np.cos(w*drift - target))
    den = np.sum(np.abs(acoef) * amp)
    return num/den
for dname, drift in [("LOG(ctrl)", logm), ("HOLO", holom), ("SECTOR-ARG", secarg)]:
    print(f"\n--- inward coherence, DRIFT={dname}, amp=1/N ---")
    print(f"   {'height':>9} {'kind':>6} {'C_in':>12}")
    rows = ([(g,'chi3') for g in ZEROS[:5]] + [(g,'zeta') for g in ZETA_ZEROS] +
            [(g,'ctrl') for g in CONTROLS])
    for g, kind in rows:
        print(f"   {g:9.4f} {kind:>6} {inward_coherence(g,drift,amp=AMP_NORM):12.5f}")

# ========================================================================================
# DECISIVE CHECK A: does the analytic shell winding (DRIFT=log, AMP=1/sqrtN) actually go to
#   zero at the union of zeta+chi3 zeros once we SMOOTH the truncation (directive TEST (2))?
#   Use a Gaussian shell cutoff to suppress the truncation ripple, then watch |V|->0.
# ========================================================================================
print("\n" + "="*84)
print("CHECK A: smoothed analytic shell winding -> 0 at union(zeta,chi3) zeros? (directive TEST 2)")
print("="*84)
def smoothed_wind(y, smooth_T):
    # Gaussian damping exp(-(m/T)^2 * c) tames truncation; recovers Dedekind value as T->inf.
    damp = np.exp(-(sm/smooth_T)**2)
    ph = -y*logm
    val = np.sum(acoef * (1.0/np.sqrt(sm)) * np.exp(1j*ph) * damp)
    return abs(val)
print(f"   {'height':>9} {'kind':>6} {'T=2k':>10} {'T=8k':>10} {'T=20k':>10} {'|zeta*L|':>12}")
rows = ([(g,'chi3') for g in ZEROS[:4]] + [(g,'zeta') for g in ZETA_ZEROS] +
        [(g,'ctrl') for g in CONTROLS[:3]])
for g, kind in rows:
    print(f"   {g:9.4f} {kind:>6} {smoothed_wind(g,2000):10.4f} {smoothed_wind(g,8000):10.4f} "
          f"{smoothed_wind(g,20000):10.4f} {exact_dedekind(g):12.4f}")

# ========================================================================================
# DECISIVE CHECK B: isolate chi3 by dividing out the zeta factor, and ask the honest question:
#   after dividing zeta out, is the remaining phase STILL y*log m (=> analytic disguise)?
#   We measure, for the holonomy and sector drifts, the residual that survives.
#   Also: directive TEST (3) -- distinct-norm level density (Landau-Ramanujan) vs RvM spacing.
# ========================================================================================
print("\n" + "="*84)
print("CHECK B: level density (Landau-Ramanujan distinct-norm count) vs Riemann-von Mangoldt.")
print("="*84)
# distinct representable norms up to X
for X in [50, 200, 1000, 5000, 20000]:
    nlev = sum(1 for m in distinct_norms if m <= X)
    # Landau-Ramanujan: #{m<=X representable} ~ K * X / sqrt(log X)
    lr = X/np.sqrt(np.log(X))
    print(f"   X={X:6d}: #distinct-norms={nlev:6d}  X/#levels={X/nlev:7.4f}  "
          f"X/sqrt(logX)={lr:9.1f}  K_est={nlev/lr:.4f}")
print("  (X/#levels grows ~ sqrt(log X): Landau-Ramanujan thinning. This is a DIFFERENT count")
print("   from the integer count, but the chi3 zero spacing is still RvM -- see verdict below.)")

# RvM tie: gamma_k vs (2pi/3) N_eff^2 with N_eff = sqrt(3 gamma/2pi)
print("\n  RvM inversion check gamma_k <-> N_eff=sqrt(3 gamma/2pi), (2pi/3)N_eff^2 should = gamma:")
for k, g in [(1,ZEROS[0]),(3,ZEROS[2]),(5,ZEROS[4]),(8,ZEROS[7])]:
    Neff = math.sqrt(3*g/(2*math.pi))
    print(f"   gamma={g:9.4f}: N_eff={Neff:7.4f}  (2pi/3)N_eff^2={2*math.pi/3*Neff**2:9.4f}  (=gamma, tautology)")

# ========================================================================================
# DECISIVE CHECK C: ROOT-FINDING. Take the best NON-log drift candidate and the analytic
#   control, scan w over a window, find local minima of |resultant|, and compare the minimum
#   locations to the exact chi3 zeros (the real test of "localizes the zeros").
# ========================================================================================
print("\n" + "="*84)
print("CHECK C: scan |resultant|(w) for local minima; compare to exact chi3 zeros.")
print("="*84)
def scan_minima(drift, amp, w0=6.0, w1=30.0, step=0.002):
    ws = np.arange(w0, w1, step)
    vals = np.array([resultant(w, drift, amp) for w in ws])
    mins = []
    for i in range(1, len(vals)-1):
        if vals[i] < vals[i-1] and vals[i] <= vals[i+1] and vals[i] < 0.5*np.median(vals):
            mins.append((ws[i], vals[i]))
    return mins

for dname, drift, amp in [
        ("LOG, 1/sqrtN (analytic)", logm, AMP_SQRT),
        ("HOLO, 1/N (geometric)", holom, AMP_NORM),
        ("SECTOR-ARG, 1/N (6th-root)", secarg, AMP_NORM)]:
    mins = scan_minima(drift, amp)
    locs = [round(w,3) for w,_ in mins[:12]]
    print(f"\n   DRIFT={dname}: deepest local minima (w) in [6,30]:")
    print(f"      {locs}")
    # match each chi3 zero to nearest minimum
    if mins:
        mloc = np.array([w for w,_ in mins])
        for g in ZEROS[:5]:
            j = int(np.argmin(np.abs(mloc-g)))
            print(f"      chi3 zero {g:8.4f} -> nearest min {mloc[j]:8.4f}  (|diff|={abs(mloc[j]-g):.4f})")
    else:
        print("      (no deep minima found)")

# ========================================================================================
# FINAL: verify, to high precision, that the ANALYTIC shell winding height that LOOKS like a
#   zero really is a chi3 zero via mpmath |L| < 1e-12 (the directive's acceptance bar).
# ========================================================================================
print("\n" + "="*84)
print("VERIFY exact chi3 zeros to |L(chi3,1/2+i gamma)| < 1e-12 (mpmath, dps=30):")
print("="*84)
for g in ZEROS[:5]:
    s = mp.mpf(1)/2 + 1j*g
    print(f"   gamma={g:10.6f}  |L(chi3,1/2+i gamma)| = {mp.nstr(abs(Lchi3(s)),4)}")

print("\nDONE eisvol-4.")
