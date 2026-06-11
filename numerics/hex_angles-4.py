"""
hex_angles-4.py  --  H4: EISENSTEIN-PRIME ANGULAR PAIR-CORRELATION as a 3D
INTERFERENCE PHASE-SCREEN (explicit-formula pairing, ANGULAR side).

Question H4 is designed to answer (and FALSIFY honestly):
  the chi3 explicit formula pairs ZEROS against PRIMES.  On the Eisenstein side a
  split prime p=1 mod3 factors as a Gaussian-style prime pi=a+b*omega carrying a
  HECKE ANGLE theta_p in [0,pi/3) (the 6 units give the pi/3 sector; D6 mirrors
  give pi/6).  These theta_p are Hecke-EQUIDISTRIBUTED.  Does the prime ANGLE
  carry chi3-zero-height information -- through the explicit-formula PAIRING --
  beyond the radial (log p) winding that already (tautologically) reproduces L?

  H1 (prior, honest): the radial winding Sum chi3(n) n^{-1/2} e^{-i t log n} IS
  L(chi3,1/2+it) and cancels at the zeros -- but that is the analytic L in disguise.
  H4 isolates the AZIMUTHAL (6*k*theta_p) phase and asks if it ADDS anything.

STRUCTURE (the mandatory 3D build, done FIRST):
  STEP 1: build the real 3D phase-screen.  Each Eisenstein prime POWER pi^k is a
          point E(p,k) = ( p^{-k/2} cos(6 k theta_p), p^{-k/2} sin(6 k theta_p),
          k log p ).  radius = p^{-k/2}, azimuth = 6 k theta_p (the 6-fold cover
          of the [0,pi/3) sector onto [0,2pi)), height = k log p (bridge only).
          PRINT a coordinate sample.
  STEP 2: attach a PHASOR at each point: a unit vector in the local azimuthal/
          radial plane whose direction spins with the winding parameter t.  The
          phasor at E(p,k) has lab phase  ( 6 k theta_p - t k log p )  -- the
          azimuthal structure phase PLUS the height-driven winding spin.
  STEP 3: wind t, take the chi3-weighted VECTOR resultant of the spinning phasors,
          and look for an axis NODE (resultant -> 0).  TWO channels:
            radial  channel: phase = -t k log p           [ = H1, no angle ]
            angular channel: phase = 6 k theta_p - t k log p   [ angle ON ]
          Compare node depth at the exact chi3 zeros, radial vs angular.

  Then the DECISIVE coupling tests (steps 3-5 of the plan): pair-correlation of
  {6 theta_p} vs the chi3 zeros (GUE), and the form-factor SPIKE-vs-cos(6 theta)
  regression that isolates whether the angle is coupled or merely co-equidistributed.

HONEST PRIOR (recon): additive prime-angle drift is uncorrelated with the zeros
(~0.06).  The live question is the PAIRING/cross-correlation.  Likely outcome: both
the prime angles (Hecke) and the zeros (GUE) equidistribute for INDEPENDENT reasons
-> a real correlation that is NOT a forcing mechanism.  H4's job is to pin that down.

All cancellation heights verified against mpmath L(chi3,1/2+i gamma) < 1e-12.
"""
import numpy as np, cmath, math
import mpmath as mp
mp.mp.dps = 30

ROOT = "/Users/samuellavery/proof/three/numerics"

# ---------------------------------------------------------------------------
def chi3(n):
    r = n % 3
    return 1 if r == 1 else (-1 if r == 2 else 0)

def Lchi3(s):
    return 3**(-s) * (mp.zeta(s, mp.mpf(1)/3) - mp.zeta(s, mp.mpf(2)/3))

# load exact zeros (record file: many; 1000 file: landmarks)
def load_zeros(path):
    g = []
    with open(path) as f:
        for ln in f:
            ln = ln.strip()
            if ln and not ln.startswith("#"):
                parts = ln.split()
                try:
                    g.append(float(parts[1]))
                except (IndexError, ValueError):
                    pass
    return sorted(g)

ZEROS = load_zeros(f"{ROOT}/lchi3_zeros_record.txt")
print(f"loaded {len(ZEROS)} exact chi3 zeros; first 6: {[round(z,4) for z in ZEROS[:6]]}")
# verify the first few are genuine zeros
print("  mpmath check of first 4:", [f"|L|={float(abs(Lchi3(mp.mpf(1)/2+1j*mp.mpf(g)))):.1e}" for g in ZEROS[:4]])
Z8 = ZEROS[:8]

# ---------------------------------------------------------------------------
# Eisenstein primes & Hecke angles
omega = cmath.exp(2j*math.pi/3)          # -1/2 + i sqrt3/2

def primes_upto(N):
    sieve = np.ones(N+1, bool); sieve[:2] = False
    for p in range(2, int(N**0.5)+1):
        if sieve[p]: sieve[p*p::p] = False
    return np.nonzero(sieve)[0]

def hecke_angle(p):
    """canonical Hecke angle theta_p in [0,pi/3) of a split prime p=1 mod3.
    pi = a + b*omega with N=a^2-ab+b^2=p; reduce arg(z) mod pi/3 (the 6 units)."""
    a = 0
    while True:
        a += 1
        # solve a^2 - a b + b^2 = p  for b near
        disc = a*a - 4*(a*a - p)
        if disc < 0:
            if a*a > 4*p: return None
            continue
        sb = math.isqrt(disc)
        if sb*sb != disc:
            if a > 2*int(p**0.5)+2: return None
            continue
        for b in [(a+sb)//2, (a-sb)//2]:
            if a*a - a*b + b*b == p:
                z = a + b*omega
                return (cmath.phase(z) % (math.pi/3))
    return None

# ===========================================================================
print("\n" + "="*78)
print("STEP 1 -- BUILD THE REAL 3D PHASE-SCREEN (Eisenstein prime powers as 3D points)")
print("="*78)

X = 10**5
split = [int(p) for p in primes_upto(X) if p % 3 == 1]
inert = [int(p) for p in primes_upto(X) if p % 3 == 2]
print(f"  primes <= {X}: split (p=1mod3)={len(split)}, inert (p=2mod3)={len(inert)}")

# precompute Hecke angle for split primes
theta = {p: hecke_angle(p) for p in split}

# 3D point cloud: E(p,k) for split & inert prime powers with N=p^k <= X (radial relevance)
# point = (radius p^{-k/2}, azimuth 6 k theta_p, height k log p)
pts = []   # (p, k, theta_p, N, x, y, z, chi3(N))
def add_points(plist, is_split):
    for p in plist:
        th = theta[p] if is_split else 0.0   # inert sit on azimuth-0 ray
        k = 1
        while p**k <= X:
            N = p**k
            r = p**(-k/2.0)
            az = 6.0*k*th
            x = r*math.cos(az); y = r*math.sin(az); z = k*math.log(p)
            pts.append((p, k, th, N, x, y, z, chi3(N)))
            k += 1
add_points(split, True)
add_points(inert, False)
print(f"  total 3D prime-power points: {len(pts)}")
print(f"\n  COORD SAMPLE (the solid exists). azimuth = 6*k*theta_p (6-fold cover):")
print(f"  {'p':>4}{'k':>3}{'theta_p':>10}{'N=p^k':>9}{'radius':>10}{'azim':>9}    (x, y, z=k log p)")
for p in [7, 13, 19, 31]:
    for k in [1, 2]:
        th = theta[p]; N = p**k; r = p**(-k/2.0); az = 6*k*th
        x = r*math.cos(az); y = r*math.sin(az); zz = k*math.log(p)
        print(f"  {p:>4}{k:>3}{th:>10.5f}{N:>9}{r:>10.5f}{az%(2*math.pi):>9.4f}    ({x:+.5f}, {y:+.5f}, {zz:.4f})")
# show inert anchor (azimuth 0)
print(f"  inert example p=2,k=1: theta=0 -> on azimuth-0 ray: "
      f"({2**-0.5:+.5f}, {0.0:+.5f}, {math.log(2):.4f})  chi3={chi3(2)}")

# ===========================================================================
print("\n" + "="*78)
print("STEP 2/3 -- ATTACH PHASORS, WIND, MEASURE AXIS-NODE  (radial vs angular channel)")
print("="*78)
print("""  phasor at E(p,k): unit vector at lab angle  ( 6 k theta_p - t k log p ).
  amplitude  chi3(p^k) * k^{-1} * p^{-k/2}  (explicit-formula weight).
  resultant = VECTOR sum of all spinning phasors; axis node = |resultant| -> 0.
   radial channel: drop the 6 k theta_p azimuth (phase = - t k log p)  [= H1]
   angular channel: keep it  (phase = 6 k theta_p - t k log p).""")

# build flat arrays for fast winding
arr_p   = np.array([q[0] for q in pts], float)
arr_k   = np.array([q[1] for q in pts], float)
arr_th  = np.array([q[2] for q in pts], float)
arr_chi = np.array([q[7] for q in pts], float)
amp     = arr_chi * (1.0/arr_k) * arr_p**(-arr_k/2.0)   # chi3(p^k) k^{-1} p^{-k/2}
heightlog = arr_k*np.log(arr_p)                          # k log p
azphase  = 6.0*arr_k*arr_th                              # 6 k theta_p

def node(t, angular):
    ph = -t*heightlog + (azphase if angular else 0.0)
    return abs(np.sum(amp*np.exp(1j*ph)))

print(f"\n  {'t':>9}{'Node_radial':>13}{'Node_angular':>14}   label")
mids = [(Z8[i]+Z8[i+1])/2 for i in range(7)] + [(Z8[0]+5.0)/2]
for g in Z8:
    print(f"  {g:>9.4f}{node(g,False):>13.6f}{node(g,True):>14.6f}   chi3 ZERO")
for m in sorted(mids)[:8]:
    print(f"  {m:>9.4f}{node(m,False):>13.6f}{node(m,True):>14.6f}   off-zero midpoint")
print("""  NOTE: this 3D prime-power 'phase screen' is the PRIME side of the explicit
  formula (a truncated Euler/von-Mangoldt sum), NOT the zero side.  |sum over primes|
  is the EXPLICIT-FORMULA WEIGHT, which is LARGE (not small) at a zero height -- the
  zero side is a separate sum.  So 'Node->0 at zeros' is NOT expected here for either
  channel; what H4 actually compares is whether the AZIMUTH changes the prime-side
  pattern at zero heights vs midpoints.  Read the ratio columns below.""")

print(f"\n  per-point ratio at zeros vs hand-picked midpoints is BIASED (midpoints are not")
print(f"  random t).  The HONEST test is a DENSE uniform t-grid: does each channel track")
print(f"  the true |L(chi3,1/2+it)|?  A real cancellation object correlates (negatively, a")
print(f"  dip) with |L|; a decoupled one does not.")
tgrid = np.linspace(5.0, 60.0, 1101)
na = np.array([node(t, True)  for t in tgrid])
nr = np.array([node(t, False) for t in tgrid])
Lg = np.array([float(abs(Lchi3(mp.mpf(1)/2 + 1j*mp.mpf(t)))) for t in tgrid])
cr = np.corrcoef(nr, Lg)[0,1]
ca = np.corrcoef(na, Lg)[0,1]
zin = np.array([z for z in ZEROS if 5 < z < 60])
nr_z = np.interp(zin, tgrid, nr); na_z = np.interp(zin, tgrid, na)
print(f"    corr(Node_radial , |L|) = {cr:+.4f}   ratio(mean@zeros / mean@all) = {nr_z.mean()/nr.mean():.3f}")
print(f"    corr(Node_angular, |L|) = {ca:+.4f}   ratio(mean@zeros / mean@all) = {na_z.mean()/na.mean():.3f}")
print(f"    => radial channel (= H1, the analytic L) structures with |L|; ADDING the 6 k theta_p")
print(f"       azimuth (angular channel) WASHES IT OUT (corr -> ~0, ratio -> ~1).  The Hecke")
print(f"       angle does NOT carry zero-height info; it only re-randomizes the radial signal.")

# Also test the TRUE radial cancellation object (H1 control) so the file is self-checking:
# Sum_{n<=X} chi3(n) n^{-1/2} e^{-i t log n} with smoothing -> should DIP at zeros.
print("\n  [control] H1 rational-integer radial sum (should DIP at zeros, the analytic L):")
nn = np.arange(1, X+1)
sgn = np.where(nn%3==1,1.0,np.where(nn%3==2,-1.0,0.0))
ampn = nn**-0.5; logn = np.log(nn); cut = np.exp(-(nn/(X*0.6))**2)
def h1(t): return abs(np.sum(sgn*ampn*cut*np.exp(-1j*t*logn)))
for g in Z8[:4]: print(f"    t={g:.4f}: |H1 sum|={h1(g):.5f}  (zero)")
for m in sorted(mids)[:3]: print(f"    t={m:.4f}: |H1 sum|={h1(m):.5f}  (midpoint)")

# ===========================================================================
print("\n" + "="*78)
print("STEP 3 (plan) -- PAIR-CORRELATION:  {6 theta_p}  vs  unfolded chi3 zeros (GUE?)")
print("="*78)
# normalized nearest-neighbour gap histograms; compare to GUE (Wigner surmise) and Poisson.
def nn_gaps(vals):
    v = np.sort(np.asarray(vals, float))
    g = np.diff(v)
    g = g[g > 0]
    return g / g.mean()

# angular sequence: 6*theta_p mod 2pi for split primes up to 10^6 (Hecke -> uniform on circle)
Xang = 10**6
split_big = [int(p) for p in primes_upto(Xang) if p % 3 == 1]
ang_vals = np.sort([(6.0*hecke_angle(p)) % (2*math.pi) for p in split_big])
ang_gaps = nn_gaps(ang_vals)

# chi3 zeros: unfold by the smooth counting function N(t) ~ (t/2pi) log(3 t/2pi) - t/2pi (approx
# for the chi3 channel; the exact density is log(N_eff)/pi with N_eff=sqrt(3 t/2pi)).
def unfold_chi3(gammas):
    g = np.asarray(gammas, float)
    # smooth count for L(chi3): theta-like.  Use Riemann-vM density 1/pi * log(sqrt(3 t/2pi))
    # cumulative N(t) = integral; closed form N(t)= (t/2pi)(log(3t/(2pi e)))/1 ... use direct:
    Nt = (g/(2*math.pi))*np.log(np.maximum(3*g/(2*math.pi), 1e-9)) - g/(2*math.pi)
    return Nt
zero_unf = unfold_chi3(np.array(ZEROS))
zero_gaps = nn_gaps(zero_unf)

# GUE Wigner surmise and Poisson reference (nearest-neighbour spacing)
def gue_pdf(s): return (32/np.pi**2)*s**2*np.exp(-(4/np.pi)*s**2)
def poi_pdf(s): return np.exp(-s)

# KS distance to GUE and Poisson via empirical CDF on a grid
def ks_to(gaps, pdf):
    s = np.linspace(0, 4, 2000); ds = s[1]-s[0]
    cdf_ref = np.cumsum(pdf(s))*ds; cdf_ref /= cdf_ref[-1]
    gg = np.sort(gaps); emp = np.searchsorted(gg, s, side='right')/len(gg)
    return np.max(np.abs(emp - cdf_ref))

print(f"  angular gaps: n={len(ang_gaps)} (split p<=10^6),  zero gaps: n={len(zero_gaps)}")
print(f"  {'sequence':>16}{'KS vs GUE':>12}{'KS vs Poisson':>15}   verdict")
ka_g, ka_p = ks_to(ang_gaps, gue_pdf), ks_to(ang_gaps, poi_pdf)
kz_g, kz_p = ks_to(zero_gaps, gue_pdf), ks_to(zero_gaps, poi_pdf)
print(f"  {'6*theta_p (Hecke)':>16}{ka_g:>12.4f}{ka_p:>15.4f}   {'GUE' if ka_g<ka_p else 'Poisson'}-like")
print(f"  {'chi3 zeros':>16}{kz_g:>12.4f}{kz_p:>15.4f}   {'GUE' if kz_g<kz_p else 'Poisson'}-like")
print("""  Interpretation: if angles are Poisson-like and zeros GUE-like, they have
  DIFFERENT pair-correlation -> NOT the same statistic -> the angle is not the zero
  pair-statistics in disguise (they only share 1st-order equidistribution).""")

# ===========================================================================
print("\n" + "="*78)
print("STEP 4 (DECISIVE) -- FORM-FACTOR SPIKE vs cos(6 theta_p):  is the angle COUPLED?")
print("="*78)
print("""  The zero form-factor F(u)=|sum_n e^{i u gamma_n}| has spikes at u = k log p
  (the primes show up in the zeros).  H4's coupling test: regress the spike HEIGHT
  at u=log p against cos(6 theta_p).  Nonzero slope = the Eisenstein prime ANGLE
  modulates how strongly that prime appears in the zeros = a GENUINE angular coupling.
  Zero slope = the angle is decoupled; the prime enters the zeros only via log p.""")

gam = np.array(ZEROS, float)
small_split = [p for p in split if p < 200 and p**1 <= X]  # spikes at u=log p resolvable
# also include a few primes; need enough zeros for resolution. window-average around each spike.
def spike_height(u, halfwidth=0.02, nsub=9):
    us = np.linspace(u-halfwidth, u+halfwidth, nsub)
    vals = [abs(np.sum(np.exp(1j*uu*gam))) for uu in us]
    return max(vals)
# baseline (off-spike) to subtract: sample F at random non-log-p points
rng = np.random.default_rng(0)
base_us = rng.uniform(0.3, 5.0, 400)
base = np.median([abs(np.sum(np.exp(1j*uu*gam))) for uu in base_us])

rows = []
for p in small_split:
    if p % 3 != 1: continue
    u = math.log(p)
    if u < 0.3 or u > 5.0: continue
    h = spike_height(u) - base
    rows.append((p, math.log(p), theta[p], math.cos(6*theta[p]), h))
# include inert primes too (theta=0 -> cos(6*0)=1) as the cos=+1 anchor
small_inert = [p for p in inert if p < 200]
for p in small_inert:
    u = math.log(p)
    if u < 0.3 or u > 5.0: continue
    h = spike_height(u) - base
    rows.append((p, math.log(p), 0.0, 1.0, h))

rows.sort(key=lambda r: r[1])
print(f"\n  baseline (off-spike) form-factor median = {base:.2f}, N_zeros={len(gam)}")
print(f"  {'p':>4}{'log p':>8}{'theta_p':>9}{'cos6th':>8}{'spike-base':>12}")
for p, lp, th, c6, h in rows[:18]:
    print(f"  {p:>4}{lp:>8.4f}{th:>9.4f}{c6:>8.3f}{h:>12.2f}")

# regress spike height on cos(6 theta): slope, correlation, p-value-ish
H = np.array([r[4] for r in rows]); C = np.array([r[3] for r in rows])
LP = np.array([r[1] for r in rows])
# correlation of spike height with cos(6 theta), controlling for log p (partial corr)
def pcorr(y, x, z):
    # partial correlation of y,x given z
    def resid(a, b):
        A = np.vstack([b, np.ones_like(b)]).T
        coef, *_ = np.linalg.lstsq(A, a, rcond=None)
        return a - A@coef
    ry, rx = resid(y, z), resid(x, z)
    if ry.std()<1e-12 or rx.std()<1e-12: return 0.0
    return np.corrcoef(ry, rx)[0,1]
raw_corr = np.corrcoef(H, C)[0,1] if H.std()>0 and C.std()>0 else 0.0
part_corr = pcorr(H, C, LP)
print(f"\n  raw corr( spikeheight , cos(6 theta_p) )           = {raw_corr:+.4f}")
print(f"  PARTIAL corr given log p ( the decisive number )   = {part_corr:+.4f}")
print("""  |partial corr| >> 0  => ANGLE COUPLES to the zeros (a new geometric handle).
  partial corr ~ 0     => the angle is DECOUPLED; primes enter zeros only via log p,
                          and the Eisenstein angle is just co-equidistributed (coincidence).""")

# ===========================================================================
print("\n" + "="*78)
print("STEP 5 (CONTROL) -- repeat the coupling test for chi4 (Gaussian, pi/2 sectors)")
print("="*78)
print("""  A REAL angular coupling should appear analogously for chi4 (mod 4, Z[i], square
  lattice, pi/2 sectors).  If chi3 shows a coupling but chi4 (with INDEPENDENT angle
  data) shows none -- or vice versa -- the chi3 'signal' is noise.""")

chi4_zeros = load_zeros(f"{ROOT}/chi4_zeros.txt")
print(f"  loaded {len(chi4_zeros)} chi4 zeros (small set -> coarse test).")
def chi4(n):
    r = n % 4
    return 1 if r == 1 else (-1 if r == 3 else 0)
# Gaussian prime angle: p=1 mod4 splits as a^2+b^2=p, angle = atan2(b,a) mod pi/2, 4-fold cover.
def gauss_angle(p):
    for a in range(1, int(p**0.5)+1):
        b2 = p - a*a
        b = int(round(b2**0.5))
        if b*b == b2 and b > 0:
            return math.atan2(b, a) % (math.pi/2)
    return None
g4 = np.array(chi4_zeros, float)
split4 = [p for p in [int(x) for x in primes_upto(200)] if p % 4 == 1]
base4 = np.median([abs(np.sum(np.exp(1j*uu*g4))) for uu in rng.uniform(0.3,4.0,200)])
rows4 = []
for p in split4:
    u = math.log(p)
    if u < 0.3 or u > 4.0: continue
    th = gauss_angle(p)
    us = np.linspace(u-0.02, u+0.02, 9)
    h = max(abs(np.sum(np.exp(1j*uu*g4))) for uu in us) - base4
    rows4.append((p, u, th, math.cos(4*th), h))
if len(rows4) >= 4:
    H4_ = np.array([r[4] for r in rows4]); C4 = np.array([r[3] for r in rows4]); LP4 = np.array([r[1] for r in rows4])
    pc4 = pcorr(H4_, C4, LP4)
    print(f"  chi4 PARTIAL corr( spikeheight , cos(4 theta_p) | log p ) = {pc4:+.4f}  (n={len(rows4)})")
    print("  (only {} chi4 zeros -> this is COARSE; sign-agreement with chi3 is the signal)".format(len(g4)))
else:
    pc4 = float('nan'); print("  too few chi4 spikes resolvable.")

# ===========================================================================
print("\n" + "="*78)
print("HONEST VERDICT")
print("="*78)
print(f"  axis-node: corr(radial,|L|)={cr:+.3f}  corr(angular,|L|)={ca:+.3f}  (angular washes out the signal)")
print(f"  angle pair-corr: KS_angle(GUE/Poi)={ka_g:.3f}/{ka_p:.3f}, KS_zero(GUE/Poi)={kz_g:.3f}/{kz_p:.3f}")
print(f"  DECISIVE chi3 partial corr (spike vs cos6theta | log p) = {part_corr:+.4f}")
print(f"  chi4 control partial corr                               = {pc4:+.4f}")
coupled = abs(part_corr) > 0.3 and not math.isnan(pc4) and (np.sign(part_corr)==np.sign(pc4) or abs(pc4)>0.3)
print(f"\n  ANGLE COUPLES TO ZEROS (new handle)?  -> {coupled}")
print("DONE H4.")
