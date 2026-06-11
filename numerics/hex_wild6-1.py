"""
hex_wild6-1.py  --  ID wild6-1: HEXAGONAL EPSTEIN SHELL SOLID with REAL 3D PHASOR VECTORS.

GOAL (user directive): a genuine geometric/algebraic handle on the chi3 zeros inside the
hexagonal / Eisenstein / 6th-root structure, MINIMIZING log/sqrt.  chi3 is the character of
Z[omega] (Eisenstein integers, omega = e^{2pi i/3}, a 6th root of unity).  The norm form is
N(a,b)=a^2-ab+b^2 and  (1/6) sum_{(a,b)!=0} N^{-s} = zeta(s) * L(chi3,s).

HARD RULE obeyed here:
  STEP 1  build the REAL 3D solid (explicit (x,y,z) per Eisenstein integer), PRINT a sample.
  STEP 2  attach a REAL 3D PHASOR VECTOR at each lattice point; define how it SPINS with winding.
  STEP 3  WIND; the cancellation event = the chi3-weighted phasor VECTOR-SUM collapsing to ~0.

We DO NOT collapse to an abstract scalar sum.  Every resultant below is the vector sum of
explicit 3D unit vectors placed at explicit 3D coordinates.  We then -- brutally -- check
whether the working resultant is secretly the analytic L, and report it.

Exact zeros via mpmath:  L(chi3,s) = 3^{-s}(zeta(s,1/3) - zeta(s,2/3)).
"""
import numpy as np, math, mpmath as mp
from collections import defaultdict
mp.mp.dps = 30

SQRT3 = math.sqrt(3.0)

def chi3(n): return [0,1,-1][n % 3]
def Lh(s):   return mp.power(3,-s)*(mp.zeta(s,mp.mpf(1)/3)-mp.zeta(s,mp.mpf(2)/3))

# exact chi3 zero heights (first 20), from lchi3_zeros_1000.txt
ZEROS = [8.0397371556814667,11.2492062077729352,15.7046191767216256,18.2619974956931276,
         20.4557708077424929,24.0594148564934508,26.5778687357745853,28.2181645062333861,
         30.7450402613824957,33.8973889272594190,35.6084126539386347,37.5517965563646270,
         39.4852072609293508,42.6163792261575676,44.1205729120722024,46.2741180235131401,
         47.5141045101173221,50.3751386506362660,52.4967495990607537,54.1938431015519136]
# zeta zeros (controls -- here L should be O(1), NOT vanish)
ZETA_ZEROS = [14.134725,21.022040,25.010858,30.424876]
# between-zero controls (neither L nor zeta vanishes)
CONTROLS = [3.0,5.0,9.0,13.0,17.0,23.0,27.0,31.0]

# ============================================================================
# STEP 1 -- BUILD THE REAL 3D EISENSTEIN SOLID (explicit (x,y,z), printed)
# ============================================================================
# Each Eisenstein integer (a,b) -> lab point  P = (x, y, z)
#   x = a + b/2          (hex lattice, real axis)
#   y = b * sqrt3/2      (fixed lattice row spacing -- a CONSTANT, not an analytic sqrt of a var)
#   z = m = a^2-ab+b^2   (the ALGEBRAIC norm -- the lift height; an integer invariant)
B = 320
NORM_MAX = 5000
pts3d = []                       # list of (a,b,x,y,z=m)
shell_pts = defaultdict(list)    # m -> list of (x,y) hex points on that horizontal shell
for a in range(-B, B+1):
    for b in range(-B, B+1):
        m = a*a - a*b + b*b
        if 0 < m <= NORM_MAX:
            x = a + b/2.0
            y = b*SQRT3/2.0
            pts3d.append((a, b, x, y, m))
            shell_pts[m].append((x, y))

def r(m):  return len(shell_pts.get(m, []))      # point count on shell m
def r6(m): return r(m)/6.0                        # Eisenstein shell weight = sum_{d|m} chi3(d)

print("="*78)
print("STEP 1 -- REAL 3D EISENSTEIN SOLID  (Point3D(a,b) = (a+b/2, b*sqrt3/2, m=N(a,b)))")
print("="*78)
print(f"built {len(pts3d)} lattice points with 0<norm<= {NORM_MAX} (B={B})")
print(f"{'a':>4}{'b':>4}  {'x':>9}{'y':>9}{'z=m':>7}   chi3-shell-weight r(m)/6")
sample = [(0,1),(1,0),(1,1),(2,1),(2,0),(1,-1),(3,1),(2,2),(5,3)]
for (a,b) in sample:
    m = a*a-a*b+b*b
    x = a+b/2.0; y = b*SQRT3/2.0
    print(f"{a:>4}{b:>4}  {x:>9.4f}{y:>9.4f}{m:>7}   r/6 = {r6(m):+.4f}  (r(m)={r(m)})")

# verify r(m)/6 == sum_{d|m} chi3(d) algebraically (NO log/sqrt used)
def divisor_chi_sum(m):
    return sum(chi3(d) for d in range(1,m+1) if m % d == 0)
ok = all(abs(r6(m) - divisor_chi_sum(m)) < 1e-9 for m in range(1,NORM_MAX+1) if r(m)>0 or divisor_chi_sum(m)!=0)
print(f"\n  ALGEBRAIC CHECK: r(m)/6 == sum_{{d|m}} chi3(d) for all m<= {NORM_MAX}?  -> {ok}")
print("  (this is the Eisenstein splitting law -- the 6-fold structure -- with NO log, NO sqrt.)")

# ============================================================================
# STEP 2 -- ATTACH A REAL 3D PHASOR VECTOR AT EACH SHELL; DEFINE ITS SPIN
# ============================================================================
# A shell m is a horizontal ring at height z=m.  We place ONE phasor per shell (the shell is
# the natural 6-fold-symmetric orbit; r(m) points all share the algebraic invariant m).
# The phasor is a REAL UNIT VECTOR living in the local horizontal plane of the shell:
#       phasor_m(w, drift) = ( cos(phi), sin(phi), 0 )         in the shell's (e_x, e_y, axis) frame
# i.e. a genuine direction in 3-space at height z=m, pointing somewhere in the horizontal plane.
# Its spin angle phi is the WINDING accumulated as we wind by amount w under a chosen DRIFT LAW.
# We then form the chi3-weighted (signed by r/6) VECTOR resultant of these 3D unit vectors,
# each scaled by an algebraic amplitude amp(m), and look at where the resultant collapses.
#
# Amplitude amp(m): to be honest we test BOTH the analytic m^{-1/2} AND log-free algebraic ones.

def phasor_unit_vector(phi):
    """real 3D unit vector in the horizontal plane of a shell: (cos phi, sin phi, 0)."""
    return np.array([math.cos(phi), math.sin(phi), 0.0])

# ----- drift laws phi_m(w): how a shell's phasor angle accumulates with winding amount w -----
LOG2, LOG3, LOG5, LOG7 = math.log(2), math.log(3), math.log(5), math.log(7)
def factor_primes(m):
    f=[]; d=2; mm=m
    while d*d<=mm:
        while mm%d==0: f.append(d); mm//=d
        d+=1
    if mm>1: f.append(mm)
    return f

def drift_norm_log(m, w):        # phi = -w * log m   (norm winding; m is the ALGEBRAIC invariant)
    return -w*math.log(m)
def drift_perprime_logp(m, w):   # FTA-additive: phi = -w * sum_{p|m, with mult} log p = -w log m
    return -w*sum(math.log(p) for p in factor_primes(m))   # == drift_norm_log (FTA identity)
def drift_pi3_sector(m, w):      # drift by the 6th-root sector k*pi/3 of m mod 6, scaled by w
    return -w*( (m % 6) * math.pi/3.0 )
def drift_pi6_step(m, w):        # constant pi/6 angular step per shell, scaled by w
    return -w*( m * math.pi/6.0 )
def drift_sqrt3(m, w):           # hexagonal magnitude drift
    return -w*( m * 0.0 + SQRT3*math.log(max(m,2)) )

DRIFTS = {
    "norm_log (-w log m)":      drift_norm_log,
    "perprime_logp (FTA)":      drift_perprime_logp,
    "pi3_sector (m mod6)":      drift_pi3_sector,
    "pi6_step (m*pi/6)":        drift_pi6_step,
}

# ----- amplitude laws amp(m) -----
def amp_invsqrt(m): return m**(-0.5)         # analytic n^{-1/2}  (the disguise -- flagged)
def amp_one(m):     return 1.0               # log/sqrt-free unit amplitude
def amp_inv(m):     return 1.0/m             # log/sqrt-free 1/m (algebraic)

print("\n"+"="*78)
print("STEP 2 -- phasor placed at each shell as a REAL 3D unit vector (cos phi, sin phi, 0)")
print("="*78)
w0 = ZEROS[0]
print(f"sample phasor 3D unit vectors at winding w = gamma_1 = {w0:.4f}, drift = norm_log:")
print(f"{'m':>5} {'r/6':>7} {'phi':>9}   phasor 3D dir (ux,uy,uz)  scaled by (r/6)*amp_invsqrt")
for m in [1,3,4,7,12,13]:
    if r(m)==0: continue
    phi = drift_norm_log(m, w0)
    u = phasor_unit_vector(phi)
    sc = r6(m)*amp_invsqrt(m)
    v = sc*u
    print(f"{m:5d} {r6(m):+7.3f} {phi:9.3f}   ({u[0]:+.3f},{u[1]:+.3f},{u[2]:+.3f})  -> vec ({v[0]:+.4f},{v[1]:+.4f},{v[2]:+.4f})")

# ============================================================================
# STEP 3 -- WIND, and form the chi3-weighted PHASOR VECTOR RESULTANT.  collapse = event.
# ============================================================================
# Resultant(w) = sum_{m>=1} (r(m)/6) * amp(m) * Abel(m) * phasor_unit_vector(phi_m(w))
# This is a genuine 3D vector (its z-component is 0 since phasors lie in horizontal planes;
# the x,y components carry the resonance).  |Resultant| -> 0 is the phasor-alignment collapse.
def resultant_vec(w, drift, amp, reg, M):
    V = np.zeros(3)
    for m in range(1, M+1):
        w6 = r6(m)
        if w6 == 0: continue
        phi = drift(m, w)
        V += (w6*amp(m)*math.exp(-reg*m)) * phasor_unit_vector(phi)
    return V

def resultant_complex(w, drift, amp, reg, M):
    """same object as a complex number x+iy (the horizontal plane) for /zeta readout."""
    z = 0j
    for m in range(1, M+1):
        w6 = r6(m)
        if w6 == 0: continue
        phi = drift(m, w)
        z += (w6*amp(m)*math.exp(-reg*m)) * complex(math.cos(phi), math.sin(phi))
    return z

print("\n"+"="*78)
print("STEP 3 -- WIND: |phasor VECTOR resultant| at chi3 zeros vs zeta zeros vs controls")
print("="*78)

reg = 0.002; M = NORM_MAX
# the canonical (amp_invsqrt, drift_norm_log) -- this is the user's stated positive-signal config
print("\n[A] config: amp=m^{-1/2}, drift=-w log m, reg=0.002, M=5000  -- and /zeta readout")
print(f"{'gamma':>9} {'kind':>10} {'|resultant|':>12} {'|res/zeta|':>11} {'|L_true|':>10}")
def report_row(g, kind):
    V = resultant_vec(g, drift_norm_log, amp_invsqrt, reg, M)
    z = resultant_complex(g, drift_norm_log, amp_invsqrt, reg, M)
    zz = mp.zeta(mp.mpf(1)/2+1j*g)
    Lt = abs(Lh(mp.mpf(1)/2+1j*g))
    magV = float(np.linalg.norm(V))
    # sanity: |V| should equal |z|
    print(f"{g:9.4f} {kind:>10} {magV:12.5f} {float(abs(z/zz)):11.5f} {float(Lt):10.5f}")
    return magV, float(abs(z/zz)), float(Lt)
for g in ZEROS[:10]: report_row(g, "chi3 ZERO")
for g in ZETA_ZEROS: report_row(g, "zeta zero")
for g in CONTROLS:   report_row(g, "control")

# ---------------------------------------------------------------------------
# BRUTAL HONESTY CHECK 1: is the resultant secretly the analytic Epstein zeta = zeta*L?
# ---------------------------------------------------------------------------
print("\n"+"="*78)
print("HONESTY CHECK 1 -- is the (amp=m^-1/2, drift=-w log m) resultant secretly  zeta*L ?")
print("="*78)
print("Resultant_complex(w) = sum_m (r(m)/6) m^{-1/2} e^{-reg m} e^{-i w log m}")
print("                     = sum_m (r(m)/6) m^{-1/2-iw} e^{-reg m}  = (1/6) sum_m r(m) m^{-s} e^{-reg m}")
print("                     = Abel-regularized hex Epstein zeta_{Q(sqrt-3)}(s) = zeta(s) L(chi3,s).")
print("  => YES. With amp=m^{-1/2} and drift=-w log m the phasor vector-sum IS the analytic Epstein")
print("     zeta.  log m enters via m^{-iw}.  This config re-derives the analytic L (tautological).")
for g in [ZEROS[0], CONTROLS[0]]:
    z = resultant_complex(g, drift_norm_log, amp_invsqrt, 1e-9, M)
    s = mp.mpf(1)/2+1j*g
    epstein = mp.zeta(s)*Lh(s)
    print(f"   w={g:7.4f}: resultant_c={complex(z):.5f}   zeta*L (mpmath)={complex(epstein):.5f}")

# ---------------------------------------------------------------------------
# (i) PHASOR DRIFT sweep -- which drift law collapses AT the chi3 zeros (log-free amps too)
# ---------------------------------------------------------------------------
print("\n"+"="*78)
print("(i) PHASOR DRIFT SWEEP -- mean |resultant/zeta| at chi3 ZEROS vs at CONTROLS")
print("    (a drift 'works' if it is SMALL at zeros and LARGE at controls). amps: invsqrt & log-free")
print("="*78)
def sweep_score(drift, amp, reg=0.002, M=4000, zsub=False):
    zero_vals, ctrl_vals = [], []
    for g in ZEROS[:8]:
        z = resultant_complex(g, drift, amp, reg, M)
        if zsub: z = z/complex(mp.zeta(mp.mpf(1)/2+1j*g))
        zero_vals.append(abs(z))
    for g in CONTROLS:
        z = resultant_complex(g, drift, amp, reg, M)
        if zsub: z = z/complex(mp.zeta(mp.mpf(1)/2+1j*g))
        ctrl_vals.append(abs(z))
    return np.mean(zero_vals), np.mean(ctrl_vals)

print(f"{'drift':>26} {'amp':>10} {'/zeta?':>7} {'mean@zeros':>11} {'mean@ctrl':>10} {'ratio c/z':>10}")
for dn, df in DRIFTS.items():
    for an, af in [("invsqrt", amp_invsqrt), ("one", amp_one), ("inv_m", amp_inv)]:
        for zsub in [True, False]:
            mz, mc = sweep_score(df, af, zsub=zsub)
            ratio = mc/mz if mz>1e-12 else float('inf')
            flag = "  <== separates" if (ratio>3 and zsub) else ""
            print(f"{dn:>26} {an:>10} {str(zsub):>7} {mz:11.5f} {mc:10.5f} {ratio:10.2f}{flag}")

# ---------------------------------------------------------------------------
# (ii) ALIGN-TO-AXIS test -- phasors aim radially inward toward the central helix axis
# ---------------------------------------------------------------------------
# Reinterpret each shell phasor as pointing radially in the lab xy-plane: at winding w the shell
# is rotated by phi_m(w); its phasor points in direction (cos phi, sin phi).  The CENTRAL AXIS is
# the z-axis (origin in xy).  "aim at axis" = the inward radial component.  We measure the net
# inward resultant: how strongly, collectively, the chi3-weighted phasors point toward the axis.
# Test: do the windings where the inward component VANISHES coincide with chi3 zeros?
print("\n"+"="*78)
print("(ii) ALIGN-TO-AXIS -- net inward (toward central z-axis) chi3-weighted phasor component")
print("     phasor at shell m points (cos phi_m, sin phi_m); inward = -radial.  We sum the signed")
print("     inward projection.  Note: for a planar phasor the 'inward' resultant magnitude == |V|,")
print("     so the axis-alignment collapse is the SAME event as the vector collapse above.")
print("="*78)
print(f"{'gamma':>9} {'kind':>10} {'|inward resultant|=|V|':>22}")
for g in ZEROS[:5]:
    V = resultant_vec(g, drift_norm_log, amp_invsqrt, reg, M)
    print(f"{g:9.4f} {'chi3 ZERO':>10} {float(np.linalg.norm(V[:2])):22.5f}")
for g in CONTROLS[:3]:
    V = resultant_vec(g, drift_norm_log, amp_invsqrt, reg, M)
    print(f"{g:9.4f} {'control':>10} {float(np.linalg.norm(V[:2])):22.5f}")

# ---------------------------------------------------------------------------
# PARAMETER SWEEP -- scale-uniqueness: replace drift -w log m by -alpha w log m; only alpha=1?
# ---------------------------------------------------------------------------
print("\n"+"="*78)
print("PARAM SWEEP -- multiplicative-winding scale alpha:  phi = -alpha*w*log m  (drift rate).")
print("   For each alpha, mean |res/zeta| at the 8 chi3 zeros.  alpha=1 should be the unique min.")
print("="*78)
def drift_alpha(alpha):
    return lambda m,w: -alpha*w*math.log(m)
print(f"{'alpha':>7} {'mean|res/zeta|@chi3zeros':>26} {'mean@controls':>15}")
for alpha in [0.5,0.75,0.9,0.95,1.0,1.05,1.1,1.25,1.5,2.0,
              math.pi/3, math.pi/6, SQRT3, math.sqrt(2)]:
    da = drift_alpha(alpha)
    mz, mc = sweep_score(da, amp_invsqrt, zsub=True)
    star = "  <-- min?" if abs(alpha-1.0)<1e-9 else ""
    print(f"{alpha:7.4f} {mz:26.6f} {mc:15.6f}{star}")

# ---------------------------------------------------------------------------
# PARAM SWEEP -- per-prime drift rates as CONSTANTS (log2,log3,log5,log7) vs uniform log p
# ---------------------------------------------------------------------------
print("\n"+"="*78)
print("PARAM SWEEP -- per-prime drift constants. phi = -w*sum_{p|m mult} c_p.  Test c_p=log p")
print("   (=> FTA gives exactly log m, the analytic winding) vs c_p = fixed angular units.")
print("="*78)
def drift_cp(cp_map, default):
    def f(m,w):
        s=0.0
        for p in factor_primes(m):
            s += cp_map.get(p, default(p))
        return -w*s
    return f
configs = {
    "c_p = log p (FTA->log m)":      drift_cp({}, lambda p: math.log(p)),
    "c_p = pi/3 (uniform sector)":   drift_cp({}, lambda p: math.pi/3),
    "c_p = pi/6 (uniform)":          drift_cp({}, lambda p: math.pi/6),
    "c_2=log2,c_3=log3,c_5..=logp":  drift_cp({2:LOG2,3:LOG3,5:LOG5,7:LOG7}, lambda p: math.log(p)),
    "c_p = log p only for split p":  drift_cp({}, lambda p: math.log(p) if p%3==1 else math.log(p)),
}
print(f"{'config':>34} {'mean|res/zeta|@zeros':>22} {'mean@ctrl':>11} {'ratio':>8}")
for name, df in configs.items():
    mz, mc = sweep_score(df, amp_invsqrt, zsub=True)
    ratio = mc/mz if mz>1e-12 else float('inf')
    print(f"{name:>34} {mz:22.6f} {mc:11.5f} {ratio:8.2f}")

# ---------------------------------------------------------------------------
# RICHARDSON push reg->0 at the first 12 zeros; verify extrapolated |res/zeta| -> 0
# ---------------------------------------------------------------------------
print("\n"+"="*78)
print("RICHARDSON reg->0 -- |res/zeta| at first 12 chi3 zeros, regs {0.004,0.002,0.001,0.0005}")
print("   plus a between-zero control row (should stay O(1)). amp=m^{-1/2}, drift=-w log m, M=5000")
print("="*78)
regs = [0.004,0.002,0.001,0.0005]
print(f"{'gamma':>9} " + " ".join(f"{'r='+str(rr):>10}" for rr in regs) + f"{'extrap':>10}")
def richardson(vals, regs):
    # linear fit |res/zeta| ~ A + B*reg, extrapolate to reg=0
    A = np.polyfit(regs, vals, 1)
    return A[1]  # intercept
for g in ZEROS[:12]:
    vals=[]
    for rr in regs:
        z = resultant_complex(g, drift_norm_log, amp_invsqrt, rr, M)
        zz = complex(mp.zeta(mp.mpf(1)/2+1j*g))
        vals.append(abs(z/zz))
    ex = richardson(vals, regs)
    print(f"{g:9.4f} " + " ".join(f"{v:10.6f}" for v in vals) + f"{ex:10.6f}")
for g in CONTROLS[:3]:
    vals=[]
    for rr in regs:
        z = resultant_complex(g, drift_norm_log, amp_invsqrt, rr, M)
        zz = complex(mp.zeta(mp.mpf(1)/2+1j*g))
        vals.append(abs(z/zz))
    ex = richardson(vals, regs)
    print(f"{g:9.4f} " + " ".join(f"{v:10.6f}" for v in vals) + f"{ex:10.6f}  (control)")

# ---------------------------------------------------------------------------
# HONESTY CHECK 2 -- can a LOG-FREE phasor object (no m^{-iw}, no m^{-1/2}) hit the zeros?
# ---------------------------------------------------------------------------
print("\n"+"="*78)
print("HONESTY CHECK 2 -- can ANY log-free drift (pi/3, pi/6 sectors; FTA per-prime sector")
print("   constants) produce a collapse AT the chi3 zeros without log m built in?")
print("   We scan w in [2,55] for the pi/3-sector & pi/6 drifts and list the deepest minima,")
print("   then compare to the true chi3 zero heights.")
print("="*78)
def scan_minima(drift, amp, reg=0.002, M=2000, wlo=2.0, whi=55.0, nw=2000):
    ws = np.linspace(wlo, whi, nw)
    mags=[]
    for w in ws:
        z = resultant_complex(w, drift, amp, reg, M)
        mags.append(abs(z))
    mags=np.array(mags)
    # local minima
    mins=[]
    for i in range(1,len(ws)-1):
        if mags[i]<mags[i-1] and mags[i]<mags[i+1]:
            mins.append((ws[i], mags[i]))
    mins.sort(key=lambda t:t[1])
    return mins[:8]
for name, df, amp in [("pi3_sector, amp=one", drift_pi3_sector, amp_one),
                      ("pi6_step,   amp=one", drift_pi6_step, amp_one),
                      ("pi3_sector, amp=inv_m", drift_pi3_sector, amp_inv)]:
    mins = scan_minima(df, amp)
    locs = ", ".join(f"{w:.2f}(|{mg:.3f}|)" for w,mg in mins[:6])
    print(f"  {name:>22}: deepest minima at w = {locs}")
print(f"\n  TRUE chi3 zero heights in [2,55]: {', '.join(f'{g:.3f}' for g in ZEROS)}")

# ---------------------------------------------------------------------------
# FINAL exact-zero verification of the working config's claimed cancellation heights
# ---------------------------------------------------------------------------
print("\n"+"="*78)
print("FINAL -- exact mpmath |L(chi3,1/2+i gamma)| at the heights where the working resultant")
print("   collapses (these ARE the input chi3 zeros).  Confirms the heights are true zeros to <1e-12.")
print("="*78)
for g in ZEROS[:8]:
    Lt = Lh(mp.mpf(1)/2+1j*mp.mpf(repr(g)))
    print(f"  gamma={g:.10f}   |L(chi3,1/2+i gamma)| = {mp.nstr(abs(Lt),4)}")
print("\nNOTE: these heights are CORRECT zeros (|L|~0), but see HONESTY CHECK 1: the working")
print("collapse there is the Abel Epstein zeta = zeta*L evaluated at its own zeros -- analytic, not new.")
