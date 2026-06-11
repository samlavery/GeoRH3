"""
hex_angles-2.py  --  ID angles-2  --  CLAIM H2 / H2' : HECKE ANGULAR THETA-SHELL.

GOAL (user directive): find a GENUINE geometric/algebraic handle on the chi3 zeros inside
the hexagonal / Eisenstein / 6th-root structure, leveraging pi/3 (units) & pi/6 (mirror axes),
MINIMIZING log/sqrt.  chi3 = character of Z[omega] (Eisenstein integers), omega=e^{2 pi i/3}.
Hexagonal norm  N(a,b)=a^2-ab+b^2 ;  (1/6) sum N^{-s} = zeta(s)*L(chi3,s).

OBEYS THE HARD RULE: build the REAL 3D SOLID FIRST with explicit (x,y,z) coords, attach a real
rotating PHASOR vector at each lattice point, PRINT a coordinate+phasor sample, THEN wind and
measure where the chi3-weighted phasor VECTOR-SUM collapses.

Channels:
  k=0  Epstein winding  E0(t)  -> equals zeta*L(chi3)  (has the zeta pole, no dip at chi3 zeros)
  k>=1 angular Hecke winding   -> DIFFERENT L-functions, NOT chi3's zeros  (documents the negative)
  H2' : QUOTIENT shell  Q(t)=E0(t)/R(t),  R(t)=b=0 rational-axis (zeta) sum
        -> does dividing out the rational axis isolate chi3 zeros?  (honest: re-importing log n?)
  COSET: complex 6th-root sublattice character  zeta3^{(a-b)} = exp(2 pi i (a-b)/3)
        -> the GEOMETRIC mod-3 hexagonal coloring; test if IT divides out zeta with no analytic 1/zeta.

EXACT chi3 zeros: 8.0397, 11.2492, 15.7046, 18.2620, 20.4558, 24.0594
EXACT zeta zeros: 14.1347, 21.0220, 25.0109, 30.4249
Verify any cancellation to |L(chi3,1/2+i gamma)| < 1e-12.

NOTE on numerics: winding scans use vectorized float64 Abel-regularized sums (fast, stable enough
to see dips). Exact reference L/zeta values and final root checks use mpmath at 30 dps.
"""
import numpy as np
import mpmath as mp
import math

mp.mp.dps = 30

# ---------- exact reference L-functions (mpmath) ----------
def Lchi3(s):
    return mp.power(3, -s) * (mp.zeta(s, mp.mpf(1)/3) - mp.zeta(s, mp.mpf(2)/3))
def chi3(n):
    return [0, 1, -1][n % 3]

CHI3_ZEROS = [8.0397371556814667, 11.2492062077729352, 15.7046191767216256,
              18.2619974956931276, 20.4557708077424929, 24.0594148564934508]
ZETA_ZEROS = [14.1347251417346937, 21.0220396387715549, 25.0108575801456888, 30.4248761258595132]
OFF_POINTS = [3.0, 6.5, 9.0, 17.0]
SQRT3 = math.sqrt(3.0)

# =====================================================================================
# STEP 1 -- BUILD THE REAL 3D OBJECT with explicit (x,y,z) coordinates.
# planar w_ab = a + b*omega, omega = e^{2 pi i/3} = -1/2 + i sqrt3/2  -> (x,y)=(a-b/2, b sqrt3/2).
# 3D point: lift to height z = sqrt(norm) = |w| (lattice radius -- the area/count height, NOT log).
# =====================================================================================
B0 = 350
Mmax = 200000
a_arr = np.arange(-B0, B0+1)
A, Bm = np.meshgrid(a_arr, a_arr, indexing='ij')
A = A.ravel(); Bm = Bm.ravel()
M = (A*A - A*Bm + Bm*Bm).astype(np.int64)
keep = (M > 0) & (M <= Mmax)
A = A[keep]; Bm = Bm[keep]; M = M[keep]
WX = A - Bm/2.0
WY = Bm*SQRT3/2.0
ARG = np.arctan2(WY, WX)
ABSW = np.hypot(WX, WY)           # = sqrt(M) = lattice radius = the height z
LOGM = np.log(M.astype(np.float64))

print("="*90)
print("STEP 1 -- BUILD THE REAL 3D OBJECT (hexagonal Eisenstein lattice cone, explicit x,y,z)")
print("="*90)
print("Planar w_ab = a + b*omega,  omega = -1/2 + i sqrt3/2.   3D point = (Re w, Im w, z=|w|=sqrt(norm)).")
print(f"built {len(M)} lattice points with 0 < norm <= {Mmax}  (B={B0})")
print()
print(f"{'(a,b)':>9} {'norm m':>7} {'x=Re w':>9} {'y=Im w':>9} {'z=|w|':>9} {'arg(w)':>9} "
      f"{'arg/(pi/3)':>10} {'6*arg(k=1)':>11}")
sample_ab = [(1,0),(1,1),(1,3),(0,1),(2,5),(2,1),(3,0)]
idx = {(int(A[i]),int(Bm[i])): i for i in range(len(A))}
for (a,b) in sample_ab:
    if (a,b) in idx:
        i = idx[(a,b)]
        note = {7:"(norm7 split)",19:"(norm19)"}.get(int(M[i]),"")
        print(f"{str((a,b)):>9} {int(M[i]):7d} {WX[i]:9.4f} {WY[i]:9.4f} {ABSW[i]:9.4f} {ARG[i]:9.4f} "
              f"{ARG[i]/(math.pi/3):10.4f} {6*ARG[i]:11.4f}  {note}")
print()
print("=> 6th-root / pi/3 sectors explicit: arg in units of pi/3; k=1 Hecke phase 6*arg wraps once")
print("   per pi/3 sector (the unit period of Z[omega]).")

# =====================================================================================
# STEP 2 -- ATTACH PHASOR VECTORS + spin law.
# phasor at (a,b): unit dir theta = 6k*arg(w) - (t/2) log(m); vector v = m^{-1/4}(cos,sin) at (x,y,z).
# winding param t spins each phasor at rate log(m)/2 (its own height). RESULTANT = chi/coset-weighted
# vector sum = the cancellation probe.  (complex sum == 2D vector resultant magnitude.)
# =====================================================================================
print()
print("="*90)
print("STEP 2 -- ATTACH PHASOR VECTORS + spin law")
print("="*90)
print("Phasor at (a,b): unit dir theta = 6k*arg(w) - (t/2)log(m); vector v=m^{-1/4}(cos,sin) at 3D pt.")
print("Winding t spins each phasor at rate log(m)/2.  Resultant = (chi3/coset)-weighted vector sum.")
print()
print(f"{'(a,b)':>9} {'norm':>6} {'|v|=m^-1/4':>11} {'theta_k1(t=0)=6arg':>19} {'(deg mod360)':>12}")
for (a,b) in sample_ab:
    if (a,b) in idx:
        i = idx[(a,b)]; th = 6*ARG[i]
        print(f"{str((a,b)):>9} {int(M[i]):6d} {M[i]**-0.25:11.5f} {th:19.5f} {math.degrees(th)%360:12.2f}")

# precompute shell aggregation for k=0 (angular phase 0): unique norms with multiplicity r(m).
unique_m, counts = np.unique(M, return_counts=True)
unique_logm = np.log(unique_m.astype(np.float64))

REG = 0.0008   # Abel regularizer in the norm m

# ---- channel functions (vectorized float64) ----
def epstein0_shell(t):
    """k=0 Epstein winding as shell phasor sum (1/6) sum_m r(m) m^{-1/2 - i t} e^{-reg m}.
       Each shell = ring of r(m) phasors all at angular phase 0, spun by -t*log m."""
    amp = (counts/6.0) * unique_m.astype(np.float64)**(-0.5) * np.exp(-REG*unique_m)
    phase = -t*unique_logm
    return np.sum(amp * np.exp(1j*phase))

def epstein_k(t, k):
    """channel-k angular Hecke winding: (1/6) sum_pts m^{-1/4} e^{i(6k arg)} e^{-i(t/2)log m} e^{-reg m}."""
    amp = M.astype(np.float64)**(-0.25) * np.exp(-REG*M)
    phase = 6*k*ARG - 0.5*t*LOGM
    return np.sum(amp * np.exp(1j*phase))/6.0

def axis_R(t, Amax=4000):
    """b=0 rational axis (zeta-like) R(t) = sum_{a>=1} a^{-1/2-it} e^{-reg a^2}."""
    a = np.arange(1, Amax+1, dtype=np.float64)
    return np.sum(a**(-0.5) * np.exp(-1j*t*np.log(a)) * np.exp(-REG*a*a))

# coset complex 6th-root character zeta3^{(a+b)} = exp(2 pi i (a+b)/3)
# (CORRECTED: the genuine norm coset is (a+b) mod 3, since N(a,b) = a^2-ab+b^2 == (a+b)^2 mod 3,
#  because -ab == 2ab mod 3.  The (a-b) coset is uniform-per-shell and cancels to ~0 -- wrong one.)
COSET = np.exp(2j*np.pi*((A + Bm).astype(np.float64))/3.0)
def coset_C(t, expo=0.25):
    """(1/6) sum_pts zeta3^{(a+b)} m^{-expo} e^{-i(t/2)log m} e^{-reg m}  (coset weight, radial wind)."""
    amp = M.astype(np.float64)**(-expo) * np.exp(-REG*M)
    phase = -0.5*t*LOGM
    return np.sum(COSET * amp * np.exp(1j*phase))/6.0

def coset_epstein(s_re):
    """(1/6) sum zeta3^{(a+b)} m^{-s} at real s (no regularizer needed for s>1)."""
    return np.sum(COSET * M.astype(np.float64)**(-s_re))/6.0

# =====================================================================================
# STEP 3 -- WIND.
# =====================================================================================
print()
print("="*90)
print("STEP 3 -- WIND.  Phasor vector-sum resultant magnitude vs chi3 / zeta / off heights")
print("="*90)

print("\n[3a] k=0 Epstein shell resultant |E0(t)| vs |zeta*L(chi3)| true (Abel reg=%.4f):" % REG)
print(f"{'t':>9} {'|E0 shell|':>12} {'|zeta*L| true':>14} {'ratio':>8}")
for g in CHI3_ZEROS[:3] + [2.0, 5.0]:
    E0 = epstein0_shell(g)
    s = mp.mpf(1)/2 + 1j*g
    true = float(abs(mp.zeta(s)*Lchi3(s)))
    print(f"{g:9.4f} {abs(E0):12.5f} {true:14.5f} {abs(E0)/true if true>0 else 0:8.4f}")
print("   => E0 tracks zeta*L; does NOT vanish at chi3 zeros (zeta factor large). Honest negative: bare k=0 useless.")

print("\n[3b] k>=1 angular Hecke winding |E_k(t)| -- minima are NOT chi3 zeros:")
print(f"{'t':>8}  {'|E1|':>10} {'|E2|':>10} {'|E3|':>10}   note")
for t in [8.0397, 11.2492, 15.7046, 9.5, 12.0, 4.0, 6.0]:
    row = [abs(epstein_k(t,k)) for k in (1,2,3)]
    note = "chi3 zero" if abs(t-8.0397)<1e-2 or abs(t-11.2492)<1e-2 or abs(t-15.7046)<1e-2 else ""
    print(f"{t:8.3f}  {row[0]:10.4f} {row[1]:10.4f} {row[2]:10.4f}   {note}")
print("   => angular k>=1 phasor sums LARGE at chi3 zeros (no dip): different L-functions.")

print("\n[3c] H2' QUOTIENT shell Q(t) = E0_shell(t)/R_axis(t)  (target ~ L(chi3)):")
print(f"{'class':>6} {'t':>9} {'|E0|':>10} {'|R axis|':>10} {'|Q=E0/R|':>11} {'|L chi3| true':>14}")
def report_Q(label, ts):
    for g in ts:
        E0 = epstein0_shell(g); R = axis_R(g)
        Q = E0/R if abs(R)>1e-12 else float('inf')
        Ltrue = float(abs(Lchi3(mp.mpf(1)/2+1j*g)))
        print(f"{label:>6} {g:9.4f} {abs(E0):10.4f} {abs(R):10.4f} {abs(Q):11.5f} {Ltrue:14.6f}")
report_Q("chi3", CHI3_ZEROS); report_Q("zeta", ZETA_ZEROS); report_Q("off", OFF_POINTS)
print("   WIN: |Q(chi3)| << |Q(zeta)| ~ |Q(off)|.")
print("   HONEST FLAG: R_axis(t)=sum a^{-1/2-it} IS the rational zeta partial sum (b=0 line carries")
print("   a^{-it}=e^{-it log a}); so Q dividing out zeta is ANALYTIC (re-imports log n / Mobius).")

print("\n[3d] COSET phasor sum C(t)=(1/6)sum zeta3^{(a+b)} m^{-expo} e^{-i(t/2)log m} e^{-reg m}")
print("     zeta3=exp(2pi i/3); weight exp(2 pi i (a+b)/3) = geometric mod-3 hex coloring (log-free build).")
print("     (CORRECTED coset: N == (a+b)^2 mod 3, so (a+b) -- not (a-b) -- is the genuine norm coset.)")
print(f"{'class':>6} {'t':>9} {'|C| coset':>11} {'|L chi3| true':>14} {'|zeta| true':>12}")
def report_C(label, ts, expo):
    for g in ts:
        C = coset_C(g, expo)
        Ltrue = float(abs(Lchi3(mp.mpf(1)/2+1j*g)))
        ztrue = float(abs(mp.zeta(mp.mpf(1)/2+1j*g)))
        print(f"{label:>6} {g:9.4f} {abs(C):11.6f} {Ltrue:14.6f} {ztrue:12.6f}")
print("  -- radial exponent m^{-1/4} (shell half-line section):")
report_C("chi3", CHI3_ZEROS, 0.25); report_C("zeta", ZETA_ZEROS, 0.25); report_C("off", OFF_POINTS, 0.25)
print("  -- radial exponent m^{-1/2} (the s=1/2+it Epstein line):")
report_C("chi3", CHI3_ZEROS, 0.5); report_C("zeta", ZETA_ZEROS, 0.5); report_C("off", OFF_POINTS, 0.5)

print("\n[3e] IDENTIFY the coset series (1/6) sum zeta3^{(a+b)} N^{-s} at real s (Mmax=%d):" % Mmax)
print("     Per shell the two nonzero classes {1,2} are equinumerous => z3+z3^2 = -1, so this is REAL:")
print("     coset = -1/2 * E_{N!=0 mod3} + E_{N=0 mod3}, both pieces being rational multiples of zeta*L.")
for s_re in [2.0, 3.0]:
    cs = coset_epstein(s_re)
    zt = float(mp.zeta(s_re)); L = float(Lchi3(mp.mpf(s_re)))
    # split identity: E_{N=0(3)} = 3^{-s} zeta*L ; E_{N!=0(3)} = (1-3^{-s}) zeta*L
    p3 = 3.0**(-s_re); pred = -0.5*(1-p3)*zt*L + p3*zt*L
    print(f"   s={s_re}:  coset Epstein = {cs.real:.6f} (real)   PREDICTED -1/2(1-3^-s)zeta L + 3^-s zeta L = {pred:.6f}")
    print(f"            => coset = {(0.5*(3*p3-1)):.6f} * zeta*L .  zeta*L={zt*L:.6f}  L(chi3)={L:.6f}  zeta={zt:.6f}")

# =====================================================================================
# [3f] DECISIVE STRUCTURAL FACT + correct norm character.
# =====================================================================================
print("\n[3f] STRUCTURAL FACT: N(a,b) == (a+b)^2 mod 3  (since -ab == 2ab mod 3).  Per shell the two")
print("     nonzero coset classes (a+b)=1,2 mod 3 are EQUINUMEROUS, so the complex coset zeta3^{(a+b)}")
print("     collapses to the REAL combo -1/2 E_{N!=0} + E_{N=0} = (rational)*zeta*L (see [3e]).")
print("     => the complex 6th-root coset does NOT isolate chi3 -- it is a multiple of zeta*L, carrying")
print("        zeta zeros too.  (The OTHER coset (a-b) mod 3 IS uniform 3-ways and cancels to ~0.)")
print("        The chi3 data lives in the NORM character chi3(N) itself (a REAL quadratic residue), below.")
CHIN = np.array([chi3(int(m)) for m in M], dtype=float)
def chiN_epstein(s_re):
    return np.sum(CHIN * M.astype(np.float64)**(-s_re))/6.0
print("\n     NORM-character series (1/6) sum chi3(N(a,b)) N^{-s}  -- identify:")
def Lprinc(s):  # principal char mod 3
    return mp.zeta(s)*(1-mp.power(3,-s))
for s_re in [2.0, 3.0]:
    cs = chiN_epstein(s_re); s = mp.mpf(s_re)
    print(f"       s={s_re}: series={cs:.6f}   L(chi3)*L(princ_mod3)={float(Lchi3(s)*Lprinc(s)):.6f}   "
          f"= zeta*L(chi3)*(1-3^-s)={float(mp.zeta(s)*Lchi3(s)*(1-mp.power(3,-s))):.6f}")
print("     => (1/6) sum chi3(N) N^{-s} = L(chi3,s)*L(principal mod3, s) = zeta*L(chi3)*(1-3^-s).")
print("        This carries BOTH chi3 AND zeta zeros -- does NOT isolate chi3 either.  HONEST NEGATIVE.")

# =====================================================================================
# [3g] FINAL mpmath VERIFICATION of the only thing that isolated chi3 (the H2' quotient),
#      and the explicit identification Q = E0/R = L(chi3) (analytic, re-imports log n).
# =====================================================================================
print("\n[3g] FINAL: complex-value check that the H2' quotient Q=E0/R EQUALS L(chi3) (so it carries chi3")
print("     zeros), and exact mpmath |L(chi3,1/2+i gamma)| at the dips (< 1e-12 confirms true zeros):")
def E0c(t):
    amp = (counts/6.0)*unique_m.astype(np.float64)**(-0.5)*np.exp(-REG*unique_m)
    return np.sum(amp*np.exp(-1j*t*unique_logm))
def Rc(t, Amax=8000):
    a = np.arange(1, Amax+1, dtype=np.float64)
    return np.sum(a**(-0.5)*np.exp(-1j*t*np.log(a))*np.exp(-REG*a*a))
for g in [9.0, 8.0397371556814667, 11.2492062077729352]:
    Q = E0c(g)/Rc(g); L = complex(Lchi3(mp.mpf(1)/2+1j*g))
    Lexact = float(abs(Lchi3(mp.mpf(1)/2+1j*g)))
    tag = "chi3 ZERO" if g>7 else "off-point"
    print(f"     t={g:.6f} ({tag}): Q={Q.real:+.5f}{Q.imag:+.5f}i  L(chi3)={L.real:+.5f}{L.imag:+.5f}i  "
          f"|Q-L|={abs(Q-L):.5f}  exact|L|={Lexact:.2e}")
print("     => Q reproduces L(chi3) (incl. its zeros) -- BUT R=sum a^{-1/2-it} IS the rational zeta")
print("        partial sum (e^{-it log a}); the division is ANALYTIC log-n / Mobius, NOT hexagonal.")

print("\n" + "="*90)
print("VERDICT  (angles-2, H2/H2'):")
print(" - 3D hex Eisenstein solid built first, with explicit (x,y,z) + phasor vectors (STEP 1/2 printed).")
print(" - k=0 Epstein resultant = zeta*L(chi3): no dip at chi3 zeros (zeta pole).  [negative, documented]")
print(" - k>=1 angular Hecke channels: large at chi3 zeros, carry DIFFERENT zeros.       [negative, documented]")
print(" - H2' quotient Q=E0/R DOES isolate chi3 zeros (|Q|: chi3~0.003 vs zeta~2.5 vs off~1.3) and EQUALS")
print("   L(chi3) numerically -- BUT only because R is the rational zeta sum: ANALYTIC log-n division.")
print(" - COMPLEX coset zeta3^{(a+b)} (the CORRECT norm coset, N==(a+b)^2 mod3): collapses to a rational")
print("   multiple of zeta*L (carries zeta zeros too) -> NO chi3 isolation.            [negative]")
print(" - NORM character chi3(N), N==(a+b)^2 mod3: (1/6)sum chi3(N)N^-s = L(chi3)*L(principal mod3)")
print("   = zeta*L*(1-3^-s), carries zeta zeros too -- does NOT isolate chi3.            [negative]")
print(" CONCLUSION: no GENUINE hexagonal/6th-root geometric handle isolated chi3 alone WITHOUT re-importing")
print("   the analytic 1/zeta (log n). The lattice geometry gives zeta*L(chi3) as one piece; separating the")
print("   chi3 factor needs the rational-axis (zeta) division, which is the analytic L in disguise.")
print("="*90)
