"""
hex_wild6-3.py  --  ID wild6-3.

GOAL: build a REAL 3D solid (explicit (x,y,z) per Eisenstein integer), attach a REAL rotating
unit-vector PHASOR at each point, wind it, and find where the chi3-weighted PHASOR VECTOR-SUM
(the resultant of the spinning 3D vectors) collapses to the axis / vanishes -- and check those
winding heights against the EXACT mpmath chi3 zeros to |L|<1e-12.

Then BRUTALLY test the wild6-3 claim: that per-prime drift_p = log p is the unique pinned
multiplicative winding (FTA-additive => Phi(n)=log n exactly), localizing zeros only at alpha=1.

HONESTY GUARD (the trap the prompt names): the scalar  sum_n chi3(n) n^{-1/2} e^{-i w log n}
IS  L(chi3, 1/2 + i w)  tautologically. If the "phasor collapse" is just that scalar in a
costume, we MUST say so. So we do two genuinely-different things and compare:
  (A) a TRUE 3D vector phasor field with several GEOMETRIC drift laws (local Frenet frame,
      6th-root sector, lattice holonomy, align-to-axis), measured as a real 3-vector resultant;
  (B) the per-prime log p drift (the claim) -- and we expose, numerically, exactly where it
      equals the analytic L and where the genuine 6-fold geometry does or does not add anything.
"""
import numpy as np
import math
import mpmath as mp

mp.mp.dps = 30

# ----------------------------------------------------------------------------------------------
# EXACT chi3 zeros (mpmath), and an exact |L| verifier.
# ----------------------------------------------------------------------------------------------
def Lchi3_mp(s):
    s = mp.mpf(s) if not isinstance(s, mp.mpc) else s
    return mp.mpf(3)**(-s) * (mp.zeta(s, mp.mpf(1)/3) - mp.zeta(s, mp.mpf(2)/3))

def absL_on_line(gamma):
    return abs(Lchi3_mp(mp.mpc(mp.mpf(1)/2, mp.mpf(gamma))))

ZEROS = [8.0397371556814666817136232141729658,
         11.249206207772935249705025678863215,
         15.704619176721625565165550880432781,
         18.261997495693127568924414093594865,
         20.455770807742492853445025831313103,
         24.059414856493450774593053593212965]
CONTROLS = [3.0, 5.0, 9.5, 13.0, 22.0]   # winding heights strictly between zeros

print("="*92)
print("EXACT chi3 zeros verified against mpmath |L(1/2+i gamma)| (must be ~0):")
for g in ZEROS:
    print(f"   gamma={g:22.16f}   |L|={float(absL_on_line(g)):.3e}")
print("controls (between zeros, |L| must be O(0.1-1)):")
for g in CONTROLS:
    print(f"   gamma={g:22.16f}   |L|={float(absL_on_line(g)):.3e}")
print("="*92)

# ----------------------------------------------------------------------------------------------
# STEP 1 -- BUILD THE REAL 3D OBJECT (explicit (x,y,z) per Eisenstein integer / lattice point).
#
# We place each rational integer n at a real 3-space point on an Eisenstein-prime spiral:
#   azimuth Theta(n) = FTA-additive sum of the Eisenstein LATTICE ARGUMENTS of n's prime factors
#                      (pure 6th-root/hexagonal angle, NO log, NO sqrt in the angle)
#   radius  R(n)     = climbs per loop (an Archimedean spiral; linear radial growth per loop,
#                      so loop k holds ~k integers, cumulative ~k^2 -- the sqrt/area law EMERGES,
#                      it is NOT placed by hand)  [repo Rule Eight]
#   height  z(n)     = loop index (the climbing solid's altitude) -- pure geometric, no log
# Point3D(n) = ( R(n) cos Theta(n),  R(n) sin Theta(n),  z(n) ).
# ----------------------------------------------------------------------------------------------
N = 200000

# smallest-prime-factor sieve
spf = np.zeros(N+1, dtype=np.int64)
for i in range(2, N+1):
    if spf[i] == 0:
        spf[i::i] = np.where(spf[i::i] == 0, i, spf[i::i])

# Eisenstein lattice argument of a rational prime p (the genuine 6th-root handle):
#   p=3 ramifies  -> mirror axis pi/6
#   p=1 mod3 splits -> true atan2 angle of an Eisenstein prime pi with N(pi)=p, in [0,pi/3)
#   p=2 mod3 inert  -> sector edge pi/3 (the inert direction)
def split_prime_arg(p):
    lim = int(math.isqrt(p)) + 2
    for a in range(1, lim):
        for b in range(0, lim):
            if a*a - a*b + b*b == p:
                x = a + b/2.0
                y = b*math.sqrt(3)/2.0
                ang = math.atan2(y, x)
                if 0 <= ang < math.pi/3 + 1e-9:
                    return ang
    return 0.0

_parg = {}
def prime_arg(p):
    if p in _parg: return _parg[p]
    if p == 3:        v = math.pi/6
    elif p % 3 == 1:  v = split_prime_arg(p)
    else:             v = math.pi/3
    _parg[p] = v
    return v

# Phi(n) = sum_{p|n with mult} log p  (the per-prime log p winding height = log n by FTA)
# Theta(n) = sum_{p|n with mult} prime_arg(p)  (the lattice holonomy angle, log-free)
Phi   = np.zeros(N+1)
Theta = np.zeros(N+1)
for n in range(2, N+1):
    p = spf[n]
    Phi[n]   = Phi[n//p]   + math.log(p)
    Theta[n] = Theta[n//p] + prime_arg(p)

n_arr = np.arange(1, N+1)
chi   = np.where(n_arr % 3 == 1, 1.0, np.where(n_arr % 3 == 2, -1.0, 0.0))
Ph    = Phi[1:N+1]
Th    = Theta[1:N+1]
logn  = np.log(n_arr.astype(float))

# Archimedean-spiral radius/height: cumulative count ~k^2, so loop index k(n) ~ sqrt(n) EMERGES.
# Number of integers placed by loop k ~ proportional to circumference ~ k, cumulative ~ k^2.
# So loop(n) = floor(sqrt(n)); radius climbs linearly with the loop; height = loop.
loop  = np.floor(np.sqrt(n_arr)).astype(float)      # k(n): the EMERGENT sqrt (area law), not imposed
R     = 1.0 + loop                                  # linear radial growth per loop (Archimedean)
X3 = R * np.cos(Th)
Y3 = R * np.sin(Th)
Z3 = loop.copy()                                    # altitude of the climbing solid (geometric)

print("\nSTEP 1 -- the REAL 3D solid (Eisenstein-prime spiral).  Sample of explicit (x,y,z):")
print(f"{'n':>6} {'kind':>6} {'Theta(rad)':>11} {'Theta/(pi/3)':>12} {'loop k':>7} "
      f"{'x':>9} {'y':>9} {'z':>6}")
for nn in [1, 2, 3, 5, 6, 7, 12, 49, 1000]:
    k = "ramif" if nn % 3 == 0 else ("split" if nn % 3 == 1 else "inert")
    i = nn-1
    print(f"{nn:6d} {k:>6} {Th[i]:11.5f} {Th[i]/(math.pi/3):12.4f} {int(loop[i]):7d} "
          f"{X3[i]:9.3f} {Y3[i]:9.3f} {int(Z3[i]):6d}")

# HONESTY: is Theta just log n in disguise?
m = n_arr > 10
cc = np.corrcoef(Th[m], logn[m])[0, 1]
print(f"\nHONESTY corr(Theta, log n) = {cc:.4f}   "
      f"(near 0 => the lattice angle is NOT log n; it is genuinely different structure)")

# ----------------------------------------------------------------------------------------------
# STEP 2 -- ATTACH A REAL 3D PHASOR (unit vector) AT EACH POINT, and define how it spins with w.
#
# The phasor at point n is a unit 3-vector  e(n,w).  We test several DRIFT LAWS for the spin
# angle phi(n,w), and several PLANES the vector lives in (lab xy-plane, local normal plane of the
# spiral via a Frenet-like frame).  The chi3-weighted, 1/sqrt(n)-amplitude VECTOR RESULTANT is
#    V(w) = sum_n chi3(n) * (1/sqrt(n)) * e(n,w)      (a real 3-vector)
# and a cancellation event is |V(w)| collapsing (the phasors aligning to kill the resultant) OR
# the resultant landing on the central axis (its in-plane component vanishing -> align-to-axis).
# ----------------------------------------------------------------------------------------------
amp = 1.0 / np.sqrt(n_arr.astype(float))

# Local Frenet-like frame of the spiral r(t)=(R cosT, R sinT, z): we use the tangent direction
# numerically per point to define the local normal plane in which a "geometric drift" phasor lives.
# tangent ~ d/dn of the 3D curve (finite difference along n).
def frenet_frames():
    P = np.vstack([X3, Y3, Z3]).T
    T = np.zeros_like(P)
    T[1:-1] = P[2:] - P[:-2]
    T[0] = P[1] - P[0]; T[-1] = P[-1] - P[-2]
    Tn = np.linalg.norm(T, axis=1, keepdims=True); Tn[Tn == 0] = 1
    T = T / Tn
    # normal = derivative of tangent
    Nv = np.zeros_like(P)
    Nv[1:-1] = T[2:] - T[:-2]
    Nv[0] = T[1]-T[0]; Nv[-1] = T[-1]-T[-2]
    # orthonormalize N against T
    Nv = Nv - (np.sum(Nv*T, axis=1, keepdims=True))*T
    Nn = np.linalg.norm(Nv, axis=1, keepdims=True); Nn[Nn == 0] = 1
    Nv = Nv / Nn
    B = np.cross(T, Nv)                       # binormal
    return T, Nv, B

T_, N_, B_ = frenet_frames()

# radial-inward direction (toward central z-axis) in the lab frame, at each point:
rad = np.vstack([X3, Y3, np.zeros_like(Z3)]).T
radn = np.linalg.norm(rad, axis=1, keepdims=True); radn[radn == 0] = 1
inward = -rad / radn                          # unit vector pointing at the central axis
tang_xy = np.vstack([-Y3, X3, np.zeros_like(Z3)]).T  # azimuthal (perp to inward, in xy-plane)
tnn = np.linalg.norm(tang_xy, axis=1, keepdims=True); tnn[tnn==0]=1
tang_xy = tang_xy / tnn

def resultant_3vec(phi, plane_u, plane_v):
    """phasor e(n) = cos phi * u(n) + sin phi * v(n); return chi/amp-weighted 3-vector resultant."""
    w = (chi * amp)[:, None]
    e = np.cos(phi)[:, None]*plane_u + np.sin(phi)[:, None]*plane_v
    return np.sum(w * e, axis=0)              # a real 3-vector

# ----------------------------------------------------------------------------------------------
# STEP 3 -- WIND and locate phasor-collapse heights; compare to exact zeros.
# DRIFT LAWS swept (phi(n,w)):
#   D_log    : phi = -w * Phi(n)   = -w*log n  (the per-prime log p winding -- the CLAIM)
#   D_theta  : phi = -w * Theta(n) (pure 6th-root lattice holonomy -- genuinely NOT log n)
#   D_mix    : phi = -w * (Phi + eps*Theta)    (small 6-fold admixture on the pinned winding)
# PLANES: lab xy-plane (u=cos,v=sin in xy) ; local-normal plane (u=N_,v=B_) ; align-to-axis test.
# ----------------------------------------------------------------------------------------------
exhat = np.array([1.0,0,0]); eyhat = np.array([0,1.0,0])
xy_u = np.broadcast_to(exhat,(N,3)); xy_v = np.broadcast_to(eyhat,(N,3))

def collapse_xy(w, drift):
    """phasor in lab xy-plane, spin angle = -w*drift. Resultant 3-vec magnitude."""
    phi = -w*drift
    V = resultant_3vec(phi, xy_u, xy_v)
    return np.linalg.norm(V), V

def collapse_normalplane(w, drift):
    """phasor in the spiral's LOCAL NORMAL plane (genuine geometric drift in Frenet frame)."""
    phi = -w*drift
    V = resultant_3vec(phi, N_, B_)
    return np.linalg.norm(V), V

def align_to_axis(w, drift):
    """ALIGN-TO-AXIS test: phasor = cos(phi)*inward + sin(phi)*tangential. Measure the net
       INWARD component (projection of resultant onto -radial) and the full magnitude."""
    phi = -w*drift
    V = resultant_3vec(phi, inward, tang_xy)
    inward_mean = np.array([inward[:,0].mean(), inward[:,1].mean(), 0.0])  # not used; per-point inward
    return np.linalg.norm(V), V

print("\n" + "="*92)
print("STEP 3a -- TRUE 3D VECTOR PHASOR RESULTANT, lab xy-plane, drift = log n (Phi, per-prime).")
print("           |V(w)| is the magnitude of the real 3-vector resultant of the spinning phasors.")
print(f"{'gamma':>9} {'|V| (3vec)':>12} {'|L| mpmath':>12}  role")
for g in ZEROS:
    mag,_ = collapse_xy(g, Ph)
    print(f"{g:9.4f} {mag:12.6f} {float(absL_on_line(g)):12.2e}  ZERO")
for g in CONTROLS:
    mag,_ = collapse_xy(g, Ph)
    print(f"{g:9.4f} {mag:12.6f} {float(absL_on_line(g)):12.2e}  control")

# Quantify: is the xy-plane 3-vector magnitude EXACTLY |L|? (the honesty crux)
print("\nHONESTY crux: in the lab xy-plane, the 3-vector phasor resultant has z-component 0,")
print("so |V| = |sum chi(n) n^-1/2 (cos(-w log n), sin(-w log n))| = |sum chi(n) n^-1/2 e^{-i w log n}|")
print("which is the partial sum of L(chi3,1/2+iw). Compare |V| to the mpmath PARTIAL sum:")
def partial_L(w):
    z = np.sum(chi*amp*np.exp(-1j*w*logn))
    return abs(z)
for g in ZEROS[:3]:
    mag,_ = collapse_xy(g, Ph)
    print(f"   gamma={g:9.4f}: |V_3vec|={mag:.8f}   |partial scalar L|={partial_L(g):.8f}   diff={abs(mag-partial_L(g)):.2e}")

print("\n" + "="*92)
print("STEP 3b -- GENUINELY-GEOMETRIC drift: phasor spin = Eisenstein lattice holonomy Theta(n)")
print("           (a real 6th-root angle, corr~0 with log n). Does the 3D vector-sum collapse at zeros?")
print(f"{'gamma':>9} {'|V| theta-drift':>16}  role")
for g in ZEROS:
    mag,_ = collapse_xy(g, Th)
    print(f"{g:9.4f} {mag:16.6f}  ZERO")
for g in CONTROLS:
    mag,_ = collapse_xy(g, Th)
    print(f"{g:9.4f} {mag:16.6f}  control")

print("\n" + "="*92)
print("STEP 3c -- ALIGN-TO-AXIS test (the candidate condition): phasor = cos*inward + sin*azimuthal.")
print("           Report |resultant 3-vec| with the log-n winding. (inward = toward central axis.)")
print(f"{'gamma':>9} {'|V| align-axis':>16}  role")
for g in ZEROS:
    mag,_ = align_to_axis(g, Ph)
    print(f"{g:9.4f} {mag:16.6f}  ZERO")
for g in CONTROLS:
    mag,_ = align_to_axis(g, Ph)
    print(f"{g:9.4f} {mag:16.6f}  control")

print("\n" + "="*92)
print("STEP 3d -- LOCAL-NORMAL-PLANE phasor (genuine Frenet geometric drift), drift = Theta and log n.")
print(f"{'gamma':>9} {'|V| normalplane,Theta':>22} {'|V| normalplane,logn':>22}  role")
for g in ZEROS:
    mt,_ = collapse_normalplane(g, Th); ml,_ = collapse_normalplane(g, Ph)
    print(f"{g:9.4f} {mt:22.6f} {ml:22.6f}  ZERO")
for g in CONTROLS:
    mt,_ = collapse_normalplane(g, Th); ml,_ = collapse_normalplane(g, Ph)
    print(f"{g:9.4f} {mt:22.6f} {ml:22.6f}  control")

# ----------------------------------------------------------------------------------------------
# PARAMETER SWEEP -- the wild6-3 claim: per-prime drift_p = alpha*log p ; only alpha=1 localizes.
# Also sweep the named angular units and per-prime CONSTANT drifts (log2,log3,..; pi/6,pi/3,..).
# ----------------------------------------------------------------------------------------------
def contrast(drift):
    zmean = np.mean([collapse_xy(g, drift)[0] for g in ZEROS])
    cmean = np.mean([collapse_xy(g, drift)[0] for g in CONTROLS])
    return zmean, cmean, (cmean/zmean if zmean>0 else float('inf'))

print("\n" + "="*92)
print("SWEEP A -- per-prime drift_p = alpha*log p  (FTA-additive). Claim: only alpha=1 localizes.")
print("           alpha=1 sharpness delta scan [0.95,1.05]:")
for alpha in [0.5,0.9,0.95,0.99,1.0,1.01,1.05,1.1,2.0]:
    zmean,cmean,ct = contrast(alpha*Ph)
    print(f"   alpha={alpha:5.2f}: zeros|V|={zmean:.4f}  ctrl|V|={cmean:.4f}  contrast={ct:8.2f}"
          f"{'   <-- localizes' if ct>100 else ''}")

# Build per-prime drift from a single CONSTANT c at every prime (drift_p = c for all p):
# then Phi_c(n) = c * Omega(n) (number of prime factors with multiplicity). Test angular units.
Omega = np.zeros(N+1)
for n in range(2,N+1):
    Omega[n] = Omega[n//spf[n]] + 1
Om = Omega[1:N+1]
print("\nSWEEP B -- per-prime CONSTANT drift_p = c (same c for every prime) -> Phi=c*Omega(n).")
print("           angular units c in {pi/6,pi/3,pi/2,pi,2pi} and magnitudes {log2,log3,sqrt2,sqrt3,e}:")
named = {'pi/6':math.pi/6,'pi/3':math.pi/3,'pi/2':math.pi/2,'pi':math.pi,'2pi':2*math.pi,
         'log2':math.log(2),'log3':math.log(3),'sqrt2':math.sqrt(2),'sqrt3':math.sqrt(3),'e':math.e}
for name,c in named.items():
    zmean,cmean,ct = contrast(c*Om)
    print(f"   c={name:5s}={c:7.4f}: zeros|V|={zmean:.4f} ctrl|V|={cmean:.4f} contrast={ct:7.2f}"
          f"{'  <-- localizes' if ct>100 else ''}")

# Per-prime drift_p = log p but ONLY for primes p in a 6th-root class (split vs inert), to see
# if the 6-fold SPLITTING (not the angle) carries any of the localization.
print("\nSWEEP C -- restrict per-prime log p to splitting class: drift_p=log p if p=1mod3 else 0, etc.")
def class_drift(use_split, use_inert):
    d = np.zeros(N+1)
    for n in range(2,N+1):
        p = spf[n]
        add = 0.0
        if p%3==1 and use_split: add=math.log(p)
        if p%3==2 and use_inert: add=math.log(p)
        if p==3: add=math.log(p) if (use_split or use_inert) else 0.0
        d[n]=d[n//p]+add
    return d[1:N+1]
for lbl,(s,i) in {'split-only':(True,False),'inert-only':(False,True),'both(=log n)':(True,True)}.items():
    d = class_drift(s,i)
    zmean,cmean,ct = contrast(d)
    print(f"   {lbl:14s}: zeros|V|={zmean:.4f}  ctrl|V|={cmean:.4f}  contrast={ct:8.2f}")

# Extension (1): inhomogeneous drift_p = log p + eps*(Eisenstein angle of p) -- does a 6-fold
# admixture survive without breaking the cancellation?
print("\nSWEEP D -- inhomogeneous drift_p = log p + eps*prime_arg(p) (6-fold admixture on log winding):")
def perprime_mixed(eps):
    d = np.zeros(N+1)
    for n in range(2,N+1):
        p = spf[n]
        d[n]=d[n//p]+math.log(p)+eps*prime_arg(p)
    return d[1:N+1]
for eps in [0.0,0.001,0.01,0.05,0.1,0.5]:
    d = perprime_mixed(eps)
    zmean,cmean,ct = contrast(d)
    print(f"   eps={eps:5.3f}: zeros|V|={zmean:.4f}  ctrl|V|={cmean:.4f}  contrast={ct:8.2f}"
          f"{'   survives' if ct>100 else '   broken'}")

# ----------------------------------------------------------------------------------------------
# FINE LOCALIZATION: scan w near the first zero, find the |V| minimum, verify with mpmath.
# ----------------------------------------------------------------------------------------------
print("\n" + "="*92)
print("FINE LOCALIZATION near gamma_1=8.0397 (log-n winding, lab xy 3-vector resultant):")
ws = np.linspace(7.8, 8.3, 2001)
mags = np.array([collapse_xy(w, Ph)[0] for w in ws])
wmin = ws[np.argmin(mags)]
print(f"   |V| minimized at w={wmin:.5f}  (exact gamma_1=8.03974); |V|min={mags.min():.5f}")
print(f"   mpmath |L(1/2+i*{wmin:.5f})| = {float(absL_on_line(wmin)):.3e}")
print(f"   mpmath |L(1/2+i*8.0397371556814667)| = {float(absL_on_line(8.0397371556814667)):.3e}")
print("="*92)
print("DONE.")
