"""
hex_theta-1.py  (ID: theta-1, H-THETA)  -- FAST, line-buffered.

MANDATE: build the REAL 3D Eisenstein/hexagonal solid FIRST (explicit (x,y,z) per
lattice point (a,b)), attach a spinning phasor at each 3D point, WIND, and measure
the chi3-weighted VECTOR resultant collapse -- never collapse straight to a scalar
sum over rational integers n (that re-derives the analytic L; PRIOR HONEST FINDING).

GEOMETRY (log-free structure):
  point (a,b) in Z[omega]  ->  (x,y,z) = ( a - b/2,  b*sqrt(3)/2,  N ),  N = a^2-ab+b^2.
  z is the INTEGER norm (the genuine log-free vertical lift). sqrt(3)/2 is a fixed
  lattice constant (planar hex aspect ratio), NOT a per-point analytic n^{-1/2}.

EXPLOITED ALGEBRA (eisenstein.py, verified):
  (1/6) sum_{(a,b)!=0} N^{-s} = zeta_{Q(sqrt-3)}(s) = zeta(s)*L(chi3,s);
  rep count  r(N) = #{(a,b):N(a,b)=N} = 6 * sum_{d|N} chi3(d)   (units x divisor twist).
"""
import sys
import numpy as np, mpmath as mp
mp.mp.dps = 30
P=lambda *a: print(*a, flush=True)

def chi3(n): return [0,1,-1][n%3]
def Lchi3(s): return 3**(-s)*(mp.zeta(s,mp.mpf(1)/3)-mp.zeta(s,mp.mpf(2)/3))
def zeta_K(s): return mp.zeta(s)*Lchi3(s)   # Dedekind zeta of Q(sqrt-3)

Z=[]
with open("lchi3_zeros_1000.txt") as f:
    for ln in f:
        ln=ln.strip()
        if ln and not ln.startswith("#"): Z.append(float(ln.split()[1]))
Z=sorted(Z)[:6]
midpts=[0.5*(Z[i]+Z[i+1]) for i in range(len(Z)-1)]
ZETA=[14.134725141734693,21.022039638771555,25.010857580145688,30.42487612585951]  # Riemann zeros

# ============================================================================
# STEP 1 -- BUILD THE REAL 3D SOLID (explicit coords) and PRINT a sample.
# ============================================================================
sqrt3=np.sqrt(3.0); B=240
A=np.arange(-B,B+1)
AA,BB=np.meshgrid(A,A,indexing='ij')
AA=AA.ravel(); BB=BB.ravel()
Nn=AA*AA-AA*BB+BB*BB
keep=Nn>0
AA,BB,Nn=AA[keep],BB[keep],Nn[keep]
Xc=AA-BB/2.0; Yc=BB*sqrt3/2.0
P("="*78)
P("STEP 1: 3D EISENSTEIN/HEXAGONAL SOLID  (a,b) -> (x,y,z=N=a^2-ab+b^2)")
P(f"  built {len(AA):,} lattice points, |a|,|b|<= {B}, max norm N={int(Nn.max()):,}")
P(f"  {'a':>4} {'b':>4} | {'x':>9} {'y':>9} {'z=N(int)':>9}")
shown=set()
for target in [1,1,1,3,3,7,13,19]:
    idx=np.where(Nn==target)[0]
    for k in idx:
        key=(int(AA[k]),int(BB[k]))
        if key not in shown:
            shown.add(key)
            P(f"  {int(AA[k]):4d} {int(BB[k]):4d} | {Xc[k]:9.4f} {Yc[k]:9.4f} {int(Nn[k]):9d}")
            break
# the six units N=1 sit on a hexagon at 6th-root angles
um=Nn==1
ang=np.sort(np.degrees(np.arctan2(Yc[um],Xc[um]))%360)
P("  six UNITS (N=1) angles (deg): "+", ".join(f"{t:.0f}" for t in ang)+
  "  multiples of 60=pi/3? "+str(bool(np.allclose(np.diff(np.r_[ang,ang[0]+360]),60))))

# rep counts r(N) on the solid (sieve), and the hexagonal identity r(N)=6 sum_{d|N} chi3(d)
maxN=int(Nn.max())
rN=np.bincount(Nn,minlength=maxN+1)
# divisor-twist b(N)=sum_{d|N} chi3(d) via sieve
bN=np.zeros(maxN+1,dtype=np.int64)
for d in range(1,maxN+1):
    c=chi3(d)
    if c: bN[d::d]+=c
P("  hexagonal rep-count identity  r(N) = 6 * sum_{d|N} chi3(d):")
for m in [1,3,7,13,19,21,49]:
    P(f"    N={m:3d}: lattice r(N)={int(rN[m]):3d}   6*b(N)={6*int(bN[m]):3d}   match={int(rN[m])==6*int(bN[m])}")

# present shells (sorted unique norms) for the phasor sums
uniqN=np.unique(Nn)
r_sh=rN[uniqN].astype(float)
b_sh=bN[uniqN].astype(float)
lgN=np.log(uniqN.astype(float))
ampN=uniqN.astype(float)**(-0.5)

# ============================================================================
# STEP 2 -- PHASOR at each 3D point: unit vector (cos(w F(N)), sin(w F(N))).
# All points in a shell share angle w*log(N); their weighted count is r(N) (lattice)
# or b(N)=r/6 (chi3-divisor twist). Amplitude N^{-1/2} (the Epstein/s=1/2 weight).
# ============================================================================
P("\n"+"="*78)
P("STEP 2: phasor unit-vector per 3D point; resultant = weighted vector sum, spins with w.")
def res_lattice(w):
    return (np.sum(r_sh*ampN*np.cos(w*lgN)), np.sum(r_sh*ampN*np.sin(w*lgN)))
def res_chi3twist(w):
    return (np.sum(b_sh*ampN*np.cos(w*lgN)), np.sum(b_sh*ampN*np.sin(w*lgN)))
P("  laws: (lattice) weight r(N); (chi3-twist) weight b(N)=sum_{d|N}chi3(d)=r(N)/6.")

# ============================================================================
# STEP 3a -- WIND raw lattice solid. Carries zeta_K=zeta*L(chi3): dips at BOTH families.
# ============================================================================
P("\n"+"="*78)
P("STEP 3a: WIND raw hex-lattice solid (Epstein/Dedekind partial sum, |a|,|b|<=240).")
P("  zeta_K=zeta*L(chi3): expect resultant DIP at BOTH zeta zeros AND chi3 zeros.")
P(f"  {'w':>9} {'|res lattice|':>14} {'|res chi3twist|':>16}  {'tag':>11}")
rows=sorted([(z,'chi3-ZERO') for z in Z[:4]]+[(z,'zeta-ZERO') for z in ZETA[:2]]+[(m,'mid') for m in midpts[:3]])
for w,tag in rows:
    lx,ly=res_lattice(w); cx,cy=res_chi3twist(w)
    P(f"  {w:9.4f} {np.hypot(lx,ly):14.5f} {np.hypot(cx,cy):16.5f}  {tag:>11}")
P("  NOTE: both weightings are real-part sums of a Dirichlet series with Mellin ~ zeta_K,")
P("  so STRUCTURALLY they carry zeta zeros too. A finite truncated phasor sum only DIPS")
P("  (doesn't vanish) -- it is a partial Epstein sum, not the completed L.")

# ============================================================================
# STEP 3b -- ALIGN-TO-AXIS directive item: do the phasors aim at the central axis
# (radially inward) at the chi3 zeros? Measure the resultant's radial vs total, and
# the mean inward alignment, on the SAME 3D solid (chi3-twist weighting).
# ============================================================================
P("\n"+"="*78)
P("STEP 3b: ALIGN-TO-AXIS test on the 3D solid (chi3-twist weight).")
P("  For each 3D point at planar angle phi=atan2(y,x), phasor dir = phi + w*log(N) (drift law:")
P("  geometric -- phase accumulates the lattice ANGLE plus winding*height). 'Inward' = -radial.")
P("  Measure mean inward component <-cos(dir-phi_radial-pi)> weighted by b(N); peak at zeros?")
# per-POINT (not shelled) so the geometry/axis is real
phi_pt=np.arctan2(Yc,Xc)             # planar angle of each 3D point
amp_pt=Nn.astype(float)**(-0.5)
sgn_pt=np.array([chi3(int(v)) for v in (AA% 3)]) if False else None
# chi3 as the lattice splitting character applied via b at the point's norm:
bpt=bN[Nn].astype(float)             # divisor-twist at each point's norm
def inward_alignment(w):
    # phasor direction at point = local planar angle phi rotated by w*log N (holonomy drift)
    ang=phi_pt + w*np.log(Nn.astype(float))
    # inward unit (toward axis) = -(cos phi, sin phi); alignment = phasor . inward
    align = -(np.cos(ang)*np.cos(phi_pt)+np.sin(ang)*np.sin(phi_pt))  # = -cos(w log N)
    # weighted mean by chi3 datum b(N)*amp
    wts=bpt*amp_pt
    return float(np.sum(wts*align)/ (np.sum(np.abs(wts))+1e-30))
P(f"  {'w':>9} {'inward-align(chi3 wt)':>22}  {'tag':>11}")
for w,tag in rows:
    P(f"  {w:9.4f} {inward_alignment(w):22.6f}  {tag:>11}")
P("  (analytically inward-align reduces to -<cos(w log N)>_b = -Re part; the 'axis aiming' is")
P("  the SAME resultant-real-part signal, just normalized. Honest: it is not new info.)")

# ============================================================================
# STEP 3c -- the chi3-ALONE completed L via the ODD chi3-theta. Isolates chi3 zeros
# (no zeta zeros). HONEST FLAG on whether it is hex-native or the analytic n-series.
# ============================================================================
P("\n"+"="*78)
P("STEP 3c: completed L(chi3) ALONE (odd chi3-theta). Mellin over the theta SCALE.")
# precompute psi_odd as vector over k once per t is slow in mpmath; do moderate Nmax with mp.
def psi_odd(t,Nmax=1500):
    s=mp.mpf(0)
    e=mp.e**(-mp.pi*t/3)   # base; term k uses e^{k^2}
    for k in range(1,Nmax+1):
        c=chi3(k)
        if c: s+= k*c*mp.power(e, k*k)
    return s
def Lambda_odd(s):
    f=lambda t: psi_odd(t)*t**((s+1)/2-1)
    return mp.quad(f,[0,mp.mpf('0.5'),1,3,12,mp.inf])
def Lambda_exact(s):
    return (mp.pi/3)**(-(s+1)/2)*mp.gamma((s+1)/2)*Lchi3(s)
P("  psi_odd(t)=sum_k k*chi3(k) e^{-pi k^2 t/3};  Lambda=int psi_odd t^{(s+1)/2} dt/t.")
P(f"  {'gamma':>11} {'|Lambda_odd|':>14} {'|Lambda_exact|':>15} {'tag':>10}")
for g,tag in [(Z[0],'chi3-ZERO'),(Z[1],'chi3-ZERO'),(Z[2],'chi3-ZERO'),(ZETA[0],'zeta-ZERO'),(10.0,'mid')]:
    s=mp.mpf('0.5')+1j*mp.mpf(repr(g))
    lo=Lambda_odd(s); le=Lambda_exact(s)
    P(f"  {g:11.5f} {float(abs(lo)):14.4e} {float(abs(le)):15.4e} {tag:>10}")
P("  Lambda_odd vanishes at chi3 zeros ONLY (no dip at zeta zero) = L(chi3) alone.")
P("  HONEST FLAG: exponents are k^2 with k a RATIONAL integer and weight k (NOT r(N)/b(N)).")
P("  => this is the ANALYTIC odd-character theta = L(chi3) directly; NOT a 2D hex-lattice")
P("     phasor sum. The genuine lattice sums (3a/3b) are zeta_K and cannot shed the zeta zeros.")

# ============================================================================
# Dirichlet identity check (fast finite partial sum, not nsum):
#   sum_{N<=M} b(N) N^{-s} -> zeta(s) L(chi3,s)
# ============================================================================
P("\n"+"="*78)
P("CHECK: sum_{N<=M} (sum_{d|N}chi3 d) N^{-s} -> zeta(s) L(chi3,s)=zeta_K(s) (so lattice=zeta_K):")
for s0 in [mp.mpf(2),mp.mpf(3)]:
    M=20000
    ps=mp.mpf(0)
    for m in range(1,M+1):
        bm=int(bN[m]) if m<=maxN else sum(chi3(d) for d in range(1,m+1) if m%d==0)
        if bm: ps+=bm*mp.power(m,-s0)
    P(f"  s={int(s0)}: partial(M={M})={mp.nstr(ps,12)}   zeta_K={mp.nstr(zeta_K(s0),12)}   "
      f"close={mp.almosteq(ps,zeta_K(s0),rel_eps=mp.mpf(10)**-6)}")
P("\nDONE.")
