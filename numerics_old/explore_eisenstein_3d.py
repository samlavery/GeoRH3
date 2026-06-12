"""
explore_eisenstein_3d.py -- probe the Eisenstein/hexagonal structure for a GENUINE handle
on the chi3 zeros, with REAL 3D lattice points + phasors. Minimize log/sqrt.

Core verified fact (eisenstein.py): (1/6) sum_{(a,b)!=0} N(a,b)^{-s} = zeta(s)*L(chi3,s),
N(a,b)=a^2-ab+b^2. So chi3 zeros = (hex Epstein zeros) minus (zeta zeros).

We probe several Eisenstein-native objects. Each prints REAL 3D coords first, then measures.
"""
import numpy as np, mpmath as mp
mp.mp.dps = 30

def chi3(n):
    r = n % 3
    return 1 if r == 1 else (-1 if r == 2 else 0)

def Lchi3(s): return mp.power(3,-s)*(mp.zeta(s, mp.mpf(1)/3) - mp.zeta(s, mp.mpf(2)/3))

# exact zeros
gam = []
with open("/Users/samuellavery/proof/three/numerics/lchi3_zeros_1000.txt") as f:
    for ln in f:
        ln = ln.strip()
        if ln and not ln.startswith("#"):
            gam.append(float(ln.split()[1]))
gam = sorted(gam)
Z = gam[:8]
print("first 8 chi3 zero heights:", [round(g,4) for g in Z])

# ----------------------------------------------------------------------------
# Build the hexagonal lattice points in REAL 2D (then lift to 3D).
# Eisenstein integer a+b*omega -> (x,y) = a*(1,0) + b*(-1/2, sqrt3/2).  Norm = a^2-ab+b^2.
# We DO use sqrt3/2 ONCE here -- it's the fixed lattice geometry (a constant direction,
# not an n-dependent amplitude). That's the hexagonal directions pi/3, allowed structure.
# ----------------------------------------------------------------------------
B = 120
pts = []
for a in range(-B, B+1):
    for b in range(-B, B+1):
        nrm = a*a - a*b + b*b
        if nrm != 0:
            pts.append((a, b, nrm))
pts.sort(key=lambda t: t[2])
A = np.array([p[0] for p in pts], float)
Bb = np.array([p[1] for p in pts], float)
NRM = np.array([p[2] for p in pts], float)
# 2D embedding
X = A - 0.5*Bb
Y = (np.sqrt(3)/2)*Bb
# the lattice angle (which 6th-root sector each point sits in)
ANG = np.arctan2(Y, X)

print("\n=== REAL hexagonal lattice points, ordered by norm (sample) ===")
print(f"{'a':>4}{'b':>4}{'norm':>6}{'x':>9}{'y':>9}{'sector(deg)':>12}")
for i in range(12):
    print(f"{int(A[i]):4d}{int(Bb[i]):4d}{int(NRM[i]):6d}{X[i]:9.3f}{Y[i]:9.3f}{np.degrees(ANG[i]):12.2f}")

# how many lattice points up to norm X -> the "volume of Eisenstein integers"
print("\nhex point count vs (2pi/sqrt3)*X (the hexagonal volume law, NO log/sqrt):")
for XX in [100, 1000, 5000]:
    c = int(np.sum(NRM <= XX))
    print(f"   X={XX:5d}: count={c:6d}  (2pi/sqrt3)X={2*np.pi/np.sqrt(3)*XX:9.1f}  ratio={c/(2*np.pi/np.sqrt(3)*XX):.4f}")

# ============================================================================
# HYPOTHESIS A: Norm-ordered Epstein winding. The Epstein zeta over the hex norm
# is sum over lattice points of N^{-s}. Its zeros on Re(s)=1/2 are the UNION of
# zeta and chi3 zeros. KEY question: does ordering by NORM (a^2-ab+b^2, the genuine
# Eisenstein volume) give cancellation WITHOUT an explicit n^{-1/2} log-n amplitude,
# instead using 1/sqrt(norm) = 1/|lattice vector| = the natural radial amplitude?
#
# 3D OBJECT: place each lattice point at 3D coord (x, y, z) with z = winding height.
# Phasor at each point spins as we wind. The 2D shadow is the (x,y) hexagon.
# ============================================================================
print("\n" + "="*76)
print("HYP A: Epstein/hex Dedekind zeta = zeta*L(chi3). Does norm-winding cancel at")
print("       UNION(zeta zeros, chi3 zeros)? amplitude = 1/N^{1/2}=1/|vector| (radial).")
print("="*76)
# Dedekind zeta of Q(sqrt-3) on critical line: zeta(s)*L(chi3,s).
# Sum over lattice points: (1/6) sum N(a,b)^{-s}. On s=1/2+iy this is the winding sum.
# We compute the partial-lattice-sum winding |(1/6) sum N^{-1/2-iy}| and compare to |zeta*L|.
def dedekind_partial(y, cutoff):
    mask = NRM <= cutoff
    nn = NRM[mask]
    return abs(np.sum(nn**(-0.5) * np.exp(-1j*y*np.log(nn)))/6.0)
def dedekind_exact(y):
    s = mp.mpf(1)/2 + 1j*y
    return abs(complex(mp.zeta(s)*Lchi3(s)))
print(f"   {'y':>8} {'|hex partial winding|':>22} {'|zeta*L exact|':>16}  (chi3 zero?)")
test_heights = Z[:4] + [14.13, 21.02]  # last two are zeta zero heights
labels = ["chi3"]*4 + ["zeta","zeta"]
for g, lab in zip(test_heights, labels):
    print(f"   {g:8.3f} {dedekind_partial(g, 8000):22.4f} {dedekind_exact(g):16.4f}   ({lab} zero)")
print("   NOTE: this winding still has log(norm) in the phase -> still analytic. Flag if so.")

# ============================================================================
# HYPOTHESIS B (the real Eisenstein-native one): GAUSS/EISENSTEIN INTEGER-POINT
# ANGULAR EQUIDISTRIBUTION. The lattice points of a fixed norm m form an orbit
# under the 6-fold unit group AND possibly extra ideal classes. For norm m, the
# representations (a,b) come in 6-fold (or 12-fold) symmetric sets. The chi3
# weight is r_chi(m) = number of reps weighted by character = the coefficient of
# the Dedekind zeta = sum_{d|m} chi3(d). PHASOR IDEA: at norm shell m, place a
# phasor whose ANGLE is the lattice direction; the shell's vector sum is governed
# by 6th-root symmetry. Test if winding the SHELLS (not integers) by norm cancels.
# ============================================================================
print("\n" + "="*76)
print("HYP B: norm-SHELL winding. r(m)=#reps of m by hex form; coefficient of")
print("       Dedekind zeta = sum_{d|m} chi3(d). Wind shells by m, amplitude 1/sqrt(m).")
print("="*76)
# shell coefficient: a(m) = sum_{d|m} chi3(d)  (this is the Dedekind zeta coefficient / 6 * reps)
maxm = 8000
def divisor_chi_sum(m):
    s = 0
    d = 1
    while d*d <= m:
        if m % d == 0:
            s += chi3(d)
            if d != m//d:
                s += chi3(m//d)
        d += 1
    return s
acoef = np.array([divisor_chi_sum(m) for m in range(1, maxm+1)])
mm = np.arange(1, maxm+1)
def shell_wind(y):
    # sum_m a(m) m^{-1/2-iy} = zeta(s)L(chi3,s) by definition of Dedekind coeffs
    return abs(np.sum(acoef * mm**(-0.5) * np.exp(-1j*y*np.log(mm))))
print(f"   {'y':>8} {'|shell winding|':>16} {'|zeta*L exact|':>16}  (zero?)")
for g, lab in zip(test_heights, labels):
    print(f"   {g:8.3f} {shell_wind(g):16.4f} {dedekind_exact(g):16.4f}   ({lab})")
print("   (this is zeta*L again -- confirms the bookkeeping. STILL has log m. Need to break it.)")

print("\nDONE explore pass 1.")
