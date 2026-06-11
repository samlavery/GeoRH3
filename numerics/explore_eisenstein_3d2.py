"""
explore_eisenstein_3d2.py -- the GENUINELY geometric probes: 6th-root angular phasors at
real 3D lattice points, and whether the hexagonal norm-count gives a cleaner zero handle
than the rational RvM. Build coords, print, then measure. Minimize log/sqrt in STRUCTURE.
"""
import numpy as np, mpmath as mp
mp.mp.dps = 30

def chi3(n):
    r = n % 3
    return 1 if r == 1 else (-1 if r == 2 else 0)
def Lchi3(s): return mp.power(3,-s)*(mp.zeta(s, mp.mpf(1)/3) - mp.zeta(s, mp.mpf(2)/3))

gam = []
with open("/Users/samuellavery/proof/three/numerics/lchi3_zeros_1000.txt") as f:
    for ln in f:
        ln = ln.strip()
        if ln and not ln.startswith("#"):
            gam.append(float(ln.split()[1]))
gam = sorted(gam); Z = gam[:8]

# ----------------------------------------------------------------------------
# Build lattice. Eisenstein a+b*omega, omega = e^{2pi i/3}.
# Embed: z_lat = a + b*omega as a COMPLEX number (the genuine Eisenstein integer).
# Then |z_lat|^2 = a^2 - ab + b^2 = norm.  arg(z_lat) = lattice angle (6th-root sector).
# ----------------------------------------------------------------------------
omega = np.exp(2j*np.pi/3)
B = 200
A_=[]; Bb_=[]
for a in range(-B,B+1):
    for b in range(-B,B+1):
        if a==0 and b==0: continue
        A_.append(a); Bb_.append(b)
A_=np.array(A_,float); Bb_=np.array(Bb_,float)
zlat = A_ + Bb_*omega                 # genuine Eisenstein integer in C
NRM = np.abs(zlat)**2                  # = a^2-ab+b^2 exactly
ANG = np.angle(zlat)                   # the lattice DIRECTION (6th-root structure)
order = np.argsort(NRM)
A_,Bb_,zlat,NRM,ANG = A_[order],Bb_[order],zlat[order],NRM[order],ANG[order]
NRM_r = np.round(NRM).astype(int)

print("="*76)
print("OBJECT: each Eisenstein integer z = a+b*omega placed at REAL 3D point")
print("   (x,y,z3) = (Re z, Im z, height).  |z|^2 = a^2-ab+b^2 = norm (NO sqrt in coord).")
print("   PHASOR at each point = a real 2D unit vector with direction = winding-spun.")
print("="*76)

# ============================================================================
# HYP C -- 6TH-ROOT ANGULAR PHASOR (the directive's centerpiece).
# Place phasor at each lattice point pointing along the lattice DIRECTION arg(z).
# As we WIND by parameter y, spin each phasor by the lattice angle times a rate.
# The chi3 character sits on the *norm class mod 3* via a(norm). Test: is there a
# drift law on the ANGLE (not on log) that makes the chi3-weighted vector sum
# collapse at the zeros? The key new ingredient: phase = y * (lattice geometry),
# NOT y*log n. Sweep the geometric phase candidates.
# ============================================================================
print("\n--- HYP C: ANGULAR / GEOMETRIC phase (replace y*log n by y*geom) ---")
# chi3 weight per lattice point: use chi3 of the norm's residue is wrong; the genuine
# Dedekind coefficient is a(m)=sum_{d|m}chi3(d) per NORM. Per lattice point, weight = a(norm)/r(norm).
# Simpler & honest: weight each point by chi3(norm mod ... ) -- NO. Use the Hecke/character:
# the Eisenstein character on points is chi3 evaluated on the norm is NOT a character.
# Correct chi3-carrying object on the lattice: chi3(a^2-ab+b^2) is NOT multiplicative.
# So we weight by the divisor sum a(m) assigned to the shell, split evenly over reps.
maxm = NRM_r.max()
def divisor_chi_sum(m):
    s=0; d=1
    while d*d<=m:
        if m%d==0:
            s+=chi3(d)
            if d!=m//d: s+=chi3(m//d)
        d+=1
    return s
# build shell coefficient lookup
shell_a = {}
for m in np.unique(NRM_r):
    shell_a[int(m)] = divisor_chi_sum(int(m))
# count reps per shell
from collections import Counter
repcount = Counter(NRM_r.tolist())
w_pt = np.array([shell_a[int(m)]/repcount[int(m)] for m in NRM_r])  # per-point chi3 weight

# candidate geometric phases (NO log): test each as the winding phase phi(point)
cands = {
    "log(norm)/2 [control=analytic]": 0.5*np.log(NRM),
    "lattice angle ANG":              ANG,
    "norm itself (linear)":           NRM,
    "sqrt(norm)=|z| (radial dist)":   np.sqrt(NRM),
    "norm^{1/3}":                     NRM**(1/3),
    "ANG*6/pi (sector index)":        ANG*6/np.pi,
}
def collapse(phase, y, amp):
    return abs(np.sum(w_pt*amp*np.exp(-1j*y*phase)))
amp_rad = NRM**(-0.5)   # 1/|z| radial amplitude (natural, = n^{-1/2} analogue but geometric)
print("  defect = |sum_pts w_pt * (1/|z|) * exp(-i y phase)| at chi3 zeros (cutoff norm<=%d):"%maxm)
print(f"  {'phase law':>34} " + " ".join(f"g={g:.1f}" for g in Z[:4]))
for nm,ph in cands.items():
    ds = [collapse(ph, g, amp_rad) for g in Z[:4]]
    print(f"  {nm:>34} " + " ".join(f"{d:7.3f}" for d in ds))
print("  (a law that gives SMALL defects ONLY at zeros = a real geometric handle.")
print("   log(norm)/2 is the analytic control; if ONLY it cancels, no new structure yet.)")

# ============================================================================
# HYP D -- HEXAGONAL NORM-COUNT RvM vs RATIONAL RvM. Does ordering events by the
# DISTINCT NORM VALUES (the hexagonal "energy levels") predict zero spacing more
# cleanly than rational RvM? The distinct norms are {1,3,4,7,9,12,13,...} (norms of
# Eisenstein integers = numbers with all primes=2mod3 to even powers). The zero
# COUNTING function N(T) ~ (T/2pi)(log(T/2pi)-1)+... ; the hex side predicts the
# density via the lattice. Test: is the kth zero height tied to the kth norm shell?
# ============================================================================
print("\n--- HYP D: hexagonal NORM SHELLS vs zero heights ---")
distinct_norms = sorted(set(NRM_r.tolist()))
print("  first 20 representable hex norms:", distinct_norms[:20])
# count of distinct norms <= X (these are the "Eisenstein energy levels")
print("  #distinct-norms <= X  vs  X / (some const):")
for X in [50, 200, 1000]:
    c = sum(1 for m in distinct_norms if m<=X)
    print(f"    X={X:5d}: #levels={c:5d}   X/#levels={X/c:.3f}")
# chi3 zero count up to T: N(T) ~ (T/2pi) log(T/(2pi e)) + ... compare height growth
print("  chi3 zero index k vs height gamma_k vs RvM N_eff=sqrt(3 g/2pi):")
for k in [1,2,3,5,8]:
    g = Z[k-1] if k<=8 else gam[k-1]
    Neff = np.sqrt(3*g/(2*np.pi))
    print(f"    k={k}: gamma={g:8.4f}  N_eff={Neff:6.3f}  N_eff^2={Neff**2:7.3f}  (2pi/3)N_eff^2={2*np.pi/3*Neff**2:.4f}")

print("\nDONE explore pass 2.")
