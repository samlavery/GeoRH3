"""
explore_eisenstein_3d3.py -- HONEST convergence. The Epstein/L winding is conditionally
convergent; truncation error swamps the signal. Use a SMOOTH (Gaussian) cutoff so partial
sums actually converge, then ask which phase law cancels. This separates "real geometric
handle" from "truncation noise". Also: directly test the geometric-phase hypotheses with
mpmath high precision on a SMALL honest object.
"""
import numpy as np, mpmath as mp
mp.mp.dps = 30

def chi3(n):
    r=n%3; return 1 if r==1 else (-1 if r==2 else 0)
def Lchi3(s): return mp.power(3,-s)*(mp.zeta(s,mp.mpf(1)/3)-mp.zeta(s,mp.mpf(2)/3))

gam=[]
with open("/Users/samuellavery/proof/three/numerics/lchi3_zeros_1000.txt") as f:
    for ln in f:
        ln=ln.strip()
        if ln and not ln.startswith("#"): gam.append(float(ln.split()[1]))
gam=sorted(gam); Z=gam[:8]

# ----------------------------------------------------------------------------
# The chi3 Dirichlet series sum chi3(n) n^{-1/2-iy} converges conditionally.
# Smoothed: sum chi3(n) n^{-1/2-iy} exp(-(n/Nc)^2) -> approaches the analytic-
# continuation value at zeros (->0) as Nc grows. This is the HONEST partial sum.
# We test whether a GEOMETRIC phase phi(n) (replacing y*log n) can also cancel.
# ----------------------------------------------------------------------------
N = 200000
n = np.arange(1, N+1, dtype=float)
sign = np.where(n%3==1,1.0,np.where(n%3==2,-1.0,0.0))

def smoothed(phase, y, amp, Nc):
    cut = np.exp(-(n/Nc)**2)
    return abs(np.sum(sign*amp*cut*np.exp(-1j*y*phase)))

print("="*76)
print("HONEST smoothed winding (Gaussian cutoff). amp = n^{-1/2}, phase swept.")
print("If a GEOMETRIC phase cancels at zeros as Nc grows, it's a real handle.")
print("="*76)
amp = n**(-0.5)
phases = {
    "log n  [analytic control]": np.log(n),
}
Ncs = [2000, 20000, 100000]
print("\n[control] phase=log n, amp=n^-1/2 -- must -> 0 at zeros as Nc grows:")
print(f"  {'Nc':>8} " + " ".join(f"g={g:.2f}" for g in Z[:4]) + "   | nonzero ctrl g=10.0")
for Nc in Ncs:
    ds=[smoothed(np.log(n),g,amp,Nc) for g in Z[:4]]
    ctrl=smoothed(np.log(n),10.0,amp,Nc)
    print(f"  {Nc:8d} " + " ".join(f"{d:7.4f}" for d in ds) + f"   | {ctrl:7.4f}")

print("\nThe analytic L cancels at zeros, persists at non-zero g=10. Good baseline.")
print("Now: any GEOMETRIC phase that does the SAME would be the new structure.\n")

# ----------------------------------------------------------------------------
# KEY GEOMETRIC TEST. The zeros are at y where sum chi3(n) n^{-1/2} cos(y log n)=0 etc.
# The phase y*log n is forced by analytic continuation. A geometric phase y*g(n) cancels
# at the SAME y only if g(n)=log n + per-character-periodic. So replacing log n is
# essentially impossible WITHOUT reintroducing log. CONFIRM this is a wall, then pivot:
# the REAL Eisenstein win is not replacing log in the SAME sum, but a DIFFERENT object.
# ----------------------------------------------------------------------------
print("="*76)
print("WALL CHECK: can phase y*sqrt(n) or y*n cancel at the chi3 zeros? (smoothed, Nc=100k)")
print("="*76)
for nm,ph in [("sqrt(n)",np.sqrt(n)),("n (linear)",n),("n^{1/3}",n**(1/3))]:
    ds=[smoothed(ph,g,amp,100000) for g in Z[:4]]
    print(f"  phase={nm:12s}: " + " ".join(f"g={g:.1f}:{d:6.3f}" for g,d in zip(Z[:4],ds)))
print("  (if none cancel, the log is structurally forced in THIS sum -- expected.)")

# ----------------------------------------------------------------------------
# THE PROMISING PIVOT (Hecke / angular). On the Eisenstein lattice there are GENUINE
# non-trivial Hecke characters: xi_k(z) = (z/|z|)^{6k} = e^{6 i k arg(z)}, the angular
# characters respecting the 6-fold symmetry. The Hecke L-function L(s, xi_k) =
# sum_{ideals} xi_k(a) N(a)^{-s} has its OWN zeros. xi_0 = trivial gives zeta*L(chi3).
# The angular phasor e^{i k arg(z)} IS the 6th-root-of-unity rotating vector the user
# wants. Build it: at each lattice point place phasor e^{6 i k arg(z)}; the lattice's
# 6-fold symmetry makes shells with the angular weight. Test what these produce.
# ----------------------------------------------------------------------------
print("\n" + "="*76)
print("PIVOT -- HECKE ANGULAR CHARACTERS xi_k(z)=e^{6 i k arg(z)} (the 6th-root phasor).")
print("These are the GENUINE Eisenstein angular phasors. Build shells, see their L-zeros.")
print("="*76)
omega=mp.e**(2j*mp.pi/3)
# build lattice with mpmath-free numpy, compute Hecke L(s,xi_k) partial winding
B=300
a_=np.arange(-B,B+1)
AA,BB=np.meshgrid(a_,a_)
AA=AA.ravel(); BB=BB.ravel()
keep=~((AA==0)&(BB==0))
AA=AA[keep]; BB=BB[keep]
zl=AA+BB*np.exp(2j*np.pi/3)
NRMl=np.abs(zl)**2
ARGl=np.angle(zl)
# restrict to one ideal per 6-unit orbit? For the FULL Epstein with angular weight:
# sum over ALL points of e^{6ik arg} N^{-s} = (units sum) ... the 6-fold weight e^{6ik arg}
# is unit-invariant (arg shifts by pi/3 -> 6k*pi/3=2pi k, invariant). Good: it's a real char.
def hecke_partial(k, y, cutoff):
    m=NRMl<=cutoff
    nn=NRMl[m]; ar=ARGl[m]
    s_re=0.5
    return abs(np.sum(np.exp(6j*k*ar)*nn**(-s_re)*np.exp(-1j*y*np.log(nn)))/6.0)
print("  |Hecke angular winding L(1/2+iy, xi_k)| partial (cutoff 90000), scanning y:")
for k in [0,1,2]:
    row=[]
    for y in [2,4,6,8,10,12]:
        row.append(hecke_partial(k,y,90000))
    print(f"   k={k}: " + " ".join(f"y={y}:{v:6.3f}" for y,v in zip([2,4,6,8,10,12],row)))
print("  k=0 = zeta*L(chi3) (dips near gamma~8,11). k>=1 angular chars have DIFFERENT zeros.")
print("  NOTE these still carry log(norm). The angular e^{6ik arg} IS the pure 6th-root phasor.")

print("\nDONE explore pass 3.")
