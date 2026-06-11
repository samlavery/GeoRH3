"""
EXP3d -- settle it: geometric log-spiral sum vs analytic sum, IDENTICAL truncation, IDENTICAL
         everything. Prove geometric = const * analytic, then both cancel at zeros (slowly,
         conditional convergence) and the geometry is a FAITHFUL realization (earned log + earned n^-1/2).
"""
import numpy as np
ZEROS=[8.0397371556814667,11.2492062077729352,15.7046191767216256,18.2619974956931276]
N=4000000
n=np.arange(1,N+1)
chi=np.where(n%3==1,1.0,np.where(n%3==2,-1.0,0.0))
c=1.0;R0=1.0;ds=1.0;K=R0*np.sqrt(1+c**2)/c
theta=(1.0/c)*np.log(1+n*ds*c/K)
R=R0*np.exp(c*theta)
amp_geo=R**(-0.5)
logn=np.log(n)
def geo(w): return abs(np.sum(chi*amp_geo*np.exp(-1j*w*theta)))
def ana(w): return abs(np.sum(chi*n**-0.5*np.exp(-1j*w*logn)))
print(f"N={N}. geometric (earned) vs analytic (placed), SAME truncation:")
print(f"{'gamma':>9} {'|geo|':>10} {'|ana|':>10} {'geo/ana':>9}")
for g in ZEROS:
    gg,aa=geo(g),ana(g)
    print(f"{g:9.4f} {gg:10.5f} {aa:10.5f} {gg/aa:9.5f}")
print(f"\n(geo/ana should be the constant amp_geo*sqrt(n)->{amp_geo[-1]*np.sqrt(N):.5f}, and BOTH small at zeros)")
print("\ncontrols (non-zero heights):")
for g in [3.0,5.0,13.0]:
    gg,aa=geo(g),ana(g)
    print(f"{g:9.4f} {gg:10.5f} {aa:10.5f} {gg/aa:9.5f}")
# ratio of zero-value to control-value (contrast): zeros should be << controls
print("\nCONTRAST: |geo| at zero 8.04 vs control 5.0:",f"{geo(8.0397):.4f} vs {geo(5.0):.4f}")
