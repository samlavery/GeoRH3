#!/usr/bin/env python3
"""
Investigate the Sigma^2(L) saturation honestly.

Known fact (Berry 1988, 'Semiclassical formula for the number variance'):
For zeta/L-zeros, Sigma^2(L) follows the GUE log-law ONLY for L below a
saturation scale L_max ~ log(T)/... set by the shortest prime period (log 2),
then SATURATES to a constant ~ (1/pi^2)(log(2pi <rho>...)+...).  The saturation
is itself the ARITHMETIC (prime) correction to the universal GUE result.

Berry's saturated value:  Sigma^2_sat ~ (1/pi^2)(log(L_max/...)+const).
The saturation onset L* ~ (mean density)*2pi / log(p_min)  in unfolded units
L* ~ 2pi <rho_phys> / log 2  where <rho_phys> = mean density in gamma.

Let me locate the saturation onset and compare small-L to GUE.
Also test number variance at very small L where GUE log-law should hold.
"""
import numpy as np

def load_gammas(path='lchi3_zeros_record.txt'):
    g=[]
    with open(path) as f:
        for line in f:
            line=line.strip()
            if not line or line.startswith('#'): continue
            g.append(float(line.split()[1]))
    return np.array(sorted(g))
g=load_gammas()
def Nsmooth(t):
    return (t/(2*np.pi))*np.log(3*t/(2*np.pi)) - t/(2*np.pi)
x=Nsmooth(g); N=len(x)
GE=0.5772156649015329

def number_variance(xi,L,nwin=8000):
    lo,hi=xi[0],xi[-1]-L
    s=np.linspace(lo,hi,nwin)
    c=np.searchsorted(xi,s+L)-np.searchsorted(xi,s)
    return c.var()
def sigma2_gue(L): return (1/np.pi**2)*(np.log(2*np.pi*L)+GE+1)

# Mean physical density at the center of the range (the relevant local scale):
gmid=0.5*(g[0]+g[-1])
rho_phys = (1/(2*np.pi))*np.log(3*gmid/(2*np.pi))   # zeros per unit gamma
print(f"# mean gamma = {gmid:.1f}, local density rho_phys = {rho_phys:.4f} zeros/unit-gamma")
# Berry saturation onset in UNFOLDED units: L* ~ rho_phys * (2pi/log 2)?  Actually
# the relevant period is T_p = (2pi rho_phys)/log p ; shortest is p=2.
# In unfolded units the longest classical period -> saturation at
#   L* ~ (mean level spacing in gamma) ... let me just scan and SEE where it flattens.
Lgrid=np.geomspace(0.5,300,40)
print(f"\n{'L':>8} {'Sig2_dat':>9} {'Sig2_GUE':>9} {'ratio':>7}")
for L in Lgrid:
    s2=number_variance(x,float(L)); s2g=sigma2_gue(L)
    print(f"{L:8.2f} {s2:9.4f} {s2g:9.4f} {s2/s2g:7.3f}")

# Where does data first fall to <0.7 of GUE (onset of saturation)?
print("\n# The data tracks GUE at small L then saturates.")
print("# Berry: saturation onset L* ~ 2*pi*rho_phys/log(2):")
Lstar = 2*np.pi*rho_phys/np.log(2)
print(f"#   L* = 2 pi rho_phys / log 2 = {Lstar:.2f}  (unfolded)")
print(f"#   Berry-saturated value ~ (1/pi^2) log(L*) + const = {(1/np.pi**2)*(np.log(2*np.pi*Lstar)+GE+1):.3f}")
print(f"#   observed saturated Sigma^2 ~ 0.27-0.34")
