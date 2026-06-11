"""
Off-line penalty test (chi3).  Move a zero off the critical line and watch two functionals:
 (1) Green-Helmholtz prime-side energy  ~ contribution  int 1/[(1/2-b)^2+(nu-g)^2]/(mu^2+nu^2) dnu
      -> does moving off-line make it NEGATIVE (forcing) or just change finitely (no forcing)?
 (2) Weil/Li per-zero contribution  c_n(rho) = 1 - Re[(1-1/rho)^n]
      -> on-line: bounded, >=0 ; off-line (Re<1/2): grows NEGATIVE = the penalty.
"""
import numpy as np
import mpmath as mp
from scipy import integrate
mp.mp.dps = 20

# --- chi3 zeros (on-line) ---
L=lambda s: mp.power(3,-s)*(mp.zeta(s,mp.mpf(1)/3)-mp.zeta(s,mp.mpf(2)/3))
ts=np.arange(0.5,80,0.05); av=np.array([float(abs(L(mp.mpf(1)/2+1j*mp.mpf(float(t))))) for t in ts])
gam=[]
for i in range(1,len(av)-1):
    if av[i]<av[i-1] and av[i]<av[i+1] and av[i]<0.4:
        r=mp.findroot(lambda t:L(mp.mpf(1)/2+1j*t),mp.mpf(float(ts[i])))
        g=float(mp.re(r))
        if (not gam or abs(g-gam[-1])>1e-3) and abs(L(mp.mpf(1)/2+1j*mp.mpf(g)))<1e-8: gam.append(g)
gam=np.array(sorted(g for g in gam if g>0)); print(f"chi3 zeros: {len(gam)} up to 80\n")

# ============ (1) Green-Helmholtz energy contribution: on-line vs off-line ============
mu=1.0; g1=gam[0]
def gh_contrib(beta):
    a=abs(0.5-beta)
    f=lambda nu: 1.0/((a*a+(nu-g1)**2))/(mu*mu+nu*nu)
    val,_=integrate.quad(f,-np.inf,np.inf,limit=200)
    return val
print("(1) Green-Helmholtz per-zero energy  int 1/[(1/2-b)^2+(nu-g)^2]/(mu^2+nu^2)  (g=%.2f):"%g1)
for beta in [0.500001,0.55,0.65,0.80,0.95]:
    print(f"    Re(rho)=beta={beta:.3f}  (off by {abs(0.5-beta):.3f})  ->  energy = {gh_contrib(beta):10.4f}")
print("    => on-line (b->1/2) diverges/large; off-line FINITE and SMALLER; all >0.  Moving off-line is CHEAPER, never negative.\n")

# ============ (2) Weil/Li per-zero contribution c_n(rho) = 1 - Re[(1-1/rho)^n] ============
def c_n(rho, n): return float(1 - mp.re((1 - 1/rho)**n))
print("(2) Weil/Li per-zero contribution  c_n(rho)=1-Re[(1-1/rho)^n]   (g=%.2f):"%g1)
print(f"{'n':>5} {'on-line b=1/2':>15} {'off-line b=0.30':>16} {'off-line b=0.10':>16}")
on=mp.mpf(1)/2+1j*mp.mpf(g1); o3=mp.mpf('0.30')+1j*mp.mpf(g1); o1=mp.mpf('0.10')+1j*mp.mpf(g1)
for n in [1,5,20,50,100,200,400,800,1500]:
    print(f"{n:>5} {c_n(on,n):>15.4f} {c_n(o3,n):>16.4f} {c_n(o1,n):>16.4f}")
print("    => on-line c_n stays in [0,2]; off-line (Re<1/2) GROWS NEGATIVE without bound = the penalty.\n")

# ============ full Li lambda_n: actual on-line set vs one zero moved off-line ============
def pair(g,n): return 2*c_n(mp.mpf(1)/2+1j*mp.mpf(g), n)   # on-line conj pair contribution
def quad(b,g,n):  # off-line FE+conj quadruple {b±ig, (1-b)±ig}
    s=mp.mpf(0)
    for re in (mp.mpf(b),1-mp.mpf(b)):
        for im in (mp.mpf(g),-mp.mpf(g)):
            s+= 1 - mp.re((1-1/(re+1j*im))**n)
    return float(s)
print("full Li lambda_n :  all-on-line   vs   gamma_1 moved off to a {0.10,0.90}±ig quadruple")
print(f"{'n':>5} {'lambda_n ON (>=0)':>18} {'lambda_n OFF':>14}")
for n in [1,10,40,100,300,700,1500,3000]:
    lon=sum(pair(g,n) for g in gam)
    loff=lon - pair(g1,n) + quad(0.10,g1,n)
    print(f"{n:>5} {lon:>18.3f} {loff:>14.3f}")
