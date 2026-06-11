"""
Hilbert-Polya fits for L(chi3) zeros:
 (A) Weyl law:  N(T) = (T/2pi) log(3T/2pi e)   -- the HP spectral density (counting staircase).
 (B) GUE spacing: unfold the gaps, fit nearest-neighbor distribution to
     GUE Wigner surmise P(s)=(32/pi^2) s^2 exp(-4 s^2/pi)  vs  Poisson e^{-s}.
     GUE (level repulsion) = the signature the zeros are eigenvalues of a self-adjoint operator.
"""
import numpy as np, math
import mpmath as mp
mp.mp.dps = 12

L = lambda s: mp.power(3,-s)*(mp.zeta(s,mp.mpf(1)/3)-mp.zeta(s,mp.mpf(2)/3))

# --- collect chi3 zeros up to T ---
T = 280.0
ts = np.arange(0.5, T, 0.04)
av = np.array([float(abs(L(mp.mpf(1)/2+1j*mp.mpf(float(t))))) for t in ts])
g = []
for i in range(1, len(av)-1):
    if av[i] < av[i-1] and av[i] < av[i+1] and av[i] < 0.35:
        r = mp.findroot(lambda t: L(mp.mpf(1)/2+1j*t), mp.mpf(float(ts[i])))
        gg = float(mp.re(r))
        if (not g or abs(gg-g[-1]) > 1e-3) and abs(L(mp.mpf(1)/2+1j*mp.mpf(gg))) < 1e-7:
            g.append(gg)
g = np.array(sorted(x for x in g if x > 0))
print(f"chi3 zeros found: {len(g)} up to T={T}\n")

# --- (A) Weyl law fit ---
def Nsmooth(t): return (t/(2*np.pi))*np.log(3*t/(2*np.pi*np.e))
k = np.arange(1, len(g)+1)
resid = k - Nsmooth(g)
print("(A) Weyl law  N(T) = (T/2pi) log(3T/2pi e):  staircase k  vs  smooth")
for j in [0, len(g)//4, len(g)//2, 3*len(g)//4, len(g)-1]:
    print(f"     gamma={g[j]:8.3f}   k={k[j]:4d}   N_smooth={Nsmooth(g[j]):8.3f}   diff={resid[j]:+.3f}")
print(f"     RMS(k - N_smooth) = {np.sqrt(np.mean(resid**2)):.3f}  (bounded fluctuation => Weyl density holds)\n")

# --- (B) unfold spacings and fit GUE vs Poisson ---
rho = (1/(2*np.pi))*np.log(3*g/(2*np.pi))      # local density N'(gamma)
s = np.diff(g) * (0.5*(rho[1:]+rho[:-1]))      # unfolded gaps, mean ~ 1
s = s[np.isfinite(s)]
print(f"(B) GUE spacing fit:  {len(s)} unfolded gaps,  mean(s) = {s.mean():.3f}")

def P_GUE(x):  return (32/np.pi**2) * x**2 * np.exp(-4*x**2/np.pi)
def P_Poi(x):  return np.exp(-x)

bins = np.linspace(0, 3.0, 13)
hist, edges = np.histogram(s, bins=bins, density=True)
ctr = 0.5*(edges[1:]+edges[:-1])
chi2_gue = np.sum((hist - P_GUE(ctr))**2)
chi2_poi = np.sum((hist - P_Poi(ctr))**2)
print(f"   sum-sq residual to GUE  = {chi2_gue:.4f}")
print(f"   sum-sq residual to Poisson = {chi2_poi:.4f}   ({'GUE wins' if chi2_gue<chi2_poi else 'Poisson wins'})")
print(f"   level repulsion: fraction of gaps < 0.5  = {np.mean(s<0.5):.3f}  "
      f"(GUE predicts {np.trapz(P_GUE(np.linspace(0,0.5,50)),np.linspace(0,0.5,50)):.3f}, "
      f"Poisson {1-np.exp(-0.5):.3f})\n")
print("   histogram vs models:")
print(f"   {'s':>6} {'data':>8} {'GUE':>8} {'Poisson':>8}")
for c,h in zip(ctr,hist):
    print(f"   {c:>6.2f} {h:>8.3f} {P_GUE(c):>8.3f} {P_Poi(c):>8.3f}")

try:
    import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt
    fig,(a1,a2)=plt.subplots(1,2,figsize=(13,5))
    a1.step(g,k,where='post',label='zeros staircase N(T)')
    tt=np.linspace(g[0],g[-1],400); a1.plot(tt,Nsmooth(tt),'r--',label='Weyl (T/2π)log(3T/2πe)')
    a1.set_xlabel('γ'); a1.set_ylabel('N(T)'); a1.legend(); a1.set_title('(A) Weyl law')
    a2.hist(s,bins=bins,density=True,alpha=.6,label='unfolded gaps')
    xx=np.linspace(0,3,200); a2.plot(xx,P_GUE(xx),'r-',lw=2,label='GUE'); a2.plot(xx,P_Poi(xx),'g--',label='Poisson')
    a2.set_xlabel('s'); a2.legend(); a2.set_title('(B) spacing: GUE vs Poisson')
    plt.tight_layout(); plt.savefig('hp_fit.png',dpi=110); print("saved -> hp_fit.png")
except Exception as ex: print("no plot:",ex)
