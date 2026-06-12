#!/usr/bin/env python3
"""
Random-matrix / operator-spectrum analysis of the L(chi3) zeros.

chi3 = odd real primitive Dirichlet character mod 3 (conductor q=3).
3580 zeros, gamma in [8.04, 3502].

Sections:
  0. Unfolding + nearest-neighbor spacing (level repulsion, Wigner surmise)
  1. Montgomery pair correlation R2(r) vs GUE 1-(sin pi r/pi r)^2
  2. Form factor K(tau) vs GUE ramp/plateau + prime explicit-formula detector
  3. Number variance Sigma^2(L) and spectral rigidity Delta3(L) vs GUE/Poisson

Parser: gamma = float(line.split()[1])  (SECOND token).
Unfolding: N_smooth(t) = (t/2pi) log(3t/2pi) - t/2pi  (q=3).
"""
import numpy as np
import math

GE = 0.5772156649015329   # Euler-Mascheroni

# ----------------------------------------------------------------------
def load_gammas(path='lchi3_zeros_record.txt'):
    g=[]
    with open(path) as f:
        for line in f:
            line=line.strip()
            if not line or line.startswith('#'): continue
            g.append(float(line.split()[1]))   # SECOND token
    return np.array(sorted(g))

g = load_gammas()
print(f"# Loaded {len(g)} chi3 zeros, gamma in [{g[0]:.4f}, {g[-1]:.4f}]")
assert np.all(np.diff(g)>0)

def Nsmooth(t):
    return (t/(2*np.pi))*np.log(3*t/(2*np.pi)) - t/(2*np.pi)

x = Nsmooth(g)            # unfolded positions (unit mean density)
N = len(x); span = x[-1]-x[0]; rho = N/span
sp = np.diff(x)

# ======================================================================
print("\n"+"="*66)
print("0. UNFOLDING & NEAREST-NEIGHBOR SPACING  (level repulsion)")
print("="*66)
print(f"Unfolded mean spacing {sp.mean():.5f} (target 1)  std {sp.std():.4f}")
print(f"  <s^2> = {(sp**2).mean():.4f}   [GUE 1.273, Poisson 2.0]")
print(f"  frac s<0.1: {np.mean(sp<0.1):.4f}   [GUE ~0.001, Poisson 0.095]  -> level repulsion")
# local density flat across spectrum?
edges=np.linspace(x[0],x[-1],11)
drift=[sp[(x[:-1]>=edges[i])&(x[:-1]<edges[i+1])].mean() for i in range(10)]
print(f"  decile mean-spacing range: [{min(drift):.4f}, {max(drift):.4f}] (flat => good unfolding)")

def wigner_gue(s):
    return (32/np.pi**2)*s**2*np.exp(-4*s**2/np.pi)
bins=np.linspace(0,4,81); ctr=0.5*(bins[:-1]+bins[1:])
h,_=np.histogram(sp,bins=bins,density=True)
print("\n  P(s) nearest-neighbor spacing vs Wigner surmise:")
print(f"  {'s':>5} {'P_data':>8} {'P_GUE':>7} {'P_Poiss':>8}")
for sq in [0.1,0.3,0.5,0.7,0.9,1.1,1.3,1.6,2.0,2.5]:
    i=np.argmin(np.abs(ctr-sq))
    print(f"  {ctr[i]:5.2f} {h[i]:8.4f} {wigner_gue(ctr[i]):7.4f} {np.exp(-ctr[i]):8.4f}")
np.savetxt('rmt_spacing.dat',np.column_stack([ctr,h,wigner_gue(ctr),np.exp(-ctr)]),
           header='s  P_data  P_GUE  P_Poisson')

# ======================================================================
print("\n"+"="*66)
print("1. MONTGOMERY PAIR CORRELATION  R2(r)   [GUE = 1 - sinc^2]")
print("="*66)
def pair_correlation(x, rmax=4.0, dr=0.05):
    edges=np.arange(0,rmax+dr,dr); ctr=0.5*(edges[:-1]+edges[1:])
    hist=np.zeros(len(ctr)); n=len(x); rho=n/(x[-1]-x[0])
    for i in range(n):
        j=i+1
        while j<n and (x[j]-x[i])<=rmax:
            k=int((x[j]-x[i])/dr)
            if k<len(hist): hist[k]+=1
            j+=1
    # one-sided ordered-pair baseline (Poisson) = n * rho * dr
    R2=hist/(n*rho*dr)
    return ctr,R2
def gue_R2(r):
    s=np.sinc(r); return 1-s**2
ctr,R2=pair_correlation(x,rmax=4.0,dr=0.05)
gue=gue_R2(ctr)
print(f"{'r':>6} {'R2_data':>9} {'GUE':>8} {'Poisson':>8}")
for rq in [0.1,0.2,0.3,0.4,0.5,0.7,1.0,1.2,1.5,2.0,2.5,3.0]:
    i=np.argmin(np.abs(ctr-rq))
    print(f"{ctr[i]:6.2f} {R2[i]:9.4f} {gue[i]:8.4f} {1.0:8.4f}")
m=(ctr>0.1)&(ctr<3.0)
print(f"\n# RMS dev from GUE     (0.1<r<3): {np.sqrt(np.mean((R2[m]-gue[m])**2)):.4f}")
print(f"# RMS dev from Poisson (0.1<r<3): {np.sqrt(np.mean((R2[m]-1)**2)):.4f}")
print(f"# R2 mean over r in (0,0.1): {R2[ctr<0.1].mean():.4f}  [GUE->0 level repulsion]")
print(f"# R2 mean over r>3:          {R2[ctr>3].mean():.4f}  [must ->1]")
np.savetxt('rmt_pair_corr.dat',np.column_stack([ctr,R2,gue]),header='r R2_data R2_GUE')

# ======================================================================
print("\n"+"="*66)
print("2. FORM FACTOR  K(tau)   [GUE: ramp tau<1, plateau=1 for tau>1]")
print("="*66)
def form_factor(x,taus):
    n=len(x)
    return np.array([np.abs(np.sum(np.exp(2j*np.pi*t*x)))**2/n for t in taus])
def gue_K(tau):
    return np.where(np.abs(tau)<1,np.abs(tau),1.0)
taus=np.linspace(0,3,1500); K=form_factor(x,taus); Kgue=gue_K(taus)
def smooth(y,w):
    return np.convolve(y,np.ones(w)/w,mode='same')
Ksm=smooth(K,41)
print(f"{'tau':>6} {'K_smooth':>9} {'GUE':>7}")
for tq in [0.1,0.2,0.3,0.5,0.7,0.9,1.0,1.2,1.5,2.0,2.5]:
    i=np.argmin(np.abs(taus-tq))
    print(f"{taus[i]:6.2f} {Ksm[i]:9.4f} {Kgue[i]:7.4f}")
m=(taus>0.1)&(taus<0.9)
print(f"\n# ramp region 0.1<tau<0.9: K_smooth/tau mean = {np.mean(Ksm[m]/taus[m]):.3f} (GUE=1)")
m=(taus>1.3)&(taus<2.7)
print(f"# plateau   1.3<tau<2.7: K_smooth mean = {np.mean(Ksm[m]):.3f} (GUE=1)")
np.savetxt('rmt_form_factor.dat',np.column_stack([taus,K,Ksm,Kgue]),
           header='tau K_raw K_smooth K_GUE')

print("\n"+"-"*66)
print("PRIME STRUCTURE (explicit formula): peaks of |sum_n e^{i u gamma_n}|")
print("  expected at u = log(p^k).  This is the arithmetic part directly.")
print("-"*66)
us=np.linspace(0.2,4.0,16000)
gc=0.5*(g[0]+g[-1]); sig=(g[-1]-g[0])/4.0
w=np.exp(-0.5*((g-gc)/sig)**2)
D=np.array([np.abs(np.sum(w*np.exp(1j*u*g))) for u in us])/np.sum(w)
def local_maxima(y,thr):
    return [i for i in range(2,len(y)-2)
            if y[i]>thr and y[i]>=y[i-1] and y[i]>y[i+1]]
thr=np.percentile(D,99.3)
peaks=local_maxima(D,thr)
prime_logs=[]
for p in [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47]:
    for k in [1,2]:
        v=k*math.log(p)
        if 0.2<v<4.0: prime_logs.append((p,k,v))
print(f"{'u_peak':>8} {'|D|':>8}   nearest log(p^k)        match")
nhit=0
for i in peaks:
    u=us[i]; p,k,v=min(prime_logs,key=lambda t:abs(t[2]-u)); err=abs(v-u)
    tag=f"log({p}^{k})={v:.4f}" if k>1 else f"log({p})={v:.4f}"
    flag=""
    if err<0.01:
        flag="  PRIME HIT"; nhit+=1
    print(f"{u:8.4f} {D[i]:8.4f}   {tag:24s} |du|={err:.4f}{flag}")
print(f"\n# {nhit} peaks matched a prime-power log to within |du|<0.01")
# Where is the prime peak in tau units?  tau_p = log p /(2pi <rho_local>) but
# since explicit formula is in gamma, the cleanest statement is the u=log p above.
np.savetxt('rmt_prime_fourier.dat',np.column_stack([us,D]),header='u |D(u)|')

# ======================================================================
print("\n"+"="*66)
print("3. NUMBER VARIANCE Sigma^2(L)  &  SPECTRAL RIGIDITY Delta3(L)")
print("="*66)
xi=x.copy()
def number_variance(xi,L,nwin=6000):
    lo,hi=xi[0],xi[-1]-L
    if hi<=lo: return np.nan
    s=np.linspace(lo,hi,nwin)
    c=np.searchsorted(xi,s+L)-np.searchsorted(xi,s)
    return c.var()
def delta3(xi,L,nwin=3000):
    lo,hi=xi[0],xi[-1]-L
    if hi<=lo: return np.nan
    starts=np.linspace(lo,hi,nwin); vals=[]
    for a0 in starts:
        i0=np.searchsorted(xi,a0); i1=np.searchsorted(xi,a0+L)
        e=xi[i0:i1]-a0; n=len(e)
        if n==0: continue
        k=np.arange(1,n+1)
        I0=np.sum(L-e); I1=np.sum((L**2-e**2)/2.0)
        e_ext=np.concatenate([e,[L]]); seg=np.diff(e_ext); I2=np.sum((k**2)*seg)
        m0,m1,m2=L,L**2/2,L**3/3; det=m0*m2-m1*m1
        a=(I0*m2-I1*m1)/det; b=(-I0*m1+I1*m0)/det
        resid=I2-2*a*I0-2*b*I1+a*a*m0+2*a*b*m1+b*b*m2
        vals.append(resid/L)
    return np.mean(vals)
def sigma2_gue(L): return (1/np.pi**2)*(np.log(2*np.pi*L)+GE+1)
def delta3_gue(L): return (1/np.pi**2)*(np.log(2*np.pi*L)+GE-5/4-np.pi**2/8)
Ls=[2,3,5,7,10,15,20,30,40,50,75,100]
print(f"{'L':>5} {'Sig2_dat':>9} {'Sig2_GUE':>9} {'Sig2_Poi':>9} | {'D3_dat':>8} {'D3_GUE':>8} {'D3_Poi':>8}")
rows=[]
for L in Ls:
    s2=number_variance(xi,float(L)); d3=delta3(xi,float(L))
    print(f"{L:5d} {s2:9.4f} {sigma2_gue(L):9.4f} {float(L):9.4f} | {d3:8.4f} {delta3_gue(L):8.4f} {L/15:8.4f}")
    rows.append([L,s2,sigma2_gue(L),L,d3,delta3_gue(L),L/15])
np.savetxt('rmt_rigidity.dat',np.array(rows),
           header='L Sig2_dat Sig2_GUE Sig2_Poi D3_dat D3_GUE D3_Poi')

print("\n# data files: rmt_spacing.dat rmt_pair_corr.dat rmt_form_factor.dat")
print("#             rmt_prime_fourier.dat rmt_rigidity.dat")
