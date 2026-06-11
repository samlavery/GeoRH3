#!/usr/bin/env python3
"""Diagnose the unfolding + R2 normalization."""
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

x=Nsmooth(g)
sp=np.diff(x)
print("unfolded spacing: mean=%.5f std=%.5f"%(sp.mean(),sp.std()))
print("nearest-neighbor spacing distribution moments:")
print("  <s>=%.4f  <s^2>=%.4f  (GUE <s^2>=4/pi=1.273, Poisson=2)"%(sp.mean(),(sp**2).mean()))
# fraction of small spacings (level repulsion)
print("  frac s<0.1: %.4f (GUE tiny, Poisson~0.095)"%np.mean(sp<0.1))
print("  frac s<0.3: %.4f"%np.mean(sp<0.3))

# Check local density: does mean spacing drift across the spectrum?
# bin x into 10 chunks, report mean spacing in each
edges=np.linspace(x[0],x[-1],11)
print("\nlocal mean spacing by decile of unfolded x:")
for i in range(10):
    m=(x[:-1]>=edges[i])&(x[:-1]<edges[i+1])
    print("  decile %d: <s>=%.4f n=%d"%(i,sp[m].mean(),m.sum()))

# The KEY diagnostic for the inflated R2 and saturating Sigma2:
# A constant std of spacing ~0.36 with mean 1 is FINE (GUE std = sqrt(4/pi-1)=0.52!).
# Wait: GUE NN spacing std should be ~0.52, ours is 0.36 -> TOO RIGID / too regular.
# That means our unfolding may be OVER-smoothing? No: 0.36 std means spacings cluster
# near 1 MORE than GUE. That is suspicious.  Let's compare to GUE Wigner surmise.
print("\n# GUE Wigner surmise NN std ~ 0.522 ; Poisson std = 1.0")
print("# Our NN std = %.3f  -> %s"%(sp.std(),
      "more rigid than GUE (!?)" if sp.std()<0.45 else "GUE-like"))

# Histogram of spacings vs GUE Wigner surmise
def wigner_gue(s):
    return (32/np.pi**2)*s**2*np.exp(-4*s**2/np.pi)
bins=np.linspace(0,4,41)
h,_=np.histogram(sp,bins=bins,density=True)
ctr=0.5*(bins[:-1]+bins[1:])
print("\n s     P_data   P_GUE   P_Poisson")
for i in range(0,40,3):
    print("%5.2f  %7.4f  %6.4f  %6.4f"%(ctr[i],h[i],wigner_gue(ctr[i]),np.exp(-ctr[i])))
