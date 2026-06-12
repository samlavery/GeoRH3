#!/usr/bin/env python3
"""Diagnose R2 normalization carefully. R2(r) must -> 1 at large r."""
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
N=len(x); span=x[-1]-x[0]
print("N=%d span=%.2f mean density=%.5f"%(N,span,N/span))

# Correct R2: number of ordered pairs with separation in [r,r+dr] is
#   sum_{i} #{j != i : x_j - x_i in [r,r+dr]}.
# For a stationary point process of density rho=N/span, the EXPECTED number of
# such ordered pairs (Poisson baseline) over the whole spectrum is
#   N * rho * dr   (each point sees rho*dr neighbors per unit, both sides).
# But we only count one side (j>i) so baseline per i is rho*dr on that side.
# R2(r) = [observed one-sided pair count in bin] / [N * rho * dr]  -> 1 for Poisson.
rho=N/span
dr=0.1; rmax=5.0
edges=np.arange(0,rmax+dr,dr); ctr=0.5*(edges[:-1]+edges[1:])
hist=np.zeros(len(ctr))
for i in range(N):
    j=i+1
    while j<N and (x[j]-x[i])<=rmax:
        k=int((x[j]-x[i])/dr)
        if k<len(hist): hist[k]+=1
        j+=1
# one-sided baseline: expected count in bin = N * rho * dr (one side)
R2=hist/(N*rho*dr)
def gue(r):
    s=np.sinc(r); return 1-s**2
print("\n r     R2     GUE")
for rq in [0.15,0.45,0.95,1.45,1.95,2.95,3.95,4.45]:
    i=np.argmin(np.abs(ctr-rq))
    print("%5.2f  %6.3f  %6.3f"%(ctr[i],R2[i],gue(ctr[i])))
print("\nlarge-r mean R2 (r>3):",R2[ctr>3].mean(),"(should be ~1)")
