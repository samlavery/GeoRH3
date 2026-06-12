"""
blocky_robust_feedback.py -- (a) N-robustness of the angle signal; (b) feedback fixed-point boundaries.
"""
import numpy as np
from blocky_helix_core import chi3
F=np.load('/tmp/foundation.npz'); G,S,p_smooth=F['G'],F['S'],F['p_smooth']
def corr(a,b):
    v=np.isfinite(a)&np.isfinite(b); return np.corrcoef(a[v],b[v])[0,1] if v.sum()>5 else np.nan

print("=== (a) N-robustness: does the blocky angle->S correlation survive as N grows? ===")
for N in [500,1000,2000,4000,8000,15000]:
    n=np.arange(1,N+1); ch=chi3(n); logn=np.log(n)
    k=np.ceil(np.sqrt(n)); amp=1/k
    s=[]
    for g in G[:64]:
        vx=np.sum(ch*amp*np.cos(g*logn)); vy=np.sum(ch*amp*np.sin(g*logn)); s.append(np.arctan2(vy,vx))
    print(f"  N={N:6d}: corr(sin(angle),S) = {corr(np.sin(np.array(s)),S[:64]):+.3f}")

print("\n=== (b) FEEDBACK fixed-point boundaries: block sets where next boundary falls ===")
# self-consistent: boundary heights T_k where cumulative GEOMETRIC phase = k*pi, using the
# block's own pitch p_k = (1/2) log(q T_k /2pi) (the geometry's emergent winding rate).
# Solve T_{k+1} = T_k + pi / p_k  with p_k from current T_k (Euler step) -- pure mean law.
q=3
def smooth_boundaries(T0,K):
    Ts=[T0]
    for _ in range(K):
        p=0.5*np.log(q*Ts[-1]/(2*np.pi)); Ts.append(Ts[-1]+np.pi/p)
    return np.array(Ts)
Tb=smooth_boundaries(G[0],63)
print(f"  smooth-feedback boundaries vs exact zeros (first 8):")
for i in range(8):
    print(f"    zero {i+1}: exact {G[i]:8.3f}  feedback {Tb[i]:8.3f}  diff {Tb[i]-G[i]:+.3f}  S={S[i]:+.3f}")
print(f"  RMS(feedback - exact) over 64 = {np.sqrt(np.mean((Tb[:64]-G[:64])**2)):.3f}")
print(f"  corr(feedback-error, -S) = {corr(Tb[:64]-G[:64], -S[:64]):+.3f}  (smooth feedback misses fluctuation)")

# NOW: feedback WITH a geometric phasor-defect correction term (the angle signal feeding back)
n=np.arange(1,8000); ch=chi3(n); logn=np.log(n); amp=1/np.ceil(np.sqrt(n))
def blocky_angle(g):
    vx=np.sum(ch*amp*np.cos(g*logn)); vy=np.sum(ch*amp*np.sin(g*logn)); return np.arctan2(vy,vx)
# does adding c*sin(angle) to the smooth boundary reduce the error?  (closing the loop)
sinang=np.array([np.sin(blocky_angle(g)) for g in G[:64]])
err=Tb[:64]-G[:64]
# best linear correction
A=np.vstack([sinang,np.ones(64)]).T
coef,_,_,_=np.linalg.lstsq(A,err,rcond=None); pred=A@coef
print(f"\n  smooth-feedback RMS error             = {np.sqrt(np.mean(err**2)):.3f}")
print(f"  after geometric sin(angle) correction = {np.sqrt(np.mean((err-pred)**2)):.3f}")
print(f"  variance of S-fluctuation explained by geometric angle = {1-np.var(err-pred)/np.var(err):.1%}")
