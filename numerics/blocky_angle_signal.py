"""
blocky_angle_signal.py -- nail down the ANGLE signal with null controls.

The blocky helix's resultant MISALIGNMENT ANGLE at each exact zero correlated +0.74 with
S(T). S(T) is itself a phase quantity (S = (1/pi) arg of something). Test rigorously:
shuffle null, surrogate-height null, and whether it holds out-of-sample (zeros 30-65).
"""
import numpy as np
from blocky_helix_core import chi3
np.random.seed(1)
F=np.load('/tmp/foundation.npz'); G,S=F['G'],F['S']
N=6000; n=np.arange(1,N+1); ch=chi3(n); logn=np.log(n)
k=np.ceil(np.sqrt(n)).astype(float); k[k<1]=1; amp=1.0/k

def resultant(w):
    vx=np.sum(ch*amp*np.cos(w*logn)); vy=np.sum(ch*amp*np.sin(w*logn)); return vx,vy
def ang_signal(heights):
    return np.array([np.arctan2(*resultant(g)[::-1]) for g in heights])  # arctan2(vy,vx)

def corr(a,b):
    v=np.isfinite(a)&np.isfinite(b); return np.corrcoef(a[v],b[v])[0,1] if v.sum()>5 else np.nan

A_all=ang_signal(G[:64])
sinA=np.sin(A_all); 
print("=== ANGLE signal vs S(T): in-sample, out-of-sample, nulls ===")
for lo,hi,name in [(0,30,"zeros 1-30"),(30,64,"zeros 31-64"),(0,64,"zeros 1-64")]:
    c=corr(sinA[lo:hi], S[lo:hi])
    print(f"  {name}: corr(sin(misalign angle), S) = {c:+.3f}  (n={hi-lo})")

# shuffle null on full set
real=corr(sinA[:64],S[:64]); cs=[]
sh=S[:64].copy()
for _ in range(5000):
    np.random.shuffle(sh); cs.append(corr(sinA[:64],sh))
cs=np.array(cs)
print(f"\n  full-set real corr {real:+.3f}; shuffle null std {cs.std():.3f}; p(|null|>=|real|)={np.mean(np.abs(cs)>=abs(real)):.4f}")

# surrogate-height null: evaluate angle at MIDPOINTS between zeros (not at zeros) -> should decorrelate
mid=0.5*(G[:64]+np.r_[G[1:64],G[63]+2])
Am=np.sin(ang_signal(mid))
print(f"  angle at MIDPOINTS (not zeros) vs S: corr = {corr(Am[:64],S[:64]):+.3f}  (should be ~0 if signal is AT zeros)")

# Is it actually measuring the same thing as S, or measuring gamma (smooth drift)?
# partial out gamma: regress sinA on gamma, correlate residual with S
G64=G[:64]
B=np.vstack([G64,np.ones(64)]).T
coef,_,_,_=np.linalg.lstsq(B,sinA[:64],rcond=None); sinA_res=sinA[:64]-B@coef
print(f"  after removing smooth gamma-drift: corr(sinA_residual, S) = {corr(sinA_res,S[:64]):+.3f}")

# And the reverse: is S just gamma-drift? remove gamma from S too
coefS,_,_,_=np.linalg.lstsq(B,S[:64],rcond=None); S_res=S[:64]-B@coefS
print(f"  corr(sinA_residual, S_residual) [both gamma-detrended] = {corr(sinA_res,S_res):+.3f}")
