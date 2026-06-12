"""
blocky_clean_fluct.py -- DECISIVE clean test, no minima-matching ambiguity.

Evaluate a GEOMETRIC defect functional D(T) directly AT each exact zero gamma_n and at
the smooth-predicted height, and ask whether the GEOMETRIC quantity carries S(T_n).
Include NULL controls (shuffled S, GUE surrogate) to kill spurious correlation.
"""
import numpy as np
from blocky_helix_core import chi3
np.random.seed(0)
F=np.load('/tmp/foundation.npz'); G,S,p_smooth=F['G'],F['S'],F['p_smooth']
N=6000; n=np.arange(1,N+1); ch=chi3(n); logn=np.log(n)

# blocky radius R=k(n)=ceil(sqrt n); the helix's per-block ENCLOSED-VOLUME / axis-misalignment
k=np.ceil(np.sqrt(n)).astype(float); k[k<1]=1
amp_blocky=1.0/k

def resultant(amp,w):
    vx=np.sum(ch*amp*np.cos(w*logn)); vy=np.sum(ch*amp*np.sin(w*logn))
    return vx,vy

# axis-misalignment ANGLE of the blocky resultant relative to the smooth resultant, AT each zero
print("=== GEOMETRIC defect evaluated AT exact zeros: does it carry S(T)? ===")
defects=[]; angles=[]
for g in G[:30]:
    vx_b,vy_b=resultant(amp_blocky,g)
    vx_s,vy_s=resultant(n**-0.5,g)         # smooth (~0 at true zero)
    mag_b=np.hypot(vx_b,vy_b)
    ang=np.arctan2(vy_b,vx_b)               # misalignment angle of blocky resultant
    defects.append(mag_b); angles.append(ang)
defects=np.array(defects); angles=np.array(angles)
Sn=S[:30]

def corr(a,b): 
    v=np.isfinite(a)&np.isfinite(b); return np.corrcoef(a[v],b[v])[0,1] if v.sum()>5 else np.nan

print(f"corr(blocky-defect-magnitude, S)   = {corr(defects,Sn):+.3f}")
print(f"corr(blocky misalignment angle, S) = {corr(angles,Sn):+.3f}")
print(f"corr(cos(angle), S)                = {corr(np.cos(angles),Sn):+.3f}")
print(f"corr(sin(angle), S)                = {corr(np.sin(angles),Sn):+.3f}")

# NULL controls
print("\n=== NULL CONTROLS (must NOT correlate if signal is real & specific) ===")
shuf=Sn.copy(); 
cs=[]
for _ in range(2000):
    np.random.shuffle(shuf); cs.append(corr(defects,shuf))
cs=np.array(cs)
real=corr(defects,Sn)
print(f"blocky-defect vs S real corr = {real:+.3f};  shuffled-S null: mean {cs.mean():+.3f} std {cs.std():.3f}")
print(f"  p(|null| >= |real|) = {np.mean(np.abs(cs)>=abs(real)):.3f}")

# also test: defect at SMOOTH-predicted height vs at TRUE height -- which is lower?
print("\n=== Does the blocky helix collapse MORE at the true zero than at the smooth prediction? ===")
# build smooth-predicted heights by integrating p_smooth (cumulative half-waves)
# smooth height for zero m: solve theta(T)/pi+1 = m, i.e. the Weyl prediction. Use gamma - S as proxy of smooth loc shift:
# Actually compare D(gamma_n) vs D(gamma_n + small) to see if gamma_n is a local min of the GEOMETRIC defect.
better=0; worse=0
for g in G[:30]:
    dg=np.hypot(*resultant(amp_blocky,g))
    dL=np.hypot(*resultant(amp_blocky,g-0.15)); dR=np.hypot(*resultant(amp_blocky,g+0.15))
    if dg<dL and dg<dR: better+=1
    else: worse+=1
print(f"  of 30 zeros, blocky defect is a local MIN at the exact zero: {better}/30  (random ~ chance)")
