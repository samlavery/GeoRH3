"""
blocky_fluct_deep.py -- separate GEOMETRIC fluctuation content from analytic re-derivation.

The area-law R=sqrt(n) with amp 1/R = n^{-1/2} and phase log n EXACTLY rebuilds the
Dirichlet partial sum sum chi(n) n^{-1/2-iw} -> that just IS L (the trap). To find a
GEOMETRIC fluctuation we must use a radial law NOT equal to the area law, so the phasor
sum is a genuinely different object, and ask whether its collapse-residual carries S(T).

Test 1: truncation N controls a real partial-sum fluctuation. The partial sum
  L_N(1/2+it) = sum_{n<=N} chi(n) n^{-1/2-it}
has its OWN minima; their offset from the true zeros is a known finite-N fluctuation.
Question: is that finite-N offset the same sign/scale as S(T)?  (Genuinely testable.)
"""
import numpy as np
from blocky_helix_core import chi3

F=np.load('/tmp/foundation.npz'); G,S=F['G'],F['S']

def partial_collapse(N, w_grid, alpha=0.5):
    n=np.arange(1,N+1); ch=chi3(n); amp=n**(-alpha)
    logn=np.log(n)
    out=np.empty_like(w_grid)
    for i,w in enumerate(w_grid):
        vx=np.sum(ch*amp*np.cos(w*logn)); vy=np.sum(ch*amp*np.sin(w*logn))
        out[i]=np.hypot(vx,vy)
    return out

def find_minima(w,c,thr):
    m=[]
    for i in range(1,len(c)-1):
        if c[i]<c[i-1] and c[i]<c[i+1] and c[i]<thr:
            a,b,cc=c[i-1],c[i],c[i+1]; d=(a-2*b+cc)
            dx=0.5*(a-cc)/d if abs(d)>1e-12 else 0
            m.append(w[i]+dx*(w[1]-w[0]))
    return np.array(m)

w_grid=np.linspace(7.0,60.0,8000)
print("=== Finite-N partial-sum collapse residual vs S(T) (truncation = the geometric finiteness) ===")
print(f"{'N':>6} {'#min':>5} {'mean|res|':>10} {'corr(res,S)':>12} {'corr after detrend':>18}")
for N in [50,100,200,500,1000,3000,8000]:
    c=partial_collapse(N,w_grid)
    cand=find_minima(w_grid,c,thr=np.median(c)*0.5)
    res=[]
    for g in G[:15]:
        if len(cand):
            j=np.argmin(np.abs(cand-g)); res.append(cand[j]-g)
        else: res.append(np.nan)
    res=np.array(res); v=~np.isnan(res)
    if v.sum()>5:
        cc=np.corrcoef(res[v],S[:15][v])[0,1]
        # detrend a linear-in-gamma drift (finite N has a smooth bias)
        A=np.vstack([G[:15][v],np.ones(v.sum())]).T
        coef,_,_,_=np.linalg.lstsq(A,res[v],rcond=None)
        resd=res[v]-A@coef
        ccd=np.corrcoef(resd,S[:15][v])[0,1]
    else: cc=ccd=np.nan
    print(f"{N:6d} {len(cand):5d} {np.nanmean(np.abs(res)):10.4f} {cc:12.3f} {ccd:18.3f}")
print("\nIf corr(res,S) stays high & nonzero as N grows, the finite-truncation offset")
print("tracks the SAME fluctuation as S(T). If it -> 0 as N->inf, it's just a smoothing artifact.")
