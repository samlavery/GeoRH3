"""
blocky_geom_fluct.py -- the GEOMETRIC (non-area-law) blocky helix and its fluctuation.

Key distinction (avoiding the trap): amplitude = 1/R with R = blockindex k(n) ~ sqrt(n)
gives amp ~ n^{-1/2} ONLY ON AVERAGE, but BLOCKILY (constant within a block, stepping at
boundaries). That blocky amplitude is a genuinely different sequence from the smooth
n^{-1/2}, so its phasor collapse is NOT the analytic L partial sum. We ask: does the
blocky-vs-smooth amplitude difference inject the per-block fluctuation S(T)?
"""
import numpy as np
from blocky_helix_core import chi3

F=np.load('/tmp/foundation.npz'); G,S=F['G'],F['S']

def find_minima(w,c,thr):
    m=[]
    for i in range(1,len(c)-1):
        if c[i]<c[i-1] and c[i]<c[i+1] and c[i]<thr:
            a,b,cc=c[i-1],c[i],c[i+1]; d=(a-2*b+cc)
            dx=0.5*(a-cc)/d if abs(d)>1e-12 else 0
            m.append(w[i]+dx*(w[1]-w[0]))
    return np.array(m)

def collapse(amp, logn, ch, w_grid):
    out=np.empty_like(w_grid)
    for i,w in enumerate(w_grid):
        vx=np.sum(ch*amp*np.cos(w*logn)); vy=np.sum(ch*amp*np.sin(w*logn))
        out[i]=np.hypot(vx,vy)
    return out

N=4000
n=np.arange(1,N+1); ch=chi3(n); logn=np.log(n)
w_grid=np.linspace(7.0,60.0,9000)

# amplitude variants
amp_smooth = n**-0.5                         # area-law (the trap / analytic L)
k = np.floor(np.sqrt(n)).astype(float); k[k<1]=1
amp_blocky = 1.0/k                           # blocky: const within block, steps at boundary
amp_block2 = 1.0/np.maximum(np.ceil(np.sqrt(n)),1)

print("=== compare SMOOTH (area-law=L) vs BLOCKY amplitude; residual vs S(T) over 15 zeros ===")
for label,amp in [("smooth n^-1/2 (=L, trap)",amp_smooth),
                  ("blocky 1/floor(sqrt n)",amp_blocky),
                  ("blocky 1/ceil(sqrt n)",amp_block2)]:
    c=collapse(amp,logn,ch,w_grid)
    cand=find_minima(w_grid,c,thr=np.median(c)*0.6)
    res=np.array([ (cand[np.argmin(np.abs(cand-g))]-g) if len(cand) else np.nan for g in G[:15]])
    v=~np.isnan(res)
    cc=np.corrcoef(res[v],S[:15][v])[0,1] if v.sum()>5 else np.nan
    # blocky-minus-smooth amplitude is the injected geometric perturbation
    print(f"{label:28s} mean|res|={np.nanmean(np.abs(res)):.4f}  #cand={len(cand)}  corr(res,S)={cc:+.3f}")

print("\n=== Is the BLOCKY amplitude difference the source? perturbation-correlation ===")
# the difference (blocky - smooth) is a sawtooth in n; its weighted phase content at gamma_n
dperturb = amp_blocky - amp_smooth
# project the perturbation onto each zero's phasor field: how much does it shift the resultant
print(f"{'n':>3} {'gamma':>9} {'S(T_n)':>8} {'perturb proj (Re-aligned)':>26}")
for idx in range(0,15):
    g=G[idx]
    # resultant of smooth at g (should be ~0), resultant of perturbation at g
    vx_s=np.sum(ch*amp_smooth*np.cos(g*logn)); vy_s=np.sum(ch*amp_smooth*np.sin(g*logn))
    vx_p=np.sum(ch*dperturb*np.cos(g*logn));   vy_p=np.sum(ch*dperturb*np.sin(g*logn))
    proj=np.hypot(vx_p,vy_p)
    print(f"{idx+1:3d} {g:9.3f} {S[idx]:8.3f} {proj:26.4f}")
