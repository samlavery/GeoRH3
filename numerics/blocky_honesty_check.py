"""
blocky_honesty_check.py -- is the 54.8% a genuine geometric capture, or a disguised L re-derivation?

THE TRAP (Rule warns): sum chi(n) n^{-1/2-it} just IS L; reading S off it is circular.
We use amp = 1/ceil(sqrt n) (BLOCKY), phase = log n. The phase IS the analytic bridge.
So the honest question: is the fluctuation capture coming from the GEOMETRIC blocky
amplitude (the radial step law), or is log-n phase alone (=L) already enough?
Decisive test: KILL the analytic phase, keep ONLY geometric winding phase, re-measure.
"""
import numpy as np
from blocky_helix_core import chi3, BlockyHelix
F=np.load('/tmp/foundation.npz'); G,S=F['G'],F['S']
def corr(a,b):
    v=np.isfinite(a)&np.isfinite(b); return np.corrcoef(a[v],b[v])[0,1] if v.sum()>5 else np.nan

N=8000
# Build the REAL blocky helix; use its GEOMETRIC winding angle phi(n) as the phase (NOT log n).
H=BlockyHelix(n_max=N); n=H.n
blk=np.ceil(np.sqrt(n)).astype(int)
# area-law spacing+radius so that geometric phi(n) ~ log n EMERGES (per CLAUDE rule: sqrt packing)
coords=H.build(pitch_law=lambda k:np.pi/3,
               radius_law=lambda nn,kk: np.sqrt(nn),     # R=sqrt n
               spacing_law=lambda k: np.pi/3, phasor_law=None, block_assign=blk)
phi=coords['phi']; ch=chi3(n)
# geometric winding phi(n) vs log n
print("geometric winding phi(n) vs log n fit:")
c=np.polyfit(np.log(n[100:]),phi[100:],1); print(f"  phi ~ {c[0]:.3f}*log n + {c[1]:.3f}  (so winding IS ~log, the bridge emerges)")

amp_blocky=1/np.ceil(np.sqrt(n))
def angsig(amp,phase,scale):
    s=[]
    for g in G[:64]:
        vx=np.sum(ch*amp*np.cos(g*scale*phase)); vy=np.sum(ch*amp*np.sin(g*scale*phase))
        s.append(np.arctan2(vy,vx))
    return np.sin(np.array(s))

# match scale so g*scale*phi ~ g*log n
scale=1.0/c[0]
print("\n=== geometric-phase (phi from the built helix) vs analytic-phase (log n) ===")
print(f"  analytic phase log n, blocky amp:  corr(sinA,S) = {corr(angsig(amp_blocky,np.log(n),1.0),S[:64]):+.3f}")
print(f"  GEOMETRIC phase phi,  blocky amp:  corr(sinA,S) = {corr(angsig(amp_blocky,phi,scale),S[:64]):+.3f}")
print(f"  GEOMETRIC phase phi,  smooth amp:  corr(sinA,S) = {corr(angsig(n**-0.5,phi,scale),S[:64]):+.3f}")

print("\n=== VERDICT ===")
print("If geometric-phase blocky still carries S but smooth-amp does NOT, the fluctuation")
print("capture is from the BLOCKY RADIAL STEP LAW (real geometry), not the log-n analytic phase.")
