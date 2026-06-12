"""
blocky_fluctuation_test.py -- THE FLUCTUATION DIRECTLY.

Build the blocky helix, sweep step laws, and ask: does any GEOMETRIC phasor quantity
(boundary fixed points, axis-misalignment angle, enclosed-volume residual) reproduce the
per-block jitter = (boundary - smooth-log-prediction) = the actual S(T_n) of chi3 zeros?

We test the phasor VECTOR-SUM collapse along the climbing helix and read where it lands
on the axis -> candidate boundaries. Compare candidate heights to exact gamma_n:
  - MEAN match: candidate spacing ~ pi/theta' (smooth log). Easy, known.
  - FLUCTUATION match: candidate_n - gamma_n correlates with S(T_n). The open question.
"""
import numpy as np
from blocky_helix_core import chi3, BlockyHelix, phasor_resultant, axis_alignment_defect

F = np.load('/tmp/foundation.npz')
G, gap, p_req, p_smooth, S = F['G'], F['gap'], F['p_req'], F['p_smooth'], F['S']

# Build a fine helix (the phasor walk uses the bridge readout log n as the analytic dictionary;
# the GEOMETRY supplies amplitude 1/R from the blocky radial law, and the block structure).
H = BlockyHelix(n_max=4000)
n = H.n

def collapse_curve(coords, w_grid, phase_field):
    """axis-defect as a function of winding freq w (the candidate-zero scan)."""
    amp = 1.0/np.maximum(coords['R'],1e-9); ch=chi3(coords['n'])
    tot=np.sum(np.abs(ch)*amp)
    out=np.empty_like(w_grid)
    for i,w in enumerate(w_grid):
        psi=w*phase_field
        vx=np.sum(ch*amp*np.cos(psi)); vy=np.sum(ch*amp*np.sin(psi))
        out[i]=np.hypot(vx,vy)/tot
    return out

def find_minima(w_grid, curve, thresh=0.5):
    mins=[]
    for i in range(1,len(curve)-1):
        if curve[i]<curve[i-1] and curve[i]<curve[i+1] and curve[i]<thresh:
            # parabolic refine
            a,b,c=curve[i-1],curve[i],curve[i+1]
            denom=(a-2*b+c)
            dx=0.5*(a-c)/denom if abs(denom)>1e-12 else 0.0
            mins.append(w_grid[i]+dx*(w_grid[1]-w_grid[0]))
    return np.array(mins)

# block assignment by sqrt-area packing
block_assign = np.floor(np.sqrt(n)).astype(int)
# A radial law family: R = base * k^alpha
results={}
print("=== SWEEP: does the phasor-collapse scan reproduce the chi3 zeros (mean? fluctuation?) ===")
print("(amplitude = 1/R from the blocky radial law; phase = bridge readout log n)\n")
w_grid=np.linspace(7.0, 40.0, 4000)
for label, radius_law, spacing in [
    ("R=k (Archimedean, ds=pi/3)",     lambda nn,kk: np.maximum(kk,1).astype(float), np.pi/3),
    ("R=sqrt(n) (area-law)",           lambda nn,kk: np.sqrt(nn),                    np.pi/3),
    ("R=k^2 (trumpet)",                lambda nn,kk: np.maximum(kk,1).astype(float)**2, np.pi/3),
]:
    coords=H.build(lambda k:np.pi/3, radius_law, lambda k:spacing, None, block_assign)
    phase=np.log(coords['n'])
    curve=collapse_curve(coords, w_grid, phase)
    cand=find_minima(w_grid, curve, thresh=0.6)
    # match candidates to first 10 exact zeros
    matched=[]
    for g in G[:10]:
        if len(cand):
            j=np.argmin(np.abs(cand-g)); matched.append(cand[j]-g)
        else: matched.append(np.nan)
    matched=np.array(matched)
    results[label]=(cand, matched)
    print(f"{label}")
    print(f"  #candidate minima in [7,40]: {len(cand)}")
    print(f"  candidate-vs-exact (first 6): " + " ".join(f"{c:.2f}" for c in cand[:6]) if len(cand) else "  none")
    print(f"  residual cand-gamma (first 6): " + " ".join(f"{m:+.3f}" for m in matched[:6]))
    # does residual correlate with S?  (the fluctuation test)
    valid=~np.isnan(matched)
    if valid.sum()>3:
        cc=np.corrcoef(matched[valid], S[:10][valid])[0,1]
        print(f"  CORR(residual, S(T)) over matched = {cc:+.3f}   <-- fluctuation signal?" )
    print()
