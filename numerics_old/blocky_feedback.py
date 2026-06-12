"""
blocky_feedback.py
==================
PART A: quantify the KNOWN finding -- the required block-pitch p_k = pi/gap_k follows
the LOG-density mean, but ~86% of its variance is per-block FLUCTUATION S(T). Establish
this on OUR exact 65 zeros so we measure past it, not rediscover it.

PART B: the SELF-CONSISTENT / FEEDBACK BLOCKY HELIX (the real attack on the fluctuation).
Build a real 3D blocky solid whose OWN accumulated phasor state decides where its next
block boundary falls. Each block winds with constant geometry; the boundary is declared
when a feedback functional of the accumulated chi3-weighted phasor vector hits a trigger
(e.g. the resultant re-aligns to the axis, or the swept signed area completes a unit).
Then compare the self-determined boundary heights to the EXACT chi3 zeros block-by-block.

We ALWAYS keep explicit (x,y,z) + a unit phasor at each integer point. The trigger is read
off the 3D phasor RESULTANT (a real vector), never an abstract scalar L.
"""
import numpy as np
import mpmath as mp
from blocky_helix_build import compute_exact_zeros, chi3, L_mp

mp.mp.dps = 30
Q = 3
GAMMA = compute_exact_zeros(65)
print("="*78)
print("PART A -- the KNOWN finding, measured on our exact zeros")
print("="*78)

# ---------------------------------------------------------------------------
# Required block pitch from the zeros: p_k = pi / gap_k. The LOG-density mean is
# pbar_k = (1/2) log(q gamma_k / 2pi). Decompose p_k = pbar_k + fluctuation.
# ---------------------------------------------------------------------------
gap = np.diff(GAMMA)
p_req = np.pi / gap                                    # required pitch per block
p_mean = 0.5*np.log(Q*GAMMA[:-1]/(2*np.pi))            # log-density mean
fluct = p_req - p_mean                                  # the per-block fluctuation
var_total = np.var(p_req)
var_fluct = np.var(fluct)
print(f"  blocks (gaps): {len(gap)}")
print(f"  mean required pitch p_req: {np.mean(p_req):.4f}   mean log-density: {np.mean(p_mean):.4f}")
print(f"  Var(p_req)  = {var_total:.5f}")
print(f"  Var(fluct)  = {var_fluct:.5f}   ->  fluctuation is {100*var_fluct/var_total:.1f}% of variance")
print(f"  corr(p_req, p_mean) = {np.corrcoef(p_req, p_mean)[0,1]:.3f}")
print("  => smooth log law gets the MEAN; the per-block jitter (S(T)) is the open content.\n")

# ---------------------------------------------------------------------------
# How well does ANY smooth law do? Fit p_req to smooth families; residual = fluctuation.
# ---------------------------------------------------------------------------
def smooth_residual(feat, name):
    A = np.vstack([feat, np.ones_like(feat)]).T
    coef, *_ = np.linalg.lstsq(A, p_req, rcond=None)
    pred = A @ coef
    res = p_req - pred
    print(f"    {name:14s}: resid std {np.std(res):.4f}  (frac var left {np.var(res)/var_total:.2f})")
    return res
print("  smooth-law fits of p_req (the unavoidable residual = the fluctuation):")
smooth_residual(0.5*np.log(Q*GAMMA[:-1]/(2*np.pi)), "log-density")
smooth_residual(np.sqrt(GAMMA[:-1]), "sqrt(T)")
smooth_residual(GAMMA[:-1], "linear T")
smooth_residual(np.log(GAMMA[:-1]), "log T")

print("\n" + "="*78)
print("PART B -- SELF-CONSISTENT / FEEDBACK BLOCKY HELIX")
print("="*78)
print("""
The feedback rule: we wind a 3D helix in HEIGHT t (the imaginary axis). At each point we
hang the chi3 phasor of the integers and accumulate the RESULTANT vector V(t). A block
BOUNDARY is declared by the structure itself when a trigger fires. The structure thereby
picks its OWN boundary heights t_k*. Success = the t_k* land on the exact gamma_k --
including the per-block fluctuation -- NOT just matching the mean spacing.
""")

# ---------------------------------------------------------------------------
# The honest 3D realization of "accumulated phasor state along height t":
# At height t, the partial-sum vector of the truncated L is
#   V(t) = sum_n chi(n) n^{-1/2} (cos(t log n), sin(t log n))   [= L(1/2+it) as a 2-vector]
# This is the GENUINE 3D phasor resultant when integers are placed with phasor phase
# = t * (winding coordinate). The trigger "resultant collapses onto axis" is |V(t)|=local min.
# A feedback boundary rule must use ONLY V and its history up to t (causal), then predict
# the NEXT boundary. We test several causal triggers and see which reproduce gamma_k.
# ---------------------------------------------------------------------------

NTERMS = 8000
nn = np.arange(1, NTERMS+1)
sgn = np.array([chi3(int(k)) for k in nn])
amp = nn**-0.5
logn = np.log(nn)

def Vvec(t):
    ph = t*logn
    return np.array([np.sum(sgn*amp*np.cos(ph)), np.sum(sgn*amp*np.sin(ph))])

def Vmag(t):
    return np.hypot(*Vvec(t))

# Trigger 1 (BASELINE collapse): boundary where |V(t)| hits a local minimum (= a zero).
# This is just "find the zeros" -- it trivially matches (it IS L). Keep as sanity ceiling.
def collapse_minima(t_lo, t_hi, step=0.01):
    ts = np.arange(t_lo, t_hi, step)
    mags = np.array([Vmag(t) for t in ts])
    mins = []
    for i in range(1, len(ts)-1):
        if mags[i] < mags[i-1] and mags[i] < mags[i+1] and mags[i] < 0.3:
            mins.append(ts[i])
    return np.array(mins)

# Trigger 2 (PHASE-WINDING feedback, the real candidate): the resultant V(t) has an
# ARGUMENT arg V(t). Between consecutive zeros arg V winds by ~pi (a half turn). A purely
# GEOMETRIC feedback boundary: declare a new block each time arg V(t) advances by pi from
# the last boundary -- the structure's own winding sets the next boundary. If the zeros
# are "one half-turn of the resultant apart", this self-consistent rule reproduces the
# FLUCTUATION because arg V winds nonuniformly (fast near a zero, slow between).
def argV_winding_boundaries(t_lo, t_hi, step=0.005, dphi=np.pi):
    ts = np.arange(t_lo, t_hi, step)
    args = np.unwrap([np.arctan2(*Vvec(t)[::-1]) for t in ts])
    bnds = []
    base = args[0]
    for i in range(len(ts)):
        if args[i] - base >= dphi:
            bnds.append(ts[i]); base = args[i]
    return np.array(bnds), ts, args

print("  [Trigger 1] |V| local minima vs exact zeros (sanity ceiling -- IS L):")
m1 = collapse_minima(7.0, 30.0, step=0.01)
for j, g in enumerate(GAMMA[:6]):
    near = m1[np.argmin(np.abs(m1-g))] if len(m1) else float('nan')
    print(f"     gamma={g:8.4f}  nearest |V|-min={near:8.4f}  err={near-g:+.4f}")

print("\n  [Trigger 2] arg V(t) winding-by-pi self-boundaries vs exact zeros:")
b2, tsg, argsg = argV_winding_boundaries(7.0, 45.0, step=0.004, dphi=np.pi)
# align: the winding boundaries should track the zeros; measure block-by-block error
matched = []
for g in GAMMA[:14]:
    if len(b2):
        near = b2[np.argmin(np.abs(b2-g))]
        matched.append(near-g)
        print(f"     gamma={g:8.4f}  nearest argV-pi-boundary={near:8.4f}  err={near-g:+.4f}")
matched = np.array(matched)
print(f"     => argV winding boundaries: mean|err|={np.mean(np.abs(matched)):.4f}, "
      f"std err={np.std(matched):.4f}")
print(f"     (if std err << gap-jitter {np.std(gap):.3f}, the winding captures the FLUCTUATION)")
