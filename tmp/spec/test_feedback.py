"""
Test BASE (delta=0) vs FEEDBACK (pitch += delta) and see if feedback can
rescale the emitted heights to track zeta zeros. Sweep delta, pitch0.
Key question: does feedback supply the increasing (log) density?
"""
import numpy as np
import json, os
from mechanism import run_mechanism

CACHE = os.path.join(os.path.dirname(__file__), "refzeros_cache.json")
ref = json.load(open(CACHE))
zeta_true = np.array(ref["zeta"])

chi_triv = lambda a: 1

def rms(a, b):
    n = min(len(a), len(b))
    if n == 0: return np.inf
    return float(np.sqrt(np.mean((np.asarray(a[:n])-np.asarray(b[:n]))**2)))

print("zeta true first 10:", np.round(zeta_true[:10],3))
print()

# Try to make emitted heights track zeta zeros by scaling pitch.
# BASE: constant pitch. The emitted heights are the H at which a new mode resolves.
# We can scale the whole thing by pitch0. Sweep.
print("=== BASE (delta=0): sweep pitch0, thresh ===")
best = None
for thresh in [0.01, 0.02, 0.05, 0.1]:
    for pitch0 in [0.05, 0.1, 0.2, 0.5]:
        em, _, _ = run_mechanism(chi_triv,1,prime_cutoff=300,thresh_rel=thresh,
                                 H0=0.5,pitch0=pitch0,delta=0.0,Hmax=120,max_emit=40)
        if len(em) >= 10:
            r = rms(em[:10], zeta_true[:10])
            if best is None or r < best[0]:
                best = (r, thresh, pitch0, em[:10].copy())
print(f"best base: rms={best[0]:.3f} thresh={best[1]} pitch0={best[2]}")
print("  emitted:", np.round(best[3],3))
print()

print("=== FEEDBACK (delta>0): sweep delta ===")
bestf = None
for thresh in [0.01,0.02,0.05]:
    for pitch0 in [0.02,0.05,0.1,0.2]:
        for delta in [0.0,0.02,0.05,0.1,0.2,0.5,-0.02]:
            em,_,_ = run_mechanism(chi_triv,1,prime_cutoff=300,thresh_rel=thresh,
                                   H0=0.3,pitch0=pitch0,delta=delta,Hmax=300,max_emit=40)
            if len(em) >= 10:
                r = rms(em[:10], zeta_true[:10])
                if bestf is None or r < bestf[0]:
                    bestf = (r,thresh,pitch0,delta,em[:12].copy())
print(f"best feedback: rms={bestf[0]:.3f} thresh={bestf[1]} pitch0={bestf[2]} delta={bestf[3]}")
print("  emitted:", np.round(bestf[4],3))
print("  true   :", np.round(zeta_true[:12],3))
