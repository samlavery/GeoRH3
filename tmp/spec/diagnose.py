"""
Diagnose the emission density of the base mechanism, and what controls it.
Compare emitted gamma_n spacings to the true zeta zero density log(T/2pi)/2pi.
"""
import numpy as np
import json, os
from mechanism import run_mechanism, source_atoms, gram, resolvable_modes

CACHE = os.path.join(os.path.dirname(__file__), "refzeros_cache.json")
ref = json.load(open(CACHE))
zeta_true = np.array(ref["zeta"])

chi_triv = lambda a: 1

def true_density(T):
    return np.log(T/(2*np.pi))/(2*np.pi)

# What does the mode count N(H) look like vs H for the base mechanism?
em, counts, fw = run_mechanism(chi_triv, 1, prime_cutoff=200,
                               thresh_rel=0.02, H0=0.5, pitch0=0.1,
                               delta=0.0, Hmax=40.0, max_emit=60)
print("num atoms:", len(fw[0]))
counts = np.array(counts)
# print N(H) at a few H
for Hq in [5,10,15,20,25,30,35]:
    idx = np.argmin(np.abs(counts[:,0]-Hq))
    print(f"  H={counts[idx,0]:.1f}  N(H)={int(counts[idx,1])}   trueN(H)approx={Hq/(2*np.pi)*(np.log(Hq/(2*np.pi))-1):.2f}")

print("\nemitted spacings (base):", np.round(np.diff(em[:20]),3))
print("true zeta spacings:", np.round(np.diff(zeta_true[:20]),3))

# The mode count here just grows ~linearly with resolved frequency pairs,
# unrelated to t-axis. Diagnose: how many SVs above threshold vs H?
freqs, weights = source_atoms(chi_triv, 1, 200)
print("\nSV-count growth vs H:")
for H in [1,2,4,8,16,32]:
    B = gram(freqs, weights, H)
    cnt, s = resolvable_modes(B, 0.02)
    print(f"  H={H:5.1f}  resolvable={cnt:3d}  s[0]={s[0]:.4f} s[-1]={s[-1]:.2e}")
