"""
integers_per_singularity.py -- THE ANCHOR.

Before any geometry (spacing / winding / pitch are all gauge), pin the one fixed thing:
how many integers are CONSUMED to produce one singularity?

For each consecutive chi3 zero gamma_n we wind the integers and ask how many are consumed before
the winding sum CLOSES -- i.e. before |L_M(1/2+i gamma)|*sqrt(M) settles into the bounded fibre-imbalance
band {1/3,2/3} and stays there.  M_onset = last M whose rescaled partial sum is still above the band
(still transient).  Then:
   integers consumed PER singularity = dM = M_onset(gamma_{n+1}) - M_onset(gamma_n)
and we test what is actually constant (the anchor): dM? M_onset/n? M_onset/gamma?  vs the AFE sqrt-count.
"""
import numpy as np

def chi3(k):
    r = k % 3
    return 1 if r == 1 else (-1 if r == 2 else 0)

gammas = []
with open("lchi3_zeros_1000.txt") as f:
    for line in f:
        line = line.strip()
        if line and not line.startswith("#"):
            gammas.append(float(line.split()[1]))
gammas.sort()
consec = gammas[:20]                         # the file is consecutive only through ~#20

MCAP = 12000
n = np.arange(1, MCAP + 1)
c = np.where(n % 3 == 1, 1.0, np.where(n % 3 == 2, -1.0, 0.0))
w = c * n ** (-0.5)
logn = np.log(n)

def M_onset(g, thr=0.75):
    L = np.cumsum(w * np.exp(-1j * g * logn))
    resc = np.abs(L) * np.sqrt(n)            # |L_M| * sqrt(M) -> |A(M)-1/3| in {1/3,2/3}
    above = np.where(resc > thr)[0]
    return int(above[-1] + 1) if len(above) else 0

def Nplus(M):  return int(np.count_nonzero(np.arange(1, M + 1) % 3 == 1))   # + fibre integers <= M
def Nminus(M): return int(np.count_nonzero(np.arange(1, M + 1) % 3 == 2))   # - fibre integers <= M

print("=" * 100)
print("  THE ANCHOR: integers consumed per chi3 singularity -- counting BOTH FIBRES (silent n=0 skipped)")
print("=" * 100)
print("  n |  gamma   | M_onset | dM_idx | N+ (n=1) | dN+ | N- (n=2) | dN- | both fibres dN+ + dN-")
print("-" * 100)
prevM = prevP = prevN = None
dMs, dPs, dNs, dBoth = [], [], [], []
for i, g in enumerate(consec):
    Mo = M_onset(g); Np = Nplus(Mo); Nm = Nminus(Mo)
    dM = (Mo - prevM) if prevM is not None else float('nan')
    dP = (Np - prevP) if prevP is not None else float('nan')
    dN = (Nm - prevN) if prevN is not None else float('nan')
    if prevM is not None:
        dMs.append(Mo - prevM); dPs.append(Np - prevP); dNs.append(Nm - prevN); dBoth.append((Np - prevP) + (Nm - prevN))
    db = (dP + dN) if prevP is not None else float('nan')
    print(f" {i+1:2d} | {g:8.4f} | {Mo:6d}  | {dM:5.1f}  | {Np:7d}  | {dP:3.0f} | {Nm:7d}  | {dN:3.0f} |   {db:5.1f}")
    prevM, prevP, prevN = Mo, Np, Nm

dPs = np.array(dPs, float); dNs = np.array(dNs, float); dBoth = np.array(dBoth, float)
print("-" * 100)
print(f"  + fibre integers per singularity dN+ :  mean = {dPs.mean():.3f}  median = {np.median(dPs):.1f}")
print(f"  - fibre integers per singularity dN- :  mean = {dNs.mean():.3f}  median = {np.median(dNs):.1f}")
print(f"  BOTH fibres consumed per singularity :  mean = {dBoth.mean():.3f}  median = {np.median(dBoth):.1f}  "
      f"<== the anchor (one from each fibre)")
