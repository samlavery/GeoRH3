"""
Push N to 10^8 (ζ): extract the radial-½ crossing at 2e7, 5e7, 1e8, combine with earlier
points, and watch convergence to exactly ½.  Memory-safe: cumsum overwrites the Λ array.
"""
import numpy as np, math, os
import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt
OUT = os.path.dirname(os.path.abspath(__file__))

Nmax = 100_000_000
print(f"sieve to {Nmax:,} ...", flush=True)
sieve = np.ones(Nmax+1, bool); sieve[:2] = False
for i in range(2, int(Nmax**0.5)+1):
    if sieve[i]: sieve[i*i::i] = False
print("  von Mangoldt ...", flush=True)
Lam = np.zeros(Nmax+1, dtype=np.float64)
for p in np.nonzero(sieve)[0].tolist():
    lp = math.log(p); pk = p
    while pk <= Nmax: Lam[pk] = lp; pk *= p
del sieve
print("  cumsum (in place) ...", flush=True)
np.cumsum(Lam, out=Lam); psi = Lam            # psi now holds ψ(n)

def mpencil(y, order):
    L = len(y)//2
    Y = np.lib.stride_tricks.sliding_window_view(y, L+1)
    _, _, Vh = np.linalg.svd(Y, full_matrices=False)
    V = Vh.conj().T[:, :order]
    return np.linalg.eigvals(np.linalg.pinv(V[:-1]) @ V[1:])

du = 0.005
A = np.linspace(0.42, 0.58, 9)
def crossing(N):
    u = np.arange(5.0, math.log(N) - 0.05, du)
    x = np.exp(u); idx = np.clip(np.floor(x).astype(int), 0, N)
    drift = []
    for a in A:
        F = (psi[idx] - x) / x**a; F = F - F.mean()
        r = np.log(mpencil(F.astype(complex), 110)) / du
        g, d = r.imag, r.real
        s = (g > 5) & (g < 40) & (np.abs(d) < 0.35)
        drift.append(np.median(d[s]))
    drift = np.array(drift)
    return float(np.interp(0.0, drift[::-1], A[::-1]))

prev = [(1e6, 0.5078), (2e6, 0.5094), (4e6, 0.5048), (8e6, 0.5026), (1.6e7, 0.5029)]
newN = [20_000_000, 50_000_000, 100_000_000]
pts = list(prev)
for N in newN:
    zc = crossing(N); pts.append((N, zc))
    print(f"  N={N:>11,}  radial-½ crossing a = {zc:.4f}   |Δ from ½| = {abs(zc-0.5):.4f}", flush=True)

Ns = [p[0] for p in pts]; cr = [p[1] for p in pts]
fig, ax = plt.subplots(figsize=(10, 5.5))
ax.semilogx(Ns, cr, 'o-', color='steelblue', ms=7)
ax.axhline(0.5, color='crimson', ls='--', lw=1, label='exact ½')
for N, c in pts:
    ax.annotate(f"{c:.4f}", (N, c), textcoords="offset points", xytext=(0, 8), fontsize=7, ha='center')
ax.set_xlabel('N'); ax.set_ylabel('radial-½ crossing a'); ax.legend()
ax.set_title('radial growth rate → ½ as N grows (ζ), now to N=10⁸')
fig.tight_layout(); fig.savefig(f'{OUT}/push_N2.png', dpi=120)
print(f"saved {OUT}/push_N2.png")
