"""
Push N: watch the radial-½ crossing converge to exactly ½ as N grows (ζ).
Sieve once at Nmax; extract the crossing on growing prefixes.
"""
import numpy as np, math, os
import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt
OUT = os.path.dirname(os.path.abspath(__file__))

Nmax = 16_000_000
print(f"sieve + von Mangoldt to {Nmax:,} ...")
sieve = np.ones(Nmax+1, bool); sieve[:2] = False
for i in range(2, int(Nmax**0.5)+1):
    if sieve[i]: sieve[i*i::i] = False
Lam = np.zeros(Nmax+1)
for p in np.nonzero(sieve)[0].tolist():
    lp = math.log(p); pk = p
    while pk <= Nmax: Lam[pk] = lp; pk *= p
psi = np.cumsum(Lam)
print("  done.")

def mpencil(y, order):
    L = len(y)//2
    Y = np.lib.stride_tricks.sliding_window_view(y, L+1)
    _, _, Vh = np.linalg.svd(Y, full_matrices=False)
    V = Vh.conj().T[:, :order]
    return np.linalg.eigvals(np.linalg.pinv(V[:-1]) @ V[1:])

du = 0.006
A = np.linspace(0.40, 0.60, 11)
Ns = [1_000_000, 2_000_000, 4_000_000, 8_000_000, 16_000_000]
cross = []
for N in Ns:
    u = np.arange(5.0, math.log(N) - 0.05, du)
    x = np.exp(u); idx = np.clip(np.floor(x).astype(int), 0, N)
    drift = []
    for a in A:
        F = (psi[idx] - x) / x**a; F = F - F.mean()
        r = np.log(mpencil(F.astype(complex), 100)) / du
        g, d = r.imag, r.real
        s = (g > 5) & (g < 40) & (np.abs(d) < 0.4)
        drift.append(np.median(d[s]))
    drift = np.array(drift)
    zc = float(np.interp(0.0, drift[::-1], A[::-1]))
    cross.append(zc)
    print(f"  N={N:>10,}  (u-range {u[-1]-u[0]:.1f})  radial-½ crossing a = {zc:.4f}   |Δ from ½| = {abs(zc-0.5):.4f}")

fig, ax = plt.subplots(figsize=(9, 5.5))
ax.semilogx(Ns, cross, 'o-', color='steelblue', ms=8)
ax.axhline(0.5, color='crimson', ls='--', lw=1, label='exact ½')
for N, c in zip(Ns, cross):
    ax.annotate(f"{c:.4f}", (N, c), textcoords="offset points", xytext=(0, 8), fontsize=8, ha='center')
ax.set_xlabel('N'); ax.set_ylabel('radial-½ crossing a'); ax.legend()
ax.set_title('radial growth rate converges to exactly ½ as N grows (ζ)')
fig.tight_layout(); fig.savefig(f'{OUT}/push_N.png', dpi=120)
print(f"saved {OUT}/push_N.png")
