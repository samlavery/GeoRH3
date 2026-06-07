"""
Geometry test INCLUDING the radial growth rate (and pitch).

Each mode of the loss field is  e^{(ρ−a)·u} = e^{(σ−a)u}·e^{iγu}:
    Re(rate) = σ − a   = radial growth   (the radial-growth-rate frame: R ∝ n^a)
    Im(rate) = γ        = pitch           (the climb frequency = the zero height)
On-line zeros (σ=½) show ZERO radial growth only when the radial frame is a=½ (R∝√n).
Scan a; the mean radial growth = ½ − a crosses 0 exactly at a=½ — the data pins the radial rate.
(Pitch = Im = γ is recovered the same at every a; it's the radial *rate* that fixes the line.)
"""
import numpy as np, math, os
import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt
OUT = os.path.dirname(os.path.abspath(__file__))

def make_char(q, vals): return lambda n: vals.get(n % q, 0)
CH = [
  dict(name='ζ',  q=1, chi=(lambda n: 1), principal=True),
  dict(name='χ₃', q=3, chi=make_char(3, {1:1, 2:-1}), principal=False),
]
N = 4_000_000
print(f"sieve + von Mangoldt to {N:,} ...")
sieve = np.ones(N+1, bool); sieve[:2] = False
for i in range(2, int(N**0.5)+1):
    if sieve[i]: sieve[i*i::i] = False
Lam = np.zeros(N+1)
for p in np.nonzero(sieve)[0].tolist():
    lp = math.log(p); pk = p
    while pk <= N: Lam[pk] = lp; pk *= p

def mpencil(y, order):
    Nn = len(y); L = Nn//2
    Y = np.lib.stride_tricks.sliding_window_view(y, L+1)
    _, _, Vh = np.linalg.svd(Y, full_matrices=False)
    V = Vh.conj().T[:, :order]
    return np.linalg.eigvals(np.linalg.pinv(V[:-1]) @ V[1:])

du = 0.006
u = np.arange(5.0, math.log(N) - 0.05, du)
x = np.exp(u); idx = np.clip(np.floor(x).astype(int), 0, N)
A = np.linspace(0.30, 0.70, 21)

fig, axes = plt.subplots(1, 2, figsize=(14, 5.5))
for ax, ch in zip(axes, CH):
    Theta = np.cumsum(Lam * np.array([ch['chi'](n) for n in range(N+1)]))
    main = x if ch['principal'] else 0.0
    drift = []
    for a in A:
        F = (Theta[idx] - main) / x**a
        F = F - F.mean()
        z = mpencil(F.astype(complex), order=100)
        rate = np.log(z) / du                       # = ρ − a:  Re = σ−a (radial growth), Im = γ (pitch)
        gam = rate.imag; gr = rate.real
        sel = (gam > 5) & (gam < 45) & (np.abs(gr) < 0.45)   # physical modes
        drift.append(np.median(gr[sel]) if sel.any() else np.nan)
    drift = np.array(drift)
    ax.plot(A, drift, 'o-', color='steelblue', label='measured radial growth (median Re)')
    ax.plot(A, 0.5 - A, 'r--', lw=1, label='½ − a  (on-line prediction)')
    ax.axhline(0, color='k', lw=0.6); ax.axvline(0.5, color='crimson', ls=':', lw=1, label='a = ½')
    # zero-crossing of measured drift
    zc = np.interp(0.0, drift[::-1], A[::-1])
    ax.set_title(f"{ch['name']}: radial growth vs radial-rate frame a\nmeasured drift = 0 at a = {zc:.4f}")
    ax.set_xlabel('radial growth exponent a  (R ∝ n^a)'); ax.set_ylabel('radial growth (σ − a)')
    ax.legend(fontsize=8)
    print(f"{ch['name']}: measured radial-growth zero-crossing at a = {zc:.4f}  (½ expected)")
fig.tight_layout(); fig.savefig(f'{OUT}/radial_rate.png', dpi=120)
print(f"saved {OUT}/radial_rate.png")
