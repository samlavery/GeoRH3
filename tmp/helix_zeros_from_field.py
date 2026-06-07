"""
Compute the zeros FROM the helix construction (not from L).

The helix places integer n at radius R=√n (area-law/critical frame). The loss field along the
helix is the √x-normalized von Mangoldt-character field
    F(u) = (Θ_χ(x) − main) / √x ,   x = e^u ,   Θ_χ(x)=Σ_{n≤x} Λ(n)χ(n)
On RH this is bounded and F(u) = −Σ_ρ e^{(ρ−½)u}/ρ, a sum of modes at complex rate (ρ−½).
Matrix-pencil (Prony/ESPRIT) recovers those rates: Im = γ (the zero heights), Re = σ−½.
"""
import numpy as np, math, os
import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt
OUT = os.path.dirname(os.path.abspath(__file__))

def make_char(q, vals):
    return lambda n: vals.get(n % q, 0)

CH = [
  dict(name='ζ',  q=1, chi=(lambda n: 1), principal=True,
       known=[14.1347,21.0220,25.0109,30.4249,32.9351,37.5862,40.9187,43.3271,48.0051,49.7738]),
  dict(name='χ₃', q=3, chi=make_char(3, {1:1, 2:-1}), principal=False,
       known=[8.0397,11.2492,15.7046,18.2620,20.4558,24.0594,26.5779,28.2182,30.7450,32.4150]),
]

N = 4_000_000
print(f"sieving + von Mangoldt to N={N:,} ...")
sieve = np.ones(N+1, bool); sieve[:2] = False
for i in range(2, int(N**0.5)+1):
    if sieve[i]: sieve[i*i::i] = False
primes = np.nonzero(sieve)[0]
Lam = np.zeros(N+1)
for p in primes.tolist():
    lp = math.log(p); pk = p
    while pk <= N:
        Lam[pk] = lp; pk *= p

def matrix_pencil(y, order):
    Nn = len(y); L = Nn // 2
    Y = np.lib.stride_tricks.sliding_window_view(y, L+1)
    _, _, Vh = np.linalg.svd(Y, full_matrices=False)
    V = Vh.conj().T[:, :order]
    return np.linalg.eigvals(np.linalg.pinv(V[:-1]) @ V[1:])

fig, axes = plt.subplots(1, 2, figsize=(14, 6))
for ax, ch in zip(axes, CH):
    cf = np.array([ch['chi'](n) for n in range(N+1)])
    Theta = np.cumsum(Lam * cf)
    du = 0.004
    u = np.arange(5.0, math.log(N) - 0.05, du)
    x = np.exp(u); idx = np.clip(np.floor(x).astype(int), 0, N)
    main = x if ch['principal'] else 0.0
    F = (Theta[idx] - main) / np.sqrt(x)
    F = F - F.mean()
    # extract modes
    z = matrix_pencil(F.astype(complex), order=120)
    rho = np.log(z) / du                      # rate (ρ − ½):  Re = σ−½, Im = ±γ
    gam = rho.imag; sig = rho.real + 0.5
    # keep upper-half, physical strip, decent damping
    sel = (gam > 3) & (gam < 55) & (np.abs(rho.real) < 0.25)
    cand = sorted(zip(gam[sel], sig[sel]))
    # match to known
    print(f"\n=== {ch['name']}: zeros recovered from the helix field ===")
    used = []
    for gk in ch['known']:
        near = [(g, s) for g, s in cand if abs(g - gk) < 0.6 and (g, s) not in used]
        if near:
            g, s = min(near, key=lambda gs: abs(gs[0]-gk)); used.append((g, s))
            print(f"   known γ={gk:8.4f}   helix γ={g:8.4f}  |Δ|={abs(g-gk):.4f}   σ={s:.4f}")
        else:
            print(f"   known γ={gk:8.4f}   (not recovered)")
    gx = [g for g, s in used]; sx = [s for g, s in used]
    ax.scatter(ch['known'][:len(gx)] if False else [k for k in ch['known']][:len(gx)], gx,
               s=30, color='steelblue')
    ax.plot([0, 55], [0, 55], 'k--', lw=0.6)
    ax.scatter(ch['known'][:len(gx)], gx, s=36, color='crimson')
    ax.set_title(f"{ch['name']}: helix γ vs known γ"); ax.set_xlabel('known γ'); ax.set_ylabel('helix-field γ')
    ax.set_xlim(0, 55); ax.set_ylim(0, 55)
fig.tight_layout(); fig.savefig(f'{OUT}/helix_zeros_from_field.png', dpi=120)
print(f"\nsaved {OUT}/helix_zeros_from_field.png")
