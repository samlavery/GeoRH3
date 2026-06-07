"""
Fold PITCH in as its own axis (ζ).

Read along the helix climb at pitch p: the height step is p·(log-x step), so a mode's measured
climb-rate is (ρ−a)/p.  Hence:
    measured climb-frequency = γ / p          (raw, depends on pitch)
    recovered γ = p × (climb-frequency) = γ    (pitch carries γ)
    radial frame: drift = (σ−a)/p  → 0 ⟺ σ=a, crossing at a=½ for ANY pitch (radial untouched)
So pitch is the height/rate scale (carries γ), independent of the radial-rate frame a (=½).
"""
import numpy as np, math, os
import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt
OUT = os.path.dirname(os.path.abspath(__file__))

N = 4_000_000
print(f"sieve + von Mangoldt (ζ) to {N:,} ...")
sieve = np.ones(N+1, bool); sieve[:2] = False
for i in range(2, int(N**0.5)+1):
    if sieve[i]: sieve[i*i::i] = False
Lam = np.zeros(N+1)
for p in np.nonzero(sieve)[0].tolist():
    lp = math.log(p); pk = p
    while pk <= N: Lam[pk] = lp; pk *= p
psi = np.cumsum(Lam)

def mpencil(y, order):
    L = len(y)//2
    Y = np.lib.stride_tricks.sliding_window_view(y, L+1)
    _, _, Vh = np.linalg.svd(Y, full_matrices=False)
    V = Vh.conj().T[:, :order]
    return np.linalg.eigvals(np.linalg.pinv(V[:-1]) @ V[1:])

du = 0.006
u = np.arange(5.0, math.log(N) - 0.05, du)
x = np.exp(u); idx = np.clip(np.floor(x).astype(int), 0, N)
known = np.array([14.1347,21.0220,25.0109,30.4249,32.9351,37.5862,40.9187,43.3271])

# --- modes at the a=½ frame (true ρ−½) ---
F = (psi[idx] - x) / np.sqrt(x); F = F - F.mean()
rate = np.log(mpencil(F.astype(complex), 110)) / du
gam = rate.imag; gr = rate.real
sel = (gam > 5) & (gam < 45) & (np.abs(gr) < 0.3)
gam_t = np.array(sorted(gam[sel]))
# match first few to known
gtrue = []
for k in known:
    c = gam_t[np.argmin(np.abs(gam_t - k))]
    if abs(c - k) < 0.5: gtrue.append(c)
gtrue = np.array(gtrue)
print("matched γ (a=½):", ", ".join(f"{g:.3f}" for g in gtrue))

# --- radial drift vs a (the radial-rate frame), independent of pitch ---
A = np.linspace(0.30, 0.70, 11); drift = []
for a in A:
    Fa = (psi[idx] - x) / x**a; Fa = Fa - Fa.mean()
    r = np.log(mpencil(Fa.astype(complex), 100)) / du
    g, d = r.imag, r.real
    s = (g > 5) & (g < 45) & (np.abs(d) < 0.45)
    drift.append(np.median(d[s]))
drift = np.array(drift)
zc = np.interp(0.0, drift[::-1], A[::-1])
print(f"radial-½ crossing at a={zc:.4f} (pitch-invariant: recovery cancels the pitch scale)")

pitches = np.linspace(0.5, 3.0, 30)
fig, (axA, axB) = plt.subplots(1, 2, figsize=(14, 5.5))
# Panel A: pitch carries γ
for g in gtrue[:5]:
    axA.plot(pitches, g/pitches, lw=0.8, color='0.6')                 # raw climb-frequency = γ/pitch
    axA.plot(pitches, pitches*(g/pitches), lw=1.6)                    # recovered γ = pitch×freq (flat)
    axA.axhline(g, color='k', ls=':', lw=0.5)
axA.set_title('PITCH carries γ\nthin grey = raw climb-freq (γ/pitch);  bold = recovered γ = pitch×freq')
axA.set_xlabel('pitch'); axA.set_ylabel('frequency / recovered γ')
# Panel B: radial-½ untouched
axB.plot(A, drift, 'o-', color='steelblue', label='recovered radial growth (any pitch)')
axB.plot(A, 0.5 - A, 'r--', lw=1, label='½ − a')
axB.axhline(0, color='k', lw=0.6); axB.axvline(0.5, color='crimson', ls=':', label='a=½')
axB.set_title(f'RADIAL-½ untouched by pitch\ncrossing at a={zc:.4f}')
axB.set_xlabel('radial growth exponent a'); axB.set_ylabel('radial growth (σ−a)'); axB.legend(fontsize=8)
fig.tight_layout(); fig.savefig(f'{OUT}/pitch_scan.png', dpi=120)
print(f"saved {OUT}/pitch_scan.png")
