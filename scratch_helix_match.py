"""
chi3: where prime-bucket cancellations MATCH real zeros and where they DON'T.
Sweep bucket size N. Small N -> too few primes -> spurious cancellations (no energy/zero)
and missed zeros. Large N -> cancellations lock onto the zeros. Energy |W| marks the real ones.
"""
import numpy as np, math
import mpmath as mp
from scipy.signal import find_peaks

mp.mp.dps = 12
def Lc(t):
    s = mp.mpf(0.5) + 1j*mp.mpf(t)
    return mp.power(3, -s) * (mp.zeta(s, mp.mpf(1)/3) - mp.zeta(s, mp.mpf(2)/3))

G = np.arange(0.20, 30.0, 0.01)
absL = np.array([float(abs(Lc(float(g)))) for g in G])
zmin, _ = find_peaks(-absL, prominence=0.25)
real_zeros = [round(float(G[i]), 2) for i in zmin if absL[i] < 0.3]

# full von Mangoldt resonance = spectral energy (peaks only at real zeros)
Ncut, Nmax = 100_000, 1_200_000
sieve = np.ones(Nmax+1, bool); sieve[:2] = False
for i in range(2, int(Nmax**0.5)+1):
    if sieve[i]: sieve[i*i::i] = False
Lam = np.zeros(Nmax+1)
for p in np.nonzero(sieve)[0].tolist():
    lp = math.log(p); pk = p
    while pk <= Nmax: Lam[pk] = lp; pk *= p
m = np.nonzero(Lam)[0]; mf = m.astype(float)
chiM = np.where(m % 3 == 1, 1.0, np.where(m % 3 == 2, -1.0, 0.0))
wv = Lam[m] * chiM * mf**(-0.5) * np.exp(-mf/Ncut); lm = np.log(mf)
Wmag = lambda g: float(abs(np.sum(wv * np.exp(-1j*g*lm))))
Wnorm = max(Wmag(z) for z in real_zeros)

print(f"true chi3 zeros 0..30: {real_zeros}")

for N in (6, 10, 40):
    nn = np.arange(1, N+1)
    chi = np.where(nn % 3 == 1, 1.0, np.where(nn % 3 == 2, -1.0, 0.0))
    keep = int((chi != 0).sum())
    amp = chi * nn**(-0.5); logn = np.log(nn)
    absS = np.array([abs(np.sum(amp * np.exp(-1j*g*logn))) for g in G])
    Smax = absS.max()
    dips, _ = find_peaks(-absS, prominence=Smax*0.05)
    dips = [i for i in dips if absS[i]/Smax < 0.35]          # genuine cancellations only
    print(f"\n===========  bucket N={N}  ({keep} terms chi3 keeps)  ===========")
    print(f"{'cancellation g':>14} {'|S|depth':>9} {'energy|W|':>9} {'nearzero':>9} {'d':>6}  verdict")
    for i in dips:
        g = float(G[i]); depth = absS[i]/Smax; E = Wmag(g)/Wnorm
        z = min(real_zeros, key=lambda z: abs(z-g)); d = g - z
        v = "MATCH (real zero)" if (abs(d) < 0.3 and E > 0.5) else "SPURIOUS (cancels, no energy/zero)"
        print(f"{g:14.2f} {depth:9.3f} {E:9.3f} {z:9.2f} {d:+6.2f}  {v}")
    missed = [z for z in real_zeros if (not dips) or min(abs(z-float(G[i])) for i in dips) > 0.4]
    print(f"   real zeros MISSED by this bucket: {missed if missed else 'none'}")
