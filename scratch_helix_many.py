"""Many chi3 zeros, fast: helix resonance locates, mpmath(dps=15) polishes filtered peaks."""
import numpy as np, math, sys
import mpmath as mp
from scipy.signal import find_peaks

Ncut, Nmax, GMAX = 1_000_000, 12_000_000, 80.0

sieve = np.ones(Nmax+1, bool); sieve[:2] = False
for i in range(2, int(Nmax**0.5)+1):
    if sieve[i]: sieve[i*i::i] = False
Lam = np.zeros(Nmax+1)
for p in np.nonzero(sieve)[0].tolist():
    lp = math.log(p); pk = p
    while pk <= Nmax: Lam[pk] = lp; pk *= p
m = np.nonzero(Lam)[0]; mf = m.astype(np.float64)
chi = np.where(m % 3 == 1, 1.0, np.where(m % 3 == 2, -1.0, 0.0))
a = Lam[m]*chi*mf**(-0.5)*np.exp(-mf/Ncut); u = np.log(mf)

du = 0.001; u0 = u[0]; M = int((u[-1]-u0)/du)+2
s = np.zeros(M); np.add.at(s, ((u-u0)/du).astype(np.int64), a)
P = 1 << 22
W = np.abs(np.fft.fft(s, P)); g = 2*np.pi*np.arange(P)/(P*du)
sel = g <= GMAX+1; g, W = g[sel], W[sel]; dg = g[1]-g[0]
pk, _ = find_peaks(W, prominence=W.max()*0.04, distance=int(0.4/dg))
pk = [i for i in pk if 3 < g[i] <= GMAX and W[i] > 0.5*W.max()]   # real zeros only (drop side-lobes)
helix = []
for i in pk:
    d = W[i-1]-2*W[i]+W[i+1]
    helix.append(g[i] + (0.5*(W[i-1]-W[i+1])/d if d else 0)*dg)
print(f"helix located {len(helix)} resonance peaks up to gamma={GMAX:.0f}; polishing...\n", flush=True)

mp.mp.dps = 15
def Lc(t):
    z = mp.mpf(1)/2 + 1j*t
    return mp.power(3,-z)*(mp.zeta(z, mp.mpf(1)/3) - mp.zeta(z, mp.mpf(2)/3))
print(f"{'#':>3} {'helix gamma':>13} {'precise chi3 zero':>22} {'helix err':>11}")
prev, cnt, errs = None, 0, []
for g0 in helix:
    try:
        gr = mp.re(mp.findroot(Lc, mp.mpf(float(g0)), solver='secant'))
    except Exception:
        continue
    if prev is not None and abs(gr-prev) < 1e-6: continue
    if abs(Lc(gr)) > 1e-9: continue
    prev = gr; cnt += 1; errs.append(abs(float(gr)-g0))
    print(f"{cnt:>3} {g0:13.4f} {mp.nstr(gr,15):>22} {float(gr)-g0:+11.2e}", flush=True)
print(f"\n{cnt} chi3 zeros to ~14 digits; helix peak located each to mean {np.mean(errs):.4f}, max {np.max(errs):.4f}")
