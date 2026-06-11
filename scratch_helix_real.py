"""
THE REAL TEST: winding from placement alone, nothing analytic injected.
  geometric winding angle of integer n ~ sqrt(n)   (Archimedean rewind; NO log)
  unit amplitude                                    (NO n^{-s}, NO 1/2)
  chi3 signs
Sweep a reading frequency t; |S(t)| = |sum_p chi3(p) e^{i t sqrt(p)}|.
Does anything zero-like (8.04, 11.24, 15.70, ...) survive WITHOUT log/half?
For contrast: the analytic injection (von Mangoldt, p^{-1/2}, log-phase) that DID give zeros.
"""
import numpy as np
from scipy.signal import find_peaks

Nmax = 2_000_000
sieve = np.ones(Nmax+1, bool); sieve[:2] = False
for i in range(2, int(Nmax**0.5)+1):
    if sieve[i]: sieve[i*i::i] = False
p = np.nonzero(sieve)[0]
p = p[p % 3 != 0]                               # primes chi3 cares about
chi = np.where(p % 3 == 1, 1.0, -1.0).astype(np.float64)
pf = p.astype(np.float64)
sp = np.sqrt(pf)                                # GEOMETRIC winding  ~ sqrt(p)   (no log)
lp = np.log(pf)                                 # bridge winding     ~ log p     (analytic)
ampL = np.log(pf) * pf**(-0.5)                  # analytic amplitude: ~Lambda(p) * p^{-1/2}

zeros = [8.04, 11.24, 15.70, 18.26, 20.46, 24.06, 26.58, 28.22]
t = np.arange(0.05, 30.0, 0.01)

def sweep(amp, phasecoord):
    return np.array([abs(np.sum(amp * np.exp(1j*tt*phasecoord))) for tt in t])

Sgeom = sweep(chi, sp)                           # REAL geometry: unit amp, sqrt(p) phase
Sfull = sweep(chi*ampL, lp)                      # analytic injection: p^{-1/2}log p, log p phase

def report(name, S):
    Sn = S / S.max()
    pk, _ = find_peaks(Sn, prominence=0.15, distance=50)
    near = sum(1 for z in zeros if min(abs(t[i]-z) for i in pk) < 0.2) if len(pk) else 0
    print(f"\n--- {name} ---  ({len(pk)} prominent peaks; {near}/{len(zeros)} land on a chi3 zero)")
    for z in zeros:
        d = min((abs(t[i]-z), t[i]) for i in pk) if len(pk) else (99,0)
        hit = "HIT" if d[0] < 0.2 else "   "
        print(f"   zero {z:6.2f}  nearest peak {d[1]:6.2f}  (d={d[0]:.2f}) {hit}")

report("REAL geometry: unit amplitude, sqrt(p) winding (no log, no 1/2)", Sgeom)
report("analytic injection: p^{-1/2} amp, log-p phase", Sfull)

# also: is the geometric curve just noise? compare its peak heights to a random-sign control
rng_like = np.array([abs(np.sum(np.where((p*7+3) % 5 < 2, 1.0, -1.0) * np.exp(1j*tt*sp))) for tt in t])
print(f"\ngeometric |S| stats: mean {Sgeom.mean():.1f}, max {Sgeom.max():.1f}, "
      f"sqrt(#primes)={np.sqrt(len(p)):.1f}  (Weyl/random-walk scale)")
print(f"control (arbitrary signs, same sqrt-p phase): max {rng_like.max():.1f}  "
      f"-- if comparable, the geometric peaks are just noise")
