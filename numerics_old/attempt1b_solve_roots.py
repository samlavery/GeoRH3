"""
ATTEMPT 1b — solve N_smooth(gamma)+S_prime(gamma) = n-1/2 for PREDICTED gamma_n
(the literal FTA-thesis test), then measure |predicted - actual| in units of the
local mean spacing. Compare smooth-only vs prime-corrected.
"""
import math
import numpy as np
from scipy.optimize import brentq

gammas = []
with open('lchi3_zeros_record.txt') as f:
    for line in f:
        line = line.strip()
        if not line or line.startswith('#'):
            continue
        toks = line.split()
        if len(toks) < 2:
            continue
        gammas.append(float(toks[1]))
gammas = np.array(sorted(gammas))
M = len(gammas)


def chi3(n):
    r = n % 3
    return 0 if r == 0 else (1 if r == 1 else -1)


def N_smooth(T):
    return (T / (2*math.pi)) * math.log(3.0*T/(2*math.pi)) - T/(2*math.pi)


def primes_up_to(N):
    s = np.ones(N+1, bool); s[:2] = False
    for p in range(2, int(N**0.5)+1):
        if s[p]:
            s[p*p::p] = False
    return np.nonzero(s)[0]


def prime_terms(X):
    out = []
    for p in primes_up_to(X):
        c = chi3(int(p))
        if c == 0:
            continue
        k = 1
        while p**k <= X:
            out.append((k*math.log(p), (c**k)/(k*(p**(k/2.0)))))
            k += 1
    ph = np.array([t[0] for t in out]); co = np.array([t[1] for t in out])
    return ph, co


# fit the constant offset so smooth ladder is centered (slope already exact 1)
n_idx = np.arange(1, M+1)
C = np.mean((n_idx-0.5) - np.array([N_smooth(g) for g in gammas]))


def Ntot(T, ph, co, use_primes):
    val = N_smooth(T) + C
    if use_primes:
        val += -(1.0/math.pi)*np.sum(co*np.sin(T*ph))
    return val


def predict(use_primes, ph=None, co=None):
    preds = np.full(M, np.nan)
    # solve Ntot(T) = n-1/2 bracketing near the actual zero
    for i in range(M):
        target = (i+1) - 0.5
        g = gammas[i]
        lo, hi = g-3.0, g+3.0
        if lo < 1.0:
            lo = 1.0
        try:
            f = lambda T: Ntot(T, ph, co, use_primes) - target
            if f(lo)*f(hi) > 0:
                # widen
                lo, hi = g-6.0, g+6.0
                if lo < 1.0: lo = 1.0
            if f(lo)*f(hi) <= 0:
                preds[i] = brentq(f, lo, hi, xtol=1e-8)
        except Exception:
            pass
    return preds


# local mean spacing for unit conversion
spacing = np.gradient(gammas)

print(f"loaded {M} zeros")
print("\n=== SMOOTH ONLY: solve N_smooth(gamma)=n-1/2 ===")
ps = predict(False)
ok = ~np.isnan(ps)
err_smooth = (ps - gammas)/spacing
print(f"  solved {ok.sum()}/{M}; |pred-actual|/spacing: std={np.nanstd(err_smooth):.4f} "
      f"mean|.|={np.nanmean(np.abs(err_smooth)):.4f} max|.|={np.nanmax(np.abs(err_smooth)):.4f}")

print("\n=== PRIME-CORRECTED: solve N_smooth+S_prime = n-1/2 ===")
print(f"  {'X':>7} {'#terms':>7} {'std/sp':>8} {'mean|.|':>8} {'max|.|':>8} {'vs smooth':>10}")
base = np.nanstd(err_smooth)
for X in [10, 50, 200, 1000, 10000, 100000]:
    ph, co = prime_terms(X)
    ps = predict(True, ph, co)
    err = (ps - gammas)/spacing
    s = np.nanstd(err)
    print(f"  {X:>7} {len(ph):>7} {s:>8.4f} {np.nanmean(np.abs(err)):>8.4f} "
          f"{np.nanmax(np.abs(err)):>8.4f} {('BETTER %.2fx'%(base/s)) if s<base else 'worse':>10}")
