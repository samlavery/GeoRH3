"""
ROUTE 2 — SPECTRAL. Build F(u) = sum_{gamma>0} w(gamma) cos(gamma u) and look for
peaks at u = log(p^k).

Explicit-formula heuristic (Riemann-Weil): for a test function with Fourier
transform h, sum over zeros = (archimedean/smooth main term) - sum_n Lambda_chi(n)/sqrt(n)
* [g(log n) + ...].  So the zero sum, after subtracting the smooth archimedean
trend, has DELTA-like contributions at u = log(p^k) with weight  -chi3(p^k) Lambda(p^k)/sqrt(p^k).

Concretely we form, with a Gaussian window in gamma (bandwidth sigma):
    F(u) = sum_gamma exp(-(gamma/G)^2 ... ) cos(gamma u)
The smooth part is the density-of-zeros transform (slowly varying in u). We
estimate & subtract it (local median / smooth fit), then the residual should peak
at log(p^k), coprime to 3, with sign -chi3(p^k), and have NO peak at log 3, log 9.
"""
import math

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
gammas.sort()
import numpy as np
g = np.array(gammas)
G = g.max()


def chi3(n):
    r = n % 3
    return 0 if r == 0 else (1 if r == 1 else -1)


def vm(n):
    if n < 2:
        return 0.0, None
    m, p = n, 2
    while p * p <= m:
        if m % p == 0:
            while m % p == 0:
                m //= p
            return (math.log(p), p) if m == 1 else (0.0, None)
        p += 1
    return math.log(n), n


# u grid
u = np.linspace(0.01, math.log(60), 6000)

# F(u) with Gaussian taper exp(-(gamma*s)^2/2) to make peaks finite-width & kill ringing.
# Peak width in u ~ 1/G_eff. We need to RESOLVE log2=0.69 vs log4=1.39 vs log5=1.61
# vs log7=1.95: gaps ~0.2-0.4, so need effective bandwidth G_eff > ~5-10. Plenty.
def F(u, s):
    w = np.exp(-0.5 * (g * s) ** 2)
    # F = sum w cos(gamma u). Vectorize over u in chunks.
    out = np.zeros_like(u)
    for i in range(len(u)):
        out[i] = np.sum(w * np.cos(g * u[i]))
    return out


# Use a moderate taper so we keep resolution but tame the ringing.
s = 1.0 / 40.0  # effective bandwidth ~40
Fu = F(u, s)

# Smooth archimedean trend: the density part is smooth in u; estimate via a wide
# moving-average and subtract. (The prime peaks are narrow; the trend is broad.)
def movavg(y, win):
    k = np.ones(win) / win
    return np.convolve(y, k, mode='same')

trend = movavg(Fu, 201)
resid = Fu - trend

# Evaluate residual at candidate u=log(p^k); report sign & magnitude.
# Predicted sign of a peak at log(p^k): F ~ + sum cos -> the prime term enters the
# explicit formula as -chi3 Lambda/sqrt(p^k); we just check empirical sign pattern
# is ANTI-correlated with chi3 (the cos transform of the zeros).
print("=== Residual spectral peaks at u=log(p^k) ===")
print("  n   u=log(n)   chi3   resid(u)   sign  | predicted ~ -chi3")
def at(uval):
    i = np.argmin(np.abs(u - uval))
    # local peak: take max-abs in small window
    lo = max(0, i - 15); hi = min(len(u), i + 15)
    j = lo + np.argmax(np.abs(resid[lo:hi]))
    return resid[j]

rows = []
for n in [2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27, 29, 31, 32, 37, 41, 43, 47, 49]:
    lam, p = vm(n)
    if lam <= 0:
        continue
    uval = math.log(n)
    r = at(uval)
    c = chi3(n)
    note = "FLAT(3^k)" if c == 0 else ("anti-chi OK" if (r > 0) != (c > 0) or c == 0 else "")
    print("%4d   %7.4f   %+d   %+9.3f   %s   %s" %
          (n, uval, c, r, '+' if r > 0 else '-',
           'mult-of-3 expect ~0' if c == 0 else ''))
    rows.append((n, c, r))

# Quantify sign anti-correlation on coprime prime powers, and flatness at 3,9,27.
import statistics
coprime = [(n, c, r) for (n, c, r) in rows if c != 0]
mult3 = [(n, c, r) for (n, c, r) in rows if c == 0]
anti = sum(1 for (n, c, r) in coprime if (r > 0) != (c > 0))
print("\nsign ANTI-correlated with chi3 (resid sign = -chi3): %d / %d coprime pp" %
      (anti, len(coprime)))
print("median |resid| at coprime pp: %.3f" % statistics.median([abs(r) for _, _, r in coprime]))
print("|resid| at 3^k:", ["%.3f" % abs(r) for n, c, r in mult3])
print("median |resid| at mult-3 pp: %.3f" %
      (statistics.median([abs(r) for _, _, r in mult3]) if mult3 else float('nan')))
