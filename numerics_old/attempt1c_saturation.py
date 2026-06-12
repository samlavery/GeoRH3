"""
ATTEMPT 1c — does the prime correction SATURATE or keep improving?
Push X up to 10^6, fit std(X) ~ A * X^(-beta) to characterize the rate.
The Euler product diverges at Re=1/2, so S_prime is an ASYMPTOTIC (divergent if
pushed to infinity at fixed t) series. We expect improvement up to X ~ (gamma)^2
scale then the omitted tail + divergence sets a floor that depends on gamma_max.
"""
import math
import numpy as np

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
    return (T/(2*math.pi))*np.log(3.0*T/(2*math.pi)) - T/(2*math.pi)


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
    return np.array([t[0] for t in out]), np.array([t[1] for t in out])


n_idx = np.arange(1, M+1)
Nv = N_smooth(gammas)
C = np.mean((n_idx-0.5) - Nv)
spacing = np.gradient(gammas)


def std_for(X):
    ph, co = prime_terms(X)
    # S_prime at each gamma; correct the unfolded residual directly (fast, equiv to root-solve to 1st order)
    Sp = -(1.0/math.pi)*(np.sin(np.outer(gammas, ph)) @ co)
    # predicted count residual
    r = (n_idx-0.5) - (Nv + C) - Sp     # remaining residual after prime correction
    # convert count-residual to gamma-units: divide by local density dN/dgamma
    dens = np.log(3.0*gammas/(2*math.pi))/(2*math.pi)
    err = r / dens / spacing  # in spacing units (dens*spacing ~1)
    return np.std(r/dens/spacing), len(ph)


Xs = [10, 30, 100, 300, 1000, 3000, 10000, 30000, 100000, 300000, 1000000]
print(f"{'X':>9} {'#terms':>7} {'std/spacing':>12}")
data = []
for X in Xs:
    s, nt = std_for(X)
    data.append((X, s))
    print(f"{X:>9} {nt:>7} {s:>12.5f}")

# fit log-log slope over the productive range
Xa = np.array([d[0] for d in data], float)
Sa = np.array([d[1] for d in data], float)
lx, ly = np.log(Xa), np.log(Sa)
beta, lnA = np.polyfit(lx, ly, 1)
print(f"\npower-law fit std ~ A * X^beta:  beta = {beta:.3f}  (A={math.exp(lnA):.3f})")
print("interpretation: beta<0 => still improving; flattening (beta->0) => saturating.")
# last-decade slope
b2, _ = np.polyfit(lx[-4:], ly[-4:], 1)
print(f"slope over last decade (X=3e4..1e6): {b2:.3f}")
