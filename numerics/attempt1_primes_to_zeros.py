"""
ATTEMPT 1 — PRIMES -> ZEROS (the FTA thesis, concrete).

Smooth Berry-Keating counting function for L(chi3) (conductor q=3, ODD character):
    N_smooth(E) = (E/2pi) * log(3 E / 2pi) - E/2pi + 7/8 + (1/pi) arg Gamma-factor...
We use the standard Riemann-von Mangoldt form for a Dirichlet L-function of
conductor q and a-value (a=1 for odd chi):
    N(T) = (T/pi) log( q T / (2 pi e) ) + (a-value phase) + S(T) + ...
The PRIME fluctuation is
    S_prime(t) = -(1/pi) * sum_{p^k <= X} chi3(p^k) sin(t k log p) / (k p^{k/2}).
We solve  N_smooth(gamma) + S_prime(gamma) = n - 1/2 + offset  for predicted gamma_n,
and compare residual std (predicted - actual, in units of mean spacing) to the
smooth-only baseline.

We FIT the smooth ladder's additive offset by least squares against the actual
zeros (a single global constant), so the comparison isolates the *fluctuation*
S_prime, not the constant. This is the honest test: does the PRIME SUM move each
prediction toward its actual zero?
"""
import math
import numpy as np

# ---- load actual zeros (gamma = SECOND token) ----
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
print(f"loaded {len(gammas)} zeros; first three: {gammas[:3]}")


def chi3(n):
    r = n % 3
    return 0 if r == 0 else (1 if r == 1 else -1)


# ---- smooth counting function N_smooth(T) for L(chi3), q=3, odd character ----
# Riemann-von Mangoldt for Dirichlet L (conductor q, a in {0,1}, here a=1 odd):
#   N(T) = (T/pi)*log(qT/(2 pi)) - T/pi + (smooth Gamma phase) + 7/8 + ...
# We collapse all smooth constants into a single fitted offset C (least squares).
def N_smooth_raw(T):
    # Riemann-von Mangoldt / Berry-Keating, conductor q=3:
    #   N(E) = (E/2pi) log(3E/2pi) - E/2pi    (slope -> 1 per zero, verified)
    return (T / (2.0 * math.pi)) * math.log(3.0 * T / (2.0 * math.pi)) - T / (2.0 * math.pi)


# ---- prime fluctuation S_prime(t) up to bound X on p^k ----
def primes_up_to(N):
    sieve = np.ones(N + 1, dtype=bool)
    sieve[:2] = False
    for p in range(2, int(N**0.5) + 1):
        if sieve[p]:
            sieve[p * p::p] = False
    return np.nonzero(sieve)[0]


def prime_power_terms(X):
    """Return list of (k*log p, chi3(p^k)/(k p^{k/2})) for all p^k <= X."""
    terms = []
    ps = primes_up_to(X)
    for p in ps:
        c = chi3(int(p))
        if c == 0:
            continue  # p=3 contributes nothing
        pk = p
        k = 1
        while pk <= X:
            # chi3(p^k) = chi3(p)^k for multiplicative real char (chi3(p)=+-1)
            ck = c**k
            terms.append((k * math.log(p), ck / (k * (p ** (k / 2.0)))))
            k += 1
            pk = p ** k
    return terms


def S_prime_factory(X):
    terms = prime_power_terms(X)
    phases = np.array([t[0] for t in terms])
    coeffs = np.array([t[1] for t in terms])

    def S(t):
        return -(1.0 / math.pi) * np.sum(coeffs * np.sin(t * phases))
    return S, len(terms)


# ---- residual evaluation ----
# For each actual zero gamma_n, the smooth-ladder PREDICTION at "rank n" is
# implicit. Instead of solving N=n (which needs the integer rank), we use the
# standard equivalence: at the actual zeros, the quantity
#     R(gamma_n) = N_smooth(gamma_n) + C  should equal an integer (n-1/2),
# and the FLUCTUATION  S(gamma_n) = -(N_smooth(gamma_n)+C - round(...))
# i.e. the *unfolded residual* of the smooth ladder at the true zeros IS S(t).
# So the cleanest test: does -pi*S_prime(gamma) track the smooth-ladder unfolded
# residual at each true zero? Equivalently, does N_smooth+S_prime hit integers
# better than N_smooth alone?
#
# We compute, for each true zero, the "ladder value" L0 = N_smooth(g)+C and
# L1 = N_smooth(g)+S_prime(g)+C. The best ladder makes these land on the integer
# lattice (n - 1/2). Residual = L - nearest-half-integer, std reported in units
# of MEAN SPACING (=1 in unfolded N, since dN/dT * spacing ~ 1).

# The unfolded smooth-ladder residual at the true zeros:
#   r_n = (n - 1/2) - [N_smooth(gamma_n) + C]
# is (up to sign) the prime fluctuation S(t)=(1/pi)arg L(1/2+it). The prime sum
# S_prime PREDICTS that fluctuation. So the test is whether r_n is explained by
# S_prime: does std(r_n - S_prime(gamma_n)) drop below std(r_n)?  (We auto-pick
# the sign of S_prime that best aligns, and report the correlation.)
n = np.arange(1, len(gammas) + 1)
Nvals = np.array([N_smooth_raw(g) for g in gammas])
C0 = np.mean((n - 0.5) - Nvals)
r = (n - 0.5) - (Nvals + C0)          # smooth-ladder unfolded residual
std0 = np.std(r)

print("\n=== Smooth-only baseline ===")
print(f"  smooth ladder unfolded-residual std: {std0:.4f}  (units = mean spacing)")

print("\n=== Add prime fluctuation S_prime, X = 10,50,200,1000,... ===")
print(f"  {'X':>6} {'#p^k':>6} {'corr(r,Sp)':>11} {'best-sign std':>14} {'vs smooth':>10}")
print(f"  {'smooth':>6} {'-':>6} {'-':>11} {std0:>14.4f} {'baseline':>10}")
results = {}
for X in [10, 50, 200, 1000, 5000, 20000, 100000]:
    S, nt = S_prime_factory(X)
    Sp = np.array([S(g) for g in gammas])
    corr = np.corrcoef(r, Sp)[0, 1]
    # best scalar alpha (least squares) for r ~ alpha*Sp, then residual std
    alpha = np.dot(r, Sp) / np.dot(Sp, Sp)
    std_corrected = np.std(r - alpha * Sp)
    results[X] = std_corrected
    arrow = "BETTER" if std_corrected < std0 else "worse"
    print(f"  {X:>6} {nt:>6} {corr:>11.4f} {std_corrected:>14.4f} {arrow:>10} (ratio {std_corrected/std0:.3f}, alpha={alpha:.3f})")

print("\n=== Saturation: does adding more primes keep helping? ===")
xs = sorted(results)
for i in range(1, len(xs)):
    d = results[xs[i]] - results[xs[i-1]]
    print(f"  X {xs[i-1]:>6} -> {xs[i]:>6}: std {results[xs[i-1]]:.4f} -> {results[xs[i]]:.4f}  (delta {d:+.4f})")
