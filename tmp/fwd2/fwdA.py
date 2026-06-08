import numpy as np, json, sys

ref = json.load(open("/Users/samuellavery/proof/three/tmp/fwd2/ref.json"))
gamma_ref = np.array(ref["gamma_ref"])      # canonical, ONLY for final comparison
nzeros = {int(k): v for k, v in ref["nzeros"].items()}

# ---- prime sieve (Eratosthenes) to modest cap ----
def primes_upto(N):
    s = np.ones(N + 1, dtype=bool)
    s[:2] = False
    for p in range(2, int(N**0.5) + 1):
        if s[p]:
            s[p*p::p] = False
    return np.nonzero(s)[0]

# build list of (log n, amplitude) for prime powers n=p^k <= X with von Mangoldt weight
# Lambda(p^k) = log p ; on-line damping n^{-1/2} = p^{-k/2}
def prime_power_terms(X):
    P = primes_upto(int(X))
    terms = []  # (logn, lambda_weight, n)
    for p in P:
        lp = np.log(p)
        pk = p
        k = 1
        while pk <= X:
            terms.append((np.log(pk), lp, pk))   # log(p^k), Lambda=log p
            pk *= p
            k += 1
    return terms

# t-grid (float64)
t = np.arange(0.0, 119.0, 0.02)   # ~5950 pts

def build_wave(X, taper=None):
    """W(t) = - sum_{p^k<=X} Lambda(n) cos(t log n) / sqrt(n),  optional taper(logn,logX)."""
    terms = prime_power_terms(X)
    W = np.zeros_like(t)
    logX = np.log(X)
    for (logn, lam, n) in terms:
        amp = lam / np.sqrt(n)
        if taper == "fejer":
            w = max(0.0, 1.0 - logn / logX)         # Cesaro/Fejer linear taper in log n
        elif taper == "gauss":
            w = np.exp(-0.5 * (logn / logX)**2 * 4)  # gaussian taper
        elif taper == "riesz":
            w = (1.0 - (logn/logX))**2 if logn < logX else 0.0
        else:
            w = 1.0
        W += -amp * w * np.cos(t * logn)
    return W, len(terms)

def crossings(t, W):
    """sign changes of W -> linear-interpolated roots."""
    s = np.sign(W)
    idx = np.nonzero((s[:-1] * s[1:]) < 0)[0]
    roots = []
    for i in idx:
        x0, x1 = t[i], t[i+1]
        y0, y1 = W[i], W[i+1]
        roots.append(x0 - y0 * (x1 - x0) / (y1 - y0))
    return np.array(roots)

def rms_to_gamma(cross, gammas):
    """for each gamma_n in window, distance to nearest crossing; RMS."""
    if len(cross) == 0:
        return np.nan, 0
    g = gammas[gammas < t[-1]]
    d = np.array([np.min(np.abs(cross - gg)) for gg in g])
    return float(np.sqrt(np.mean(d**2))), len(g)

print("=== APPROACH A: prime-power von Mangoldt forward wave, crossings vs gamma_n ===")
print("t in [0,119), dt=0.02. RMS = nearest-crossing distance to canonical gamma_n.")
print()
for taper in [None, "fejer", "riesz", "gauss"]:
    print(f"--- taper = {taper} ---")
    print(f"{'X':>8} {'#terms':>8} {'#cross<119':>11} {'RMS(gamma)':>11} {'#gamma':>7}")
    for X in [50, 200, 1000, 5000, 20000, 100000]:
        W, nt = build_wave(X, taper)
        cr = crossings(t, W)
        # only crossings in [10,119] (below 10 there are no zeros; gamma_1=14.13)
        cr = cr[(cr > 6) & (cr < 119)]
        rms, ng = rms_to_gamma(cr, gamma_ref)
        print(f"{X:>8} {nt:>8} {len(cr):>11} {rms:>11.4f} {ng:>7}")
        sys.stdout.flush()
    print()
