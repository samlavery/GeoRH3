"""
Step 2: APPROACH A - regularized prime-power explicit-formula forward wave.

Build the real wave from PRIME POWERS only, on-line damping p^{-k/2}, von Mangoldt weight:
    W_X(t) = - sum_{p^k <= X} (log p) * cos(t * k * log p) / p^{k/2}

This is the "prime side" of the explicit formula. The explicit formula says:
    sum_n delta(t - gamma_n)  <-->  (smooth log-T density)  -  (1/pi) sum_{p^k} (log p) p^{-k/2} cos(t k log p)
i.e. the zeros are encoded in the SUM, against a SMOOTH background.

We test, with NO Gamma/zeta inserted:
  (1) crossings of W_X (and of regularized variants) vs gamma_n  -- per-zero residual (SECONDARY)
  (2) COLLECTIVE dual spectrum D(u) = sum_n cos(gamma_n u) sampled at u = k log p:
      canonical D vs what the construction implies. (PRIMARY)
  (3) crossing COUNT / density vs canonical N(T) -- does prime-power-only develop log T density?

All wave eval in numpy float64. Loop over terms to keep memory O(#t).
"""
import numpy as np
import json

with open("/Users/samuellavery/proof/three/tmp/fwd2/ref.json") as f:
    ref = json.load(f)
gamma_ref = np.array(ref["gamma_ref"])
nzeros_ref = {int(k): v for k, v in ref["nzeros_ref"].items()}

# ---- prime powers via numpy sieve, modest cap ----
def primes_upto(n):
    sieve = np.ones(n + 1, dtype=bool)
    sieve[:2] = False
    for i in range(2, int(n**0.5) + 1):
        if sieve[i]:
            sieve[i*i::i] = False
    return np.nonzero(sieve)[0]

PRIME_CAP = 100000  # 1e5, prime powers p^k <= 1e5
primes = primes_upto(PRIME_CAP)

def prime_powers_upto(X):
    """Return list of (logp, k, pk_value, weight=logp, damp=pk^{-1/2}) for p^k <= X."""
    terms = []
    for p in primes:
        if p > X:
            break
        lp = np.log(p)
        pk = p
        k = 1
        while pk <= X:
            terms.append((lp, k, pk))
            pk *= p
            k += 1
    return terms

# ---- t-grid (numpy float64) ----
t = np.arange(0.0, 120.0, 0.02)  # ~6000 pts

def build_wave(X, taper=None):
    """W_X(t) = - sum_{p^k<=X} (log p) cos(t k log p) / p^{k/2}, looped (O(#t) mem).
    taper: None | 'gauss' | 'fejer'  (smooth cutoff in log scale to aid convergence,
           NO Gamma/zeta inserted)."""
    terms = prime_powers_upto(X)
    W = np.zeros_like(t)
    logX = np.log(X)
    for (lp, k, pk) in terms:
        freq = k * lp
        amp = lp / np.sqrt(pk)
        if taper == 'gauss':
            # gaussian taper in log(n): exp(-(log pk / logX)^2 * c)  -- pure regularization
            u = np.log(pk) / logX
            amp *= np.exp(-(u**2) * 4.0)
        elif taper == 'fejer':
            # Fejer/Cesaro triangular taper: (1 - log pk / logX)_+
            u = np.log(pk) / logX
            amp *= max(0.0, 1.0 - u)
        W -= amp * np.cos(freq * t)
    return W

def find_crossings(W, tgrid):
    """sign changes of W -> linear-interpolated crossing t-values."""
    s = np.sign(W)
    idx = np.nonzero(np.diff(s) != 0)[0]
    cr = []
    for i in idx:
        t0, t1 = tgrid[i], tgrid[i+1]
        w0, w1 = W[i], W[i+1]
        if w1 != w0:
            cr.append(t0 - w0 * (t1 - t0) / (w1 - w0))
    return np.array(cr)

def per_zero_residual(crossings, gammas):
    """For each gamma_n, nearest crossing; RMS (accumulates drift -- SECONDARY)."""
    if len(crossings) == 0:
        return float('nan'), []
    res = []
    for g in gammas:
        j = np.argmin(np.abs(crossings - g))
        res.append(crossings[j] - g)
    res = np.array(res)
    return float(np.sqrt(np.mean(res**2))), res

# ---- COLLECTIVE dual spectrum metric (PRIMARY) ----
# canonical dual spectrum at u = k log p: D_can(u) = sum_n cos(gamma_n u) (truncated to known zeros)
# The prime side IS the construction; by the explicit formula the construction's spectral content
# at frequency u=k log p should equal the canonical D_can(u) (up to smooth + normalization).
# We compute correlation of the construction's amplitude/phase structure vs canonical.
def dual_spectrum_canonical(u_vals, gammas):
    D = np.array([np.sum(np.cos(gammas * u)) for u in u_vals])
    return D

print("="*70, flush=True)
print("APPROACH A: prime-power von Mangoldt wave -> crossings vs gamma_n", flush=True)
print("="*70, flush=True)

Xs = [50, 200, 1000, 5000, 20000, 100000]
print(f"\n{'X':>7} {'#terms':>7} {'#cross(<102)':>12} {'N_can(102)~':>11} {'RMS_perzero':>12}", flush=True)
N_can_102 = nzeros_ref[100]  # canonical count near our gamma range top
for X in Xs:
    terms = prime_powers_upto(X)
    W = build_wave(X, taper=None)
    cr = find_crossings(W, t)
    cr_in = cr[(cr > 5) & (cr < 102)]
    rms, res = per_zero_residual(cr, gamma_ref)
    # each gamma is one zero -> crossing count should approach N(T). zeros->crossings count
    print(f"{X:>7} {len(terms):>7} {len(cr_in):>12} {N_can_102:>11} {rms:>12.4f}", flush=True)

print("\n(NOTE: per-zero RMS is SECONDARY and accumulates drift; #crossings density is the honest signal)", flush=True)
