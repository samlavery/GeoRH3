"""
DECISIVE FORWARD TEST: primes/prime-powers -> zeta zeros, WITHOUT inputting zeta zero values.

Canonical gamma_n used ONLY for final convergence comparison, NEVER fed into construction.

We build the "forward collapse wave" and look for sign-change crossings, then compare to
the true gamma_n. We test several constructions and report ACTUAL NUMBERS.

Constructions:
  (S1) BARE prime-power sum (control, expected to FAIL):
         W(t) = -2 * sum_{p^k <= X} (log p) p^{-k/2} cos(t k log p)
       (This is the explicit-formula fluctuation term, no smooth part.)
  (S2) Riemann-Siegel Z(t) main sum (control, expected to WORK but BORROWS Gamma via theta):
         Z(t) ~ 2 sum_{n<=sqrt(t/2pi)} n^{-1/2} cos(theta(t) - t log n)
       theta = arg Gamma(1/4+it/2) - (t/2) log pi  <-- BORROWED.
  (S3) APPROACH B: prime-power fluctuation + GEOMETRIC smooth phase N_geo(T).
       The smooth count law derived from helix geometry / PNT (NOT arg Gamma).
       We will DERIVE N_geo and test whether it reproduces the log T density.

The "crossings" of the forward wave should be the gamma_n if the model works.
"""
import mpmath as mp
import math
import numpy as np

mp.mp.dps = 30

# ---------- canonical gamma_n (ONLY for final comparison) ----------
def canonical_gammas(M):
    return [float(mp.im(mp.zetazero(n))) for n in range(1, M+1)]

# ---------- prime powers up to X ----------
def prime_powers(X):
    """Return list of (p, k, log p) for all prime powers p^k <= X."""
    Xc = int(X)
    sieve = np.ones(Xc+1, bool); sieve[:2] = False
    for i in range(2, int(Xc**0.5)+1):
        if sieve[i]: sieve[i*i::i] = False
    primes = np.nonzero(sieve)[0]
    out = []
    for p in primes.tolist():
        lp = math.log(p); pk = p; k = 1
        while pk <= Xc:
            out.append((p, k, lp))
            pk *= p; k += 1
    return out

# ---------- the prime-power fluctuation (von Mangoldt explicit formula form) ----------
def fluct(t, pps):
    """ -2 sum_{p^k<=X} (log p) p^{-k/2} cos(t k log p) .
        This is the oscillating part of psi'(x) <-> sum over zeros, evaluated as a wave in t.
        Actually the standard 'wave' whose zeros track gamma_n in RS is sum n^{-s}.
        Here we use the von Mangoldt / log-derivative fluctuation. """
    s = 0.0
    for (p, k, lp) in pps:
        s += lp * (p ** (-k/2.0)) * math.cos(t * k * lp)
    return -2.0 * s

if __name__ == "__main__":
    print("=== sanity: canonical first 10 gamma_n ===")
    g = canonical_gammas(10)
    for i, gi in enumerate(g, 1):
        print(f"  gamma_{i} = {gi:.6f}")
    print()
    print("=== prime powers up to X=50 ===")
    pps = prime_powers(50)
    for x in pps: print("  ", x)
