"""
HONEST DIAGNOSTIC: the crossing DENSITY.

The bare prime-power wave W_X(t) = -sum logp cos(t k logp)/p^{k/2} is a sum of
cosines with frequencies k*log p in [log2, logX]. Its zero-crossing density is
governed by its highest frequency ~ logX / (2pi) per unit t -- it has NOTHING to
do with the zeta zero density N'(T) ~ (1/2pi) log(T/2pi).

Test:
 (1) crossing count of W_X on (0,T) vs nzeros(T). Does it match? On what?
 (2) The TRUE zero density is theta-driven: N(T)=(1/pi)theta(T)+1.
     theta(T)=arg Gamma(1/4+iT/2) - (T/2)log pi. This is the SMOOTH part.
     Does ANY prime-power-only object produce this? -> NO: prime sum freqs are
     fixed constants k logp; the t-DEPENDENT phase log(t) of theta comes from
     Gamma, not from primes.
"""
import numpy as np
import mpmath as mp
from sympy import primerange

mp.mp.dps = 25

def prime_powers_up_to(X):
    out = []
    for p in primerange(2, int(X) + 1):
        lp = np.log(p); pk = p; k = 1
        while pk <= X:
            out.append((pk, lp, k)); pk *= p; k += 1
    return out

def build_wave(X):
    pps = prime_powers_up_to(X)
    freqs = np.array([k * lp for (pk, lp, k) in pps])
    amps = np.array([lp / np.sqrt(pk) for (pk, lp, k) in pps])
    def W(t):
        return -np.sum(amps * np.cos(t * freqs)), freqs.max()
    return W, len(pps), freqs.max()

def crossings_count(X, Tmax, N):
    pps = prime_powers_up_to(X)
    freqs = np.array([k * lp for (pk, lp, k) in pps])
    amps = np.array([lp / np.sqrt(pk) for (pk, lp, k) in pps])
    ts = np.linspace(0.5, Tmax, N)
    # vectorized
    vals = -(amps[None, :] * np.cos(np.outer(ts, freqs))).sum(axis=1)
    sc = np.sum(np.sign(vals[:-1]) != np.sign(vals[1:]))
    return sc, freqs.max()

print("Crossing density of bare prime-power wave vs true zeta count")
print(f"{'X':>8} {'maxfreq=logX':>12} {'#cross(0,100)':>13} {'nzeros(100)':>11} {'predicted~maxfreq*T/2pi':>22}")
Tmax = 100.0
for X in [100, 1000, 10000, 100000, 1000000]:
    sc, fmax = crossings_count(X, Tmax, N=400000)
    pred = fmax * Tmax / (2 * np.pi)
    print(f"{X:>8} {np.log(X):>12.3f} {sc:>13} {int(mp.nzeros(Tmax)):>11} {pred:>22.1f}")

print()
print("INTERPRETATION:")
print(" - true zeta count nzeros(100) is fixed at 29.")
print(" - bare-wave crossing count GROWS without bound as X grows (tracks maxfreq=logX).")
print(" - the wave density is set by its highest prime frequency, NOT by zeta's log-T density.")
print(" - => the crossings are arithmetic ripples, not zero markers.")
