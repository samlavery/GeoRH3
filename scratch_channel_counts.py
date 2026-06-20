"""
The fiber rides up, crossing numbers 1..N.  The 'interesting' primes (chi(p) != 0)
generate phasors, bucketed into POS / NEG channels by the Frobenius/character sign.

chi3 (mod 3):  p % 3 == 1 -> POS (+1) ,  p % 3 == 2 -> NEG (-1) ,  p == 3 -> killed (0)

Report, per channel: count of phasors  vs  count of numbers crossed (N).
Pure arithmetic on the carrier -- no zeta, no logs in the signal.
"""
import numpy as np

Nmax = 1_000_000
sieve = np.ones(Nmax + 1, dtype=bool); sieve[:2] = False
for i in range(2, int(Nmax**0.5) + 1):
    if sieve[i]:
        sieve[i*i::i] = False
primes = np.nonzero(sieve)[0]

pos_primes = primes[primes % 3 == 1]     # + channel
neg_primes = primes[primes % 3 == 2]     # - channel  (note: 2 is here)
killed = primes[primes % 3 == 0]         # only {3}

print(f"first POS-channel primes (p≡1 mod 3): {pos_primes[:10].tolist()}")
print(f"first NEG-channel primes (p≡2 mod 3): {neg_primes[:10].tolist()}")
print(f"killed (p≡0 mod 3): {killed.tolist()}\n")

print(f"{'numbers crossed N':>17} | {'POS phasors':>11} {'NEG phasors':>11} {'all phasors':>11} | "
      f"{'POS/N':>8} {'NEG/N':>8} {'phasor/N':>9} | {'NEG−POS (bias)':>14}")
print("-" * 110)
for N in [10, 30, 100, 300, 1000, 3000, 10_000, 30_000, 100_000, 300_000, 1_000_000]:
    pos = int(np.searchsorted(pos_primes, N, side="right"))
    neg = int(np.searchsorted(neg_primes, N, side="right"))
    tot = pos + neg
    print(f"{N:>17,} | {pos:>11,} {neg:>11,} {tot:>11,} | "
          f"{pos/N:>8.4f} {neg/N:>8.4f} {tot/N:>9.4f} | {neg-pos:>14,}")

print()
print("Readings:")
print("  • phasors (interesting primes) are SPARSE vs numbers crossed: phasor/N → 0 like 1/log N.")
print("  • POS and NEG counts track each other (Dirichlet: primes split evenly between residues),")
print("    with NEG (p≡2) running slightly ahead — the Chebyshev bias (NEG−POS > 0, grows slowly).")
print("  • each channel's phasor count ≈ ½·π(N); the small NEG−POS imbalance is what the fiber 'feels'.")
