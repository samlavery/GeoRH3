"""
THE OBJECT: takes in numbers, builds phasors, measures where they cancel.

  - numbers       : integers n the fiber crosses
  - prime phasors : each interesting prime p gets a phase theta_p (its climb coord) and a
                    channel chi3(p) = +1 (POS) / -1 (NEG) / 0 (killed)
  - FTA winding   : the number n's phase is BUILT from its primes, additively
                       phi(n) = sum_{p^a || n} a * theta_p        (Theta(mn)=Theta(m)+Theta(n))
                    -> with theta_p = climb coord, phi(n) is the number's own climb coord
  - the fiber     : F(t) = sum_n chi3(n) * |amp_n| * e^{ i t phi(n) }   (the + and - channels,
                    conjugate spins, accumulated as the fiber rides to climb-height t)
  - measure       : where |F(t)| cancels (the phasors meet at 0)

No zeta in the signal. mpmath only at the very end as an external ruler.
"""
import numpy as np

X = 200_000
# smallest-prime-factor sieve (for the FTA recurrence)
spf = np.zeros(X + 1, dtype=np.int64)
for i in range(2, X + 1):
    if spf[i] == 0:
        spf[i::i] = np.where(spf[i::i] == 0, i, spf[i::i])

n = np.arange(0, X + 1)
# chi3 (mod 3): the pos/neg channel bucketing of the *primes* propagates multiplicatively
chi3 = np.where(n % 3 == 1, 1.0, np.where(n % 3 == 2, -1.0, 0.0))

# prime phase = climb coordinate of the prime.  Built so the FTA winding gives the number's
# climb coord.  (theta_p = log p is the exp-carrier's climb coordinate of prime p.)
theta_p = np.zeros(X + 1)
theta_p[2:] = np.log(np.arange(2, X + 1))          # only used at primes below

# FTA-ADDITIVE winding: phi(n) = phi(n/p) + theta_p,  p = spf(n).   Build the number's phase
# from its prime phases -- the log-free multiplication->addition law.
phi = np.zeros(X + 1)
for m in range(2, X + 1):
    p = spf[m]
    phi[m] = phi[m // p] + theta_p[p]              # theta_p[p] = log p

# check the FTA winding really reconstructs the number's climb coord (phi(n) == log n)
err = np.max(np.abs(phi[2:] - np.log(np.arange(2, X + 1))))
print(f"FTA winding check:  max |phi(n) - log n| over n<= {X} = {err:.2e}")
print(f"  (phi BUILT additively from prime phases; equals the number's own climb coord)\n")

# THE FIBER: accumulate the integer phasors (chi3 sorts primes->channels multiplicatively)
idx = np.arange(1, X + 1)
chi = chi3[1:]
amp = chi * idx ** (-0.5) * np.exp(-(idx / X) ** 2)    # |amp| = n^{-1/2}, smooth taper
ph = phi[1:]

def fiber_abs(ts):
    out = np.empty(len(ts))
    A = amp.astype(complex)
    for i in range(0, len(ts), 200):
        M = np.exp(1j * np.outer(ts[i:i+200], ph))
        out[i:i+200] = np.abs(M @ A)
    return out

ts = np.linspace(2.0, 40.0, 9000)
F = fiber_abs(ts)
base = np.median(F)
# cancellation events = deep local minima of |F|
mins = ts[1:-1][(F[1:-1] < F[:-2]) & (F[1:-1] < F[2:]) & (F[1:-1] < 0.35 * base)]
print("WHERE THE PHASORS CANCEL  (deep minima of |F(t)|):")
print("  ", [round(float(x), 2) for x in mins[:14]])

# external ruler ONLY (not used to build anything): the chi3 L-zeros
chi3_zeros = [8.04, 11.25, 15.70, 18.26, 20.46, 24.06, 26.58, 28.22, 30.42, 32.4]
print("\n  external ruler — known chi3 L-zeros:")
print("  ", chi3_zeros)
print("\n  (the object's cancellations, built from numbers+prime phasors, vs the ruler)")
