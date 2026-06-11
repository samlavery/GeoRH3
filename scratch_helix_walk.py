"""
Walk up the helix. Collect primes by the mod-6 fiber:  + for p=1 mod6, - for p=5 mod6.
Running signed sum S. Spit out every HEIGHT z where S = 0 exactly (the buckets balance).
"""
import numpy as np

N = 10_000_000
sieve = np.ones(N+1, bool); sieve[:2] = False
for i in range(2, int(N**0.5)+1):
    if sieve[i]: sieve[i*i::i] = False
primes = np.nonzero(sieve)[0]

chi = np.where(primes % 6 == 1, 1, np.where(primes % 6 == 5, -1, 0))   # +1 / -1 / 0(=2,3)
S = np.cumsum(chi)                                                     # running bucket balance

# heights z(n) on the helix, by arc length s(Phi)=n*pi/3  (same build as before)
e6 = np.exp(6.0); U = np.pi/3; A = e6/(4*np.pi)
Phi_grid = np.linspace(0.0, 620.0, 6_000_000)
s_grid = A*(Phi_grid*np.sqrt(Phi_grid**2 + 1) + np.arcsinh(Phi_grid))
def height(nv):
    Phi = np.interp(np.asarray(nv, float)*U, s_grid, Phi_grid)
    return U * (Phi/(2*np.pi))           # z = (pi/3) * k

# ties: running sum exactly zero (exclude the trivial p=2,3 start where chi=0)
tie = primes[(S == 0) & (primes >= 5)]
z = height(tie)

print(f"primes up to {N}: {len(primes)};  balance points (S=0): {len(tie)}\n")
print("first balance heights (tie prime  ->  height z  [loop k]):")
for p, zz in list(zip(tie, z))[:40]:
    print(f"   p={p:9d}   z={zz:10.5f}   k={zz/U:8.4f}")

print("\nlast few balance heights:")
for p, zz in list(zip(tie, z))[-8:]:
    print(f"   p={p:9d}   z={zz:10.5f}   k={zz/U:8.4f}")

# structure: gaps between consecutive balance heights
if len(z) > 3:
    dz = np.diff(z)
    print(f"\nheight range: {z.min():.4f} .. {z.max():.4f}")
    print(f"consecutive-gap stats:  mean {dz.mean():.4f}  median {np.median(dz):.4f}  min {dz.min():.4f}  max {dz.max():.4f}")
    print(f"z vs sqrt(tie prime): z/sqrt(p) mean = {np.mean(z/np.sqrt(tie)):.5f} (const => z∝√p)")
