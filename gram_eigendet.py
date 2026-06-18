"""
Eigenvalue determinant — eigenvalues = phasor absolute values.

B = phasor synthesis: column n is  v_n(y) = n^(-1/2)·e^(-i y log n),  |v_n| = n^(-1/2).
Normalized inner product (1/T)∫_0^T, so ‖v_n‖ = n^(-1/2) = the phasor magnitude.

The eigenvalues that EQUAL the phasor absolute values are the eigenvalues of the
von Neumann modulus  |B| = (B*B)^(1/2)  = the singular values of B  ( = √ of the B*B
eigenvalues).  B*B gives the squares; |B| gives the magnitudes.

We diagonalize |B| and show its spectrum is exactly {n^(-1/2)} = {1, 1/√2, 1/√3, …},
the shrinking phasor magnitudes, and give the eigenvalue determinant det(zI - |B|).
"""

import numpy as np

N = 60
T = 800.0
M = 24000
y = np.linspace(0.0, T, M)
n = np.arange(1, N + 1)

# normalized synthesis operator (so column norms are exactly the phasor magnitudes)
B = (n[None, :] ** (-0.5)) * np.exp(-1j * np.outer(y, np.log(n))) / np.sqrt(M)

# eigenvalues of |B| = (B*B)^(1/2)  ==  singular values of B  ==  phasor magnitudes
sv = np.sort(np.linalg.svd(B, compute_uv=False))[::-1]
mag = n.astype(float) ** (-0.5)

print("=" * 64)
print("eigenvalues of |B| = (B*B)^(1/2)   vs   phasor abs value n^(-1/2)")
print("=" * 64)
print(f"{'n':>3} {'eigenvalue σ_n':>16} {'|phasor| n^(-1/2)':>20} {'|Δ|':>10}")
for i in range(min(16, N)):
    print(f"{i+1:>3} {sv[i]:>16.6f} {mag[i]:>20.6f} {abs(sv[i]-mag[i]):>10.2e}")

print(f"\nmax |σ_n − n^(-1/2)| over all {N} modes: {np.max(np.abs(sv - mag)):.2e}")
print(f"eigenvalues shrink toward 0:  σ_1={sv[0]:.4f}  σ_10={sv[9]:.4f}  σ_60={sv[-1]:.4f}")

# eigenvalue determinant  det(zI - |B|) = Π (z - σ_n)
print("\neigenvalue determinant  det(zI - |B|) = Π_n (z - σ_n):")
for z in [2.0, 1.0, 0.5, 0.0]:
    logabsdet = np.sum(np.log(np.abs(z - sv)))
    print(f"  z = {z:>4}:  log|det| = {logabsdet:>9.4f}")
