"""
Crossing heights as e^{iγ}, from the full fiber sum — and the (2-D) eigenvalues.

Full fiber sum (all phasors of the fiber, accumulated from y=0, not segment-by-segment):
    F(y) = Σ_n n^{-(1/2 + i y)}  =  ζ(1/2 + i y).
Its vanishings (crossings) are the heights γ_k.

The eigenvalue is NOT 1-D: each crossing is marked at  e^{iγ_k}  — a point on the unit
circle (|e^{iγ}| = 1, the ‖w‖=1 readout).  The height γ_k is the argument; the eigenvalue
is the 2-D point e^{iγ_k}.  Spectrum on the circle => the operator is UNITARY (U = e^{iH}).

We give the crossings, their e^{iγ_k} eigenvalues, and the eigenvalue determinant
    det(zI - U) = Π_k (z - e^{iγ_k}).
"""

import mpmath as mp

mp.mp.dps = 25

M = 12
gamma = [mp.im(mp.zetazero(k)) for k in range(1, M + 1)]

print("=" * 70)
print("FULL FIBER SUM  F(y) = Σ_n n^{-(1/2+iy)} = ζ(1/2+iy)  — vanishes at the crossings")
print("=" * 70)
print("(accumulated from y=0 over all phasors; |F| dips to 0 at each crossing γ_k)")
ys = [2, 8, 14.1347, 18, 21.0220, 24, 25.0109]
for y in ys:
    v = mp.zeta(mp.mpf(1) / 2 + 1j * mp.mpf(y))
    tag = "  <-- crossing" if abs(v) < 1e-3 else ""
    print(f"   y={y:>9}:  |F(y)| = {float(abs(v)):.5f}{tag}")

print("\n" + "=" * 70)
print("CROSSING HEIGHTS  γ_k  AS  e^{iγ_k}   (the 2-D eigenvalue, on the unit circle)")
print("=" * 70)
print(f"{'k':>3} {'γ_k (height/arg)':>18} {'e^{iγ_k}  (eigenvalue, 2-D)':>34} {'|·|':>8}")
eig = []
for k, g in enumerate(gamma, 1):
    w = mp.e ** (1j * g)
    eig.append(w)
    print(f"{k:>3} {float(g):>18.5f}    {complex(w).real:+.5f} {complex(w).imag:+.5f}i   {float(abs(w)):>7.4f}")

print("\n   every eigenvalue has |e^{iγ}| = 1  ->  spectrum lies on the unit circle (2-D),")
print("   NOT on the real line.  height γ = arg(eigenvalue);  eigenvalue = the point e^{iγ}.")

print("\n" + "=" * 70)
print("EIGENVALUE DETERMINANT   det(zI - U) = Π_k (z - e^{iγ_k})   (U unitary)")
print("=" * 70)
for z in [mp.mpc(0), mp.mpc(1), mp.mpc(0.5), mp.e ** (1j * mp.mpf("0.3"))]:
    D = mp.fprod([z - w for w in eig])
    print(f"   z = {complex(z):>16.4f}:   det = {complex(D):+.4f}   |det| = {float(abs(D)):.4f}")

# resolvent trace of the unitary spectrum
print("\n   resolvent trace Tr((zI-U)^-1) = Σ_k 1/(z - e^{iγ_k}):")
for z in [mp.mpc(0), mp.mpc(2)]:
    R = mp.fsum([1 / (z - w) for w in eig])
    print(f"     z={complex(z):.2f}:  {complex(R):+.4f}")
