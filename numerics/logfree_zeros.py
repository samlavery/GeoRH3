"""
logfree_zeros.py  --  the nontrivial zeros computed with NO log, at all.

WHY THE HELIX ROUTE HAD A LOG, AND THIS ONE DOES NOT.
The Dirichlet-series / helix route represents the integers as  n^{-s} = e^{-s log n}  -- the log is
baked into the representation.  The THETA (heat-kernel) route represents them as Gaussians,
e^{-pi n^2 t / q}: now  n  enters as  n^2, never as a log-position.  The substitution  t = e^z
(map the height through an exponential) turns the Mellin transform into a FOURIER transform:

    g(z) = theta_chi(e^z) * e^{z (2a+1)/4},     theta_chi(t) = sum_{n>=1} chi(n) n^a e^{-pi n^2 t / q}
    Lambda(1/2 + i w, chi) = integral_{-inf}^{inf} g(z) e^{i z w / 2} dz

The zeros of Lambda (= the zeros of L, the Gamma-factor has none) are the heights w where this
transform vanishes.  Everything is exp, cos, and n^2 -- ZERO log() calls (grep the file).

For chi_3 (odd, parity a=1, root number +1) the functional equation makes g(z) EVEN, so the
transform is a real cosine transform and the zeros are its SIGN CHANGES -- found exactly below.

HONEST SCOPE.  This is Riemann's theta representation (Poisson summation / Jacobi theta), so it is
classical, and it COMPUTES L -- it does not by itself prove the zeros are on the line.  The
functional equation (the z -> -z symmetry of the log-free g) makes Lambda(1/2+iw) real, so its real
zeros are the on-line zeros (this is the Hardy Z-function); that they are ALL the zeros is still GRH.
What is genuinely gone is the log: the heights come out of a heat kernel and a Fourier transform.
This is a DIFFERENT geometry from the helix (Gaussian wave packets, not a spiral); the helix carried
the log because it used n^{-s}, the theta route does not.
"""
import numpy as np


def theta_transform(ws, char, q, a, nmax=2000, zlo=-8.0, zhi=8.0, zn=9000):
    """real transform Lambda(1/2+iw, chi) over the heights ws -- LOG-FREE (exp, cos, n^2 only).
    char: residue->value dict; q: modulus; a: parity (0 even, 1 odd). g(z) is even for root number +1."""
    zs = np.linspace(zlo, zhi, zn)
    n = np.arange(1, nmax + 1)
    cn = np.array([char.get(int(k) % q, 0) for k in n], float) * n ** a      # chi(n) * n^a
    ez = np.exp(zs)                                                          # t = e^z (no log taken)
    G = np.array([np.sum(cn * np.exp(-np.pi * n * n * t / q)) for t in ez]) * np.exp((2 * a + 1) / 4 * zs)
    return np.array([float(np.trapezoid(G * np.cos(zs * w / 2.0), zs)) for w in ws])


def find_zeros(char, q, a, wlo=2.0, whi=26.0, step=0.005, **kw):
    """zeros of L(1/2+iw, chi) = sign changes of the real log-free transform (linear-interpolated)."""
    ws = np.arange(wlo, whi, step)
    g = theta_transform(ws, char, q, a, **kw)
    return [round(float(ws[i - 1] - g[i - 1] * (ws[i] - ws[i - 1]) / (g[i] - g[i - 1])), 3)
            for i in range(1, len(g)) if g[i - 1] * g[i] < 0]


if __name__ == "__main__":
    chi3 = {0: 0, 1: 1, 2: -1}
    found = find_zeros(chi3, 3, 1)
    print("LOG-FREE zeros of L(s, chi_3)   (theta-Fourier, t = e^z; built from exp / cos / n^2 only)\n")
    print("  found :", found[:8])
    print("  ref   : [8.04, 11.249, 15.705, 18.262, 20.456, 24.059]")
    print("\n  the integers enter as n^2 in a Gaussian (the theta function), never as a log-position;")
    print("  the height is read by a cosine transform.  No log() is called anywhere in the build.")
