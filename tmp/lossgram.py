"""
LOSS-GRAM SINGULAR-MODE COUNTING MECHANISM  (Sam's chain, verbatim build).

Chain:
  height H -> accumulated source subspace H_F(H) -> Gram/block operator B(H)
           -> new resolvable singular mode -> emitted height increment -> cumulative gamma_n.

Source atoms: prime powers q=p^k up to a cutoff. Atom i has:
  - frequency  u_i = k*log(p)         (position in the FTA-additive winding spectrum)
  - weight     w_i = chi(p^k) * log(p) / p^{k/2}   (on-line p^-1/2 radial loss weight, twisted by chi)

B(H): the FINITE-HEIGHT (windowed) Gram of the atom oscillators e^{i u_i t} correlated over t in [0,H]:
  (1/H) int_0^H cos(u_i t) cos(u_j t) dt  ~  (1/2)[ sinc((u_i-u_j)H) + sinc((u_i+u_j)H) ]
  B_ij(H) = w_i w_j * 0.5*( sinc((u_i-u_j)*H/pi) + sinc((u_i+u_j)*H/pi) )
  (numpy.sinc(x)=sin(pi x)/(pi x), so sinc(z/pi) gives sin(z)/z.)

A NEW RESOLVABLE SINGULAR MODE = a singular value of B(H) crossing a fixed resolution threshold
as H grows. The rank of B(H) above threshold is the cumulative mode-count N(H). Each upward
crossing emits a height increment; the H at which the k-th mode crosses is the emitted gamma_k.

ONLY geometry-level constants are tuned (resolution threshold, cutoff). The SAME code runs for
zeta (chi trivial) and Dirichlet chi (only chi changed). Reference zeros NEVER enter here.

numpy float64 throughout; M = #atoms <= few hundred; Gram MxM cheap SVD.
"""
import sys, math
import numpy as np

def pr(*a): print(*a); sys.stdout.flush()

# ---------------------------------------------------------------------------
# SOURCE ATOMS  (the only place chi enters)
# ---------------------------------------------------------------------------
def prime_powers(Xc):
    """Return list of (p, k, p^k) for all prime powers p^k <= Xc."""
    sieve = np.ones(Xc+1, bool); sieve[:2] = False
    for i in range(2, int(Xc**0.5)+1):
        if sieve[i]: sieve[i*i::i] = False
    primes = np.nonzero(sieve)[0]
    out = []
    for p in primes.tolist():
        pk = p; k = 1
        while pk <= Xc:
            out.append((p, k, pk)); pk *= p; k += 1
    return out

def atoms(Xc, chi):
    """Atom frequencies u_i = k log p and weights w_i = chi(p^k) log p / p^{k/2}.
    chi(n): trivial -> 1 for all n; Dirichlet -> chi(n mod q). Atoms with chi=0 dropped."""
    U, W = [], []
    for (p, k, pk) in prime_powers(Xc):
        c = chi(pk)
        if c == 0:
            continue
        U.append(k*math.log(p))
        W.append(c * math.log(p) / pk**0.5)
    return np.array(U, np.float64), np.array(W, np.float64)

# ---------------------------------------------------------------------------
# FINITE-HEIGHT GRAM  B(H)
# ---------------------------------------------------------------------------
def sinc(z):
    # sin(z)/z, safe at 0
    return np.sinc(z/np.pi)

def gram(U, W, H):
    """B_ij(H) = w_i w_j * 0.5*( sinc((u_i-u_j)H) + sinc((u_i+u_j)H) )."""
    diff = U[:,None] - U[None,:]
    summ = U[:,None] + U[None,:]
    corr = 0.5*(sinc(diff*H) + sinc(summ*H))
    return (W[:,None]*W[None,:]) * corr

# ---------------------------------------------------------------------------
# MODE COUNTING:  N(H) = # singular values of B(H) above resolution threshold
# ---------------------------------------------------------------------------
def mode_count(U, W, H, thresh):
    B = gram(U, W, H)
    sv = np.linalg.svdvals(B)
    return int(np.sum(sv > thresh)), sv

def sweep(U, W, Hgrid, thresh):
    """Cumulative mode-count N(H) over an H grid, and emitted heights (upward crossings)."""
    counts = np.empty(len(Hgrid), int)
    for i, H in enumerate(Hgrid):
        counts[i], _ = mode_count(U, W, H, thresh)
    # emitted heights: H at which count increments
    emitted = []
    for i in range(1, len(Hgrid)):
        for _ in range(max(0, counts[i] - counts[i-1])):
            # linear: assign the crossing to the grid point
            emitted.append(Hgrid[i])
    return counts, np.array(emitted)
