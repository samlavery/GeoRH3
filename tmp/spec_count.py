"""
SPECTRAL COUNTING MECHANISM on real L-function zeros  (Sam's chain, honest build).

Chain (verbatim):
  height H -> accumulated source subspace H_F(H) -> Gram/block operator A_H
           -> new RESOLVABLE singular/harmonic mode -> emitted height increment -> cumulative gamma_n.

SOURCE ATOMS (the ONLY place chi enters):
  prime powers q = p^k up to cutoff Xc.  Atom carries:
    frequency  u = log(q)                          (FTA-additive winding spectrum: log(p^k)=k log p)
    weight     w = chi(q) * Lambda(q) / q^{1/2}    (von Mangoldt loss energy, on-line p^{-1/2}, chi-twisted)
  The accumulated SOURCE FIELD along the climb at height t:
    F(t) = sum_atoms w * cos(u * t)        (real source / loss field; = -Re sum Lambda chi q^{-1/2-it})
  Its oscillation FREQUENCIES in t are exactly the imaginary parts of the L-zeros (explicit formula);
  a NEW RESOLVABLE MODE as the climb window grows to H = a new resolved frequency = a new gamma_n.

LOSS / GRAM OPERATOR  A_H  (Implementation 1 -- the B(H) the prompt names):
  Sample F on a uniform height grid t in [0,H].  Form the HANKEL (data/loss) matrix of that signal;
  its Gram A_H = Hankel^T Hankel.  The number of singular values of A_H above a resolution threshold
  = number of distinct oscillation modes resolved in [0,H] = cumulative mode-count N(H).
  This is a Gram/block operator of the accumulated source subspace H_F(H) (rows = shifted windows of F),
  exactly "the loss matrix using all source atoms up to accumulated height H".  As H grows, the Hankel
  acquires a NEW resolvable singular mode each time the window is long enough to separate one more
  closely-spaced frequency -- those crossing-heights are the emitted gamma_n (poles of the resolvent).

PITCH FEEDBACK (the key test):
  BASE: constant pitch -- uniform t-grid, dt fixed; window grows linearly with H.
  FEEDBACK: each time a NEW mode is acquired (threshold crossing), pitch -> pitch + delta, i.e. the
  height-per-grid-step changes, so the resolution/height for the next mode self-consistently shifts.
  We FIT delta to best match the (un-fed) zeros' log density and report its sign.

CHARACTER-AGNOSTIC: identical code, ONLY chi changed.  trivial -> zeta; chi mod 3 / mod 4 -> Dirichlet L.
Reference zeros NEVER enter the construction.  numpy float64 everywhere.
"""
import sys, math
import numpy as np

def pr(*a): print(*a); sys.stdout.flush()

# ---------------------------------------------------------------------------
# SOURCE ATOMS
# ---------------------------------------------------------------------------
def prime_powers(Xc):
    sieve = np.ones(Xc+1, bool); sieve[:2] = False
    for i in range(2, int(Xc**0.5)+1):
        if sieve[i]: sieve[i*i::i] = False
    primes = np.nonzero(sieve)[0].tolist()
    out = []
    for p in primes:
        pk = p; k = 1
        while pk <= Xc:
            out.append((p, k, pk)); pk *= p; k += 1
    return out

def atoms(Xc, chi):
    """u = log(p^k), w = chi(p^k) * log(p) / (p^k)^{1/2}.  chi=0 atoms dropped."""
    U, W = [], []
    for (p, k, pk) in prime_powers(Xc):
        c = chi(pk)
        if c == 0:
            continue
        U.append(math.log(pk))
        W.append(c * math.log(p) / math.sqrt(pk))
    return np.array(U, np.float64), np.array(W, np.float64)

# ---------------------------------------------------------------------------
# SOURCE FIELD along the climb
# ---------------------------------------------------------------------------
def field(U, W, t):
    """F(t) = sum_i w_i cos(u_i t).  t: array of heights."""
    # t outer u : shape (len(t), M) -- keep modest
    return (np.cos(np.outer(t, U)) * W[None, :]).sum(axis=1)

# ---------------------------------------------------------------------------
# LOSS / GRAM (HANKEL) OPERATOR and NEW-MODE COUNTING
# ---------------------------------------------------------------------------
def hankel_svals(sig, L):
    """Singular values of the Hankel matrix of signal sig with L columns (window length)."""
    n = len(sig)
    rows = n - L + 1
    if rows < 2 or L < 2:
        return np.array([0.0])
    H = np.lib.stride_tricks.sliding_window_view(sig, L)   # (rows, L) Hankel
    return np.linalg.svdvals(H)

def mode_count(sig, L, thresh):
    sv = hankel_svals(sig, L)
    if sv[0] <= 0:
        return 0, sv
    return int(np.sum(sv / sv[0] > thresh)), sv   # relative threshold (geometry-level constant)

# ---------------------------------------------------------------------------
# matrix-pencil READOUT of the actual emitted frequencies (gamma_n) from the
# accumulated subspace.  This is the "principal-part field" pole readout: the
# poles of the resolvent built on H_F(H).  No reference zeros used.
# ---------------------------------------------------------------------------
def pencil_freqs(sig, dt, order):
    """Frequencies (rad/height) of sig via matrix-pencil on the Hankel subspace."""
    n = len(sig); L = n // 2
    H = np.lib.stride_tricks.sliding_window_view(sig, L + 1)
    _, _, Vh = np.linalg.svd(H, full_matrices=False)
    V = Vh.conj().T[:, :order]
    ev = np.linalg.eigvals(np.linalg.pinv(V[:-1]) @ V[1:])
    z = np.log(ev.astype(complex)) / dt
    return z   # imag = frequency = gamma, real = damping (should ~0 on line)
