"""
MECHANISM v2 -- corrected axis.

The zeros gamma_n are the t-FREQUENCIES present in the prime-power loss signal
  F(t) = -Re d/ds log L (1/2+it)   restricted to prime powers
       = sum_i w_i cos(t * om_i)         (om_i = log p^k, w_i = chi*Lambda/sqrt)
By the explicit formula the oscillations of the prime side are carried by the
zeros: the autocorrelation spectrum of F(t) over [0,H] peaks at the zero
ordinates' DIFFERENCES, and the principal-part / resolvent of the windowed
covariance acquires a new pole each time a new zero-frequency becomes resolvable.

We realize Sam's "loss-Gram acquires a new resolvable singular mode" as a
SUBSPACE / covariance construction in t:
  - Sample F(t) on a t-grid up to accumulated height H.
  - Build the lag-covariance (Toeplitz) matrix B(H) of the windowed signal.
  - Its eigen/singular spectrum's resolvable modes = resolvable t-frequencies.
  - A NEW resolvable mode appears at the H where the window first resolves
    the next zero-frequency: emit that H as gamma.

This keeps the SAME atoms (chi-twisted prime powers, p^-1/2 weight, FTA winding)
and the SAME "count new resolvable singular modes of the accumulated loss
operator" rule -- only the operator is built on the correct (t) axis.

PITCH:
  BASE: t-grid step constant.
  FEEDBACK: each emission alters the grid pitch (pitch += delta).
numpy float64 only.
"""
import numpy as np

def primes_upto(n):
    sieve = np.ones(n+1, dtype=bool); sieve[:2]=False
    for p in range(2,int(n**0.5)+1):
        if sieve[p]: sieve[p*p::p]=False
    return np.nonzero(sieve)[0]

def source_atoms(chi, prime_cutoff):
    ps = primes_upto(prime_cutoff)
    freqs=[]; weights=[]
    for p in ps:
        pk=p
        while pk<=prime_cutoff:
            c=chi(int(pk))
            if c!=0:
                freqs.append(np.log(pk))
                weights.append(c*np.log(p)/np.sqrt(pk))
            pk*=p
    return np.array(freqs), np.array(weights)

def loss_signal(freqs, weights, t):
    # F(t) = sum_i w_i cos(t om_i)  (real loss signal on the line)
    return (weights[None,:]*np.cos(np.outer(t,freqs))).sum(axis=1)

# ---- lag-covariance (Toeplitz) of the windowed loss signal ----
def lag_cov(freqs, weights, H, nlag=64, npts=4000):
    """Build B(H): the lag-covariance matrix of F(t) over t in [0,H].
    B[j,l] = (1/N) sum_t F(t_j-shift) ... realized as autocovariance r(|j-l|).
    Toeplitz from autocovariance r(tau) = <F(t)F(t+tau)>_[0,H].
    The eigen-spectrum of this Toeplitz matrix resolves the t-frequencies in F,
    which by the explicit formula are the zero ordinates.
    """
    t = np.linspace(0.0, H, npts)
    dt = t[1]-t[0]
    F = loss_signal(freqs, weights, t)
    F = F - F.mean()
    # autocovariance up to nlag via FFT
    n = len(F)
    nfft = 1
    while nfft < 2*n: nfft<<=1
    Fp = np.zeros(nfft); Fp[:n]=F
    S = np.fft.rfft(Fp)
    ac = np.fft.irfft(S*np.conj(S))[:nlag]
    ac = ac/ (np.arange(n,n-nlag,-1))   # unbiased-ish normalization
    # Toeplitz
    from scipy.linalg import toeplitz
    B = toeplitz(ac)
    return B, ac

def resolvable_modes(B, thresh_rel):
    s = np.linalg.eigvalsh(B)[::-1]   # descending, symmetric
    s = np.clip(s, 0, None)
    if s[0] <= 0: return 0, s
    return int(np.sum(s >= thresh_rel*s[0])), s
