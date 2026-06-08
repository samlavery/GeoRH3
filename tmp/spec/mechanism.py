"""
THE MECHANISM (Sam, verbatim build):
  B(H) = loss matrix using all source atoms up to accumulated height H.
  Emit at H when B(H) acquires a NEW RESOLVABLE SINGULAR / HARMONIC MODE.
  gamma_n is a COUNTING FUNCTION N(H).

Source atoms: prime powers q=p^k up to a cutoff.
  frequency  om_i = log(p^k)
  weight     w_i  = chi(p^k) * Lambda(p^k) / (p^k)^{1/2}  = chi * log(p) / p^{k/2}

Finite-height Gram (windowed almost-periodic correlation over tau in [0,H]):
  B_ij(H) = w_i w_j * D_H(om_i - om_j),  D_H(Delta) = (1/H) int_0^H e^{i Delta tau} dtau
          = w_i w_j * sinc-type kernel; for i=j, D_H=1.
This is the natural windowed Gram of the atom frequencies.

Detect NEW RESOLVABLE SINGULAR MODE: as H grows the off-diagonal coupling
D_H(Delta) -> 0 like 1/(Delta H), so frequencies separated by > ~1/H become
resolved. A new singular value of B(H) emerges above the resolution floor each
time the window is long enough to resolve another pair/cluster. We count
singular values of B(H) above a fixed relative threshold; each NEW one is an
emitted mode.

PITCH LAW:
  BASE:     height advances by constant pitch each step.
  FEEDBACK: each threshold crossing sets pitch -> pitch + delta.
The emitted heights at which a new resolvable mode appears = gamma_n.

numpy float64 only.  M = #atoms <= few hundred.
"""
import numpy as np

# ---------- source atoms ----------
def primes_upto(n):
    sieve = np.ones(n+1, dtype=bool)
    sieve[:2] = False
    for p in range(2, int(n**0.5)+1):
        if sieve[p]:
            sieve[p*p::p] = False
    return np.nonzero(sieve)[0]

def source_atoms(chi, q_char, prime_cutoff):
    """Return (freqs, weights) for prime powers p^k <= prime_cutoff.
    chi: function a->value (mod q_char). For trivial (zeta) chi(a)=1 for gcd(a,1)=1 -> always 1.
    """
    ps = primes_upto(prime_cutoff)
    freqs = []
    weights = []
    for p in ps:
        pk = p
        k = 1
        while pk <= prime_cutoff:
            c = chi(int(pk))            # chi(p^k)
            if c != 0:
                w = c * np.log(p) / np.sqrt(pk)   # chi * Lambda(p^k)/sqrt(p^k)
                freqs.append(np.log(pk))
                weights.append(w)
            pk *= p
            k += 1
    return np.array(freqs, dtype=np.float64), np.array(weights, dtype=np.float64)

# ---------- finite-height Gram ----------
def gram(freqs, weights, H):
    """B_ij(H) = w_i w_j * D_H(om_i - om_j), D_H windowed correlation over [0,H].
    D_H(Delta) = (e^{i Delta H} - 1)/(i Delta H); D_H(0)=1.  Real symmetric variant:
    use real part (cosine windowed correlation) -> symmetric PSD-ish Gram.
    """
    M = len(freqs)
    d = freqs[:, None] - freqs[None, :]          # MxM
    x = d * H
    # D_H real part = sin(x)/x  (Fejer/sinc); handle x=0
    with np.errstate(invalid='ignore', divide='ignore'):
        sinc = np.where(np.abs(x) < 1e-12, 1.0, np.sin(x)/np.where(x==0,1.0,x))
    W = np.outer(weights, weights)
    B = W * sinc
    return B

# ---------- mode counting ----------
def resolvable_modes(B, thresh_rel):
    """Number of singular values of B above thresh_rel * (max sv)."""
    s = np.linalg.svdvals(B)
    if s[0] <= 0:
        return 0, s
    return int(np.sum(s >= thresh_rel * s[0])), s

# ---------- the height sweep with pitch law ----------
def run_mechanism(chi, q_char, prime_cutoff, thresh_rel,
                  H0=0.5, pitch0=0.05, delta=0.0, Hmax=60.0,
                  max_emit=45):
    """Sweep H upward with pitch law. Emit gamma when mode count increases.
    BASE: delta=0 (constant pitch). FEEDBACK: delta!=0 (pitch+=delta per emission).
    Returns list of emitted heights (gamma_n) and the running mode count.
    """
    freqs, weights = source_atoms(chi, q_char, prime_cutoff)
    H = H0
    pitch = pitch0
    prev_count = 0
    emitted = []
    counts = []
    while H <= Hmax and len(emitted) < max_emit:
        B = gram(freqs, weights, H)
        cnt, _ = resolvable_modes(B, thresh_rel)
        if cnt > prev_count:
            # one or more new resolvable modes appeared at this H
            for _ in range(cnt - prev_count):
                emitted.append(H)
            prev_count = cnt
            # FEEDBACK: each threshold crossing alters pitch
            pitch = pitch + delta
        counts.append((H, cnt))
        H += pitch
    return np.array(emitted), counts, (freqs, weights)

if __name__ == "__main__":
    # quick smoke test on zeta
    chi_triv = lambda a: 1
    em, counts, fw = run_mechanism(chi_triv, 1, prime_cutoff=200,
                                   thresh_rel=0.02, H0=0.5, pitch0=0.1,
                                   delta=0.0, Hmax=40.0, max_emit=30)
    print("num atoms:", len(fw[0]))
    print("emitted (base):", np.round(em[:15], 3))
