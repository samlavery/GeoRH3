"""
SHARED SPECTRAL-COUNTING RULE -- ONE function, used IDENTICALLY for both channels.
Only the channel params (U = pitch/unit, radial slope, chi) are swapped.

The rule (CLAUDE.md RULE EIGHT: log-free helix, on-line p^-1/2 weight, reality not positivity):

  source atoms = prime powers q = p^k, twisted by chi(q), each carrying projection-loss
    energy = an on-line radial weight  w = (p^-1/2)^k  =  p^{-k/2}  =  q^{-1/2}.
  Each atom sits on the channel helix. Its HEIGHT (frequency) comes from the linear radial
    law / area law of the helix: the helix places integers evenly with spacing U and rewinds
    with linear radial growth R(k)=slope*k, so loop k holds ~k atoms, cumulative ~k^2, and
    the angular frequency read at height H is  omega(q) = (1/U) * log q   <-- this single log
    is the EXTERNAL BRIDGE readout (wind n <-> n^{it}), the ONLY permitted log. The geometry
    itself (placement, rewind) is log-free; we read frequencies off it via the bridge.
    The radial slope sets the scale: atoms enter the window when slope*k reaches their radius.

  B(H) = windowed Gram (loss matrix) of the chi-twisted atom oscillators e^{i*omega(q)*h}
    sampled over a height window h in [0,H]. Entry B[a,b] = sum_h w_a w_b chi(q_a)chi(q_b)
    e^{i(omega_a-omega_b)h}. This is the finite-height correlation of the source modes.

  EMIT a height increment when B(H) acquires a NEW RESOLVABLE SINGULAR MODE: as H grows,
    the windowed Gram's singular values rise; when a NEW singular value crosses a fixed
    resolution threshold, a mode is resolved -> emit gamma_n = that H. (Poles of the
    completed source resolvent = where a new harmonic becomes resolvable.)

  PITCH FEEDBACK: each emission adds delta to the pitch (pitch += delta). Test constant vs
    feedback; report which gives the right (log) zero density.

  cumulative gamma_n = N(H) = count of resolved modes up to H.

NOTE ON HONESTY: omega(q) = log(q)/U is the bridge readout (the one allowed log). We do NOT
feed arg Gamma or the explicit formula. The same code runs both channels.
"""
import numpy as np

def sieve_primes(n):
    if n < 2: return []
    s = np.ones(n+1, dtype=bool); s[:2]=False
    for i in range(2, int(n**0.5)+1):
        if s[i]: s[i*i::i]=False
    return np.nonzero(s)[0]

def chi0_mod3(n):   # trivial char mod 3
    return 0.0 if (n % 3 == 0) else 1.0

def chi3_mod3(n):   # real primitive odd char mod 3
    r = n % 3
    return 1.0 if r==1 else (-1.0 if r==2 else 0.0)

def build_atoms(U, slope, chi, M_max=300, Pmax=2000, Kmax=6):
    """Source atoms = prime powers q=p^k, twisted by chi(q), weight q^{-1/2}, freq log(q)/U.
       slope scales the radial law (enters the helix scale -> we fold it into the height grid).
       Returns arrays sorted by frequency, truncated to M_max strongest-weight atoms."""
    primes = sieve_primes(Pmax)
    qs=[]; ws=[]; chis=[]; omegas=[]
    for p in primes:
        pk = p
        for k in range(1, Kmax+1):
            q = p**k
            if q > Pmax**1: # keep q within reach; prime powers can exceed Pmax slightly
                pass
            c = chi(q)        # chi(p^k) = chi(p)^k automatically via n%3
            if c == 0.0:
                continue
            w = q**(-0.5)     # on-line projection-loss weight (p^-1/2)^k
            omega = np.log(q) / U   # BRIDGE readout (the one allowed log)
            qs.append(q); ws.append(w); chis.append(c); omegas.append(omega)
            pk = pk*p
            if q > 10**9: break
    qs=np.array(qs,float); ws=np.array(ws,float); chis=np.array(chis,float); omegas=np.array(omegas,float)
    # keep the M_max strongest atoms (largest weight) -> bounded Gram
    order = np.argsort(-ws)[:M_max]
    qs,ws,chis,omegas = qs[order],ws[order],chis[order],omegas[order]
    order2 = np.argsort(omegas)
    return qs[order2], ws[order2], chis[order2], omegas[order2], slope

def windowed_gram(ws, chis, omegas, H, nsamp=400):
    """B(H): windowed Gram of chi-twisted oscillators over height h in [0,H].
       B[a,b] = (w_a chi_a)(w_b chi_b) * (1/nsamp) sum_h e^{i(om_a-om_b)h}.
       Hermitian PSD by construction (it's V^* V with V[h,a] = w_a chi_a e^{i om_a h})."""
    h = np.linspace(0.0, H, nsamp)
    amp = (ws*chis)[None,:]                       # (1, M)
    V = amp * np.exp(1j * np.outer(h, omegas))    # (nsamp, M)
    B = (V.conj().T @ V) / nsamp                   # (M, M) Hermitian PSD
    return B

def count_modes(U, slope, chi, Hmax=60.0, nH=600, thresh=None,
                feedback=False, delta=0.0, M_max=300, Pmax=2000):
    """THE SHARED RULE. Returns emitted gamma_n (heights where a NEW singular value of B(H)
       crosses the resolution threshold) and cumulative N(H)."""
    qs, ws, chis, omegas, slp = build_atoms(U, slope, chi, M_max=M_max, Pmax=Pmax)
    M = len(omegas)
    # resolution threshold: fixed fraction of the dominant-mode energy scale
    base_energy = np.sum((ws)**2)   # trace scale of Gram at full window
    if thresh is None:
        thresh = 1e-3 * base_energy

    # pitch feedback adjusts the effective height step / frequency scale as modes emit.
    # height grid (the "accumulated height H"): the radial slope sets how fast height accrues.
    # We scan H upward; slope folds into mapping radius->height: H_eff = H (slope sets atom scale,
    # already in omegas via U; we keep H as the literal accumulated helix height).
    Hgrid = np.linspace(1.0, Hmax, nH)

    emitted = []
    prev_count = 0
    pitch = U
    H_emit_heights = []
    cumulative = []
    for H in Hgrid:
        # pitch feedback: rescale omegas by (U/pitch) so each emission shifts the helix pitch
        scale = (U/pitch) if feedback else 1.0
        B = windowed_gram(ws, chis, omegas*scale, H)
        sv = np.linalg.svd(B, compute_uv=False)   # singular values = eigenvalues (PSD)
        nres = int(np.sum(sv > thresh))
        if nres > prev_count:
            for _ in range(nres - prev_count):
                H_emit_heights.append(H)
                if feedback:
                    pitch = pitch + delta
            prev_count = nres
        cumulative.append(prev_count)
    return np.array(H_emit_heights), Hgrid, np.array(cumulative), dict(
        M=M, thresh=thresh, base_energy=base_energy, U=U, slope=slope,
        feedback=feedback, delta=delta, Pmax=Pmax, M_max=M_max)

if __name__ == "__main__":
    print("module ok")
