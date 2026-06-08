import numpy as np

# ============================================================
# IMPLEMENTATION 2: explicit accumulated source subspace H_F(H)
# ------------------------------------------------------------
# Source atoms: prime powers q = p^k up to cutoff Q.
#   weight w(q) = chi(q) / sqrt(q)        (on-line p^-1/2 radial weight)
#   each atom is a COLUMN sampled along the climb on a height grid t in [0,H]:
#        column_q(t) = w(q) * cos( t * log q )       (real winding readout)
#   FTA-additive winding: phase of atom q at "height" t is t*log q; since
#        log(q1*q2)=log q1+log q2, the winding is additive over FTA -> coherent dirs.
# Build matrix F_H (rows=grid points, cols=atoms up to height H), Gram A_H = F_H^T F_H,
# SVD -> singular values. NEW resolvable mode = new s.v. crossing threshold as H grows.
# Emit cumulative gamma_n = N(H) = count of resolvable modes.
# ============================================================

def primes_upto(n):
    sieve = np.ones(n+1, dtype=bool); sieve[:2]=False
    for i in range(2,int(n**0.5)+1):
        if sieve[i]: sieve[i*i::i]=False
    return np.nonzero(sieve)[0]

def prime_powers(Q):
    """all prime powers p^k <= Q with their log and the prime p, exponent k."""
    ps = primes_upto(Q)
    out = []
    for p in ps:
        q = p; k = 1
        while q <= Q:
            out.append((q, p, k))
            q *= p; k += 1
    return out  # list of (q, p, k)

def chi_trivial(n, q_mod=1): return 1.0
def make_chi(q_mod, table):
    def chi(n):
        r = n % q_mod
        return table.get(r, 0.0)
    return chi
chi3 = make_chi(3, {1:1.0, 2:-1.0, 0:0.0})
chi4 = make_chi(4, {1:1.0, 3:-1.0, 0:0.0, 2:0.0})

def build_and_count(chi, Q=400, Hgrid=None, ngrid=600, thresh_ratio=1e-3):
    pp = prime_powers(Q)
    # atom data
    qs = np.array([q for q,p,k in pp], dtype=np.float64)
    logs = np.log(qs)
    # chi(q): for prime power p^k, chi(p^k)=chi(p)^k
    ch = np.array([ (chi(p)**k) for q,p,k in pp ], dtype=np.float64)
    w = ch / np.sqrt(qs)                         # weight chi(q)/sqrt(q)
    keep = np.abs(w) > 0                          # drop atoms killed by chi
    qs, logs, w = qs[keep], logs[keep], w[keep]
    order = np.argsort(logs)                      # accumulate by increasing log q (height ordering)
    qs, logs, w = qs[order], logs[order], w[order]

    if Hgrid is None:
        Hgrid = np.linspace(2.0, 50.0, 96)
    results = []
    Nprev = 0
    # fixed sampling grid in t (the climb height coordinate)
    t = np.linspace(0.0, 1.0, ngrid)             # normalized; scaled per H below
    for H in Hgrid:
        tt = t * H                                # sample t in [0,H]
        # atoms whose log q <= log(H)?? -> "accumulated up to height H":
        # include atoms whose winding completes at least ~1 cycle by height H, i.e. log q up to a cutoff.
        # Use accumulation rule: include atoms with log q <= log(Hcut) where Hcut grows with H.
        # Simpler/literal: accumulate ALL atoms but restrict matrix to height window [0,H].
        # Number of atoms scales with the resolution; here include atoms up to count m(H).
        m = qs.shape[0]
        # F_H : ngrid x m,   F[i,j] = w_j cos(tt_i * log q_j)
        F = (np.cos(np.outer(tt, logs))) * w[None,:]   # ngrid x m
        # Gram A_H = F^T F  (m x m)
        A = F.T @ F
        # singular values via eigvals of symmetric Gram
        ev = np.linalg.eigvalsh(A)
        ev = np.clip(ev, 0, None)
        sv = np.sqrt(ev)[::-1]                    # descending
        thr = thresh_ratio * sv[0] if sv[0]>0 else 0
        N = int(np.sum(sv > thr))
        results.append((H, N, sv[0]))
    return results

for name, chi in [("zeta", chi_trivial), ("chi3", chi3), ("chi4", chi4)]:
    res = build_and_count(chi)
    print(name, "sample (H,N):", [(round(h,1),n) for (h,n,s) in res[::12]])
