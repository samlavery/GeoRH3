"""
REFERENCE ZEROS ONLY -- for FINAL comparison. Never fed into the construction.
zeta: mpmath.zetazero(n).
Dirichlet L(chi,s) via Hurwitz: L = q^-s sum_{a=1..q} chi(a) zeta(s, a/q).
chi mod 3: chi(1)=1, chi(2)=-1 (real primitive odd).
chi mod 4: chi(1)=1, chi(3)=-1 (real primitive odd).
Both odd real primitive -> root number 1, completed L real on the line.
Find low zeros as sign-changes of the COMPLETED real L(chi,1/2+it) along t.
"""
import sys, math
import numpy as np
import mpmath as mp
mp.mp.dps = 15

def pr(*a): print(*a); sys.stdout.flush()

# ---- zeta zeros ----
def zeta_zeros(N):
    return [float(mp.zetazero(n).imag) for n in range(1, N+1)]

# ---- Dirichlet L via Hurwitz ----
def make_chi(q, table):
    # table: dict residue->value
    def chi(n):
        return table.get(n % q, 0)
    return chi

CHARS = {
    3: {1: 1, 2: -1},   # odd real primitive mod 3
    4: {1: 1, 3: -1},   # odd real primitive mod 4
}

def Lval(q, chi, s):
    # L(chi,s) = q^-s sum_{a=1..q} chi(a) zeta(s, a/q)
    return q**(-s) * mp.fsum(chi(a) * mp.zeta(s, mp.mpf(a)/q) for a in range(1, q+1))

def completed_real(q, chi, t):
    # For odd primitive chi, completed Lambda(s) = (q/pi)^((s+1)/2) Gamma((s+1)/2) L(chi,s).
    # On s=1/2+it with real root number +1, Lambda(1/2+it) is real (up to a fixed phase).
    # We use the Hardy-Z-like real function: rotate L by the gamma-factor phase so it is real.
    s = mp.mpf('0.5') + 1j*mp.mpf(t)
    a = 1  # odd character -> a=1 in the gamma factor exponent
    # gamma factor for odd char: Gamma((s+a)/2) (q/pi)^(s/2)
    gam = mp.gamma((s + a)/2) * (mp.mpf(q)/mp.pi)**(s/2)
    L = Lval(q, chi, s)
    val = gam * L
    # Lambda(1/2+it) is real for these chars; take real part (imag ~ 0)
    return float(val.real)

def dirichlet_zeros(q, N, tmax=60.0, step=0.01):
    chi = make_chi(q, CHARS[q])
    ts = np.arange(0.01, tmax, step)
    vals = np.array([completed_real(q, chi, float(t)) for t in ts])
    s = np.sign(vals)
    idx = np.nonzero(s[:-1]*s[1:] < 0)[0]
    zeros = []
    for i in idx:
        # linear interp of crossing
        t0, t1 = ts[i], ts[i+1]
        v0, v1 = vals[i], vals[i+1]
        zeros.append(t0 - v0*(t1-t0)/(v1-v0))
        if len(zeros) >= N:
            break
    return zeros

if __name__ == "__main__":
    pr("ZETA zeros (first 20):")
    zz = zeta_zeros(20)
    pr(np.round(zz, 4).tolist())
    pr("")
    for q in (3, 4):
        pr(f"Dirichlet L mod {q} zeros (first 18):")
        dz = dirichlet_zeros(q, 18)
        pr(np.round(dz, 4).tolist())
        pr("")
