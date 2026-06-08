"""
Reference zeros for FINAL comparison ONLY. Never fed into the construction.
- zeta zeros via mpmath.zetazero(n)
- Dirichlet L(chi,s) via Hurwitz: L = q^{-s} sum_{a=1..q} chi(a) zeta(s, a/q)
  chi mod 3: chi(1)=1, chi(2)=-1 (real primitive odd)
  chi mod 4: chi(1)=1, chi(3)=-1 (real primitive odd)
  Both odd, root number +1; completed L real on the line.
mpmath dps=15 only.
"""
import mpmath as mp
import numpy as np
import json, os

mp.mp.dps = 15

CACHE = os.path.join(os.path.dirname(__file__), "refzeros_cache.json")

def zeta_zeros(N=40):
    return [float(mp.zetazero(n).imag) for n in range(1, N+1)]

def make_chi(q, vals):
    # vals: dict a->chi(a) for a coprime to q; 0 otherwise
    def chi(a):
        a = a % q
        return vals.get(a, 0)
    return chi

def Lchi(chi, q, s):
    # L(chi,s) = q^{-s} sum_{a=1..q} chi(a) zeta(s, a/q)
    tot = mp.mpf(0)
    for a in range(1, q+1):
        c = chi(a)
        if c != 0:
            tot += c * mp.zeta(s, mp.mpf(a)/q)
    return q**(-s) * tot

def completed_real_L(chi, q, t):
    # For odd primitive real chi (root number +1), the completed
    # Lambda(s) = (q/pi)^{(s+1)/2} Gamma((s+1)/2) L(chi,s) is real on s=1/2+it.
    # We just need a real-valued function whose sign changes locate zeros.
    s = mp.mpf("0.5") + 1j*t
    L = Lchi(chi, q, s)
    # gamma factor for odd character: Gamma((s+1)/2) (q/pi)^{(s+1)/2}
    gfac = (mp.mpf(q)/mp.pi)**((s+1)/2) * mp.gamma((s+1)/2)
    Lam = gfac * L
    return Lam

def find_zeros_signchange(chi, q, tmax=40.0, dt=0.01, N=20):
    # scan completed_real_L real part for sign changes; refine by bisection
    ts = np.arange(0.05, tmax, dt)
    prev_t = ts[0]
    prev_v = float(completed_real_L(chi, q, prev_t).real)
    zeros = []
    for t in ts[1:]:
        v = float(completed_real_L(chi, q, t).real)
        if prev_v == 0:
            zeros.append(prev_t)
        elif prev_v * v < 0:
            # bisect
            lo, hi = prev_t, t
            flo = prev_v
            for _ in range(60):
                mid = 0.5*(lo+hi)
                fm = float(completed_real_L(chi, q, mid).real)
                if flo * fm <= 0:
                    hi = mid
                else:
                    lo, flo = mid, fm
            zeros.append(0.5*(lo+hi))
        prev_t, prev_v = t, v
        if len(zeros) >= N:
            break
    return zeros[:N]

def main():
    out = {}
    print("computing zeta zeros...")
    out["zeta"] = zeta_zeros(40)
    print("zeta first 5:", out["zeta"][:5])

    chi3 = make_chi(3, {1:1, 2:-1})
    print("computing chi mod 3 zeros...")
    out["chi3"] = find_zeros_signchange(chi3, 3, tmax=45.0, dt=0.01, N=20)
    print("chi3 first 5:", out["chi3"][:5])

    chi4 = make_chi(4, {1:1, 3:-1})
    print("computing chi mod 4 zeros...")
    out["chi4"] = find_zeros_signchange(chi4, 4, tmax=45.0, dt=0.01, N=20)
    print("chi4 first 5:", out["chi4"][:5])

    with open(CACHE, "w") as f:
        json.dump(out, f, indent=2)
    print("cached ->", CACHE)

if __name__ == "__main__":
    main()
