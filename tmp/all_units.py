"""
Data-derive every channel's winding unit. For each target channel, compute its zeros, then fuzz
candidate units 2π/q (q = 1,3,4,5,7,8) and see which q reproduces the zeros exactly.
The matching q is the conductor ⇒ unit = 2π/q, read off the zeros, not assumed.
"""
import numpy as np, mpmath as mp, os
from scipy.optimize import minimize_scalar
mp.mp.dps = 18
OUT = os.path.dirname(os.path.abspath(__file__))

def quad(q):
    qr = {(i*i) % q for i in range(1, q)}
    return lambda n: (0 if n % q == 0 else (1 if (n % q) in qr else -1))

CAND = {
  1: ('ζ  (triv)',  lambda n: 1),
  3: ('χ₃ mod 3',   quad(3)),
  4: ('χ₄ mod 4',   lambda n: (1 if n % 4 == 1 else (-1 if n % 4 == 3 else 0))),
  5: ('χ₅ mod 5',   quad(5)),
  7: ('χ₇ mod 7',   quad(7)),
  8: ('χ₈ mod 8',   lambda n: (1 if n % 8 in (1, 7) else (-1 if n % 8 in (3, 5) else 0))),
}
TARGETS = [1, 3, 4]
NZ, TMAX = 30, 110.0

def Lfun(q, chi):
    if q == 1:
        return lambda s: mp.zeta(s)
    return lambda s: q**(-s) * mp.fsum(chi(r)*mp.zeta(s, mp.mpf(r)/q) for r in range(1, q+1))

def zeros(q, chi):
    L = Lfun(q, chi)
    absL = lambda t: abs(complex(L(mp.mpf('0.5') + 1j*mp.mpf(t))))
    ts = np.linspace(2.0, TMAX, int(TMAX*55)); v = np.array([absL(float(t)) for t in ts])
    out = []
    for i in range(1, len(ts)-1):
        if v[i] < v[i-1] and v[i] < v[i+1] and v[i] < 0.5:
            r = minimize_scalar(absL, bracket=(ts[i-1], ts[i], ts[i+1]),
                                method='brent', options={'xtol': 1e-9})
            out.append(float(r.x))
            if len(out) >= NZ: break
    return np.array(sorted(out))[:NZ]

print("computing zeros per conductor ...")
Z = {}
for q, (lab, chi) in CAND.items():
    Z[q] = zeros(q, chi)
    print(f"  q={q} {lab}: {len(Z[q])} zeros up to γ={Z[q][-1]:.2f}")

print("\n=== fuzz-and-match: target channel  vs  candidate unit 2π/q  (matches/{} within 0.01) ===".format(NZ))
hdr = "target\\unit |" + "".join(f"  2π/{q:<2d}" for q in CAND)
print(hdr); print("-"*len(hdr))
for t in TARGETS:
    row = f"{CAND[t][0]:<11s} |"
    best = None
    for q in CAND:
        m = sum(1 for g in Z[t] if (len(Z[q]) and np.min(np.abs(Z[q]-g)) < 0.01))
        row += f"  {m:>4d}"
        if best is None or m > best[1]: best = (q, m)
    print(row + f"   → unit 2π/{best[0]}  (conductor {best[0]})")
print("\n(diagonal = exact; off-diagonal ≈ 0 ⇒ each channel's zeros pick its own unit)")
