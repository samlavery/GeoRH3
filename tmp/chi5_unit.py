"""
Compute ~50 χ₅ (mod 5) zeros, then FUZZ the helix winding unit over 2π/3, 2π/5, 2π/7.

A helix winding unit 2π/q realizes the mod-q character, i.e. the channel is L(s, χ_q); its zeros
are {γ_q}. So "which unit matches the χ₅ zeros exactly" = which q's zero-set coincides with the
computed χ₅ zeros. Only the true conductor (q=5, unit 2π/5) should match.
"""
import numpy as np, mpmath as mp, math, os
from scipy.optimize import minimize_scalar
import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt
mp.mp.dps = 18
OUT = os.path.dirname(os.path.abspath(__file__))

def quad_char(q):
    qr = {(i*i) % q for i in range(1, q)}
    return lambda n: (0 if n % q == 0 else (1 if (n % q) in qr else -1))

UNITS = [
  dict(q=3, label='2π/3', chi=quad_char(3)),
  dict(q=5, label='2π/5', chi=quad_char(5)),   # χ₅ — the true channel
  dict(q=7, label='2π/7', chi=quad_char(7)),
]

def Lfun(q, chi):
    return lambda s: q**(-s) * mp.fsum(chi(r)*mp.zeta(s, mp.mpf(r)/q) for r in range(1, q+1))

def zeros(q, chi, tmax, want):
    L = Lfun(q, chi)
    absL = lambda t: abs(complex(L(mp.mpf('0.5') + 1j*mp.mpf(t))))
    ts = np.linspace(2.0, tmax, int(tmax*70)); v = np.array([absL(float(t)) for t in ts])
    out = []
    for i in range(1, len(ts)-1):
        if v[i] < v[i-1] and v[i] < v[i+1] and v[i] < 0.5:
            r = minimize_scalar(absL, bracket=(ts[i-1], ts[i], ts[i+1]),
                                method='brent', options={'xtol': 1e-9})
            out.append(float(r.x))
            if len(out) >= want: break
    return np.array(sorted(set(round(x, 6) for x in out)))[:want]

print("computing χ₅ (mod 5) zeros ...")
chi5 = quad_char(5)
g5 = zeros(5, chi5, tmax=95.0, want=50)
print(f"  got {len(g5)} χ₅ zeros, up to γ={g5[-1]:.3f}")
print(f"  first ten: {', '.join(f'{x:.4f}' for x in g5[:10])}")

fig, ax = plt.subplots(figsize=(11, 6))
print("\n=== fuzzing the helix winding unit ===")
for u in UNITS:
    gq = zeros(u['q'], u['chi'], tmax=float(g5[-1])+3, want=200)
    # match: each χ₅ zero to nearest candidate zero
    matched = 0; deltas = []
    for g in g5:
        d = np.min(np.abs(gq - g)) if len(gq) else 9.9
        deltas.append(d)
        if d < 0.01: matched += 1
    deltas = np.array(deltas)
    print(f"  unit {u['label']} (mod {u['q']}):  {matched}/{len(g5)} χ₅ zeros matched within 0.01 "
          f"| median |Δ| = {np.median(deltas):.4f}")
    ax.scatter(g5, deltas, s=18, label=f"{u['label']} (mod {u['q']}): {matched}/{len(g5)} exact")
ax.axhline(0.01, color='k', ls=':', lw=0.8)
ax.set_yscale('log'); ax.set_xlabel('χ₅ zero height γ'); ax.set_ylabel('|Δ| to nearest candidate zero')
ax.set_title('Which winding unit reproduces the χ₅ zeros?  (lower = better match)')
ax.legend()
fig.tight_layout(); fig.savefig(f'{OUT}/chi5_unit.png', dpi=120)
print(f"\nsaved {OUT}/chi5_unit.png")
