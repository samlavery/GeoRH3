"""
Figure out the helix winding unit FROM THE DATA.

Wind each channel's zeros at rate ω (angle per unit height): a_j = ω·γ_j (mod 2π).
Scan ω; measure clustering of {a_j}.  Two metrics:
  R1(ω) = |mean exp(i·ω·γ_j)|             (single-cluster phase alignment)
  Rk(ω) = max_{K≤8} |mean exp(i·K·ω·γ_j)| (best K-fold spoke alignment)
Peaks ⇒ data-preferred units.  Mark 2π/5 (the test) and the π/helixUnit guesses.
"""
import numpy as np, mpmath as mp, math, os
import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt
mp.mp.dps = 15
OUT = os.path.dirname(os.path.abspath(__file__))

def make_char(q, vals):  # vals: dict residue->±1
    return lambda n: vals.get(n % q, 0)

CH = [
  dict(name='ζ',  q=1, chi=(lambda n: 1),                       hu=6),
  dict(name='χ₃', q=3, chi=make_char(3, {1:1, 2:-1}),           hu=3),
  dict(name='χ₄', q=4, chi=make_char(4, {1:1, 3:-1}),           hu=2),
  dict(name='χ₅', q=5, chi=make_char(5, {1:1, 4:1, 2:-1, 3:-1}), hu=1),  # quadratic char mod 5
]

def Lfun(ch):
    q, chi = ch['q'], ch['chi']
    if q == 1:
        return lambda s: mp.zeta(s)
    return lambda s: q**(-s) * mp.fsum(chi(r)*mp.zeta(s, mp.mpf(r)/q) for r in range(1, q+1))

def zeros_of(ch, tmax=60.0):
    L = Lfun(ch); ts = np.linspace(2.0, tmax, 2600)
    v = np.array([abs(complex(L(mp.mpf('0.5')+1j*mp.mpf(float(t))))) for t in ts])
    return np.array([ts[i] for i in range(1, len(ts)-1)
                     if v[i] < v[i-1] and v[i] < v[i+1] and v[i] < 0.4])

TEST = 2*math.pi/5
om = np.linspace(0.05, 3.6, 1400)
fig, axes = plt.subplots(2, 4, figsize=(22, 9))
for col, ch in enumerate(CH):
    g = zeros_of(ch)
    R1 = np.array([abs(np.mean(np.exp(1j*w*g))) for w in om])
    Rk = np.array([max(abs(np.mean(np.exp(1j*K*w*g))) for K in range(1, 9)) for w in om])
    print(f"{ch['name']}: {len(g)} zeros;  R1(2π/5)={abs(np.mean(np.exp(1j*TEST*g))):.3f}, "
          f"Rk(2π/5)={max(abs(np.mean(np.exp(1j*K*TEST*g))) for K in range(1,9)):.3f};  "
          f"argmax R1 at ω={om[np.argmax(R1)]:.3f}, argmax Rk at ω={om[np.argmax(Rk)]:.3f}")
    ax = axes[0, col]
    ax.plot(om, R1, color='steelblue', lw=1, label='R1 (1 cluster)')
    ax.plot(om, Rk, color='seagreen', lw=1, alpha=0.7, label='Rk (best K-fold)')
    ax.axvline(TEST, color='crimson', ls='--', lw=1.2, label='2π/5')
    ax.axvline(math.pi/ch['hu'], color='purple', ls=':', lw=1, label=f'π/{ch["hu"]}')
    ax.set_title(f"{ch['name']} — clustering vs winding unit ω"); ax.set_xlabel('ω'); ax.set_ylabel('R')
    ax.legend(fontsize=6); ax.set_ylim(0, 1)
    # polar: zeros wound at 2π/5
    axp = axes[1, col]; axp.remove(); axp = fig.add_subplot(2, 4, 4+col+1, projection='polar')
    a = (TEST*g) % (2*math.pi)
    axp.scatter(a, g, s=22, color='crimson')
    axp.set_title(f"{ch['name']} — zeros wound at 2π/5 (radius=γ)", fontsize=9)
fig.tight_layout(); fig.savefig(f'{OUT}/find_unit.png', dpi=115)
print(f"\nsaved {OUT}/find_unit.png   (2π/5 = {TEST:.4f})")
