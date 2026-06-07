"""
"That looks like cosh" — yes, and it's the whole point.

A mode at σ and its functional-equation dual at 1−σ have radial envelopes e^{σs} and e^{(1−σ)s}.
Their sum is

    e^{σs} + e^{(1−σ)s} = 2·e^{s/2}·cosh((σ−½)·s)

so the FE-pair envelope is a cosh riding the geometric-mean rate e^{s/2} (= √x). The cosh is
FLAT (≡1) exactly at σ=½ and flares for any σ≠½. The radius law R = e^m·k is the one-sided
growth; pair it with its FE-mirror and you get the cosh bowl, whose floor IS the critical line.

(This is the Lean fact `asymmetry_eq_floor_iff_half`: e^{σθ}+e^{(1−σ)θ} = 2e^{θ/2} ⟺ σ=½.)
"""
import numpy as np, math, os
import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt
OUT = os.path.dirname(os.path.abspath(__file__))

s = np.linspace(-8, 8, 800)

fig, (axA, axB, axC) = plt.subplots(1, 3, figsize=(17, 5))

# A — the FE-pair envelope e^{σs}+e^{(1−σ)s}, with the σ=½ floor 2e^{s/2}
for sigma, c in [(0.5,'seagreen'), (0.6,'darkorange'), (0.7,'crimson'), (0.8,'purple')]:
    E = np.exp(sigma*s) + np.exp((1-sigma)*s)
    axA.semilogy(s, E, color=c, lw=1.2, label=f'σ={sigma}')
axA.semilogy(s, 2*np.exp(s/2), 'k--', lw=0.9, label='floor 2e^{s/2} (σ=½)')
axA.set_title('FE-pair radial envelope  e^{σs}+e^{(1−σ)s}\n= 2·e^{s/2}·cosh((σ−½)s)')
axA.set_xlabel('s (height up the helix)'); axA.set_ylabel('paired radius'); axA.legend(fontsize=8)

# B — the cosh itself: cosh((σ−½)s). Flat (=1) only at σ=½.
for sigma, c in [(0.5,'seagreen'), (0.55,'goldenrod'), (0.6,'darkorange'), (0.7,'crimson')]:
    axB.plot(s, np.cosh((sigma-0.5)*s), color=c, lw=1.3, label=f'σ={sigma}')
axB.axhline(1.0, color='k', ls=':', lw=0.8)
axB.set_title('the cosh:  cosh((σ−½)·s)\nflat ≡ 1  ⟺  σ = ½  (the no-drift floor)')
axB.set_xlabel('s'); axB.set_ylabel('cosh((σ−½)s)'); axB.legend(fontsize=8); axB.set_ylim(0.5, 6)

# C — the cone radius R = e^m·k (linear in loop k) for the three channels (normalized by e^m)
for mode, c, name in [(3,'seagreen','ζ (e³)'), (6,'darkorange','χ₃ (e⁶)'), (8,'crimson','χ₄ (e⁸)')]:
    k = np.linspace(0, 6, 200)
    R = math.exp(mode) * k
    axC.plot(k, R/math.exp(mode), color=c, lw=1.4, label=f'{name}: R=e^{mode}·k')
axC.set_title('radius is LINEAR in the loop k:  R = e^m·k\n(shown ÷e^m; the cone wall, combined with pitch)')
axC.set_xlabel('loop counter k'); axC.set_ylabel('R / e^m  (= k)'); axC.legend(fontsize=8)

fig.tight_layout(); fig.savefig(f'{OUT}/helix_cosh.png', dpi=120)
print(f"saved {OUT}/helix_cosh.png")

# numeric witness: the floor is attained only at σ=½
print("=== FE-pair envelope at s=6, vs the σ=½ floor 2·e³ = %.3f ===" % (2*math.exp(3)))
for sigma in [0.5, 0.55, 0.6, 0.7, 0.8]:
    val = math.exp(sigma*6) + math.exp((1-sigma)*6)
    print(f"  σ={sigma}:  e^(σ·6)+e^((1−σ)·6) = {val:10.3f}   excess over floor = {val-2*math.exp(3):+.3f}")
print("\nThe minimum over σ is exactly at σ=½ (cosh(0)=1). Off-line ⇒ the pair flares — the cosh opens up.")
