"""
Number of ON-FIBRE primes between each consecutive pair of zeros, on the shared height axis t.

On the helix θ=(π/d)t, R=t/(2d), height=t, an integer dropped at arc n·(π/d) lands at
height t_n = 2√(d·n)  (since arc(t) ≈ (π/4d²)t²).  So:
    on-fibre prime p   →  height t_p = 2√(d·p)
    zero j             →  height γ_j
Count on-fibre primes with t_p in (γ_j, γ_{j+1}), i.e. p in (γ_j²/4d, γ_{j+1}²/4d).
On-fibre = χ(p) ≠ 0 (coprime to the conductor).
"""
import numpy as np, math, os
import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt
OUT = os.path.dirname(os.path.abspath(__file__))

def make_char(q, plus, minus):
    return lambda n: (1 if n % q in plus else (-1 if n % q in minus else 0))

CH = [
  dict(name='ζ  (π/6)', d=6, q=1, chi=(lambda n: 1),
       zeros=[14.134725,21.022040,25.010858,30.424876,32.935062,37.586178,40.918719,
              43.327073,48.005151,49.773832,52.970321,56.446248,59.347044,60.831779]),
  dict(name='χ₃ (π/3)', d=3, q=3, chi=make_char(3,{1},{2}),
       zeros=[8.0397,11.2492,15.7046,18.2620,20.4558,24.0594,26.5779,28.2182,30.7450,
              32.4150,34.6738,36.4727,39.2451,40.7146,43.1926,45.2000]),
  dict(name='χ₄ (π/2)', d=2, q=4, chi=make_char(4,{1},{3}),
       zeros=[6.0209,10.2438,12.9881,16.3426,18.2920,21.4506,23.2784,25.7288,28.3596,
              29.6564,32.5922,34.1999,37.0,38.5,40.0,42.0]),
]

fig, axes = plt.subplots(1, 3, figsize=(18, 5))
for ax, ch in zip(axes, CH):
    d, chi = ch['d'], ch['chi']
    g = np.cumsum(np.array(sorted(ch['zeros'])))     # PROGRESSIVE heights: S_j = Σ_{i≤j} γ_i
    Pmax = int((g[-1]**2)/(4*d)) + 5
    s = np.ones(Pmax+1, bool); s[:2] = False
    for i in range(2, int(Pmax**0.5)+1):
        if s[i]: s[i*i::i] = False
    primes = [p for p in np.nonzero(s)[0] if chi(int(p)) != 0]      # on-fibre primes
    tp = np.array([2*math.sqrt(d*p) for p in primes])               # their heights
    dens, mids = [], []
    print(f"\n{ch['name']}  (on-fibre prime heights t_p = 2√({d}p)):")
    for j in range(len(g)-1):
        dg = g[j+1]-g[j]
        c = int(np.sum((tp > g[j]) & (tp <= g[j+1])))
        density = c/dg
        dens.append(density); mids.append(0.5*(g[j]+g[j+1]))
        print(f"   γ {g[j]:7.3f} → {g[j+1]:7.3f}  (Δ={dg:5.3f}) :  {c} primes  →  density {density:5.3f}/unit")
    mids = np.array(mids)
    ax.plot(mids, dens, 'o-', color='steelblue', label='count / zero-spacing')
    # theoretical local on-fibre prime density in this coord: t / (2d·log(t²/4d))
    tt = np.linspace(mids.min(), mids.max(), 200)
    theo = tt/(2*d*np.log(np.maximum(tt**2/(4*d), 1.01)))
    ax.plot(tt, theo, 'r--', lw=1, label='t/(2d·log(t²/4d))')
    ax.set_title(ch['name'] + " — on-fibre prime density per unit height")
    ax.set_xlabel('mid-gap height t'); ax.set_ylabel('primes per unit height'); ax.legend(fontsize=7)
fig.tight_layout(); fig.savefig(f'{OUT}/primes_between_zeros.png', dpi=120)
print(f"\nsaved {OUT}/primes_between_zeros.png")
