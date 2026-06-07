"""
Unwind → drop integers 1 helix-unit apart → rewind.  Top-down this is a prime spiral
(θ ∝ √n, R ∝ √n, the arc-length placement), and the primes fall on CURVES — the lines.

Big, clean: primes black, composites faint, one panel per helix unit.
"""
import numpy as np, math, os
import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt
OUT = os.path.dirname(os.path.abspath(__file__))

def sieve(N):
    s = np.ones(N+1, bool); s[:2] = False
    for i in range(2, int(N**0.5)+1):
        if s[i]: s[i*i::i] = False
    return s

CH = [dict(name='ζ (π/6)', d=6, pitch=math.pi/6),
      dict(name='χ₃ (π/3)', d=3, pitch=math.pi/3),
      dict(name='χ₄ (π/2)', d=2, pitch=math.pi/2)]
N = 9000
isP = sieve(N)
kg = np.linspace(0, 90, 700000)

fig, axes = plt.subplots(1, 3, figsize=(21, 7.2))
for ax, ch in zip(axes, CH):
    d, pitch = ch['d'], ch['pitch']
    dsdk = np.sqrt(1 + (2*math.pi*kg)**2 + pitch**2)
    s = np.concatenate([[0.0], np.cumsum((dsdk[1:]+dsdk[:-1])/2*np.diff(kg))])
    n = np.arange(1, N+1)
    kn = np.interp(n*(math.pi/d), s, kg)
    th = 2*math.pi*kn
    x, y = kn*np.cos(th), kn*np.sin(th)
    pr = isP[1:N+1]
    ax.scatter(x[~pr], y[~pr], s=1.0, color='0.85', alpha=0.5)
    ax.scatter(x[pr], y[pr], s=2.2, color='black')
    ax.set_aspect('equal'); ax.axis('off')
    ax.set_title(f"{ch['name']}  — primes on curves (arc = n·π/{ch['d']}),  {kn.max():.0f} loops")
fig.tight_layout(); fig.savefig(f'{OUT}/helix_spiral.png', dpi=130)
print(f"saved {OUT}/helix_spiral.png")
