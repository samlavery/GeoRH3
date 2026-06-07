"""
Clean side-on + top-down pair per helix unit, so the winding reads directly.

helix:  θ(t)=(π/d)·t,  R(t)=t/(2d) (=e^m·k ÷e^m),  height = t.
zeros at their heights t=γ.

  side : horizontal = x = R cosθ,   vertical = height t      (winding shows as oscillation)
  top  : (x, y) = (R cosθ, R sinθ), looking down the axis     (winding shows as the spiral)
"""
import numpy as np, math, os
import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt
OUT = os.path.dirname(os.path.abspath(__file__))

CH = [
  dict(name='ζ  (π/6)', d=6, c='seagreen',
       zeros=[14.134725,21.022040,25.010858,30.424876,32.935062,37.586178,40.918719]),
  dict(name='χ₃ (π/3)', d=3, c='darkorange',
       zeros=[8.0397,11.2492,15.7046,18.2620,20.4558,24.0594,26.5779,28.2182,30.7450,32.4150,34.6738,36.4727]),
  dict(name='χ₄ (π/2)', d=2, c='crimson',
       zeros=[6.0209,10.2438,12.9881,16.3426,18.2920,21.4506,23.2784,25.7288,28.3596,29.6564,32.5922,34.1999]),
]

t = np.linspace(0.0, 42.0, 8000)
fig, axes = plt.subplots(len(CH), 2, figsize=(13, 14))
for row, ch in enumerate(CH):
    d = ch['d']
    th = (math.pi/d)*t; R = t/(2*d)
    x, y = R*np.cos(th), R*np.sin(th)
    g = np.array(ch['zeros']); thg = (math.pi/d)*g; Rg = g/(2*d)
    xg, yg = Rg*np.cos(thg), Rg*np.sin(thg)

    # --- side view: x vs height t ---
    axs = axes[row, 0]
    axs.plot(x, t, color=ch['c'], lw=0.9)
    axs.scatter(xg, g, s=42, color='black', zorder=5)
    for xi, gi in zip(xg, g):
        axs.plot([0, xi], [gi, gi], color='0.6', lw=0.5)
    axs.axvline(0, color='0.85', lw=0.6)
    axs.set_title(f"{ch['name']} — side (winding ↕)"); axs.set_xlabel('x = R cosθ'); axs.set_ylabel('height t = γ')

    # --- top-down: x vs y ---
    axt = axes[row, 1]
    axt.plot(x, y, color=ch['c'], lw=0.7, alpha=0.8)
    axt.scatter(xg, yg, s=42, color='black', zorder=5)
    for xi, yi in zip(xg, yg):
        axt.plot([0, xi], [0, yi], color='0.6', lw=0.5)
    axt.set_aspect('equal'); axt.set_title(f"{ch['name']} — top-down (spiral)")
    axt.set_xlabel('x'); axt.set_ylabel('y')
fig.tight_layout(); fig.savefig(f'{OUT}/helix_pair.png', dpi=120)
print(f"saved {OUT}/helix_pair.png")
