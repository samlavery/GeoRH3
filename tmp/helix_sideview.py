"""
Helix side-view, height = spectral height t, with the zeros marked at their heights z = γ.

helix:  θ(t) = (π/d)·t  (winds, the helix unit per unit height)
        R(t) = e^m·k = e^m·t/(2d)  (out; shown ÷e^m, so R = t/(2d))
        z    = t        (UP — the height axis IS the spectral height)
zeros placed at z = γ_j (where the loss field −L'/L had its pole).
"""
import numpy as np, math, os
import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt
OUT = os.path.dirname(os.path.abspath(__file__))

CH = [
  dict(name='ζ  (π/6)', d=6, c='seagreen',
       zeros=[14.134725,21.022040,25.010858,30.424876,32.935062,37.586178]),
  dict(name='χ₃ (π/3)', d=3, c='darkorange',
       zeros=[8.0397,11.2492,15.7046,18.2620,20.4558,24.0594,26.5779,28.2182,30.7450,32.4150]),
  dict(name='χ₄ (π/2)', d=2, c='crimson',
       zeros=[6.0209,10.2438,12.9881,16.3426,18.2920,21.4506,23.2784,25.7288,28.3596,29.6564]),
]

fig = plt.figure(figsize=(18, 7))
t = np.linspace(0, 42, 6000)
for col, ch in enumerate(CH):
    d = ch['d']
    th = (math.pi/d) * t
    R = t / (2*d)                         # = e^m·k / e^m
    x, y, z = R*np.cos(th), R*np.sin(th), t
    g = np.array(ch['zeros'])
    thg = (math.pi/d) * g; Rg = g/(2*d)
    xg, yg, zg = Rg*np.cos(thg), Rg*np.sin(thg), g
    ax = fig.add_subplot(1, 3, col+1, projection='3d')
    ax.plot(x, y, z, color=ch['c'], lw=0.8, alpha=0.8)
    ax.scatter(xg, yg, zg, s=40, color='black', depthshade=False)
    for xi, yi, zi in zip(xg, yg, zg):
        ax.plot([0, xi], [0, yi], [zi, zi], color='0.5', lw=0.5)   # tick to the axis at each height
    ax.set_title(ch['name'] + " — side view, zeros at their heights z=γ")
    ax.set_xlabel('x'); ax.set_ylabel('y'); ax.set_zlabel('height t = γ')
    ax.view_init(elev=4, azim=0)          # side-on
fig.tight_layout(); fig.savefig(f'{OUT}/helix_sideview.png', dpi=120)
print(f"saved {OUT}/helix_sideview.png")
