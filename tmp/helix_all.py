"""
All FOUR helices defined in the project (HelixDefs.channels = chTrivial3, chChi3, chMode8, chMode12).

per channel (loop counter k):
    R(k) = e^mode · k      (out — loopRadius; shown ÷e^mode for comparison)
    θ(k) = 2π · k          (one turn per loop)
    z(k) = (π/helixUnit)·k (up — pitch = the angle unit)
"""
import numpy as np, math, os
import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt
OUT = os.path.dirname(os.path.abspath(__file__))

CH = [
  dict(name='ζ  (trivial mod 3)', helixUnit=6, mode=3,  c='seagreen'),
  dict(name='χ₃',                 helixUnit=3, mode=6,  c='darkorange'),
  dict(name='mode-8  (χ₄/χ₈)',    helixUnit=2, mode=8,  c='crimson'),
  dict(name='mode-12 (χ₅)',       helixUnit=1, mode=12, c='purple'),
]

KMAX = 6.0
k = np.linspace(0, KMAX, 5000)

fig = plt.figure(figsize=(15, 13))
for i, ch in enumerate(CH):
    pitch = math.pi / ch['helixUnit']
    theta = 2*math.pi * k
    R = k                                  # = (e^mode·k)/e^mode, normalized
    z = pitch * k
    x, y = R*np.cos(theta), R*np.sin(theta)
    ax = fig.add_subplot(2, 2, i+1, projection='3d')
    ax.plot(x, y, z, color=ch['c'], lw=1.3)
    ax.set_title(f"{ch['name']}\nangle unit π/{ch['helixUnit']}, radial e^{ch['mode']}, "
                 f"pitch π/{ch['helixUnit']}")
    ax.set_xlabel('x'); ax.set_ylabel('y'); ax.set_zlabel('z (pitch·k)')
    ax.view_init(elev=22, azim=40)
fig.tight_layout(); fig.savefig(f'{OUT}/helix_all.png', dpi=120)
print(f"saved {OUT}/helix_all.png  (pitches: " +
      ", ".join(f"{ch['name'].split()[0]}=π/{ch['helixUnit']}" for ch in CH) + ")")
