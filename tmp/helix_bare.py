"""
The bare helix curve per unit — no integers yet.

Continuous loop counter k:
    R(k) = e^m · k     (OUT — radius linear in the loop, the cone wall)
    z(k) = pitch · k   (UP  — the pitch climb)
    θ(k) = 2π · k      (one full turn per loop)

    x = R cosθ,  y = R sinθ,  z

ζ: m=3, pitch π/6   |   χ₃: m=6, pitch π/3   |   χ₄: m=8, pitch π/2
(Radius shown ÷ e^m so the three are comparable; the true radial rate is e^m.)
"""
import numpy as np, math, os
import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt
OUT = os.path.dirname(os.path.abspath(__file__))

CH = [
  dict(name='ζ  (m=3, pitch π/6)', m=3, pitch=math.pi/6, c='seagreen'),
  dict(name='χ₃ (m=6, pitch π/3)', m=6, pitch=math.pi/3, c='darkorange'),
  dict(name='χ₄ (m=8, pitch π/2)', m=8, pitch=math.pi/2, c='crimson'),
]

KMAX = 6.0           # number of loops to draw
k = np.linspace(0, KMAX, 4000)

fig = plt.figure(figsize=(18, 6.4))
for col, ch in enumerate(CH):
    m, pitch = ch['m'], ch['pitch']
    theta = 2*math.pi * k
    R = k                      # = (e^m · k) / e^m, normalized for display
    z = pitch * k
    x, y = R*np.cos(theta), R*np.sin(theta)
    ax = fig.add_subplot(1, 3, col+1, projection='3d')
    ax.plot(x, y, z, color=ch['c'], lw=1.3)
    ax.set_title(ch['name'] + "\nR = e^m·k (out), z = pitch·k (up), θ = 2πk")
    ax.set_xlabel('x'); ax.set_ylabel('y'); ax.set_zlabel('z (pitch·k)')
    ax.view_init(elev=22, azim=40)
fig.tight_layout(); fig.savefig(f'{OUT}/helix_bare.png', dpi=120)
print(f"saved {OUT}/helix_bare.png")

# a side-on view so the pitch (up) and the cone widening (out) are both legible
fig2 = plt.figure(figsize=(18, 6.0))
for col, ch in enumerate(CH):
    m, pitch = ch['m'], ch['pitch']
    theta = 2*math.pi * k; R = k; z = pitch * k
    x, y = R*np.cos(theta), R*np.sin(theta)
    ax = fig2.add_subplot(1, 3, col+1, projection='3d')
    ax.plot(x, y, z, color=ch['c'], lw=1.3)
    ax.set_title(ch['name'] + " — side view")
    ax.set_xlabel('x'); ax.set_ylabel('y'); ax.set_zlabel('z')
    ax.view_init(elev=6, azim=0)
fig2.tight_layout(); fig2.savefig(f'{OUT}/helix_bare_side.png', dpi=120)
print(f"saved {OUT}/helix_bare_side.png")
