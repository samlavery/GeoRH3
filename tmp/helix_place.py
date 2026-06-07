"""
Place integers on the bare helix by ARC LENGTH: integer n sits at arc s_n = n·(π/d)
("actual ground covered around the arc"). Invert arc → loop k, read off (x,y,z), color primes.

helix:  R = k (radial rate normalized to 1 for the winding view; true rate e^m),  θ = 2πk,  z = pitch·k
arc(k) = ∫₀ᵏ √(R'² + (Rθ')² + z'²) dκ  = ∫₀ᵏ √(1 + (2πκ)² + pitch²) dκ
integer n  ⇒  arc = n·(π/d)  ⇒  invert for k_n.
"""
import numpy as np, math, os
import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt
OUT = os.path.dirname(os.path.abspath(__file__))

def sieve(N):
    s = np.ones(N+1, bool); s[:2] = False
    for i in range(2, int(N**0.5)+1):
        if s[i]: s[i*i::i] = False
    return s

CH = [
  dict(name='ζ  (π/6)', short='zeta', d=6, m=3, pitch=math.pi/6),
  dict(name='χ₃ (π/3)', short='chi3', d=3, m=6, pitch=math.pi/3),
  dict(name='χ₄ (π/2)', short='chi4', d=2, m=8, pitch=math.pi/2),
]
N = 3000
isP = sieve(N)

def place(ch):
    d, pitch = ch['d'], ch['pitch']
    kg = np.linspace(0, 60, 400000)
    dsdk = np.sqrt(1 + (2*math.pi*kg)**2 + pitch**2)     # arc-length element (R=k normalized)
    s = np.concatenate([[0.0], np.cumsum((dsdk[1:]+dsdk[:-1])/2*np.diff(kg))])
    n = np.arange(1, N+1)
    kn = np.interp(n*(math.pi/d), s, kg)                 # arc = n·π/d  →  loop k_n
    th = 2*math.pi*kn
    return kn*np.cos(th), kn*np.sin(th), pitch*kn, kn

# top-down (clearest for lines/spokes)
figT, axesT = plt.subplots(1, 3, figsize=(18, 6))
for ax, ch in zip(axesT, CH):
    x, y, z, kn = place(ch)
    pr = isP[1:N+1]; m = ch['m']
    ax.scatter(x[~pr], y[~pr], s=3, color='0.8', alpha=0.35)
    res = (np.arange(1, N+1)) % m
    cop = [r for r in range(m) if math.gcd(r, m) == 1]
    for i, r in enumerate(cop):
        sel = pr & (res == r)
        ax.scatter(x[sel], y[sel], s=10, color=plt.cm.tab10(i % 10), label=f'p≡{r} mod {m}')
    ax.set_aspect('equal'); ax.set_title(ch['name'] + f"  (arc = n·π/{ch['d']}, top-down)")
    ax.legend(fontsize=7, markerscale=1.5)
figT.tight_layout(); figT.savefig(f'{OUT}/helix_place_topdown.png', dpi=120)
print(f"saved {OUT}/helix_place_topdown.png  (loops: " +
      ", ".join(f"{ch['short']}={place(ch)[3].max():.1f}" for ch in CH) + ")")

# 3D up-and-out
fig = plt.figure(figsize=(18, 6.2))
for col, ch in enumerate(CH):
    x, y, z, kn = place(ch)
    pr = isP[1:N+1]; m = ch['m']
    ax = fig.add_subplot(1, 3, col+1, projection='3d')
    ax.scatter(x[~pr], y[~pr], z[~pr], s=2, color='0.8', alpha=0.25)
    res = (np.arange(1, N+1)) % m; cop = [r for r in range(m) if math.gcd(r, m) == 1]
    for i, r in enumerate(cop):
        sel = pr & (res == r)
        ax.scatter(x[sel], y[sel], z[sel], s=8, color=plt.cm.tab10(i % 10), label=f'p≡{r} mod {m}')
    ax.set_title(ch['name'] + " — up & out"); ax.legend(fontsize=6); ax.view_init(elev=20, azim=40)
fig.tight_layout(); fig.savefig(f'{OUT}/helix_place_3d.png', dpi=120)
print(f"saved {OUT}/helix_place_3d.png")
