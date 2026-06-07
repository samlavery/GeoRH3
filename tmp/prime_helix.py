"""
The prime helix, per unit — a real helix: winds (θ = 2π n / m, m integers per turn),
climbs (z = pitch · n/m, UP), grows out (R = √n, OUT). Residue mod m sets the angle, so each
residue class is a spoke; the primes (coprime residues = the fibre) form LINES up the helix.

    ζ   : m=3  (e³),  pitch π/6   fibre = coprime residues mod 3
    χ₃  : m=6  (e⁶),  pitch π/3   fibre = {1,5} mod 6
    χ₄  : m=8  (e⁸),  pitch π/2   fibre = {1,3,5,7} mod 8
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
  dict(name='ζ  (m=3, e³, pitch π/6)', short='zeta', m=3, pitch=math.pi/6),
  dict(name='χ₃ (m=6, e⁶, pitch π/3)', short='chi3', m=6, pitch=math.pi/3),
  dict(name='χ₄ (m=8, e⁸, pitch π/2)', short='chi4', m=8, pitch=math.pi/2),
]

N = 240
isP = sieve(N)
fig = plt.figure(figsize=(19, 6.4))
for col, ch in enumerate(CH):
    m, pitch = ch['m'], ch['pitch']
    n = np.arange(1, N+1)
    theta = 2*math.pi * n / m          # WINDS; residue (n mod m) sets the spoke
    R = np.sqrt(n)                      # OUT
    z = pitch * (n / m)                # UP
    x, y = R*np.cos(theta), R*np.sin(theta)
    ax = fig.add_subplot(1, 3, col+1, projection='3d')
    # helix spine (continuous)
    nn = np.linspace(1, N, 6000)
    ax.plot(np.sqrt(nn)*np.cos(2*math.pi*nn/m), np.sqrt(nn)*np.sin(2*math.pi*nn/m),
            pitch*(nn/m), color='0.85', lw=0.4)
    pr = isP[1:N+1]; comp = ~pr
    ax.scatter(x[comp], y[comp], z[comp], s=5, color='0.75', alpha=0.35)
    # primes colored by residue mod m (each coprime residue = its own spoke/line)
    res = n % m
    coprime = [r for r in range(m) if math.gcd(r, m) == 1]
    cmap = plt.cm.tab10
    for i, r in enumerate(coprime):
        sel = pr & (res == r)
        ax.scatter(x[sel], y[sel], z[sel], s=20, color=cmap(i % 10), label=f'p ≡ {r} mod {m}')
    ax.set_title(ch['name'] + "  — primes form spokes by residue")
    ax.legend(fontsize=7, loc='upper left')
    ax.set_xlabel('x'); ax.set_ylabel('y'); ax.set_zlabel('z (pitch)')
    ax.view_init(elev=18, azim=35)
fig.tight_layout(); fig.savefig(f'{OUT}/prime_helix.png', dpi=120)
print(f"saved {OUT}/prime_helix.png")

# also a top-down view (the spokes are clearest looking straight down the axis)
fig2 = plt.figure(figsize=(19, 6.2))
for col, ch in enumerate(CH):
    m = ch['m']; n = np.arange(1, N+1)
    theta = 2*math.pi * n / m; R = np.sqrt(n)
    x, y = R*np.cos(theta), R*np.sin(theta)
    ax = fig2.add_subplot(1, 3, col+1)
    pr = isP[1:N+1]
    ax.scatter(x[~pr], y[~pr], s=5, color='0.8', alpha=0.4)
    res = n % m; coprime = [r for r in range(m) if math.gcd(r, m) == 1]
    for i, r in enumerate(coprime):
        sel = pr & (res == r)
        ax.scatter(x[sel], y[sel], s=18, color=plt.cm.tab10(i % 10), label=f'p≡{r} mod {m}')
    ax.set_aspect('equal'); ax.set_title(ch['name'] + " — top-down: prime spokes")
    ax.legend(fontsize=7)
fig2.tight_layout(); fig2.savefig(f'{OUT}/prime_helix_topdown.png', dpi=120)
print(f"saved {OUT}/prime_helix_topdown.png")
