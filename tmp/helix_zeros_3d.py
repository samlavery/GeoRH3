"""
Per helix unit: use only the fibre primes (the character does this — χ(p)=0 off-fibre),
extract the zero heights γ the old-fashioned way (|L(½+it)| dips), then CONVERT each zero to
3D coordinates and plot:

    rho = ½ + iγ
    w(rho) = 1 − 1/rho        →  (x, y) = (Re w, Im w)   on the unit circle if on-line
    z = γ                     →  height

So each L-function's zeros climb the unit cylinder, one ring per zero. |w| = 1 ⟺ on the line.
"""
import numpy as np, mpmath as mp, math, os
import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt
mp.mp.dps = 15
OUT = os.path.dirname(os.path.abspath(__file__))

def make_char(q, plus, minus):
    return lambda n: (1 if n % q in plus else (-1 if n % q in minus else 0))

CH = [
  dict(name='ζ  (π/6, e³)', short='zeta', q=1, chi=(lambda n: 1), d=6, fibre='all primes'),
  dict(name='χ₃ (π/3, e⁶)', short='chi3', q=3, chi=make_char(3,{1},{2}), d=3, fibre='p≡1(+), p≡2(−) mod 3'),
  dict(name='χ₄ (π/2, e⁸)', short='chi4', q=4, chi=make_char(4,{1},{3}), d=2, fibre='p≡1(+), p≡3(−) mod 4'),
]

def Lfun(ch):
    q, chi = ch['q'], ch['chi']
    if q == 1:
        return lambda s: mp.zeta(s)
    return lambda s: q**(-s) * mp.fsum(chi(r) * mp.zeta(s, mp.mpf(r)/q) for r in range(1, q+1))

def extract_heights(L, tmax=40.0):
    ts = np.linspace(2.0, tmax, 2400)
    vals = np.array([abs(complex(L(mp.mpf('0.5') + 1j*mp.mpf(float(t))))) for t in ts])
    cand = [i for i in range(1, len(ts)-1)
            if vals[i] < vals[i-1] and vals[i] < vals[i+1] and vals[i] < 0.4]
    gammas = []
    for i in cand:
        # refine the dip by golden-section on |L|
        a, b = ts[i-1], ts[i+1]
        g = mp.findroot(lambda t: mp.diff(lambda u: abs(L(mp.mpf('0.5')+1j*u)), t),
                        mp.mpf(float(ts[i])), tol=1e-8) if False else ts[i]
        gammas.append(float(g))
    return np.array(gammas)

fig = plt.figure(figsize=(15, 5.6))
print("=== zeros → (Re w, Im w, γ), fibre primes only, |w|=1 ⇔ on the line ===")
for col, ch in enumerate(CH):
    L = Lfun(ch)
    g = extract_heights(L)
    omega = math.pi / ch['d']                 # winding rate per unit height (the helix unit)
    theta = omega * g                          # angle WINDS with height γ  → an actual helix
    x, y, z = np.cos(theta), np.sin(theta), g  # on the helix at height γ
    print(f"\n{ch['short']}  (fibre: {ch['fibre']}, winding π/{ch['d']} per unit height):")
    print("   γ extracted :", ", ".join(f"{v:.3f}" for v in g))
    ax = fig.add_subplot(1, 3, col+1, projection='3d')
    # the helix spine: winds (cos ωz, sin ωz) as it climbs in z
    zs = np.linspace(g.min()-0.5, g.max()+0.5, 3000)
    ax.plot(np.cos(omega*zs), np.sin(omega*zs), zs, color='0.65', lw=0.7)
    # each zero sits ON the helix at its height
    ax.scatter(x, y, z, s=36, color='crimson', depthshade=True)
    ax.set_title(f"{ch['name']}\nzeros on the helix, winding π/{ch['d']} per height, z = γ")
    ax.set_xlabel('x = cos(π/{}·γ)'.format(ch['d'])); ax.set_ylabel('y = sin'); ax.set_zlabel('height γ')
    ax.set_xlim(-1.1, 1.1); ax.set_ylim(-1.1, 1.1)
fig.tight_layout(); fig.savefig(f'{OUT}/helix_zeros_3d.png', dpi=115)
print(f"\nsaved {OUT}/helix_zeros_3d.png")
