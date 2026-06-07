"""
The log-free helix, drawn — grows UP (pitch) and OUT (radius), both linear in the loop k.

Integers placed at loop k_n = √n (area law n≈k²):
    R(k) = slope · k        (out  — radial, Archimedean)
    z(k) = pitch · k        (up   — axial pitch; the easy-to-forget one)
    θ(k) = ω · k            (winding around)
Primes highlighted; per-channel ± fibre colored. No log anywhere in the placement.

Then a log-free field test: place Λ(n)·χ(n) by radius √n (no log), form the √x-normalized
field, and measure its envelope slope (the radial-drift readout). Honest check included for
whether log re-enters via the √n↔n² area law.
"""
import numpy as np, math, os
import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt

OUT = os.path.dirname(os.path.abspath(__file__))

def make_char(q, plus, minus):
    return lambda n: (1 if n % q in plus else (-1 if n % q in minus else 0))

CH = [
  dict(name='ζ  (π/6, e³)', short='zeta', q=1, chi=(lambda n: 1), d=6, pitch=math.pi/6),
  dict(name='χ₃ (π/3, e⁶)', short='chi3', q=3, chi=make_char(3,{1},{2}), d=3, pitch=math.pi/3),
  dict(name='χ₄ (π/2, e⁸)', short='chi4', q=4, chi=make_char(4,{1},{3}), d=2, pitch=math.pi/2),
]

def sieve_primes(N):
    s = np.ones(N+1, bool); s[:2] = False
    for i in range(2, int(N**0.5)+1):
        if s[i]: s[i*i::i] = False
    return s  # boolean mask

# ---------- Figure 1: the 3D helix, up and out, per channel ----------
N = 400
fig = plt.figure(figsize=(15, 5.2))
isprime = sieve_primes(N)
for col, ch in enumerate(CH):
    ax = fig.add_subplot(1, 3, col+1, projection='3d')
    pitch = ch['pitch']
    n = np.arange(1, N+1)
    arc = n.astype(float)                  # integers 1 helix unit apart ALONG THE ARC
    phi = np.sqrt(2*arc)                   # Archimedean: arc = φ²/2 ⇒ φ = √(2n) ⇒ R ∝ √n
    R = phi                                # OUT  (radius grows ∝ √n)
    z = pitch * phi                        # UP   (pitch · φ)
    x, y = R*np.cos(phi), R*np.sin(phi)
    # continuous spine
    aa = np.linspace(1, N, 4000); pp = np.sqrt(2*aa)
    ax.plot(pp*np.cos(pp), pp*np.sin(pp), pitch*pp, color='0.85', lw=0.5)
    # composites (grey), primes by fibre
    comp = ~isprime[1:N+1]
    ax.scatter(x[comp], y[comp], z[comp], s=4, color='0.6', alpha=0.4)
    pr = isprime[1:N+1]
    if ch['q'] == 1:
        ax.scatter(x[pr], y[pr], z[pr], s=14, color='crimson', label='primes')
    else:
        chv = np.array([ch['chi'](int(m)) for m in n])
        pos = pr & (chv > 0); neg = pr & (chv < 0); nul = pr & (chv == 0)
        ax.scatter(x[pos], y[pos], z[pos], s=14, color='royalblue', label='p: + fibre')
        ax.scatter(x[neg], y[neg], z[neg], s=14, color='darkorange', label='p: − fibre')
        ax.scatter(x[nul], y[nul], z[nul], s=24, color='black', label='conductor null')
    ax.set_title(f"{ch['name']}  — up (pitch z) & out (R∝√n)")
    ax.legend(fontsize=7, loc='upper left'); ax.set_xlabel('x'); ax.set_ylabel('y'); ax.set_zlabel('z (pitch)')
fig.tight_layout(); fig.savefig(f'{OUT}/helix_geometry.png', dpi=110)
print(f"saved {OUT}/helix_geometry.png")

# ---------- Figure 2 + honest log-free field test ----------
Nbig = 200000
isP = sieve_primes(Nbig)
primes = np.nonzero(isP)[0]
Lam = np.zeros(Nbig+1)
for p in primes.tolist():
    lp = math.log(p); pk = p
    while pk <= Nbig:
        Lam[pk] = lp; pk *= p

def envelope_slope_in(coord, F, c0):
    m = coord > c0
    cc, FF = coord[m], np.abs(F[m]); rm = np.maximum.accumulate(FF); rm[rm<1e-9]=1e-9
    A = np.vstack([cc, np.ones_like(cc)]).T
    return np.linalg.lstsq(A, np.log(rm), rcond=None)[0][0]

fig2, axes = plt.subplots(1, 3, figsize=(15, 4.2))
print("\n=== log-free field test: place Λ(n)χ(n) by RADIUS R=√n (no log in placement) ===")
for ax, ch in zip(axes, CH):
    cf = np.array([ch['chi'](m) for m in range(Nbig+1)])
    Theta = np.cumsum(Lam*cf)                      # Σ_{n≤x} Λ(n)χ(n)
    n = np.arange(1, Nbig+1)
    R = np.sqrt(n.astype(float))                   # radial placement (1 unit apart in arc ⇒ R∝√n)
    main = n.astype(float) if ch['q'] == 1 else 0.0  # ψ(x) ≈ x main term (principal only)
    F = (Theta[1:] - main) / R                     # fluctuation field, √x-normalized
    F = F - F.mean()
    # envelope slope measured in the radial coordinate R (NOT in log)
    sR = envelope_slope_in(R, F, math.sqrt(Nbig)*0.1)
    # envelope slope measured in log-coordinate (the classical readout)
    u = np.log(n.astype(float)); slog = envelope_slope_in(u, F, 8.0)
    ax.plot(R[::50], F[::50], color='teal', lw=0.4)
    ax.set_title(f"{ch['name']}\nradial-coord slope={sR:+.3f}   log-coord slope={slog:+.3f}")
    ax.set_xlabel('radius R = √n'); ax.set_ylabel('(Θ)/R, centered')
    print(f"  {ch['short']:5s}: envelope slope in R (log-free) = {sR:+.4f}   |   in log-coord = {slog:+.4f}")
fig2.tight_layout(); fig2.savefig(f'{OUT}/helix_field_logfree.png', dpi=110)
print(f"saved {OUT}/helix_field_logfree.png")
print("\nHonest note: a flat envelope (slope ~0) = no radial drift = consistent with σ=½.")
print("If zeros are to be *extracted* (their γ's), the frequency analysis still lives in log R")
print("because R=√n ⇒ log R = ½ log n — that's where 'log' re-enters, in the readout, not the build.")
