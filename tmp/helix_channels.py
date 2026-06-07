"""
Plan B — channel-family computation across helix units.

For each helix unit (channel), build L(s,χ) from its character via Hurwitz zeta, show its
zeros land where expected (|L(½+it)| dips), confirm the on-circle discriminator |w(ρ)|=1 ⟺
Re ρ = ½, and run the injected-warp test (a synthetic off-line defect tilts the envelope).

Channels (helix unit π/d ↔ radial e^mode ↔ character):
    ζ   : π/6, e^3, trivial (mod 1)
    χ₃  : π/3, e^6, odd mod 3
    χ₄  : π/2, e^8, odd mod 4
"""
import numpy as np, mpmath as mp, math, os
import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt
mp.mp.dps = 15
OUT = os.path.dirname(os.path.abspath(__file__))

def make_char(q, plus, minus):
    def chi(n):
        r = n % q
        if r in plus: return 1
        if r in minus: return -1
        return 0
    return chi

CH = [
  dict(name='ζ  (trivial, mod 1)', short='zeta', q=1, chi=(lambda n: 1), unit='π/6', mode=3,
       zeros=[14.134725,21.022040,25.010858,30.424876,32.935062,37.586178,40.918719]),
  dict(name='χ₃ (odd, mod 3)', short='chi3', q=3, chi=make_char(3,{1},{2}), unit='π/3', mode=6,
       zeros=[8.0397,11.2492,15.7046,18.2620,20.4558,24.0594,26.5779]),
  dict(name='χ₄ (odd, mod 4)', short='chi4', q=4, chi=make_char(4,{1},{3}), unit='π/2', mode=8,
       zeros=[6.0209,10.2438,12.9881,16.3426,18.2920,21.4506,23.2784]),
]

def Lfun(ch):
    q, chi = ch['q'], ch['chi']
    if q == 1:
        return lambda s: mp.zeta(s)
    return lambda s: q**(-s) * mp.fsum(chi(r) * mp.zeta(s, mp.mpf(r)/q) for r in range(1, q+1))

# ---------- 1. |L(½+it)| dips at the zeros, one panel per helix unit ----------
ts = np.linspace(2.0, 42.0, 900)
fig, axes = plt.subplots(len(CH), 1, figsize=(11, 9))
print("=== zero recovery per helix unit (detected dip vs known zero) ===")
for ax, ch in zip(axes, CH):
    L = Lfun(ch)
    vals = np.array([abs(complex(L(mp.mpf('0.5') + 1j*mp.mpf(float(t))))) for t in ts])
    ax.semilogy(ts, vals, color='steelblue', lw=0.9)
    # detect local minima as candidate zeros
    mins = [ts[i] for i in range(1, len(ts)-1) if vals[i] < vals[i-1] and vals[i] < vals[i+1]
            and vals[i] < 0.5]
    print(f"\n{ch['short']}  (unit {ch['unit']}, radial e^{ch['mode']}):")
    for z in ch['zeros']:
        if mins:
            d = min(mins, key=lambda m: abs(m-z))
            print(f"   known γ={z:8.4f}   detected={d:8.4f}   |Δ|={abs(d-z):.4f}")
        ax.axvline(z, color='crimson', ls='--', lw=0.8)
    ax.set_title(f"{ch['name']}   —   helix unit {ch['unit']},  radial e^{ch['mode']}   "
                 f"(blue dip = zero, red = known γ)")
    ax.set_xlabel('height t'); ax.set_ylabel('|L(½+it)|'); ax.set_xlim(2, 42)
fig.tight_layout(); fig.savefig(f'{OUT}/helix_channels_zeros.png', dpi=110)
print(f"\nsaved {OUT}/helix_channels_zeros.png")

# ---------- 2. the on-circle discriminator |w(ρ)|=1 ⟺ Re ρ=½ (channel-independent) ----------
fig2, (axd, axw) = plt.subplots(1, 2, figsize=(12, 4.5))
sig = np.linspace(0.0, 1.0, 400)
for g in [8.0, 14.1, 21.0]:
    w = np.array([abs(1 - 1/(s + 1j*g)) for s in sig])
    axd.plot(sig, w, lw=1.1, label=f'γ={g}')
axd.axhline(1.0, color='k', ls=':', lw=0.8); axd.axvline(0.5, color='crimson', ls='--', lw=0.8)
axd.set_title('discriminator  |w(ρ)| = |1−1/ρ|  = 1  ⟺  Re ρ = ½')
axd.set_xlabel('σ = Re ρ'); axd.set_ylabel('|w(ρ)|'); axd.legend(fontsize=8)

# ---------- 3. injected-warp test: a synthetic off-line defect tilts the envelope ----------
u = np.linspace(4, 26, 4000)
# on-line field: sum of unit-modulus zero modes (flat envelope)
zg = CH[0]['zeros']
F_on = sum(2*np.cos(g*u)/abs(0.5+1j*g) for g in zg)
def env_slope(u, F):
    rm = np.maximum.accumulate(np.abs(F)); rm[rm < 1e-9] = 1e-9
    A = np.vstack([u, np.ones_like(u)]).T
    return np.linalg.lstsq(A, np.log(rm), rcond=None)[0][0]
axw.plot(u, F_on, color='seagreen', lw=0.5, label=f'on-line: slope {env_slope(u,F_on):+.3f}')
for s0, col in [(0.6, 'darkorange'), (0.7, 'crimson')]:
    F_warp = F_on + np.cos(14.1347*u) * np.exp((s0-0.5)*u)
    axw.plot(u, F_warp, color=col, lw=0.4, alpha=0.8,
             label=f'warp σ₀={s0}: slope {env_slope(u,F_warp):+.3f} (→{0.5+env_slope(u,F_warp):.2f})')
axw.set_title('injected-warp discriminator: off-line defect tilts the √x envelope by σ₀−½')
axw.set_xlabel('height u'); axw.set_ylabel('field'); axw.legend(fontsize=8)
fig2.tight_layout(); fig2.savefig(f'{OUT}/helix_discriminator.png', dpi=110)
print(f"saved {OUT}/helix_discriminator.png")

print("\n=== injected-warp readout (envelope slope = measured σ−½) ===")
print(f"  on-line          : slope {env_slope(u,F_on):+.4f}  -> σ ~ {0.5+env_slope(u,F_on):.4f}")
for s0 in [0.6, 0.7]:
    F_warp = F_on + np.cos(14.1347*u) * np.exp((s0-0.5)*u)
    print(f"  warp σ₀={s0}      : slope {env_slope(u,F_warp):+.4f}  -> σ ~ {0.5+env_slope(u,F_warp):.4f}")
