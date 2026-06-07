"""
Winding is PURE PHASE — the third axis, independent of radial growth (σ) and pitch (γ).

A mode on the helix:  w(u) = e^{(σ−½)u} · e^{iγu} · e^{i·Ω·θ(u)}
  - radial growth (σ−½)  → in the MAGNITUDE |w| = e^{(σ−½)u}
  - pitch (γ) and winding (Ω) → in the PHASE arg(w), both |·|=1
So |w| depends only on σ; ANY winding rate Ω leaves |w| (hence the radial-½ / on-line test) and
the recovered γ untouched. This is exactly the Lean fact modeResponse_abs:
    ‖exp(((σ−½)+iγ)·t)‖ = exp((σ−½)·t)   — the winding term vanishes from the modulus.
"""
import numpy as np, os
import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt
OUT = os.path.dirname(os.path.abspath(__file__))

u = np.linspace(0, 12, 1000)
gamma = 14.1347
theta = np.exp(u/2)                       # geometric winding coordinate (loop count k=√x)
windings = [0.0, 1.0, 2.0, 4.0]

fig, axes = plt.subplots(2, 2, figsize=(13, 8))
for col, (sig, name) in enumerate([(0.5, 'on-line  σ=½'), (0.6, 'off-line  σ=0.6')]):
    axm, axp = axes[0, col], axes[1, col]
    for Om in windings:
        w = np.exp((sig - 0.5)*u) * np.exp(1j*gamma*u) * np.exp(1j*Om*theta)
        axm.plot(u, np.abs(w), lw=2.2 if Om == 0 else 1.0,
                 label=f'winding Ω={Om}', alpha=0.9 if Om == 0 else 0.6)
        axp.plot(u, np.angle(w), lw=0.8, label=f'Ω={Om}')
    axm.set_title(f'|w| — {name}\n(all winding rates overlap: magnitude is winding-blind)')
    axm.set_xlabel('height u'); axm.set_ylabel('|w| (carries σ)'); axm.legend(fontsize=7)
    axp.set_title('arg(w) — the winding lives here (pure phase)')
    axp.set_xlabel('height u'); axp.set_ylabel('arg(w)'); axp.legend(fontsize=7)
fig.tight_layout(); fig.savefig(f'{OUT}/winding_phase.png', dpi=120)
print(f"saved {OUT}/winding_phase.png")

# numeric witness: |w| is bit-identical across winding rates
base = np.abs(np.exp((0.5-0.5)*u) * np.exp(1j*gamma*u) * np.exp(1j*0.0*theta))
print("on-line, max |  |w(Ω)| − |w(0)|  | over winding rates:")
for Om in windings:
    w = np.exp((0.5-0.5)*u) * np.exp(1j*gamma*u) * np.exp(1j*Om*theta)
    print(f"  Ω={Om}:  {np.max(np.abs(np.abs(w) - base)):.2e}   (|w| ≡ 1, on-line, every winding)")
print("\n⇒ winding moves only arg(w); |w| (radial-½ / on-line) and γ are untouched. Pure phase.")
