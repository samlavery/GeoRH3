"""
radial_step_scan.py

Diagnose WHERE the radial-step helix's phasor collapse lives.  The geometric
radial stepping earns z ~ log(n) at the LOOP level, but integers within a loop
share nearly the same height, so the per-integer phase is coarse.  Here we make
height advance PER INTEGER and densely scan w to see whether the collapse minima
coincide with the chi3 zeros (the MEAN) and/or track each individual zero (the
FLUCTUATION).

Two builds:
  (A) PER-INTEGER LOG HEIGHT, area-law radius.  z_n = log(n) earned as the
      cumulative arc-on-cone height; amplitude n^{-1/2}.  This is the analytic
      object made geometric -- expect it to collapse AT the zeros (mean + fluct),
      because phase=log(n) exactly.  Sanity that the machinery reproduces L.
  (B) BLOCKY STEPPED HEIGHT: height is piecewise-constant per block (pitch steps
      at each zero), radius steps per block.  Test whether STEPPING (not smooth
      log) still hits the zeros -- the real question.
"""
import numpy as np
import mpmath as mp
mp.mp.dps = 25

def chi3(n):
    r = n % 3
    return 1.0 if r == 1 else (-1.0 if r == 2 else 0.0)

def load_zeros(path="lchi3_zeros_1000.txt", k=20):
    g = []
    with open(path) as f:
        for ln in f:
            ln = ln.strip()
            if ln and not ln.startswith("#"):
                g.append(float(ln.split()[1]))
    return np.array(sorted(g))[:k]
GAMMA = load_zeros(k=20)

def phasor_resultant(phase, amp, sign, w):
    a = w * phase
    Vx = np.sum(sign * amp * np.cos(a)); Vy = np.sum(sign * amp * np.sin(a))
    return np.hypot(Vx, Vy)

# ---------------- BUILD A: per-integer log height (geometric, area-law) -------
N = 40000
n = np.arange(1, N + 1).astype(float)
sign = np.array([chi3(int(k)) for k in n])
# area-law cone: arc-spacing constant ds, radius R=A*phi linear -> s ~ (A/2)phi^2,
# integer n at s_n = n*ds -> phi_n ~ sqrt(n), R_n ~ sqrt(n).  Height = log(arc-area).
# The EARNED per-integer log height: z_n = log(n) (= log swept count). amp = n^{-1/2}.
R = np.sqrt(n)
z = np.log(n)        # earned log height, per integer
amp = 1.0 / R        # = n^{-1/2}
phi = np.cumsum(1.0 / R) * 2  # winding ~ 2*sqrt(n) (area law) -- recorded, not used as phase

def build_grid(ws, phase, amp, sign):
    return np.array([phasor_resultant(phase, amp, sign, w) for w in ws])

print("=" * 78)
print("BUILD A: per-integer EARNED log height as phasor phase (z=log n, amp=n^-1/2)")
print("=" * 78)
print("This is the area-law cone with log height; phase=log(n) is earned per integer.")
print(f"{'gamma':>9} {'|resultant|':>12}   vs nearby off-zero minima")
for g in GAMMA[:10]:
    print(f"{g:9.3f} {phasor_resultant(z, amp, sign, g):12.5f}")

# dense scan: do the MINIMA of |resultant(w)| sit at the zeros?
ws = np.linspace(6.0, 35.0, 6000)
vals = build_grid(ws, z, amp, sign)
# find local minima
mins = []
for i in range(1, len(ws)-1):
    if vals[i] < vals[i-1] and vals[i] < vals[i+1] and vals[i] < 0.5:
        mins.append((ws[i], vals[i]))
print()
print(f"--- local minima of |resultant(w)| below 0.5 (BUILD A) ---")
print("These should land on the gamma_k if phase=log(n) reproduces L:")
for w, v in mins[:25]:
    # nearest zero
    j = np.argmin(np.abs(GAMMA - w))
    d = w - GAMMA[j]
    print(f"  w={w:8.4f}  |res|={v:.5f}   nearest gamma={GAMMA[j]:.4f}  (dw={d:+.4f})")
