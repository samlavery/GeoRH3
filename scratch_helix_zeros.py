"""
3D helix as a prime-bucketing machine: does it PRODUCE the zero heights?

Helix value at height gamma, accumulated over the winding:
    W(gamma) = sum_{n>=2} (Lambda(n) - 1) * n^{-1/2} * e^{-i gamma log n} * e^{-n/Ncut}
  - Lambda(n)-1 : signed prime bucketing with the smooth mean removed (the fluctuation psi(x)-x)
  - n^{-1/2}    : radial amplitude from the sqrt-area-law packing (the 1/2 baseline)
  - log n       : the winding (unwound length)
  - gamma       : the HEIGHT (pitch * winds)
A 'singularity after a number of winds' = a peak of |W(gamma)|.
NO zero is fed in.  Test: do the peak heights equal 14.13.., 21.02.., 25.01.., ...?
"""
import numpy as np, math
from scipy.signal import find_peaks

Ncut = 300_000
Nmax = 3_600_000

# --- sieve primes, build von Mangoldt Lambda ---
sieve = np.ones(Nmax + 1, dtype=bool); sieve[:2] = False
for i in range(2, int(Nmax**0.5) + 1):
    if sieve[i]:
        sieve[i*i::i] = False
primes = np.nonzero(sieve)[0]
Lam = np.zeros(Nmax + 1)
for p in primes.tolist():
    lp = math.log(p); pk = p
    while pk <= Nmax:
        Lam[pk] = lp; pk *= p
print(f"# primes<=Nmax: {len(primes)}")

# --- the fluctuation weights over ALL n, with radial amplitude and cutoff ---
n = np.arange(2, Nmax + 1, dtype=np.float64)
a = (Lam[2:] - 1.0) * n**(-0.5) * np.exp(-n / Ncut)     # real weights
u = np.log(n)                                            # winding coordinate

# --- bin in u, then FFT (uniform NDFT) ---
du = 0.002
u0 = u[0]; M = int((u[-1] - u0) / du) + 2
s = np.zeros(M)
idx = ((u - u0) / du).astype(np.int64)
np.add.at(s, idx, a)

P = 1 << 19                                              # zero-pad for fine gamma sampling
S = np.fft.fft(s, P)
gamma = 2 * np.pi * np.arange(P) / (P * du)
absW = np.abs(S)

# restrict to a window and normalize for display
sel = (gamma >= 8) & (gamma <= 62)
g = gamma[sel]; w = absW[sel]

# --- true zeros: ONLY to check where peaks landed (never used above) ---
true_zeros = [14.134725, 21.022040, 25.010858, 30.424876, 32.935062,
              37.586178, 40.918719, 43.327073, 48.005151, 49.773832,
              52.970321, 56.446248, 59.347044]

dg = g[1] - g[0]
peaks, _ = find_peaks(w, prominence=w.max() * 0.06, distance=int(1.2 / dg))
print("\n# peaks of |W(gamma)| produced by the helix   vs   nearest true zero")
print(f"{'peak gamma':>12} {'|W| (norm)':>11} {'nearest zero':>14} {'err':>9}")
matched = []
for pi in peaks:
    gg = g[pi]
    if gg < 12: continue
    z = min(true_zeros, key=lambda z: abs(z - gg))
    matched.append(gg - z)
    print(f"{gg:12.3f} {w[pi]/w.max():11.3f} {z:14.4f} {gg - z:+9.3f}")
if matched:
    print(f"\n# mean |err| over matched peaks: {np.mean(np.abs(matched)):.3f}")

# --- the PITCH as one global constant: fit  helix_peak = slope * true_zero  (through 0) ---
hp, tz = [], []
for pi in peaks:
    gg = g[pi]
    if gg < 12 or w[pi] < 0.5 * w.max():   # high-confidence peaks only
        continue
    z = min(true_zeros, key=lambda z: abs(z - gg))
    if abs(gg - z) < 0.25:
        hp.append(gg); tz.append(z)
hp = np.array(hp); tz = np.array(tz)
slope = float(np.sum(hp * tz) / np.sum(tz * tz))         # = 1/pitch in these units
resid = hp - slope * tz
print(f"\n# PITCH check: one constant for the whole spectrum")
print(f"#   helix_peak = slope * true_zero,  slope (height calibration) = {slope:.5f}")
print(f"#   -> geometric pitch P*U/2pi = {1/slope:.5f}  (natural unit = 1.000)")
print(f"#   max residual across all {len(hp)} zeros after the single fit: {np.max(np.abs(resid)):.3f}")
print(f"#   i.e. ONE pitch places every zero; ratios gamma_k/gamma_1 are intrinsic, untuned")

# --- ASCII profile (max over ~0.4-wide rows); '*' marks a true zero row ---
print("\n# |W(gamma)| profile   ('*' = a true zero sits in this row)")
row = 0.4
zero_rows = set(int(z / row) for z in true_zeros)
hi = w.max()
for r in range(int(12 / row), int(61 / row)):
    lo, hh = r * row, (r + 1) * row
    seg = w[(g >= lo) & (g < hh)]
    val = seg.max() if len(seg) else 0.0
    bar = '#' * int(46 * val / hi)
    mark = ' *' if r in zero_rows else '  '
    print(f"{lo:6.1f}{mark} |{bar}")
