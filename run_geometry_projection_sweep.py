#!/usr/bin/env python3
"""
run_geometry_projection_sweep.py

Geometry-side test.

Question:
  Is the correct L-function projection the pure area/count law,
  the exact arc-radius law, or an interpolation between them?

We test a one-parameter projection family:

  log R_alpha(n)
    = (1-alpha) log R_area(n) + alpha log R_exact(n)

  alpha = 0 -> area/count projection:
      R_area(n)^2 = (e^mode * U / pi) n

  alpha = 1 -> exact geometric arc projection:
      arc(n)=nU
      arc(n)=∫_0^k sqrt(slope^2 + (2π slope t)^2 + U^2) dt
      R_exact(n)=slope*k(n)

For each alpha:
  L-style response dips:
      S_L = Σ χ(n)/R(n) exp(-iγ 2logR(n))

  pole-style response peaks:
      S_P = Σ log(p)χ(p^a)/R(p^a) exp(-iγ 2logR(p^a))

  self-dual emits:
      persistent L-dip with nearby persistent pole-peak

Metrics:
  - reference zero matches, RMS
  - number of persistent dips
  - number of self-dual filtered emits
  - mean dip->nearest peak distance

Source is still log-free.
Log appears only in projection readout 2logR.
"""

import math
import numpy as np


# ----------------------------
# Characters
# ----------------------------

class Char:
    def __init__(self, q, vals, name):
        self.q = int(q)
        self.vals = {int(k): complex(v) for k, v in vals.items()}
        self.name = name

    def chi(self, n):
        n = np.asarray(n, dtype=np.int64)
        return np.array([self.vals[int(x % self.q)] for x in n], dtype=complex)


CHARS = {
    "zeta": Char(1, {0: 1}, "zeta"),
    "chi3": Char(3, {0: 0, 1: 1, 2: -1}, "chi3"),
    "chi4": Char(4, {0: 0, 1: 1, 2: 0, 3: -1}, "chi4"),
    "chi8": Char(8, {0: 0, 1: 1, 2: 0, 3: -1, 4: 0, 5: -1, 6: 0, 7: 1}, "chi8"),
}

PARAMS = {
    "zeta": (math.pi / 6, 3),
    "chi3": (math.pi / 3, 6),
    "chi4": (math.pi / 2, 8),
    "chi8": (math.pi, 12),
}

REF = {
    "zeta": np.array([
        14.1347251417,21.0220396388,25.0108575801,30.4248761259,
        32.9350615877,37.5861781588,40.9187190121,43.3270732809,
        48.0051508812,49.7738324777,52.9703214777,56.4462476971,
        59.3470440026,60.8317785246,65.1125440481,67.0798105295,
        69.5464017112,72.0671576745,75.7046906991,77.1448400689,
    ]),
    "chi3": np.array([
        8.0397371556,11.2492067376,15.7046191755,18.2619977877,
        20.4557709554,24.0594141888,26.577868,28.218189,
        30.74505,33.897363,35.608410,37.551800,39.485253,
        42.616405,44.120631,46.274132,47.514120,
    ]),
    "chi8": np.array([
        4.899974,7.628429,10.806588,12.310543,15.195754,17.022286,
        18.805959,21.131646,23.083850,24.201964,26.958535,28.097445,
        29.930764,31.638139,33.845631,34.745777,36.541664,38.775578,
        39.786881,41.342206,
    ]),
}


# ----------------------------
# Prime powers
# ----------------------------

def primes_upto(N):
    s = np.ones(N + 1, dtype=bool)
    s[:2] = False
    for i in range(2, int(N**0.5) + 1):
        if s[i]:
            s[i*i::i] = False
    return np.nonzero(s)[0]


def prime_power_triples(N):
    out = []
    for p in primes_upto(N):
        p = int(p)
        q = p
        a = 1
        while q <= N:
            out.append((p, a, q))
            q *= p
            a += 1
    return out


# ----------------------------
# Radius laws
# ----------------------------

_RADIUS_CACHE = {}

def helix_arc(k, U, slope):
    """
    Exact arc length:
      ∫ sqrt((2π slope t)^2 + slope^2 + U^2) dt
    """
    a = 2 * math.pi * slope
    b = math.sqrt(slope*slope + U*U)
    k = np.asarray(k, dtype=float)
    return (
        0.5 * k * np.sqrt((a*k)**2 + b*b)
        + (b*b / (2*a)) * np.arcsinh(a*k / b)
    )


def exact_radius_table(N, U, mode, grid_steps=80_000):
    key = (int(N), float(U), int(mode), int(grid_steps))
    if key in _RADIUS_CACHE:
        return _RADIUS_CACHE[key]

    slope = math.exp(mode)
    max_arc = N * U
    kmax = math.sqrt(max_arc / (math.pi * slope)) * 1.35 + 2.0

    kg = np.linspace(0.0, kmax, grid_steps + 1)
    sg = helix_arc(kg, U, slope)

    arcs = np.arange(1, N + 1, dtype=float) * U
    k = np.interp(arcs, sg, kg)
    R = slope * k

    _RADIUS_CACHE[key] = R
    return R


def area_radius_table(N, U, mode):
    C = math.exp(mode) * U / math.pi
    n = np.arange(1, N + 1, dtype=float)
    return np.sqrt(C * n)


def blended_radius_table(N, U, mode, alpha):
    R_area = area_radius_table(N, U, mode)
    if alpha == 0:
        return R_area

    R_exact = exact_radius_table(N, U, mode)

    if alpha == 1:
        return R_exact

    return np.exp((1 - alpha) * np.log(R_area) + alpha * np.log(R_exact))


# ----------------------------
# Events and responses
# ----------------------------

def l_events(ch, U, mode, N, alpha):
    n = np.arange(1, N + 1, dtype=np.int64)
    chi = ch.chi(n)
    keep = np.abs(chi) > 1e-12

    Rall = blended_radius_table(N, U, mode, alpha)

    n = n[keep]
    chi = chi[keep]
    R = Rall[n - 1]

    phase = 2.0 * np.log(R)
    amp = chi / R
    return phase, amp, n


def pole_events(ch, U, mode, N, alpha):
    Rall = blended_radius_table(N, U, mode, alpha)

    phase = []
    amp = []
    qvals = []

    for p, a, q in prime_power_triples(N):
        cq = ch.chi(np.array([q]))[0]
        if abs(cq) < 1e-12:
            continue

        R = float(Rall[q - 1])
        phase.append(2.0 * math.log(R))
        amp.append(math.log(p) * cq / R)
        qvals.append(q)

    return np.array(phase), np.array(amp, dtype=complex), np.array(qvals, dtype=np.int64)


def response(gammas, phase, amp, chunk=512):
    y = np.empty(len(gammas), dtype=float)
    for i in range(0, len(gammas), chunk):
        gg = gammas[i:i+chunk]
        y[i:i+chunk] = np.abs(
            (amp[None, :] * np.exp(-1j * np.outer(gg, phase))).sum(axis=1)
        )
    return y


def local_dips(gammas, y, max_rel=0.95):
    mx = float(y.max())
    idx = np.where(
        (y[1:-1] < y[:-2])
        & (y[1:-1] < y[2:])
        & (y[1:-1] < max_rel * mx)
    )[0] + 1
    return gammas[idx]


def local_peaks(gammas, y, min_rel=0.02):
    mx = float(y.max())
    idx = np.where(
        (y[1:-1] > y[:-2])
        & (y[1:-1] > y[2:])
        & (y[1:-1] > min_rel * mx)
    )[0] + 1
    return gammas[idx]


def persistent(sets, tol=0.30):
    base = sets[-1]
    keep = []
    for x in base:
        if all(len(s) and np.min(np.abs(s - x)) < tol for s in sets):
            keep.append(x)
    return np.array(keep)


def match_dips_to_peaks(dips, peaks, tol=0.30):
    out = []
    dists = []

    for d in np.sort(dips):
        if len(peaks) == 0:
            continue
        dist = float(np.min(np.abs(peaks - d)))
        if dist < tol:
            out.append(d)
            dists.append(dist)

    return np.array(out), np.array(dists)


def score(modes, refs, gamma_max, tol=0.50):
    refs = refs[refs < gamma_max]
    rows = []
    for z in refs:
        if len(modes) == 0:
            continue
        d = modes[np.argmin(np.abs(modes - z))]
        if abs(d - z) < tol:
            rows.append((z, d, d - z))

    rms = float(np.sqrt(np.mean([e*e for _, _, e in rows]))) if rows else float("nan")
    return rows, rms, len(refs)


def test_alpha(name, alpha, gamma_max, step, cutoffs):
    ch = CHARS[name]
    U, mode = PARAMS[name]
    gammas = np.arange(1.0, gamma_max, step)

    dip_sets = []
    peak_sets = []

    for N in cutoffs:
        phase, amp, _ = l_events(ch, U, mode, N, alpha)
        y = response(gammas, phase, amp)
        dip_sets.append(local_dips(gammas, y))

    for N in cutoffs:
        phase, amp, _ = pole_events(ch, U, mode, N, alpha)
        y = response(gammas, phase, amp)
        peak_sets.append(local_peaks(gammas, y))

    dips = persistent(dip_sets)
    peaks = persistent(peak_sets)
    filtered, dists = match_dips_to_peaks(dips, peaks)

    mean_dist = float(np.mean(dists)) if len(dists) else float("nan")

    rows = []
    rms = float("nan")
    total = 0
    if name in REF:
        rows, rms, total = score(filtered, REF[name], gamma_max)

    return {
        "alpha": alpha,
        "dips": dips,
        "peaks": peaks,
        "filtered": filtered,
        "match_count": len(rows),
        "ref_total": total,
        "rms": rms,
        "mean_dip_peak_dist": mean_dist,
    }


def run_channel(name, gamma_max=60.0, step=0.03, cutoffs=(3000, 10000)):
    U, mode = PARAMS[name]
    print("=" * 96)
    print(f"{name}: U={U:.9f}, mode={mode}")
    print("alpha=0 area/count projection; alpha=1 exact arc-radius projection")
    print("alpha   dips  peaks  filtered  refmatch     RMS     mean|dip-peak|   first filtered")

    for alpha in [0.0, 0.10, 0.25, 0.50, 0.75, 0.90, 1.0]:
        r = test_alpha(name, alpha, gamma_max, step, cutoffs)

        print(
            f"{alpha:4.2f} "
            f"{len(r['dips']):6d} "
            f"{len(r['peaks']):6d} "
            f"{len(r['filtered']):9d} "
            f"{r['match_count']:4d}/{r['ref_total']:<4d} "
            f"{r['rms']:9.5f} "
            f"{r['mean_dip_peak_dist']:15.5f} "
            f"{np.round(r['filtered'][:10], 3)}"
        )

    print()


def main():
    # Focused defaults. Add zeta if desired; it is slower/noisier.
    run_channel("chi3", gamma_max=60.0, step=0.03, cutoffs=(3000, 10000))
    run_channel("chi8", gamma_max=60.0, step=0.03, cutoffs=(3000, 10000))
    run_channel("zeta", gamma_max=80.0, step=0.03, cutoffs=(3000, 10000))

    print("=" * 96)
    print("Interpretation:")
    print("  Best geometry is the alpha with high refmatch, low RMS, and low dip-peak distance.")
    print("  If alpha=0 wins, the L-readout is area/count projection.")
    print("  If alpha>0 wins, exact helix curvature contributes to the projection.")


if __name__ == '__main__':
    main()
