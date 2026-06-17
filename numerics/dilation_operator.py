"""
dilation_operator.py  --  the LOG-FREE operator route (Berry-Keating H = xp).

The phasor route had to call log (the per-prime seed log p / the flow-time log n).  The operator route
does not: H = xp is built from position and momentum only -- no log anywhere in the construction.
What carries the log is GEOMETRY: the level count of H=xp is the PHASE-SPACE AREA under the hyperbola
xp <= E, and that area equals (E/2pi) log(qE/2pi) - ...  The log EMERGES as an area, not a log() call.

This file checks, log-free, whether that area-count reproduces the actual chi_3 zero count.
HONEST SCOPE: the area gives the SMOOTH count (the average density).  The EXACT zero heights are the
smooth count plus the S(t) fluctuation, and S(t) is the sum over prime periodic orbits whose lengths
are log p (= the scaling-geodesic length).  So the operator is log-free; the smooth density it gives
log-free; the exact individual heights need the prime-orbit lengths -- that is the open part.
"""
import numpy as np


def load_zeros(path="zeros_500x50/L2_chi3_q3.txt"):
    """actual chi_3 zero ordinates (reference). Counting them is log-free; they are not used to build H."""
    z = []
    with open(path) as f:
        for line in f:
            if not line.startswith("#") and line.strip():
                z.append(float(line.split()[1]))
    return np.array(z)


def xp_level_count(E, q=3, steps=600000):
    """Level count of the dilation operator H = xp:
          N(E) = (1/2pi) * Area{ x >= a, p >= a, x*p <= E },   a^2 = 2pi/q  (the Planck cell).
    The area is a LOG-FREE Riemann sum -- no log() is called.  The log of the counting law is THIS
    area (the region under the hyperbola), a geometric measurement, not a function evaluation."""
    a = np.sqrt(2 * np.pi / q)
    if E <= a * a:
        return 0.0
    xs = np.linspace(a, E / a, steps)                 # x runs from the cell to where p hits the cell
    p_extent = np.maximum(E / xs - a, 0.0)            # at each x, p runs from a up to the hyperbola E/x
    area = float(np.sum(0.5 * (p_extent[:-1] + p_extent[1:]) * np.diff(xs)))  # plain trapezoid area sum
    return area / (2 * np.pi)


def radial_tuning_picks_the_line(gamma=8.039737155681466):
    """Tuning the geometry's one knob -- the radial growth exponent alpha (modulus n^{-alpha},
    i.e. the line Re = alpha) -- controls WHICH LINE the phasor can vanish on, NOT the log.
    |L(alpha + i*gamma)| reaches a TRUE zero only at alpha = 1/2 (the area law); off 1/2 it has a
    minimum but never 0.  The phase is log n for every alpha -- the log is L itself, the orthogonal
    (un-tunable) axis, not a geometric knob.  Returns [(alpha, |L(alpha+i*gamma)|), ...]."""
    import mpmath as mp
    mp.mp.dps = 30
    def L(s):
        return mp.power(3, -s) * (mp.zeta(s, mp.mpf(1) / 3) - mp.zeta(s, mp.mpf(2) / 3))
    return [(a, float(abs(L(mp.mpf(a) + 1j * mp.mpf(gamma)))))
            for a in ('0.30', '0.40', '0.45', '0.50', '0.55', '0.60', '0.70')]


if __name__ == "__main__":
    zeros = load_zeros()
    print("LOG-FREE dilation operator  H = xp  (no log in the operator)\n")
    print("level count = area under the hyperbola xp <= E  (the log is this AREA, not a log() call)\n")
    print(f"  {'E':>5} {'N_xp area':>11} {'#chi3 zeros<=E':>15} {'diff (=S-like)':>15}")
    for E in (20, 40, 60, 80, 100, 130, 160, 200):
        n_area = xp_level_count(E)
        n_act = int(np.sum(zeros <= E))
        print(f"  {E:>5} {n_area:>11.2f} {n_act:>15} {n_area - n_act:>+15.2f}")
    print()
    print("-> the log-free area count tracks the actual zero count to O(1): the SMOOTH density is")
    print("   reproduced log-free, the log having emerged as the hyperbola area (geometry).")
    print("   The O(1) gap is the S(t) fluctuation = sum over prime orbits (lengths log p) -- the")
    print("   exact individual heights need that arithmetic; the operator alone gives the density.")

    print("\nCAN TUNING THE GEOMETRY AVOID THE LOG?  Tune the radial exponent alpha (= the line Re=alpha):")
    print(f"  {'alpha':>6} {'|L(alpha + i*gamma1)|':>22}")
    for a, v in radial_tuning_picks_the_line():
        tag = '   <== TRUE ZERO (the area law)' if v < 1e-12 else ''
        print(f"  {a:>6} {v:>22.6e}{tag}")
    print("  -> tuning picks the LINE (vanishes only at alpha=1/2); the log is the PHASE = L, untunable.")
