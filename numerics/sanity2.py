import mpmath as mp

mp.mp.dps = 80

def L_chi3(s):
    return mp.power(3, -s) * (
        mp.zeta(s, mp.mpf(1)/3) - mp.zeta(s, mp.mpf(2)/3)
    )

def abs_L_chi3_y(y):
    s = mp.mpf("0.5") + 1j * mp.mpf(y)
    return abs(L_chi3(s))

# refine a zero ordinate near a guessed y
def refine_chi3_zero(y_guess):
    y0 = mp.mpf(y_guess)
    f = lambda y: mp.re(L_chi3(mp.mpf("0.5") + 1j*y))
    g = lambda y: mp.im(L_chi3(mp.mpf("0.5") + 1j*y))

    # For real primitive chi3, zeros on the critical line are better found
    # through a real-valued Hardy-style rotated function. This simple fallback
    # minimizes |L| locally.
    objective = lambda y: abs_L_chi3_y(y)

    # local search around guess
    return mp.findroot(
        lambda y: mp.im(L_chi3(mp.mpf("0.5") + 1j*y)),
        (y0 - mp.mpf("0.01"), y0 + mp.mpf("0.01"))
    )

import cmath
import math
from dataclasses import dataclass
from typing import Callable, Iterable, Optional


# ----------------------------
# Characters
# ----------------------------

def chi_mod3(n: int) -> complex:
    """Primitive real character mod 3."""
    r = n % 3
    if r == 1:
        return 1.0
    if r == 2:
        return -1.0
    return 0.0


def chi_mod4(n: int) -> complex:
    """Primitive real character mod 4."""
    r = n % 4
    if r == 1:
        return 1.0
    if r == 3:
        return -1.0
    return 0.0


def chi_mod5_order4(n: int) -> complex:
    """
    Example complex primitive character mod 5.
    Generator: chi(2)=i.
    Residues:
      1 -> 1
      2 -> i
      4 -> -1
      3 -> -i
      0 -> 0
    """
    r = n % 5
    table = {
        0: 0.0,
        1: 1.0,
        2: 1j,
        4: -1.0,
        3: -1j,
    }
    return table[r]


# ----------------------------
# Phasor model
# ----------------------------

def phasor_sum(
    y: float,
    chi: Callable[[int], complex],
    N: int,
    sigma: float = 0.5,
    smooth: bool = True,
    cutoff_scale: Optional[float] = None,
) -> complex:
    """
    Finite L-like phasor sum:

        C(y) = sum chi(n) n^(-sigma) exp(-i y log n)

    If smooth=True, applies exp(-n/cutoff_scale).
    This is not analytic continuation; it is a finite/smoothed sanity test.
    """
    if cutoff_scale is None:
        cutoff_scale = N / 3

    total = 0j

    for n in range(1, N + 1):
        c = chi(n)
        if c == 0:
            continue

        mag = n ** (-sigma)

        if smooth:
            mag *= math.exp(-n / cutoff_scale)

        phase = -y * math.log(n)
        total += c * mag * cmath.exp(1j * phase)

    return total


def scan_minima(
    y_min: float,
    y_max: float,
    steps: int,
    chi: Callable[[int], complex],
    N: int,
    sigma: float = 0.5,
    smooth: bool = True,
) -> list[tuple[float, float, complex]]:
    """
    Crude scan for local minima of |C(y)|.
    Returns [(y, abs(C), C), ...].
    """
    ys = [
        y_min + (y_max - y_min) * i / steps
        for i in range(steps + 1)
    ]

    vals = [
        phasor_sum(y, chi, N, sigma=sigma, smooth=smooth)
        for y in ys
    ]

    mags = [abs(v) for v in vals]

    out = []
    for i in range(1, len(ys) - 1):
        if mags[i] <= mags[i - 1] and mags[i] <= mags[i + 1]:
            out.append((ys[i], mags[i], vals[i]))

    return sorted(out, key=lambda x: x[1])


# ----------------------------
# Helix geometry
# ----------------------------

@dataclass
class HelixParams:
    pitch: float          # p, height per loop
    radial_growth: float  # r, radius increment per loop
    integer_spacing: float = math.pi / 3  # fixed scaling n -> n*pi/3


def loop_from_height(z: float, hp: HelixParams) -> float:
    return z / hp.pitch


def height_from_ordinate(y: float) -> float:
    return math.exp(y)


def helix_point_from_y(y: float, hp: HelixParams) -> tuple[float, float, float]:
    """
    Uses z=e^y, z=p*k, R=r*k.
    """
    z = math.exp(y)
    k = z / hp.pitch
    R = hp.radial_growth * k
    theta = 2 * math.pi * k

    x = R * math.cos(theta)
    yy = R * math.sin(theta)

    return x, yy, z

def helix_arclength(k, p, r):
    k = mp.mpf(k)
    p = mp.mpf(p)
    r = mp.mpf(r)

    A2 = p*p + r*r

    if r == 0:
        return mp.sqrt(A2) * k

    A = mp.sqrt(A2)
    B = 2 * mp.pi * r

    return (
        mp.mpf("0.5") * k * mp.sqrt(A2 + (B*k)**2)
        +
        A2 / (2*B) * mp.asinh(B*k / A)
    )


def arclength_to_loop(k: float, hp: HelixParams, steps: int = 20_000) -> float:
    """
    Numerical arclength:

        S(k)=∫ sqrt(p^2+r^2+(2πrt)^2) dt

    Simpson-ish midpoint integration.
    """
    p = hp.pitch
    r = hp.radial_growth

    if k <= 0:
        return 0.0

    h = k / steps
    total = 0.0

    for i in range(steps):
        t = (i + 0.5) * h
        density = math.sqrt(p*p + r*r + (2 * math.pi * r * t) ** 2)
        total += density * h

    return total


def integer_count_to_y(y: float, hp: HelixParams) -> float:
    """
    Continuous geometric integer index induced by arclength spacing pi/3.
    """
    z = math.exp(y)
    k = z / hp.pitch
    S = arclength_to_loop(k, hp)
    return S / hp.integer_spacing


def calibrate_ratio_for_wall(
    y: float,
    wall_N: float,
    q_lo: float = 0.0,
    q_hi: float = 1e-3,
    iters: int = 80,
) -> float:
    """
    Solves for q=r/p such that:

        wall_N * (pi/3)
        =
        ∫_0^{e^y} sqrt(1 + q^2 + (2π q x)^2) dx

    This determines r/p for one crossing wall.
    """
    z = math.exp(y)
    target_S = wall_N * math.pi / 3

    def S_of_q(q: float) -> float:
        # midpoint integral over height x
        steps = 40_000
        h = z / steps
        total = 0.0
        for i in range(steps):
            x = (i + 0.5) * h
            total += math.sqrt(1 + q*q + (2 * math.pi * q * x) ** 2) * h
        return total

    lo, hi = q_lo, q_hi

    while S_of_q(hi) < target_S:
        hi *= 2
        if hi > 10:
            raise RuntimeError("Could not bracket q")

    for _ in range(iters):
        mid = (lo + hi) / 2
        if S_of_q(mid) < target_S:
            lo = mid
        else:
            hi = mid

    return (lo + hi) / 2


# ----------------------------
# Example usage
# ----------------------------

if __name__ == "__main__":
    # First few known-ish ordinates for primitive chi mod 3, for sanity tests.
    # Use your trusted source / high-precision code for production.
    chi3_ys = [
        8.03973715568,
        11.24920620777,
        15.70461917672,
        18.261997,
        20.455771,
        24.059415,
    ]

    y1 = chi3_ys[0]
    z1 = math.exp(y1)

    print("first chi3 height exp(y1):", z1)

    # Fixed pi/3 integer scaling.
    vertical_index = z1 / (math.pi / 3)
    print("vertical index:", vertical_index)

    # Nearest mod-6 wall above the vertical index.
    wall_N = 6 * math.ceil(vertical_index / 6)
    print("chosen wall_N:", wall_N)

    q = calibrate_ratio_for_wall(y1, wall_N)
    print("calibrated q = r/p:", q)

    # Choose a loop normalization.
    # Example: first crossing at k=wall_N/6 loops.
    k1 = wall_N / 6
    p = z1 / k1
    r = q * p

    hp = HelixParams(pitch=p, radial_growth=r)

    print("pitch p:", p)
    print("radial growth r:", r)
    print("radius at first crossing:", r * k1)

    for y in chi3_ys[:3]:
        pt = helix_point_from_y(y, hp)
        N_geom = integer_count_to_y(y, hp)
        C = phasor_sum(y, chi_mod3, N=20_000, sigma=0.5, smooth=True)

        print()
        print("y:", y)
        print("height exp(y):", math.exp(y))
        print("helix point:", pt)
        print("continuous integer count:", N_geom)
        print("phasor abs:", abs(C))
        print("phasor value:", C)

    # Crude scan for phasor minima for chi3.
    minima = scan_minima(
        y_min=5.0,
        y_max=25.0,
        steps=2000,
        chi=chi_mod3,
        N=30_000,
        sigma=0.5,
        smooth=True,
    )

    print()
    print("lowest crude phasor minima:")
    for y, mag, val in minima[:10]:
        print(f"y={y:.6f}, |C|={mag:.6g}, C={val}")