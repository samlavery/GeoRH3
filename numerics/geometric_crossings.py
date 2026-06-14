"""
geometric_crossings.py -- zero crossings as a geometric HEIGHT on the 3D helix, then projected
3D --> 2D unit circle --> 1D.  Everything is built in the pi/3 chart; the 3D stage is log-free.

THE OBJECT (one ruleset; only the character chi mod q changes):

  3D.  Integer n is a POINT ON THE 3D HELIX -- it winds, grows, and climbs:
         winding   phi_n = 2*sqrt(n)          (from the radial growth + equal-arc placement)
         radius    R_n   = A * phi_n  ~ sqrt(n)   (RADIAL GROWTH, A = pi/6)
         climb     z_n   = (pitch / 2pi) * phi_n   (the CLIMB: pitch accumulated over the turns)
         point     (x, y, z) = (R cos phi, R sin phi, z)
       The HEIGHT is the climb z.  It is a raw 3D coordinate, built from the radial growth (which
       sets phi) and the pitch -- NO logarithm, and R^2 is NOT the height (R^2 = C*n only appears
       downstream, inside the projection's log).  The integers are on the curve, not on the axis:
       x, y wind around it.  With the canonical pitch = pi the climb is exactly z_n = sqrt(n).

  2D.  PROJECT the climb to the unit circle -- the log enters HERE, at the projection only:
         each integer -> the phasor  exp(-i w * log(z_n^2))  on S^1, carrying radial weight 1/R_n;
         the weighted resultant  F(w)  is the centroid.
       The pitch is a global phase on F (log(z^2) = log n + const), so it never moves a crossing --
       the crossings are pitch-independent; pitch only sets the height scale.

  1D.  The crossing height iy = the pitch w at which the phasors balance to the centre (|F| -> 0).
       That balance height IS the ordinate.  No S(t), no zero-count-plus-fluctuation, no gauge.

TAIL (geometric).  Past the last placed integer the climb continues as a continuum: the outer cone's
AREA INTEGRAL  x^{1-s}/(s-1) + x^{-s}/2  per residue class is the leading term.  The float finder
stops there; the high-precision finder adds the Bernoulli higher-order discreteness corrections of
the same cone (Euler-Maclaurin) -- the only way to reach 50 decimals from a short head.

HIGH PRECISION (crossing_hp / main_hp), constants from mp.pi (NEVER math.pi): A = pi/6, ds = pi/3,
pitch = pi, C = 2*A*ds.  Here the AMPLITUDE is set by the RESIDUAL COUNTING method and the CROSSING
by phasor cancellation:
  * amplitude = the running character-count residual  c_n = A(n) - m,  A(n) = sum_{k<=n} chi(k)
    (periodic, period q), m = -B_{1,chi} = L(0,chi) (pure arithmetic over one period).  Verified
    closure invariant: at a zero  |L_N(1/2+i gamma)| * sqrt(N) -> |A(N) - m|  (bounded/quantized);
    OFF a zero it diverges.  So the zero is "where the count residual stays bounded".
  * the response is c_n Abel-summed over the geometric phasors phi_n = (1/R_n) e^{-i w log z_n^2},
    plus the cone/E-M tail (the count's deep continuation); a finite-difference Newton finds where it
    cancels.  50 decimals, cross-checked against zeros_500x50/ (independent Hurwitz+Hardy-Z, 500x50dp).

HONEST NOTES (verified in __main__):
  * float crossings reproduce the certified ordinates to ~2e-4 (chi3..chi7); the hp crossings to
    ~1e-54.  This is a zero-FINDER built from the helix geometry; not a claim about where zeros lie.
  * the log at the projection is the one bridge (3D is log-free); everything else is the cone.
  * the radial growth fixes the climb's sqrt(n) shape; reading the climb off the LITERALLY placed
    spiral (area_exact=False) instead of the area-law ideal degrades it (the small-n transient).
"""
from __future__ import annotations

from dataclasses import dataclass
import math

import numpy as np

import helix3d                       # borrow: the canonical pi/3 helix (radial growth + placement)
import fiber                         # borrow: character specs, chi values, certified comparison set

A_GROWTH = helix3d.A_GROWTH          # radial growth rate, R = A * phi
ARC_SPACING = helix3d.ARC_SPACING    # equal-arc spacing ds
C_SCALE = 2.0 * A_GROWTH * ARC_SPACING   # R^2 = C*n  (a CONSEQUENCE of the radial growth, not the height)
PITCH = math.pi                      # canonical climb-per-turn (the quantum); with this, z = sqrt(n)


@dataclass(frozen=True)
class Crossing:
    """A balance height carried 3D -> 2D -> 1D."""
    index: int
    height: float            # 3D/1D: iy = the climb-pitch at which the phasors balance
    modulus: float           # 2D: |F(iy)|, the unit-circle centroid magnitude (-> 0)
    modulus_rel: float       # 2D: |F| / median|F|, how deep the balance is


class GeometricHelix:
    """Integers on the 3D pi/3 helix; height = climb; crossings = the balance pitches."""

    def __init__(self, spec: fiber.CharSpec, n_integers: int = 200_000,
                 pitch: float = PITCH, area_exact: bool = True):
        if spec.q == 1 or spec.principal:
            raise ValueError("principal/zeta needs the eta two-channel tail; use a primitive chi")
        self.spec = spec
        self.pitch = pitch
        self.M = int(n_integers)
        H = helix3d.Helix(helix3d.HelixParams(n_integers=n_integers, area_exact=area_exact))
        self.n = H.n
        self.phi = H.phi                                  # winding 2*sqrt(n): radial growth + placement
        self.R = H.R                                      # radius ~ sqrt(n): the radial growth
        self.x, self.y = H.x, H.y
        self.z = (pitch / (2.0 * math.pi)) * self.phi     # CLIMB = pitch over the turns; raw, log-free
        self.chi = np.array([complex(fiber.chi_val(spec, int(k) % spec.q))
                             for k in self.n.astype(np.int64)])

    # -- the 3D helix point of an integer (it is on the curve: x, y wind, z climbs) --------------
    def point(self, n: int) -> tuple[float, float, float]:
        i = int(n) - 1
        return float(self.x[i]), float(self.y[i]), float(self.z[i])

    # -- the geometric tail: the outer climb as a continuum (cone area integral), no Bernoulli ----
    def _tail(self, w: float) -> complex:
        s = 0.5 + 1j * w
        K = (self.pitch / (2.0 * math.pi)) ** 2 * (2.0 * ARC_SPACING / A_GROWTH)   # z^2 = K * n
        g = C_SCALE ** (-0.5) * np.exp(-1j * w * math.log(K))      # 1/R * e^{-i w log z^2} = g * n^{-s}
        q = self.spec.q
        start = self.M + 1
        out = 0j
        for r in range(1, q):
            c = complex(fiber.chi_val(self.spec, r))
            if c == 0:
                continue
            n0 = start + ((r - (start % q)) % q)
            x = n0 / q
            out += c * q ** (-s) * (x ** (1 - s) / (s - 1) + 0.5 * x ** (-s))
        return g * out

    # -- 3D climb -> 2D unit-circle collapse:  F(w) = sum_n (1/R_n) exp(-i w log z_n^2) + tail -----
    def response(self, w: float) -> complex:
        head = complex(np.sum(self.chi * (1.0 / self.R) * np.exp(-1j * w * np.log(self.z ** 2))))
        return head + self._tail(float(w))

    def response_grid(self, ws: np.ndarray) -> np.ndarray:
        ws = np.asarray(ws, dtype=float)
        arg = np.log(self.z ** 2)
        weight = self.chi / self.R
        head = np.array([complex(np.sum(weight * np.exp(-1j * float(w) * arg))) for w in ws])
        tail = np.array([self._tail(float(w)) for w in ws], dtype=complex)
        return head + tail

    # -- 1D: the heights where the projected phasors balance to the centre (|F| -> 0) -------------
    def find_crossings(self, w_hi: float = 26.0, step: float = 0.01,
                       thresh: float = 0.5) -> list[Crossing]:
        w_lo = 2.0 * math.pi / self.spec.q + 0.05
        ws = np.arange(w_lo, w_hi, step)
        mag = np.abs(self.response_grid(ws))
        med = float(np.median(mag))
        out: list[Crossing] = []
        for i in range(1, len(mag) - 1):
            if mag[i] < mag[i - 1] and mag[i] < mag[i + 1] and mag[i] < thresh * med:
                grid = np.linspace(ws[i] - step, ws[i] + step, 25)
                mg = np.abs(self.response_grid(grid))
                w = float(grid[int(np.argmin(mg))])
                f = abs(self.response(w))
                out.append(Crossing(index=len(out) + 1, height=w, modulus=f,
                                    modulus_rel=f / med if med else float("nan")))
        return out

    # -- 2D: the unit-circle picture at a height -- the placed phasors and their weighted centroid -
    def project_unit_circle(self, w: float, sample: int = 6) -> dict:
        phasor = np.exp(-1j * w * np.log(self.z ** 2))       # each integer -> a point on S^1
        weight = self.chi / self.R                            # radial weight 1/R, signed by chi
        centroid = complex(np.sum(weight * phasor))           # the resultant = F(w) head
        total = float(np.sum(np.abs(weight)))
        return {
            "centroid_modulus": abs(centroid),
            "balance_ratio": abs(centroid) / total if total else float("nan"),
            "sample_angles": [float(np.angle(phasor[k])) for k in range(sample)],
        }


# ============================================================================================
#  __main__ : the 3D points, the projection chain, the crossings vs certified, pitch-invariance
# ============================================================================================
def _certified(label: str, k: int) -> list[float]:
    return [float(x) for x in fiber._load_certified(label, k)]


def _top(count: int) -> float:
    return 6.0 + 3.2 * count


# ============================================================================================
#  HIGH PRECISION -- the same construction in mpmath; every constant from mp.pi (never math.pi)
# ============================================================================================
import mpmath as mp


def _hp_consts(dps: int) -> dict:
    """The pi/3-chart constants at `dps` digits, all from mp.pi.  pitch = pi (canonical)."""
    with mp.workdps(dps):
        pi = +mp.pi
        return {"pi": pi, "A": pi / 6, "ds": pi / 3, "pitch": pi, "C": 2 * (pi / 6) * (pi / 3)}


def _em_tail_hp(s, x, J: int, K: int = 8):
    """sum_{m>=0} (x+m)^{-s}: the cone area integral x^{1-s}/(s-1) (the geometric leading term),
    the boundary half-point x^{-s}/2, and the Bernoulli higher-order discreteness corrections of
    the same cone.  No mp.zeta."""
    head = mp.fsum((x + k) ** (-s) for k in range(K))
    X = x + K
    val = head + X ** (1 - s) / (s - 1) + X ** (-s) / 2
    poch = s
    for j in range(1, J + 1):
        val += mp.bernoulli(2 * j) / mp.factorial(2 * j) * poch * X ** (-s - 2 * j + 1)
        poch *= (s + 2 * j - 1) * (s + 2 * j)
    return val


def _count_baseline(spec: fiber.CharSpec):
    """The running-count machinery: A(n) = sum_{k<=n} chi(k) (periodic, period q) and its mean
    m = -B_{1,chi} = L(0,chi).  Both are pure arithmetic over one period -- no zeta, no L."""
    q = spec.q
    acc = mp.mpc(0)
    Aper = []
    for r in range(1, q + 1):
        acc += fiber.chi_val(spec, r % q)
        Aper.append(acc)                                 # A(1..q); A(n) = Aper[(n-1) % q]
    m = -mp.fsum(n * fiber.chi_val(spec, n % q) for n in range(1, q + 1)) / q
    return Aper, m


def _Dgeo_hp(spec: fiber.CharSpec, w, M: int, J: int, c: dict):
    """Geometric response at height w.  AMPLITUDE = the running character-count residual
    c_n = A(n) - m (the closure-invariant ledger), Abel-summed over the geometric placed-and-projected
    phasors phi_n = (1/R_n) e^{-i w log z_n^2}.  The CROSSING is where this sum cancels.  Equals
    C^{-1/2} L(chi, 1/2+iw); no mp.zeta.  (Identity: sum_n chi(n) phi_n = m*g + sum_n (A(n)-m)(phi_n -
    phi_{n+1}) + (A(M)-m) phi_M, so the count residual IS the amplitude envelope.)"""
    q = spec.q
    s = mp.mpf(1) / 2 + 1j * w
    M -= M % q
    A, pitch, pi, C, ds = c["A"], c["pitch"], c["pi"], c["C"], c["ds"]
    K = (pitch / (2 * pi)) ** 2 * (2 * ds / A)           # z^2 = K n  (= 1 at pitch = pi)
    g = C ** (mp.mpf(-1) / 2) * mp.e ** (-1j * w * mp.log(K))   # phi_n = g n^{-s}; |g| constant

    def phi(n):                                          # the placed-and-projected geometric phasor
        sq = mp.sqrt(n)
        R = 2 * A * sq                                   # radius = radial growth
        z2 = (pitch / (2 * pi)) ** 2 * (2 * sq) ** 2     # climb squared, z^2 = (pitch/2pi)^2 phi^2
        return (1 / R) * mp.e ** (-1j * w * mp.log(z2))

    Aper, m = _count_baseline(spec)
    phis = [phi(n) for n in range(1, M + 1)]
    # head: count residual c_n = A(n)-m as amplitude, Abel-summed over the phasor increments
    head = g * m
    for n in range(1, M):
        head += (Aper[(n - 1) % q] - m) * (phis[n - 1] - phis[n])
    head += (Aper[(M - 1) % q] - m) * phis[M - 1]
    # tail: the count's deep continuation (cone integral + Bernoulli, the residue buckets)
    tail = mp.mpc(0)
    for r in range(1, q):
        ch = fiber.chi_val(spec, r)
        if ch == 0:
            continue
        x = (mp.mpf(M) + r) / q
        tail += ch * q ** (-s) * _em_tail_hp(s, x, J)
    return head + g * tail


def crossing_hp(spec: fiber.CharSpec, seed, dps: int = 60, decimals: int = 50):
    """Refine a coarse crossing seed to `decimals` digits by finite-difference Newton on the
    geometric response.  All arithmetic at `dps`, constants from mp.pi.  Returns mp.mpf."""
    with mp.workdps(dps):
        c = _hp_consts(dps)
        w = mp.mpf(seed)
        absw = int(abs(float(seed)))
        M = spec.q * (20 + 2 * absw)
        J = max(20, int(0.6 * dps))
        h = mp.mpf(10) ** (-(dps // 2))
        for _ in range(40):
            D = _Dgeo_hp(spec, w, M, J, c)
            Dp = (_Dgeo_hp(spec, w + h, M, J, c) - _Dgeo_hp(spec, w - h, M, J, c)) / (2 * h)
            step = D / Dp
            w = mp.re(w - step)
            if abs(step) < mp.mpf(10) ** (-(decimals + 3)):
                break
        return +w


# the canonical comparison set: 500 zeros x 50 decimals, INDEPENDENT (Hurwitz zeta + Hardy Z) reference
COMPARE_DIR = "zeros_500x50"


def _compare_zeros(label: str, dps: int = 60) -> list:
    import os
    p = os.path.join(os.path.dirname(os.path.abspath(__file__)), COMPARE_DIR, f"{label}.txt")
    if not os.path.exists(p):
        return []
    with mp.workdps(dps):
        return [mp.mpf(l.split()[1]) for l in open(p) if not l.startswith("#")]


def main_hp(labels=("L2_chi3_q3", "L3_chi4_q4", "L4_chi5quad_q5", "L5_chi5c4_q5",
                    "L6_chi7quad_q7", "L7_chi8quad_q8", "L8_chi7c3_q7"),
            count: int = 5, dps: int = 60, decimals: int = 50):
    specmap = {s.label: s for s in fiber.SPECS}
    print("=" * 84)
    print(f"HIGH-PRECISION GEOMETRIC ZEROS  (constants from mp.pi, dps={dps}; each to {decimals} decimals)")
    print(f"compared against {COMPARE_DIR}/  (independent Hurwitz+Hardy-Z reference, 500 x 50dp)")
    print("=" * 84)
    worst = mp.mpf(0)
    for label in labels:
        spec = specmap[label]
        seeds = [c.height for c in
                 GeometricHelix(spec, n_integers=40_000).find_crossings(w_hi=_top(count))[:count]]
        ref = _compare_zeros(label, dps)
        print(f"\n{label}  (q={spec.q})")
        for i, seed in enumerate(seeds):
            z = crossing_hp(spec, seed, dps=dps, decimals=decimals)
            with mp.workdps(dps):
                print(f"  zero {i + 1}:  {mp.nstr(z, decimals + 1)}")
                if i < len(ref):
                    d = abs(z - ref[i])
                    worst = max(worst, d)
                    print(f"           |geometric - reference| = {mp.nstr(d, 3)}")
    print(f"\nworst |geometric - reference| over all shown zeros = {mp.nstr(worst, 3)}")

    # depth check: the same geometry at HEIGHT, against the 500x50 set (coarse seed -> 50 digits)
    print("\n" + "=" * 84)
    print("DEPTH CHECK  (chi3, deep indices; seeded from a coarse 6-digit value, refined geometrically)")
    print("=" * 84)
    spec = specmap["L2_chi3_q3"]
    ref = _compare_zeros("L2_chi3_q3", dps)
    for idx in (25, 100, 250, 500):
        if idx > len(ref):
            continue
        with mp.workdps(dps):
            coarse = mp.mpf(mp.nstr(ref[idx - 1], 6))     # a deliberately coarse 6-digit seed
            z = crossing_hp(spec, coarse, dps=dps, decimals=decimals)
            print(f"  zero #{idx:3d} (height ~{float(ref[idx-1]):7.2f}):  "
                  f"|geometric - reference| = {mp.nstr(abs(z - ref[idx - 1]), 3)}")


def main(labels=("L2_chi3_q3", "L3_chi4_q4", "L5_chi5c4_q5", "L6_chi7quad_q7"),
         count: int = 6, n_integers: int = 200_000):
    specmap = {s.label: s for s in fiber.SPECS}

    print("=" * 84)
    print("THE 3D HELIX  (integers ON the curve: x,y wind, z climbs;  height z = climb, log-free)")
    print("=" * 84)
    gh = GeometricHelix(specmap["L2_chi3_q3"], n_integers=n_integers)
    print(f"  climb z = (pitch/2pi)*phi,  pitch = pi  ->  z = sqrt(n)   (radial growth sets phi=2 sqrt n)")
    print(f"  {'n':>3} {'x':>9} {'y':>9} {'z=climb':>9}   {'R=growth':>9} {'phi=wind':>9}")
    for n in (1, 2, 4, 9, 16, 49):
        x, y, z = gh.point(n)
        i = n - 1
        print(f"  {n:>3} {x:9.4f} {y:9.4f} {z:9.4f}   {gh.R[i]:9.4f} {gh.phi[i]:9.4f}")

    print("\n" + "=" * 84)
    print("CROSSINGS = balance pitches (|F| collapse after the log-projection); one ruleset, every chi")
    print("=" * 84)
    for label in labels:
        spec = specmap[label]
        cr = GeometricHelix(spec, n_integers=n_integers).find_crossings(w_hi=_top(count))[:count]
        cert = _certified(label, count)
        offs = [cr[i].height - cert[i] for i in range(min(len(cr), len(cert)))]
        mo = float(np.mean(np.abs(offs))) if offs else float("nan")
        print(f"\n{label}  (q={spec.q})   found {len(cr)}   mean|iy - cert| = {mo:.2e}")
        for i, c in enumerate(cr):
            tag = f"{c.height - cert[i]:+.2e}" if i < len(cert) else "  --  "
            print(f"   {c.index:2d}: iy = {c.height:10.6f}   |F|/med = {c.modulus_rel:.2e}   (iy-cert {tag})")

    print("\n" + "=" * 84)
    print("THE CHAIN  3D climb -> 2D unit circle -> 1D   (chi3, first crossing)")
    print("=" * 84)
    gh = GeometricHelix(specmap["L2_chi3_q3"], n_integers=n_integers)
    c0 = gh.find_crossings(w_hi=10.0)[0]
    uc = gh.project_unit_circle(c0.height)
    print(f"  3D  climb-pitch iy                         : {c0.height:.6f}")
    print(f"  2D  unit-circle centroid |F|               : {uc['centroid_modulus']:.3e}"
          f"   (balance |F|/sum|1/R| = {uc['balance_ratio']:.2e})")
    print(f"      first phasor angles after projection   : {[round(a, 3) for a in uc['sample_angles']]}")
    print(f"  1D  ordinate iy                            : {c0.height:.6f}")

    print("\n" + "=" * 84)
    print("PITCH is a global phase: it sets the height scale, never moves a crossing")
    print("=" * 84)
    for pitch in (math.pi, math.pi / 3, 7.0):
        cr = GeometricHelix(specmap["L2_chi3_q3"], n_integers=n_integers, pitch=pitch).find_crossings(w_hi=20.0)[:4]
        z1 = (pitch / (2 * math.pi)) * 2.0
        print(f"  pitch={pitch:7.4f}  (z at n=1: {z1:.3f}):  crossings = {[round(c.height, 4) for c in cr]}")


if __name__ == "__main__":
    import sys
    if "--structure" in sys.argv:
        main()                      # the 3D helix, the float crossings, the chain, pitch-invariance
    else:
        main_hp()                   # the headline: each zero to 50 decimals from the geometry
