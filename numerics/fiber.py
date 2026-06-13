"""
fiber.py -- zero heights of the Dirichlet L-function  L(chi,s) = sum_{n>=1} chi(n) n^{-s},  found as the
sign flips of its real (Hardy-Z) standing wave.  This is the classical Hardy-Z / Riemann-Siegel
computation; honest about what here is geometry and what is analysis.

    V(t) = Re[ e^{i(theta(t)+alpha)} * F(1/2 + i t) ],   F(s) = sum_n chi(n) n^{-s},
    theta(t) = Im logGamma((1/2 + a + i t)/2) + (t/2) log(q/pi),   alpha = -arg(eps)/2.

V is real on the line, so its SIGN FLIPS are on-line zeros (Hardy 1914 -- a lower count of on-line zeros;
it says NOTHING about whether ALL zeros are on the line).  The "spiral / channels / midpoint" language
is a reading of this object, not a new one.

WHAT IS GEOMETRY HERE:
  - sigma = 1/2 = (pi/6)/(pi/3), the midpoint of the unit (a relabeling of 1/2);
  - the conductor's +/- residue-channel split.
WHAT IS ANALYSIS (NOT geometry), in every method below:
  - the amplitude exponent is ASSERTED as n^{-1/2} (the area-law ideal) -- it is NOT read off any placed
    spiral; using the actual spiral radius is worse (see find_zeros_geometric);
  - the winding is the log-n bridge; the gauge theta is logGamma; the high-precision tail is Euler-Maclaurin.

THREE METHODS for F (precision vs how much real geometry):
  * find_zeros           -- n^{-s} (ideal exponent) + E-M tail.  EXACT, 50+ decimals.  No mp.zeta, but the
                            amplitude is the ideal n^{-1/2}, gauge is logGamma.
  * find_zeros_direct    -- n^{-s} (ideal), head only (numpy).  ~1e-4 capture floor.
  * find_zeros_geometric -- amplitude 1/R(k_n) READ OFF THE ACTUAL helix3d spiral.  The only genuinely
                            geometric amplitude, and the WORST: ~1e-2 (chi3: 8.4e-3 vs 1.95e-4), from the
                            cone's small-n radius transient.
None of the three is fully geometric: all use the logGamma gauge and the log-n winding.

TRIVIAL/PRINCIPAL CHARACTER -- special.  q=1: F = the bare zeta sum (head + E-M tail); the literal
head-only sum diverges (the s=1 pole).
"""
from __future__ import annotations
from dataclasses import dataclass
import math
import os
import cmath
import numpy as np
import mpmath as mp

HERE = os.path.dirname(os.path.abspath(__file__))


@dataclass(frozen=True)
class CharSpec:
    label: str
    q: int
    parity: int             # a = 0 even (chi(-1)=1), 1 odd (chi(-1)=-1)
    values: dict            # residue -> chi(residue), OR residue -> exponent k if order>0
    order: int = 0          # if >0: chi(r) = exp(2 pi i k / order) (roots of unity, full precision)
    principal: bool = False  # q=1 zeta / trivial: fiber = zeta(s), no root-number gauge


@dataclass(frozen=True)
class FiberCrossing:
    """One state-machine crossing of the projected fiber."""
    index: int
    height: float
    incremental_cost: float
    cumulative_level: float
    sign_before: int
    sign_after: int
    cancellation_ratio: float
    unit_circle: complex


def _legendre(q):
    """{r: (r|q)} for an odd prime q -- a real (quadratic) character, exact."""
    return {r: (1 if pow(r, (q - 1) // 2, q) == 1 else -1) for r in range(1, q)}


SPECS = [
    CharSpec("L1_zeta_q1",           1, 0, {}, principal=True),
    CharSpec("L2_chi3_q3",           3, 1, {1: 1, 2: -1}),
    CharSpec("L3_chi4_q4",           4, 1, {1: 1, 3: -1}),
    CharSpec("L4_chi5quad_q5",       5, 0, {1: 1, 2: -1, 3: -1, 4: 1}),
    CharSpec("L5_chi5c4_q5",         5, 1, {1: 1, 2: 1j, 3: -1j, 4: -1}),
    CharSpec("L6_chi7quad_q7",       7, 1, {1: 1, 2: 1, 3: -1, 4: 1, 5: -1, 6: -1}),
    CharSpec("L7_chi8quad_q8",       8, 0, {1: 1, 3: -1, 5: -1, 7: 1}),
    CharSpec("L8_chi7c3_q7",         7, 0, {1: 0, 2: 2, 3: 1, 4: 1, 5: 2, 6: 0}, order=3),
    CharSpec("L9_chi1009quad_q1009", 1009, 0, _legendre(1009)),
]

ZETA_SPEC = SPECS[0]     # L1_zeta_q1 (the principal/trivial case)
ALL_SPECS = SPECS


def chi_val(spec: CharSpec, r: int):
    """chi(residue) at full mpmath precision (roots of unity exact when order>0)."""
    if r not in spec.values:
        return mp.mpc(0)
    if spec.order:
        return mp.exp(2j * mp.pi * spec.values[r] / spec.order)
    return mp.mpc(spec.values[r])


UNIT = mp.pi / 3                 # an arbitrary unit; (pi/6)/(pi/3) = 1/2 regardless (the pi cancels)


def midpoint_abscissa():
    """Returns 1/2.  Written as (pi/6)/(pi/3) -- the midpoint of the unit pi/3 -- which is a relabeling
    of one-half, NOT an explanation of why zeros lie on the critical line."""
    return (mp.pi / 6) / (mp.pi / 3)


# ============================================================================================
#  the gauge (root number) and the residue-fibre fiber (the buckets, continued)
# ============================================================================================
def alpha_gauge(spec: CharSpec):
    """alpha = -arg(eps)/2,  eps = tau(chi)/(i^a sqrt q) -- the FE gauge (theory, never fitted)."""
    if spec.q == 1 or spec.principal:
        return mp.mpf(0)
    tau = sum(chi_val(spec, r) * mp.exp(2j * mp.pi * r / spec.q) for r in range(1, spec.q))
    eps = tau / (mp.mpc(0, 1) ** spec.parity * mp.sqrt(spec.q))
    return -mp.arg(eps) / 2


def _em_tail(s, x, J):
    """Continue ONE residue class's tail, sum_{m>=0}(x+m)^{-s}, by Euler-Maclaurin: a short head,
    the smooth integral X^{1-s}/(s-1), and Bernoulli corrections of the SAME placed-naturals sum.
    No mp.zeta -- this is the spiral's own tail, continued."""
    head = mp.fsum((x + n) ** (-s) for n in range(8))
    X = x + 8
    val = head + X ** (1 - s) / (s - 1) + X ** (-s) / 2
    poch = s
    for j in range(1, J + 1):
        val += mp.bernoulli(2 * j) / mp.factorial(2 * j) * poch * X ** (-s - 2 * j + 1)
        poch *= (s + 2 * j - 1) * (s + 2 * j)
    return val


def _em_tail_np(s: np.ndarray, x: float, J: int = 8) -> np.ndarray:
    """Vectorized Euler-Maclaurin continuation of sum_{m>=0} (x+m)^(-s)."""
    s = np.asarray(s, dtype=complex)
    head = np.zeros_like(s, dtype=complex)
    for n in range(8):
        head += np.exp(-s * math.log(x + n))
    X = x + 8
    logX = math.log(X)
    val = head + np.exp((1.0 - s) * logX) / (s - 1.0) + 0.5 * np.exp(-s * logX)
    poch = s.copy()
    for j in range(1, J + 1):
        b = float(mp.bernoulli(2 * j))
        coeff = b / math.factorial(2 * j)
        val += coeff * poch * np.exp((-s - 2 * j + 1) * logX)
        poch *= (s + 2 * j - 1) * (s + 2 * j)
    return val


def fiber_value(spec: CharSpec, s, M, J):
    """The helix sum  sum_{n>=1} chi(n) n^{-s}, OFF THE HELIX (no mp.zeta): a head over the LITERAL
    placed naturals n = 1..M (the geometry summing itself), plus the Euler-Maclaurin continuation of
    each residue class's own tail.  M is chosen so the tail's X = M/q exceeds |Im s| (E-M convergence)."""
    q = spec.q
    if q == 1:
        head = mp.fsum(mp.mpf(n) ** (-s) for n in range(1, M + 1))
        return head + _em_tail(s, mp.mpf(M + 1), J)
    M -= M % q
    head = mp.fsum(chi_val(spec, n % q) * mp.power(n, -s) for n in range(1, M + 1))
    tail = mp.mpc(0)
    for r in range(1, q):
        c = chi_val(spec, r)
        if c != 0:
            tail += c * q ** (-s) * _em_tail(s, (mp.mpf(M) + r) / q, J)
    return head + tail


def _em_M_J(spec: CharSpec, t):
    """Head length M and Bernoulli order J for E-M to reach the working precision at height t."""
    absT = abs(float(mp.re(t)))
    M = spec.q * (20 + 2 * int(absT))          # X = M/q ~ 2|t| >> |t|: terms decrease, geometry-heavy
    J = max(12, int(0.55 * mp.mp.dps))
    return M, J


def standing_wave_exact(spec: CharSpec, t):
    """V(t): the helix fiber gauged to a REAL standing wave; its sign flips are the heights.

    The abscissa is the midpoint of the unit dropped from the 2D unit circle into 1D: sigma =
    (pi/6)/(pi/3) = 1/2 (the pi cancels).  The value is the literal helix sum (head over placed
    naturals + E-M tail) -- no mp.zeta."""
    sigma = midpoint_abscissa()
    s = sigma + 1j * t
    M, J = _em_M_J(spec, t)
    th = mp.im(mp.loggamma((sigma + spec.parity + 1j * t) / 2)) + (t / 2) * mp.log(mp.mpf(spec.q) / mp.pi)
    return mp.re(mp.exp(1j * (th + alpha_gauge(spec))) * fiber_value(spec, s, M, J))


def find_zeros(spec: CharSpec, count: int = 100, dps: int = 30, scan: float = 0.1,
               scan_dps: int = 20):
    """HIGH-PRECISION heights from the geometry: sign flips of the real standing wave.

    Two stage so high precision stays affordable: (1) coarse scan at scan_dps to find the
    sign-flip brackets; (2) refine each bracket at full dps by Anderson-Bjorck (stays inside the
    bracket -- cannot overshoot a close pair)."""
    old = mp.mp.dps
    try:
        # stage 1 -- coarse brackets
        mp.mp.dps = max(scan_dps, 15)
        brackets = []
        t = float(2 * math.pi / spec.q + 0.05)
        v = float(standing_wave_exact(spec, mp.mpf(t)))
        while len(brackets) < count:
            t2 = t + scan
            v2 = float(standing_wave_exact(spec, mp.mpf(t2)))
            if v * v2 < 0:
                brackets.append((t, t2))
            t, v = t2, v2
        # stage 2 -- refine each bracket at full precision
        mp.mp.dps = dps
        zeros = []
        for a, b in brackets:
            z = mp.findroot(lambda u: standing_wave_exact(spec, u), (mp.mpf(a), mp.mpf(b)),
                            solver="anderson")
            zeros.append(mp.re(z))
        return zeros
    finally:
        mp.mp.dps = old


# ============================================================================================
#  the DIRECT resolution: the literal placed naturals (numpy), capture-truncation floor
# ============================================================================================
_BERN = {2: 1/6, 4: -1/30, 6: 1/42, 8: -1/30}


def _arg_gamma(z, terms=4):
    shift = 0.0
    while abs(z) < 10:
        shift -= cmath.log(z).imag
        z = z + 1
    s = (z - 0.5) * cmath.log(z) - z + 0.5 * math.log(2 * math.pi)
    for k in range(1, terms + 1):
        s += _BERN[2 * k] / ((2 * k) * (2 * k - 1) * z ** (2 * k - 1))
    return s.imag + shift


def find_zeros_direct(spec: CharSpec, count: int = 100, M: int = 4_000_000, step: float = 0.01):
    """Heights from the LITERAL placed naturals: sign flips of the truncated helix standing wave."""
    n = np.arange(1, M + 1, dtype=np.int64)
    if spec.q == 1 or spec.principal:
        chi = np.ones(M, dtype=complex)
    else:
        chi = np.array([complex(chi_val(spec, int(k) % spec.q)) for k in n])
    a = 1.0 / np.sqrt(n.astype(float))
    logn = np.log(n.astype(float))
    alpha = float(alpha_gauge(spec))
    t_top = _approx_top(spec, count)
    ts = np.arange(2 * math.pi / spec.q + 0.05, t_top + 1.0, step)
    V = np.empty(len(ts))
    for i in range(0, len(ts), 200):
        tt = ts[i:i + 200][:, None]
        F = np.zeros(tt.shape[0], dtype=complex)
        for j in range(0, M, 1_000_000):
            F += (chi[None, j:j + 1_000_000] * a[None, j:j + 1_000_000]
                  * np.exp(-1j * tt * logn[None, j:j + 1_000_000])).sum(axis=1)
        th = np.array([_arg_gamma(complex((0.5 + spec.parity) / 2, t / 2))
                       + (t / 2) * math.log(spec.q / math.pi) for t in ts[i:i + 200]])
        V[i:i + 200] = np.real(np.exp(1j * (th + alpha)) * F)
    idx = np.nonzero(V[:-1] * V[1:] < 0)[0]
    return list((ts[idx] + step * V[idx] / (V[idx] - V[idx + 1]))[:count])


def _approx_top(spec: CharSpec, count: int) -> float:
    t = 10.0
    for _ in range(300):
        N = t / (2 * math.pi) * math.log(spec.q * t / (2 * math.pi * math.e))
        if N >= count + 2:
            return t
        t *= 1.12
    return t


class HelixFiber:
    """Finite 3D fiber in the canonical pi/3 coordinates, then projected to S^1."""

    def __init__(self, spec: CharSpec, n_integers: int = 4_000_000, area_exact: bool = True,
                 use_tail: bool = True, tail_order: int = 24):
        import helix3d
        self.spec = spec
        self.use_tail = use_tail
        self.tail_order = tail_order
        self.helix = helix3d.Helix(helix3d.HelixParams(n_integers=n_integers, area_exact=area_exact))
        self.bridge_shift = math.log(2.0 * self.helix.params.A * self.helix.params.ds)
        self.alpha = float(alpha_gauge(spec))
        nn = self.helix.n.astype(np.int64)
        if spec.q == 1 or spec.principal:
            # Principal/zeta is read through the eta-regularized two-channel fiber:
            # eta(s) = (1 - 2^(1-s)) zeta(s), with odd/even signs (+,-).
            self.chi = np.where((nn % 2) == 1, 1.0, -1.0).astype(complex)
        else:
            self.chi = np.array([complex(chi_val(spec, int(k) % spec.q)) for k in nn])

    def geometry_report(self) -> dict:
        """Pi/3-coordinate geometry and projection checks for this fiber."""
        r = self.helix.self_test()
        r.update({
            "label": self.spec.label,
            "n_integers": int(self.helix.params.n_integers),
            "Cgeom": 2.0 * self.helix.params.A * self.helix.params.ds,
            "tail": "geometric Euler-Maclaurin tail from M+1" if self.use_tail else "finite head only",
            "crossing_costs": "pi/2, then pi per crossing",
            "circle_projection": "3D (x,y,z) -> (x+iy)/R",
            "fiber_phase": "exp(-i*t*log(R^2))",
        })
        return r

    def _channels(self) -> tuple[int, list[tuple[int, complex]]]:
        if self.spec.q == 1 or self.spec.principal:
            return 2, [(1, 1.0 + 0j), (0, -1.0 + 0j)]
        out = []
        for r in range(self.spec.q):
            c = complex(chi_val(self.spec, r))
            if c != 0:
                out.append((r, c))
        return self.spec.q, out

    def _tail_response_grid(self, ts: np.ndarray) -> np.ndarray:
        if not self.use_tail or not self.helix.params.area_exact:
            return np.zeros(len(ts), dtype=complex)
        ts = np.asarray(ts, dtype=float)
        s = 0.5 + 1j * ts
        C = 2.0 * self.helix.params.A * self.helix.params.ds
        Cfac = np.exp(-s * math.log(C))
        q, channels = self._channels()
        M = int(self.helix.params.n_integers)
        out = np.zeros(len(ts), dtype=complex)
        start = M + 1
        for r, c in channels:
            n0 = start + ((r - (start % q)) % q)
            x = n0 / q
            out += c * Cfac * np.exp(-s * math.log(q)) * _em_tail_np(s, x, self.tail_order)
        return out

    def residue_law(self) -> list[dict]:
        """Closed-form residue consumption law for the projected pi/3 fiber.

        For s = 1/2 + it and C = 2*A*ds = (pi/3)^2, the area-law projection gives

            R_n^2 ~ C*n,
            term_n(t) = chi(n)/R_n * exp(-i*t*log(R_n^2))
                      ~ chi(n) * (C*n)^(-s).

        On one residue class n = q*m + r this becomes

            F_r(s) = chi(r) * C^(-s) * q^(-s) * zeta(s, r/q).

        The model generates with the placed head plus a geometric Euler-Maclaurin tail from the
        last placed integer. The formulas below are the residue bookkeeping for that area-law tail.
        """
        C = 2.0 * self.helix.params.A * self.helix.params.ds
        q = self.spec.q
        if q == 1 or self.spec.principal:
            return [{
                "residue": 1,
                "chi": "+1",
                "amplitude": "1/R_(2*m+1)",
                "phase": "-t*log(R_(2*m+1)^2)",
                "closed_form": f"({C:.12g})^(-s) * 2^(-s) * zeta(s, 1/2)",
            }, {
                "residue": 0,
                "chi": "-1",
                "amplitude": "-1/R_(2*m+2)",
                "phase": "pi - t*log(R_(2*m+2)^2)",
                "closed_form": f"-({C:.12g})^(-s) * 2^(-s) * zeta(s, 1)",
            }, {
                "residue": "eta",
                "chi": "odd-even",
                "amplitude": "eta-regularized zeta fiber",
                "phase": "divide by arg(1 - 2^(1-s)) in the standing readout",
                "closed_form": f"({C:.12g})^(-s) * (1 - 2^(1-s)) * zeta(s)",
            }]

        rows = []
        for r in range(1, q):
            c = chi_val(self.spec, r)
            if c == 0:
                continue
            rows.append({
                "residue": r,
                "chi": mp.nstr(c, 12),
                "amplitude": f"chi({r}) / R_(q*m+{r})",
                "phase": f"arg(chi({r})) - t*log(R_(q*m+{r})^2)",
                "closed_form": (
                    f"chi({r}) * ({C:.12g})^(-s) * {q}^(-s) "
                    f"* zeta(s, {r}/{q})"
                ),
            })
        return rows

    def response_grid(self, ts: np.ndarray) -> np.ndarray:
        """Projected complex fiber response after 3D placement and S^1 projection."""
        ts = np.asarray(ts, dtype=float)
        return self.helix.projected_response_grid(self.chi, ts) + self._tail_response_grid(ts)

    def residue_response(self, t: float) -> dict[int, complex]:
        """Projected response split by conductor residue class."""
        s = 0.5 + 1j * float(t)
        C = 2.0 * self.helix.params.A * self.helix.params.ds
        Cfac = np.exp(-s * math.log(C))
        M = int(self.helix.params.n_integers)

        def tail_for(q: int, r: int, c: complex) -> complex:
            if not self.use_tail or not self.helix.params.area_exact:
                return 0j
            start = M + 1
            n0 = start + ((r - (start % q)) % q)
            x = n0 / q
            return complex(c * Cfac * np.exp(-s * math.log(q))
                           * _em_tail_np(np.array([s]), x, self.tail_order)[0])

        if self.spec.q == 1 or self.spec.principal:
            n = self.helix.n.astype(np.int64)
            return {
                1: np.sum(self.chi[n % 2 == 1] * self.helix.amp[n % 2 == 1]
                          * np.exp(-1j * t * self.helix.bridge[n % 2 == 1]))
                   + tail_for(2, 1, 1.0 + 0j),
                0: np.sum(self.chi[n % 2 == 0] * self.helix.amp[n % 2 == 0]
                          * np.exp(-1j * t * self.helix.bridge[n % 2 == 0]))
                   + tail_for(2, 0, -1.0 + 0j),
            }
        n = self.helix.n.astype(np.int64)
        out = {}
        for r in range(1, self.spec.q):
            c = complex(chi_val(self.spec, r))
            if c == 0:
                continue
            mask = (n % self.spec.q) == r
            out[r] = np.sum(self.chi[mask] * self.helix.amp[mask]
                            * np.exp(-1j * t * self.helix.bridge[mask])) + tail_for(self.spec.q, r, c)
        return out

    def standing_wave_grid(self, ts: np.ndarray) -> np.ndarray:
        """Real standing-wave readout of the projected fiber."""
        ts = np.asarray(ts, dtype=float)
        F = self.response_grid(ts)
        th = np.array([
            _arg_gamma(complex((0.5 + self.spec.parity) / 2, float(t) / 2))
            + (float(t) / 2) * math.log(self.spec.q / math.pi)
            + float(t) * self.bridge_shift
            for t in ts
        ])
        if self.spec.q == 1 or self.spec.principal:
            eta_factor_arg = np.array([
                cmath.phase(1.0 - 2.0 ** (1.0 - complex(0.5, float(t))))
                for t in ts
            ])
            th = th - eta_factor_arg
        return np.real(np.exp(1j * (th + self.alpha)) * F)

    def standing_wave(self, t: float) -> float:
        return float(self.standing_wave_grid(np.array([float(t)]))[0])

    def _refine_sign_flip(self, a: float, b: float, iterations: int = 48) -> float:
        fa = self.standing_wave(a)
        fb = self.standing_wave(b)
        if fa == 0.0:
            return a
        if fb == 0.0:
            return b
        for _ in range(iterations):
            m = 0.5 * (a + b)
            fm = self.standing_wave(m)
            if fa * fm <= 0:
                b, fb = m, fm
            else:
                a, fa = m, fm
        return 0.5 * (a + b)

    def find_zeros(self, count: int = 20, step: float = 0.01) -> list[float]:
        """Sign flips of the finite pi/3-coordinate fiber standing wave."""
        start = 0.1 if self.spec.q == 1 or self.spec.principal else 2 * math.pi / self.spec.q + 0.05
        ts = np.arange(start, _approx_top(self.spec, count) + 1.0, step)
        V = np.empty(len(ts))
        for i in range(0, len(ts), 200):
            V[i:i + 200] = self.standing_wave_grid(ts[i:i + 200])
        idx = np.nonzero(V[:-1] * V[1:] < 0)[0]
        return [self._refine_sign_flip(float(ts[i]), float(ts[i + 1])) for i in idx[:count]]

    def crossing_events(self, count: int = 20, step: float = 0.01) -> list[FiberCrossing]:
        """State-machine view: cancellation + crossing-cost ladder + S^1 projection."""
        import helix3d

        start = 0.1 if self.spec.q == 1 or self.spec.principal else 2 * math.pi / self.spec.q + 0.05
        ts = np.arange(start, _approx_top(self.spec, count) + 1.0, step)
        V = np.empty(len(ts))
        for i in range(0, len(ts), 200):
            V[i:i + 200] = self.standing_wave_grid(ts[i:i + 200])
        idx = np.nonzero(V[:-1] * V[1:] < 0)[0][:count]
        costs = helix3d.crossing_costs(len(idx))
        levels = helix3d.crossing_levels(len(idx))
        events = []
        for j, i in enumerate(idx):
            h = self._refine_sign_flip(float(ts[i]), float(ts[i + 1]))
            parts = self.residue_response(h)
            denom = sum(abs(v) for v in parts.values())
            total = sum(parts.values())
            ratio = float(abs(total) / denom) if denom else float("nan")
            level = float(levels[j])
            events.append(FiberCrossing(
                index=j + 1,
                height=h,
                incremental_cost=float(costs[j]),
                cumulative_level=level,
                sign_before=1 if V[i] > 0 else -1,
                sign_after=1 if V[i + 1] > 0 else -1,
                cancellation_ratio=ratio,
                unit_circle=complex(math.cos(level), math.sin(level)),
            ))
        return events

    def local_crossing(self, t0: float, delta: float = 0.5, samples: int = 200) -> float:
        """Refine the crossing near a supplied height, without using earlier crossings."""
        grid = np.linspace(t0 - delta, t0 + delta, samples + 1)
        vals = self.standing_wave_grid(grid)
        idx = np.nonzero(vals[:-1] * vals[1:] <= 0)[0]
        if len(idx) == 0:
            raise ValueError(f"no sign flip found in [{t0 - delta}, {t0 + delta}]")
        j = int(idx[np.argmin(np.abs(grid[idx] - t0))])
        return self._refine_sign_flip(float(grid[j]), float(grid[j + 1]))


def find_zeros_geometric(spec: CharSpec, count: int = 20, M: int = 4_000_000, step: float = 0.01):
    """Heights using the actual placed helix projection: a_n = 1/R_n and phase log(R_n^2)."""
    return HelixFiber(spec, n_integers=M).find_zeros(count=count, step=step)


def main_fiber_model(label: str = "L2_chi3_q3", count: int = 5, M: int = 200_000,
                     compare: bool = False, events: bool = False, head_only: bool = False):
    spec = {s.label: s for s in SPECS}[label]
    model = HelixFiber(spec, n_integers=M, use_tail=not head_only)
    print("PI/3 3D FIBER MODEL")
    for k, v in model.geometry_report().items():
        print(f"  {k:20s} = {v}")
    print("\nclosed-form residue consumption, s = 1/2 + i*t")
    for row in model.residue_law():
        print(f"  r={row['residue']}: chi={row['chi']}")
        print(f"       amplitude   {row['amplitude']}")
        print(f"       phase       {row['phase']}")
        print(f"       readout     {row['closed_form']}")
    z = model.find_zeros(count=count, step=0.02)
    cert = _load_certified(label, count) if compare else []
    source = "projected standing-wave sign flips"
    if compare:
        source += " compared to numerics/zeros"
    print(f"\n{label}: {source}")
    for i, h in enumerate(z):
        if i < len(cert):
            off = float(h - cert[i])
            print(f"  {i + 1:2d}: h={h:.6f}  h-cert={off:+.3e}")
        else:
            print(f"  {i + 1:2d}: h={h:.6f}")

    if events:
        print("\nstate-machine crossings")
        for ev in model.crossing_events(count=count, step=0.02):
            print(f"  {ev.index:2d}: h={ev.height:.6f}"
                  f"  cost/pi={ev.incremental_cost / math.pi:.1f}"
                  f"  level/pi={ev.cumulative_level / math.pi:.1f}"
                  f"  sign={ev.sign_before:+d}->{ev.sign_after:+d}"
                  f"  cancel={ev.cancellation_ratio:.3e}"
                  f"  S1=({ev.unit_circle.real:+.1f},{ev.unit_circle.imag:+.1f})")


def diagnose_chi3(M: int = 200_000, count: int = 3):
    spec = SPECS[1]
    cert = [float(x) for x in _load_certified(spec.label, count)]
    print(f"CHI3 DIAGNOSTIC, M={M}")
    for area_exact in (True, False):
        model = HelixFiber(spec, n_integers=M, area_exact=area_exact)
        z = model.find_zeros(count=count, step=0.02)
        off = [z[i] - cert[i] for i in range(min(len(z), len(cert)))]
        print(f"\ngeometry area_exact={area_exact}")
        print(f"  zeros   {[round(float(x), 6) for x in z]}")
        print(f"  offsets {[f'{x:+.3e}' for x in off]}")

    model = HelixFiber(spec, n_integers=M, area_exact=True)
    C = 2.0 * model.helix.params.A * model.helix.params.ds
    print("\nresidue consumption at certified ordinates, area_exact=True")
    for t in cert:
        parts = model.residue_response(t)
        total = sum(parts.values())
        denom = sum(abs(v) for v in parts.values())
        print(f"  t={t:.6f}  |sum|/sum|parts|={abs(total)/denom:.3e}")
        for r, v in parts.items():
            s = mp.mpf("0.5") + 1j * mp.mpf(t)
            closed = chi_val(spec, r) * (mp.mpf(C) ** (-s)) * (mp.mpf(spec.q) ** (-s)) \
                * mp.zeta(s, mp.mpf(r) / spec.q)
            print(f"    r={r} chi={mp.nstr(chi_val(spec, r), 4):>8s}"
                  f" |finite|={abs(v):.6f} arg={math.atan2(v.imag, v.real):+.6f}"
                  f" |closed|={float(abs(closed)):.6f}")



# ============================================================================================
#  verification: high-precision heights from the geometry, no drift, every L
# ============================================================================================
def _load_certified(label, k=100):
    p = os.path.join(HERE, "zeros", f"{label}.txt")
    if not os.path.exists(p):
        return []
    return [mp.mpf(l.split()[1]) for l in open(p) if not l.startswith("#")][:k]


def main(count: int = 100, dps: int = 30):
    print(f"HEIGHTS OFF THE HELIX (literal placed-naturals sum + E-M tail, no mp.zeta; dps={dps}); "
          f"no drift, every L")
    print(f"{'L-function':18} {'q':>2} {'#':>4} {'mean|h-cert|':>13} {'max':>10} "
          f"{'early->late (drift?)':>22}")
    for spec in SPECS:
        zc = _load_certified(spec.label, count)
        if not zc:
            print(f"{spec.label:18} {spec.q:>4}   (no certified file)")
            continue
        n = len(zc)
        zh = find_zeros(spec, n, dps=dps)
        m = min(len(zh), n)
        d = [abs(float(zh[i] - zc[i])) for i in range(m)]
        early = sum(d[:m // 2]) / max(1, m // 2)
        late = sum(d[m // 2:]) / max(1, m - m // 2)
        print(f"{spec.label:18} {spec.q:>4} {m:>4} {sum(d)/m:13.2e} {max(d):10.2e} "
              f"  {early:.1e} -> {late:.1e}", flush=True)
    print("  (|h-cert| ~ 1e-12 = the 12-digit certified floor; refine the table to see the dps floor.)")


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser()
    parser.add_argument("--model", action="store_true",
                        help="run the finite 3D pi/3 fiber model")
    parser.add_argument("--compare", action="store_true",
                        help="compare model ordinates against numerics/zeros")
    parser.add_argument("--events", action="store_true",
                        help="print state-machine crossing events")
    parser.add_argument("--head-only", action="store_true",
                        help="disable residue Euler-Maclaurin tail in the model")
    parser.add_argument("--diagnose-chi3", action="store_true",
                        help="isolate chi3 geometry vs residue consumption")
    parser.add_argument("--label", default="L2_chi3_q3")
    parser.add_argument("--count", type=int, default=5)
    parser.add_argument("--M", type=int, default=200_000)
    parser.add_argument("--dps", type=int, default=30)
    args = parser.parse_args()

    if args.diagnose_chi3:
        diagnose_chi3(M=args.M, count=args.count)
    elif args.model:
        main_fiber_model(label=args.label, count=args.count, M=args.M,
                         compare=args.compare, events=args.events, head_only=args.head_only)
    else:
        main(count=args.count, dps=args.dps)
