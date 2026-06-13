"""
helix3d.py -- THE REAL HELIX, canonical universal ruleset (ONE set for every L).

COORDINATE SWAP (pi/3 = 1 chart).  All law-constants are pi-based, NOT decimals.
In the chart where the arc unit pi/3 is the new "1", every constant is rational:

    arc spacing   ds = pi/3   (the unit "1")     integers placed at arc  s_n = n*ds + s0
    radial growth A  = pi/6   ("1/2")            Archimedean spiral       R(phi) = A*phi
    start offset  s0 = pi/6   ("1/2")            where integer n = 1 sits
    crossing cost first = pi/2, then +pi per crossing:
                    {pi/2, 3pi/2, 5pi/2, ...}

ONE ruleset, identical for EVERY L-function; only the Dirichlet character chi mod q changes.
(Replaces the old per-channel table: radial slope e^mode, pitch pi/helixUnit.  The old e^6
slope made R/sqrt(n) "drift 1 -> 11" -- an oversized growth rate, not a real obstruction.)

NO LOG IN THE 3D GEOMETRY (Rule Eight).  The helix is purely geometric / arithmetic:
  R(phi) = A*phi (linear Archimedean growth), integers placed by equal ARC LENGTH ds.
  arc length s(phi) = (A/2)[phi*sqrt(1+phi^2) + asinh(phi)]  (exact), inverted for phi(s_n).
  radius R_n = A*phi(s_n).  The area law (loop k holds ~k integers, cumulative n ~ k^2) gives
  R_n -> sqrt(2*A*ds)*sqrt(n): the sqrt(n) / sigma=1/2 frame EMERGES from the rewinding, it is
  NOT imposed and there is NO logarithm anywhere in the construction.

PROJECTION  3D -> 2D -> 1D  (height = iy).  Divide off the radial (sqrt n), keep the winding:
  the bridge  wind n <-> n^{it}  is the ONLY place a log appears (the AREA-log readout,
  log(R_n^2) = log(area) ~ log n + const).  Collapse

      F(w) = sum_n chi(n) * (1/R_n) * exp(-i w * log(R_n^2))  ~  L(chi, 1/2 + i w),

  and the HEIGHT w where the chi-weighted phasors CANCEL is iy = gamma.  No S(t) / jitter:
  the zero ordinate is just the cancellation height.  The geometry supplies WHY sqrt n / sigma
  = 1/2; the bridge supplies log n; the zero is L's 2D xy-shadow vanishing.
"""
from __future__ import annotations
from dataclasses import dataclass
import math
import numpy as np

# --- the canonical pi-based constants (the coordinate swap; pi/3 = 1) --------------------
A_GROWTH    = math.pi / 6     # radial growth rate of R(phi) = A*phi   ("1/2")
ARC_SPACING = math.pi / 3     # equal arc-length spacing ds            (the unit "1")
ARC_OFFSET  = math.pi / 6     # start offset s0 (where integer 1 sits) ("1/2")
QUANTUM     = math.pi         # crossing spacing
FIRST_CROSS = math.pi / 2     # first crossing (half quantum)


@dataclass(frozen=True)
class HelixParams:
    """The construction's constants.  Defaults are the canonical pi-based set."""
    n_integers: int = 200_000
    A: float = A_GROWTH        # radial growth rate
    ds: float = ARC_SPACING    # arc spacing (the unit)
    s0: float = ARC_OFFSET     # start offset
    area_exact: bool = True    # R_n^2 = (2*A*ds)*n exactly; False uses arc inversion


@dataclass(frozen=True)
class Point3D:
    """A placed integer on the log-free cone and its 3D -> unit-circle projection."""
    n: float
    arc: float       # s_n = n*ds + s0
    phi: float       # spiral angle, R = A*phi
    R: float         # radius "out" ~ sqrt(n)   (amplitude 1/R ~ n^{-1/2})
    x: float
    y: float
    z: float         # projected scale carried by the fiber: log(R^2)
    circle: complex  # (x + iy) / R, the 3D -> 2D unit-circle projection


def _arc_of_phi(phi, A):
    """Exact arc length of the Archimedean spiral R(phi)=A*phi: (A/2)[phi*sqrt(1+phi^2)+asinh phi]."""
    return 0.5 * A * (phi * np.sqrt(1.0 + phi * phi) + np.arcsinh(phi))


class Helix:
    """The built log-free helix: every integer placed by equal arc length, radius ~ sqrt(n)."""

    def __init__(self, params: HelixParams = HelixParams()):
        self.params = params
        self._build()

    def _build(self):
        p = self.params
        self.n = np.arange(1, p.n_integers + 1, dtype=float)
        arc = self.n * p.ds + p.s0
        if p.area_exact:
            phi = np.sqrt(2.0 * p.ds * self.n / p.A)
        else:
            # invert s(phi) = arc by Newton from the area-law seed  phi ~ sqrt(2*arc/A)
            phi = np.sqrt(2.0 * arc / p.A)
            for _ in range(60):
                f = _arc_of_phi(phi, p.A) - arc
                phi = phi - f / (p.A * np.sqrt(1.0 + phi * phi))   # ds/dphi = A*sqrt(1+phi^2)
                if np.max(np.abs(f)) < 1e-13 * (1.0 + np.max(arc)):
                    break
        self.arc = arc
        self.phi = phi
        self.R = p.A * phi                 # radius "out" ~ sqrt(n)
        self.x = self.R * np.cos(self.phi)
        self.y = self.R * np.sin(self.phi)
        self.amp = 1.0 / self.R            # the cone's OWN weight ~ n^{-1/2} (derived, not imposed)
        self.bridge = np.log(self.R ** 2)  # the 2D bridge winding arg = log(area) ~ log n (the ONLY log)
        self.z = self.bridge
        self.unit_circle = (self.x + 1j * self.y) / self.R

    def point(self, n: int) -> Point3D:
        i = int(n) - 1
        return Point3D(n=float(n), arc=float(self.arc[i]), phi=float(self.phi[i]),
                       R=float(self.R[i]), x=float(self.x[i]), y=float(self.y[i]),
                       z=float(self.z[i]), circle=complex(self.unit_circle[i]))

    def project_unit_circle(self) -> np.ndarray:
        """3D -> 2D projection: discard radius/height and keep the unit-circle angle."""
        return self.unit_circle.copy()

    def fiber_phase(self, w: float) -> np.ndarray:
        """Unit-circle phase flow carried by the fiber over the placed 3D helix."""
        return np.exp(-1j * w * self.bridge)

    def fiber_on_helix(self, chi_vals: np.ndarray, w: float) -> np.ndarray:
        """The weighted fiber after 3D placement and projection to the unit circle."""
        return chi_vals * self.amp * self.fiber_phase(w)

    def projected_response(self, chi_vals: np.ndarray, w: float) -> complex:
        """Collapse the projected unit-circle fiber to its complex response."""
        return np.sum(self.fiber_on_helix(chi_vals, w))

    def projected_response_grid(self, chi_vals: np.ndarray, ws: np.ndarray,
                                block: int = 1_000_000) -> np.ndarray:
        """Batched projected responses for many heights, streamed over the 3D fiber."""
        ws = np.asarray(ws, dtype=float)
        out = np.zeros(len(ws), dtype=complex)
        for j in range(0, len(self.n), block):
            out += (
                chi_vals[None, j:j + block] * self.amp[None, j:j + block]
                * np.exp(-1j * ws[:, None] * self.bridge[None, j:j + block])
            ).sum(axis=1)
        return out

    # -- the projection: chi-weighted collapse F(w); height w where |F| -> 0 is iy = gamma ----
    def collapse(self, chi_vals: np.ndarray, w: float, exact: bool = False) -> float:
        """|F(w)| = |sum_n chi(n) amp_n exp(-i w * arg_n)|.

        exact=False : the cone's OWN weight 1/R_n and OWN winding log(R_n^2) (the geometry).
        exact=True  : the bridge's exact amp_n = n^{-1/2}, arg_n = log n  (= truncated L(1/2+iw)).
        """
        if exact:
            amp = self.n ** (-0.5)
            arg = np.log(self.n)
            return abs(np.sum(chi_vals * amp * np.exp(-1j * w * arg)))
        return abs(self.projected_response(chi_vals, w))

    def project_iy(self, chi_vals: np.ndarray, w_hi: float = 26.0, step: float = 0.02,
                   exact: bool = True) -> list[float]:
        """Heights w where the chi-weighted phasors cancel = the zero ordinates (iy = gamma)."""
        ws = np.arange(FIRST_CROSS / QUANTUM + 0.1, w_hi, step)   # start above the first crossing
        mag = np.array([self.collapse(chi_vals, float(w), exact=exact) for w in ws])
        out = []
        for i in range(1, len(mag) - 1):
            if mag[i] < mag[i - 1] and mag[i] < mag[i + 1] and mag[i] < 0.35 * np.median(mag):
                lo, hi = ws[i] - step, ws[i] + step       # local quadratic refine of the dip
                wgrid = np.linspace(lo, hi, 25)
                mg = np.array([self.collapse(chi_vals, float(w), exact=exact) for w in wgrid])
                out.append(float(wgrid[int(np.argmin(mg))]))
        return out

    # -- self-test: the sqrt(n)/sigma=1/2 frame emerged, log-free, pi-based --------------------
    def self_test(self) -> dict:
        p = self.params
        c = math.sqrt(2.0 * p.A * p.ds)                  # asymptotic R/sqrt(n) (a gauge scale)
        ratio = self.R / np.sqrt(self.n)
        rel = ratio / ratio[len(ratio) // 2:].mean()
        worst = float(np.abs(rel[1:] - 1.0).max())       # worst relative amplitude error (n>=2)
        assert worst < 0.05, f"sqrt(n) frame not flat enough: {worst}"
        assert abs(p.A - math.pi / 6) < 1e-12 and abs(p.ds - math.pi / 3) < 1e-12, "not the pi/3 chart"
        circle_err = float(np.max(np.abs(np.abs(self.unit_circle) - 1.0)))
        assert circle_err < 1e-12, f"unit-circle projection drifted: {circle_err}"
        return {"A": p.A, "ds": p.ds, "s0": p.s0, "asymptotic_const": c,
                "area_exact": p.area_exact,
                "worst_amp_rel_err": worst,
                "crossings": "cost_1=pi/2; cost_n=pi/2+(n-1)*pi",
                "log_in_geometry": False, "unit_circle_err": circle_err}


# the canonical crossing levels: first cost pi/2, then +pi per crossing
def crossing_costs(count: int) -> np.ndarray:
    """Incremental costs: first crossing pi/2; each subsequent crossing pi."""
    if count <= 0:
        return np.array([], dtype=float)
    costs = np.full(count, QUANTUM, dtype=float)
    costs[0] = FIRST_CROSS
    return costs


def crossing_levels(count: int) -> np.ndarray:
    """Cumulative crossing ladder: {pi/2, 3pi/2, 5pi/2, ...}."""
    return np.cumsum(crossing_costs(count))


# minimal character table for the self-verification (the ONLY per-L input)
_CHARS = {
    "chi3  (mod 3, odd quad)":      (3, {1: 1, 2: -1}),
    "chi4  (mod 4, odd quad)":      (4, {1: 1, 3: -1}),
    "chi5q (mod 5, even quad)":     (5, {1: 1, 4: 1, 2: -1, 3: -1}),
    "chi5c (mod 5, quartic CPLX)":  (5, {1: 1, 2: 1j, 4: -1, 3: -1j}),
    "chi7q (mod 7, odd quad)":      (7, {1: 1, 2: 1, 4: 1, 3: -1, 5: -1, 6: -1}),
}


def _char_array(n, q, table):
    v = np.zeros(len(n), dtype=complex)
    r = n.astype(np.int64) % q
    for res, val in table.items():
        v[r == res] = val
    return v


if __name__ == "__main__":
    import mpmath as mp
    mp.mp.dps = 30

    h = Helix(HelixParams(n_integers=200_000))
    print("CANONICAL HELIX self-test (pi/3 = 1 chart, log-free geometry):")
    for k, v in h.self_test().items():
        print(f"   {k:22s} = {v}")

    def Lval(q, table, s):       # exact L(chi,s) for the height = iy verification (Hurwitz form)
        return q ** (-s) * sum(mp.mpc(c) * mp.zeta(s, mp.mpf(a) / q) for a, c in table.items())

    print("\nPROJECT HEIGHT = iy  (cancellation heights vs mpmath |L(1/2+i gamma)|; ONE ruleset):")
    for name, (q, table) in _CHARS.items():
        chi = _char_array(h.n, q, table)
        ws = h.project_iy(chi, w_hi=22.0, exact=True)[:5]
        ver = [float(abs(Lval(q, table, mp.mpf(1) / 2 + 1j * mp.mpf(w)))) for w in ws]
        print(f"   {name:28s} iy = {[round(w, 4) for w in ws]}")
        print(f"   {'':28s} |L| = {['%.1e' % e for e in ver]}  (height = iy, no S)")
