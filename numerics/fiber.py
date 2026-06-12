"""
fiber.py -- THE FIBER: an L-function traversing the built helix, accumulating energy,
            and marking a potential zeta each time it has paid for the next harmonic.

Constructor takes the L-function's parameters (a CharSpec from compute_zeros) and a
Helix (from helix3d) -- the fiber never builds geometry itself; it consumes the
object through the helix API. Honest division of labor:

  helix3d   : WHERE everything is   (placement, coordinates, projections)
  fiber     : WHAT the climb costs  (energy accumulation, harmonic thresholds)

ENERGY (the geometric accumulator). Climbing from integer n-1 to integer n raises the
fiber by dz = z_n - z_{n-1} (read off the object). The model's accumulation rate at
height z is (1/2) * log(q*z / (2*pi)) -- conductor (log q)/2 plus the universal
log-of-scale term; accumulation begins where the rate turns positive (z > 2*pi/q,
the monotone regime -- below it the resonator has not yet formed). So

    E_n = sum over consumed integers of  rate(z) * dz      (trapezoid on the object)

HARMONICS. The quantum is pi; the ray offset is arg(eps)/2 from the ROOT NUMBER
(theory, never fitted; sign derived from Z = eps^(-1/2) * omega * L). The fiber
realizes it has accumulated the m-th harmonic's worth when E crosses

    L_m = (m + 1/2) * pi + arg(eps)/2 ,   m = 0, 1, 2, ...

and at that moment it calls the helix projection to MARK A POTENTIAL ZETA at the
crossing height (linear interpolation of the crossing between the two bracketing
integers, then helix.point at the interpolated line position).

CROSS-CHECK. At each mark the exact analytic accumulation
theta_chi(t) = Im logGamma((1/2+it+a)/2) + (t/2) log(q/pi) is evaluated (mpmath) and
the geometric-vs-exact gap is reported -- measured, not hidden.

SELF-TESTS:
  * constants-invariance: the marks are IDENTICAL (to numerical tolerance) across
    different radial/spacing constants -- the slope-cancellation theorem
    (HelixDefs: "the slope e^mode cancels; only the defect survives") observed on
    the actual object;
  * the six-function comparison against the certified reference zeros.
"""
from __future__ import annotations
from dataclasses import dataclass
import math
import os
import sys
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from helix3d import Helix, HelixParams, Point3D            # noqa: E402
from compute_zeros import CharSpec, SPECS, root_number      # noqa: E402
import mpmath as mp                                         # noqa: E402

TWO_PI = 2.0 * math.pi

ZETA_SPEC = CharSpec(
    label="L1_zeta_q1", q=1, values=(1,), parity=0,
    description="Riemann zeta (q = 1, principal/trivial character; eps = 1)")

ALL_SPECS = (ZETA_SPEC,) + SPECS


@dataclass(frozen=True)
class HarmonicMark:
    """The fiber's record of one realized harmonic: a potential zeta."""
    index: int          # m: which harmonic (0-based threshold index)
    n_at: int           # the integer being consumed when the budget filled
    nu_star: float      # interpolated line position of the crossing
    point: Point3D      # the projected 3D mark (helix.project_absolute)
    height: float       # the collapsed height -- the potential zeta ordinate
    E_at: float         # accumulated energy at the mark (== threshold)


class Fiber:
    """An L-function's fiber, traversing a Helix and tracking harmonic creation."""

    def __init__(self, spec: CharSpec, helix: Helix):
        self.spec = spec
        self.helix = helix
        if spec.q == 1:
            self.eps = complex(1.0, 0.0)
        else:
            self.eps = complex(root_number(spec))
        self.ray_offset = float(mp.arg(self.eps)) / 2.0   # arg(eps)/2 -- theory
        self.marks: list[HarmonicMark] = []
        self._E = None                                     # cumulative energy array

    # -- the accumulation, integer by integer off the object -----------------
    def _accumulate(self) -> np.ndarray:
        """Cumulative energy E_n after consuming integer n (trapezoid on the helix)."""
        q, z = self.spec.q, self.helix.z
        z0 = TWO_PI / q                                    # rate turns positive here
        rate = 0.5 * np.log(np.maximum(q * z / TWO_PI, 1.0))   # clamp: no negative energy
        dz = np.diff(z, prepend=0.0)
        dE = 0.5 * (rate + np.concatenate(([rate[0]], rate[:-1]))) * dz
        dE[z < z0] = 0.0                                   # nothing accumulates pre-regime
        E = np.cumsum(dE)
        # constant correction, THEORY ONLY (verified against measurement in convergence.py):
        # the consumption integral carries lower-endpoint term +pi/q, while the exact
        # accumulation's asymptotic constant is (2a-1)*pi/8; align E to the exact constant.
        E -= (math.pi / q - (2 * self.spec.parity - 1) * math.pi / 8)
        return E

    # -- harmonic creation tracking ------------------------------------------
    def run(self, num_harmonics: int = 100) -> list[HarmonicMark]:
        """Traverse, accumulate, and mark a potential zeta per realized harmonic."""
        E = self._accumulate()
        self._E = E
        # first level: the first half-integer (in pi-units, ray-shifted) ABOVE the
        # accumulation's starting value -- same crossing protocol as model_ladder
        E_start = float(np.min(E))
        m0 = math.floor((E_start - self.ray_offset) / math.pi - 0.5) + 1
        levels = (np.arange(num_harmonics) + m0 + 0.5) * math.pi + self.ray_offset
        if levels[-1] > E[-1]:
            raise RuntimeError(
                f"{self.spec.label}: helix too short -- E_max={E[-1]:.1f} < "
                f"last threshold {levels[-1]:.1f}; build a longer helix")
        idx = np.searchsorted(E, levels)                   # first n with E_n >= level
        marks = []
        n_arr, z_arr = self.helix.n, self.helix.z
        for m, (lvl, i) in enumerate(zip(levels, idx)):
            E_lo, E_hi = (E[i - 1], E[i]) if i > 0 else (0.0, E[0])
            frac = 0.0 if E_hi == E_lo else (lvl - E_lo) / (E_hi - E_lo)
            nu_star = float((n_arr[i - 1] if i > 0 else 0.0) * (1 - frac) + n_arr[i] * frac)
            nu_star = max(nu_star, 1e-9)
            pt = self.helix.project_absolute(nu_star)
            marks.append(HarmonicMark(index=m, n_at=int(n_arr[i]), nu_star=nu_star,
                                      point=pt, height=pt.height, E_at=float(lvl)))
        self.marks = marks
        return marks

    # -- exact-theta cross-check at the marks ---------------------------------
    def crosscheck_exact(self) -> dict:
        """|geometric E - exact theta_chi| at every mark (mpmath), max and mean."""
        q, a = self.spec.q, self.spec.parity
        gaps = []
        for mk in self.marks:
            t = mk.height
            theta = float(mp.im(mp.loggamma((mp.mpf(1) / 2 + 1j * t + a) / 2))
                          + (t / 2) * mp.log(mp.mpf(q) / mp.pi))
            # at a geometric mark E(z*) = threshold exactly; exact theta(z*) should match it
            gaps.append(abs(theta - mk.E_at))
        return {"mean_gap": float(np.mean(gaps)), "max_gap": float(np.max(gaps))}

    # -- comparison against the certified reference set -----------------------
    def compare(self, zeros_dir: str) -> dict:
        path = os.path.join(zeros_dir, f"{self.spec.label}.txt")
        zeros = []
        with open(path) as f:
            for ln in f:
                if not ln.startswith('#'):
                    p = ln.split()
                    if len(p) == 2:
                        zeros.append(float(p[1]))
        m = min(len(zeros), len(self.marks))
        zs, hs = zeros[:m], [mk.height for mk in self.marks[:m]]
        ds = [hs[i] - zs[i] for i in range(m)]
        gaps = [zs[i + 1] - zs[i] for i in range(m - 1)]
        mg = sum(gaps) / len(gaps)
        viol = 0
        for i in range(m):
            lo = zs[i - 1] if i > 0 else 0.0
            hi = zs[i + 1] if i < m - 1 else float('inf')
            if not (lo < hs[i] < hi):
                viol += 1
        return {"label": self.spec.label, "n": m,
                "mean_off": float(np.mean(np.abs(ds))), "max_off": float(np.max(np.abs(ds))),
                "mean_gap": mg, "pct_gap": float(np.mean(np.abs(ds))) / mg * 100,
                "interlace_viol": viol}


# -- self-tests ----------------------------------------------------------------
def test_constants_invariance() -> float:
    """Slope/spacing cancellation ON THE OBJECT: the marks' heights depend only on z,
    so two helices with different radial/spacing constants -- built to cover the SAME
    height range -- must produce the same marks. (Different constants pack a different
    number of integers per unit height, so the integer count is scaled to equalize
    coverage; the residual deviation is the trapezoid discretization, reported.)"""
    spec = SPECS[0]                                        # chi_3
    n1 = 120_000
    A2, U2 = 2.0, 0.7
    n2 = int(n1 * A2 / U2) + 10                            # equal z-coverage
    h1 = Helix(HelixParams(radial=1.0, pitch=1.0, spacing=1.0, n_integers=n1))
    h2 = Helix(HelixParams(radial=A2, pitch=1.0, spacing=U2, n_integers=n2))
    m1 = Fiber(spec, h1).run(50)
    m2 = Fiber(spec, h2).run(50)
    dev = max(abs(a.height - b.height) for a, b in zip(m1, m2))
    assert dev < 1e-4, f"slope cancellation violated on the object: {dev}"
    return dev


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    zeros_dir = os.path.join(here, 'zeros')
    print("fiber self-test: constants invariance (slope/spacing cancellation on the object)")
    dev = test_constants_invariance()
    print(f"  PASSED: max mark deviation across (A,U) variants = {dev:.2e}")
    print()
    helix = Helix(HelixParams())                           # the default 250k object
    print(f"helix built: {helix.params.n_integers} integers, z_max={helix.z[-1]:.2f}")
    print()
    print(f"{'function':22s} {'mean%gap':>9s} {'max off':>8s} {'violations':>11s}   first mark vs first zero")
    rows = []
    for spec in ALL_SPECS:
        f = Fiber(spec, helix)
        f.run(100)
        r = f.compare(zeros_dir)
        rows.append(r)
        print(f"{r['label']:22s} {r['pct_gap']:9.1f} {r['max_off']:8.3f} "
              f"{r['interlace_viol']:>8d}/100   {f.marks[0].height:8.4f} vs (file)")
    total_viol = sum(r['interlace_viol'] for r in rows)
    print(f"\nTOTAL interlacing violations across {sum(r['n'] for r in rows)} marks: {total_viol}")


if __name__ == "__main__":
    main()


# ===========================================================================
# THE ACTUAL FIBER: values captured off the helix, S as OUTPUT not residual
# ===========================================================================
class ActualFiber(Fiber):
    """A fiber that accumulates the ACTUAL arithmetic phase, not the mean field.

    Per consumed integer n, the captured values are
        channel   chi(n)        -- the fiber's own character value,
        amplitude 1 / R(k_n)    -- read off the OBJECT's placed radius (the global
                                   constant sqrt(A*pi/U) cancels in the phase),
        phase     t * log n     -- the bridge angle (the ONE permitted logarithm:
                                   the geometric winding's analytic readout).

    The fiber's state at height t is the full captured sum
        F(t) = sum_n chi(n) * amp_n * exp(-i t log n),
    which for non-principal chi CONVERGES to L(1/2+it) at rate M^(-1/2)
    (kernel: HelixFlowClosureLedger.flow_rate_bound) -- truncation ~ q/sqrt(M).
    The actual accumulation is then
        E_actual(t) = theta_chi(t) + arg_cont F(t)
    (continuous branch by unwrapping on a fine grid), and its threshold crossings
    are compared against the certified zeros. If the model is right the offsets
    collapse to truncation order: S stops being a residual and becomes output.

    zeta (principal character) is excluded: the captured sum does not converge on
    the line for the principal character (same kernel ledger, A(M) unbounded).
    """

    def __init__(self, spec: CharSpec, helix: Helix, grid_step: float = 0.02):
        if spec.q == 1:
            raise ValueError("ActualFiber requires a non-principal character "
                             "(the captured sum converges only for chi != 1)")
        super().__init__(spec, helix)
        self.grid_step = grid_step
        self._capture()

    def _capture(self):
        """Capture per-integer values off the object."""
        n = self.helix.n
        q = self.spec.q
        # channel values chi(n) for every placed integer
        table = np.array([complex(v) for v in self.spec.values])
        self.channel = table[(n.astype(np.int64)) % q]
        # amplitude off the object: 1/R(k_n); normalize the global constant so
        # that amp_n -> n^(-1/2) exactly in scale (constant cancels in arg anyway)
        R = self.helix.params.radial * self.helix.k
        c0 = R[0] * math.sqrt(1.0)                  # R(k_1) ~ const * sqrt(1)
        self.amp = c0 / R
        # the bridge angle rate per integer: log n (the one permitted log)
        self.logn = np.log(n)

    def _theta(self, t):
        q, a = self.spec.q, self.spec.parity
        return float(mp.im(mp.loggamma((mp.mpf(1)/2 + 1j*t + a)/2))
                     + (t/2)*mp.log(mp.mpf(q)/mp.pi))

    def E_grid(self, t_floor: float | None = None, t_max: float | None = None):
        """The accumulation E(t) = theta + arg_cont F on a grid; raw, no levels.

        Memory-safe double chunking (grid x integers), so multi-million-integer
        objects (dense packing / the configured table) evaluate without blowup.
        """
        q = self.spec.q
        t0 = t_floor if t_floor is not None else TWO_PI / q + 0.05
        t_max = t_max or float(self.helix.z[-1] * 0.65)
        ts = np.arange(t0, t_max, self.grid_step)
        w = self.channel * self.amp                       # fixed complex weights
        F = np.zeros(len(ts), dtype=complex)
        tchunk, nchunk = 250, 100_000
        for i in range(0, len(ts), tchunk):
            tt = ts[i:i+tchunk][:, None]                  # (T,1)
            acc = np.zeros(tt.shape[0], dtype=complex)
            for j in range(0, len(w), nchunk):
                ln = self.logn[j:j+nchunk][None, :]
                acc += (w[None, j:j+nchunk] * np.exp(-1j * tt * ln)).sum(axis=1)
            F[i:i+tchunk] = acc
        argF = np.unwrap(np.angle(F))
        # smooth theta on the grid: exact anchor + cumulative trapezoid of theta'
        rate = 0.5 * np.log(q * ts / TWO_PI)
        theta_grid = np.concatenate(([0.0], np.cumsum(0.5*(rate[1:]+rate[:-1])*np.diff(ts))))
        theta_grid += self._theta(float(ts[0]))           # exact anchor
        return ts, theta_grid + argF

    def run_actual(self, num_harmonics: int = 100, t_max: float | None = None):
        """Accumulate the ACTUAL phase on a grid and mark threshold crossings."""
        ts, E = self.E_grid(t_max=t_max)
        # thresholds: nearest-level start, same protocol as the smooth fiber
        m0 = math.floor((float(E[0]) - self.ray_offset) / math.pi - 0.5) + 1
        levels = (np.arange(num_harmonics + 4) + m0 + 0.5) * math.pi + self.ray_offset
        marks = []
        j = 0
        for i in range(1, len(ts)):
            while j < len(levels) and E[i-1] < levels[j] <= E[i]:
                frac = (levels[j] - E[i-1]) / (E[i] - E[i-1])
                marks.append(float(ts[i-1] + frac * (ts[i] - ts[i-1])))
                j += 1
        return marks[:num_harmonics]

    def compare_actual(self, zeros_dir: str, num: int = 100) -> dict:
        marks = self.run_actual(num)
        path = os.path.join(zeros_dir, f"{self.spec.label}.txt")
        zeros = [float(l.split()[1]) for l in open(path) if not l.startswith('#')]
        m = min(len(zeros), len(marks))
        ds = [marks[i] - zeros[i] for i in range(m)]
        gaps = [zeros[i+1] - zeros[i] for i in range(m-1)]
        mg = sum(gaps)/len(gaps)
        viol = sum(1 for i in range(m)
                   if not ((zeros[i-1] if i else 0.0) < marks[i] < (zeros[i+1] if i < m-1 else 1e18)))
        return {"label": self.spec.label, "n": m,
                "mean_off": float(np.mean(np.abs(ds))), "max_off": float(np.max(np.abs(ds))),
                "pct_gap": float(np.mean(np.abs(ds)))/mg*100, "interlace_viol": viol}


def main_actual():
    here = os.path.dirname(os.path.abspath(__file__))
    zeros_dir = os.path.join(here, 'zeros')
    helix = Helix(HelixParams())
    print("THE ACTUAL FIBER -- values captured off the helix; S as output")
    print(f"{'function':22s} {'mean%gap':>9s} {'max off':>8s} {'violations':>11s}")
    for spec in SPECS:
        f = ActualFiber(spec, helix)
        r = f.compare_actual(zeros_dir)
        print(f"{r['label']:22s} {r['pct_gap']:9.2f} {r['max_off']:8.4f} {r['interlace_viol']:>8d}/{r['n']}")


if __name__ == "__main__" and os.environ.get("ACTUAL") == "1":
    main_actual()


# ===========================================================================
# CHANNEL BUCKETS + the configuration table (HelixDefs.lean)
# ===========================================================================
# The kernel's configurator table (RequestProject/HelixDefs.lean):
#   angle unit U = pi/helixUnit, radial slope e^mode, pitch = U (HelixArcLength:
#   "pitch = unit is the single fitted line").  Four rows are assigned:
#     trivial chi0 mod 3 : d=6, mode=3      chi_3 : d=3, mode=6
#     mode-8 (chi4/chi8) : d=2, mode=8      mode-12 : d=1, mode=12
#   q=5 and q=7 rows are NOT in the table -- configuration parameters to be set.
# FILLED TABLE (2026-06-11).  Two inputs:
#   (1) the PARITY LAW, exact on all four kernel rows (trivial3, chi3, chi4, chi6):
#           mode = q * (1 + a)        (a = 0 even, a = 1 odd)
#       so the radial slope e^mode is fixed by conductor and parity;
#   (2) the DATA: universal-linear-cost calibration of the certified zero sets
#       (zerodata.py), anchored at chi3's kernel row, pins the density coefficient
#       C = A*pi/U^3 per channel; then U = (e^mode * pi / C)^(1/3).
# Kernel-assigned rows keep their kernel constants (chi3: U=pi/3, e^6; chi4:
# U=pi/2, e^8 -- Sam-confirmed).  NOTE the chi4 tension: data-implied C = 1167
# (U = 2.0021) vs kernel row C = 2416 (U = pi/2) -- factor 2.07 in C; the kernel
# row stays primary, the data alternative is recorded here.
CHANNEL_TABLE = {
    "L1_zeta_q1":      dict(helixUnit=13.92198, mode=1.0,  src="data"),
    "L2_chi3_q3":      dict(helixUnit=3.0,      mode=6.0,  src="kernel"),
    "L3_chi4_q4":      dict(helixUnit=2.0,      mode=8.0,  src="kernel"),
    # "L3_chi4_q4":    dict(helixUnit=1.56917,  mode=8.0,  src="data")  # C=1167 alt
    "L4_chi5quad_q5":  dict(helixUnit=4.43819,  mode=5.0,  src="data"),
    "L5_chi5c4_q5":    dict(helixUnit=0.83554,  mode=10.0, src="data"),
    "L6_chi7quad_q7":  dict(helixUnit=0.22741,  mode=14.0, src="data"),
}

def configured_helix(label: str, n_integers: int = 250_000) -> Helix:
    """Helix with the channel's own constants when the table assigns them."""
    cfg = CHANNEL_TABLE.get(label)
    if cfg is None:
        return Helix(HelixParams(n_integers=n_integers))      # defaults; config unset
    U = math.pi / cfg["helixUnit"]
    return Helix(HelixParams(radial=math.exp(cfg["mode"]), pitch=U, spacing=U,
                             n_integers=n_integers))


class BucketedFiber(ActualFiber):
    """The actual fiber with its captured values BUCKETED by the conductor:

        positive : Re chi(n) > 0      negative : Re chi(n) < 0      neutral : chi(n) = 0

    (exact channel split for quadratic characters; sector split for complex ones).
    Per bucket the fiber tracks, at every consumed integer: the count, the captured
    mass sum(amp), and the captured complex sum -- and reports the bucket state at
    each harmonic mark, including the running imbalance (pos - neg counts and the
    full complex channel sum, the object the kernel's closure ledger quantizes).
    """

    def _capture(self):
        super()._capture()
        re = np.real(self.channel)
        self.b_pos = re > 1e-12
        self.b_neg = re < -1e-12
        self.b_neu = np.abs(self.channel) < 1e-12

    def bucket_state(self, n_consumed: int) -> dict:
        sl = slice(0, n_consumed)
        return {
            "n": n_consumed,
            "count": (int(self.b_pos[sl].sum()), int(self.b_neg[sl].sum()),
                      int(self.b_neu[sl].sum())),
            "mass": (float(self.amp[sl][self.b_pos[sl]].sum()),
                     float(self.amp[sl][self.b_neg[sl]].sum()),
                     float(self.amp[sl][self.b_neu[sl]].sum())),
            "imbalance_count": int(self.b_pos[sl].sum()) - int(self.b_neg[sl].sum()),
            "channel_sum": complex((self.channel[sl]).sum()),
        }

    def marks_with_buckets(self, num: int = 20):
        """Harmonic marks plus the bucket state at the integer last consumed."""
        marks = self.run_actual(num)
        out = []
        for t in marks:
            # integers consumed by height t: z_n <= t
            n_consumed = int(np.searchsorted(self.helix.z, t))
            out.append((t, self.bucket_state(n_consumed)))
        return out


def main_buckets():
    here = os.path.dirname(os.path.abspath(__file__))
    print("CHANNEL BUCKETS at the first 12 marks (count +/-/0, imbalance, channel sum)")
    for spec in SPECS:
        helix = configured_helix(spec.label)
        cfg = "CONFIGURED" if spec.label in CHANNEL_TABLE else "default (config UNSET)"
        f = BucketedFiber(spec, helix)
        print(f"\n{spec.label}  [{cfg}]  q={spec.q}")
        print(f"  {'mark t':>9s} {'consumed':>9s} {'+':>7s} {'-':>7s} {'0':>6s} {'imb':>5s}  channel sum")
        for t, st in f.marks_with_buckets(12):
            cs = st['channel_sum']
            print(f"  {t:9.4f} {st['n']:9d} {st['count'][0]:7d} {st['count'][1]:7d}"
                  f" {st['count'][2]:6d} {st['imbalance_count']:5d}  {cs.real:+.3f}{cs.imag:+.3f}i")


# ===========================================================================
# CALIBRATION: the honest cost of the harmonics (no level indexing)
# ===========================================================================
# The question (Sam): "put the integers on the helix super closely, or change
# the energy cost of the harmonics -- pi is too cheap for the first one."
# The two knobs coincide geometrically: dense packing (small U) and the table's
# constants (U/A tiny) both put the first ~A/(2 pi U) integers on the nearly
# straight bottom segment, where radii grow LINEARLY (amp ~ 1/n) before the
# spiral regime (amp ~ 1/sqrt n).  Equivalent default-density of the table rows:
#   chi3 row  : n(t) = 1103.7 t^2  ~  351 x default
#   chi4 row  : n(t) = 2416.5 t^2  ~  769 x default
# This section measures, with NO level indexing:
#   c_birth = (E(g1) - E(2pi/q)) / pi      cost of harmonic 1 from fiber birth
#   c_base  = (E(g1) - E(t_floor)) / pi    ... from the object's base (t ~ 0.25)
#   c_dip   = (E(g1) - min E) / pi         ... from the accumulation minimum
#   delta_m = (E(g_m) - E(g_{m-1})) / pi   cost of each later harmonic
# and the model's own first purchase: the t where E first reaches anchor + pi.

def helix_covering(label: str, z_max: float, density: float | None = None) -> Helix:
    """A helix whose placed integers cover heights up to z_max.

    density=None uses the table config when assigned (else default D=1);
    a numeric density D places integers at spacing U = 1/D (default constants).
    """
    cfg = CHANNEL_TABLE.get(label) if density is None else None
    if cfg is not None:
        U = math.pi / cfg["helixUnit"]; A = math.exp(cfg["mode"]); P = U
    else:
        D = float(density if density is not None else 1.0)
        A, P, U = 1.0, 1.0, 1.0 / D
    n_need = int((A * math.pi / U) * (z_max / P) ** 2 * 1.03) + 16
    h = Helix(HelixParams(radial=A, pitch=P, spacing=U, n_integers=n_need))
    assert float(h.z[-1]) >= z_max, f"coverage short: {h.z[-1]:.2f} < {z_max}"
    return h


def measure_costs(spec: CharSpec, helix: Helix, zeros_dir: str,
                  n_zeros: int = 10, grid_step: float = 0.05,
                  t_floor: float = 0.25) -> dict:
    f = BucketedFiber(spec, helix, grid_step=grid_step)
    path = os.path.join(zeros_dir, f"{spec.label}.txt")
    zeros = [float(l.split()[1]) for l in open(path) if not l.startswith('#')][:n_zeros]
    ts, E = f.E_grid(t_floor=t_floor, t_max=zeros[-1] + 1.5)
    Ez = np.interp(zeros, ts, E)
    birth = TWO_PI / spec.q + 0.05
    E_birth = float(np.interp(birth, ts, E))
    i_dip = int(np.argmin(E)); E_dip = float(E[i_dip]); t_dip = float(ts[i_dip])
    deltas = np.diff(Ez) / math.pi

    def first_purchase(anchor):                 # first t with E = anchor + pi
        lvl = anchor + math.pi
        idx = np.nonzero((E[:-1] < lvl) & (E[1:] >= lvl))[0]
        if len(idx) == 0:
            return float('nan')
        i = idx[0]
        return float(ts[i] + (lvl - E[i]) / (E[i+1] - E[i]) * grid_step)

    buckets = [f.bucket_state(int(np.searchsorted(f.helix.z, g))) for g in zeros]
    return {
        "label": spec.label, "n_int": helix.params.n_integers,
        "c_birth": (float(Ez[0]) - E_birth) / math.pi,
        "c_base":  (float(Ez[0]) - float(E[0])) / math.pi,
        "c_dip":   (float(Ez[0]) - E_dip) / math.pi, "t_dip": t_dip,
        "buy_birth": first_purchase(E_birth),
        "buy_dip":   first_purchase(E_dip),
        "g1": zeros[0],
        "deltas": deltas, "mean_d": float(np.mean(deltas)), "std_d": float(np.std(deltas)),
        "imb": [b["imbalance_count"] for b in buckets],
        "neu": [b["count"][2] for b in buckets],
    }


def main_costs():
    here = os.path.dirname(os.path.abspath(__file__))
    zeros_dir = os.path.join(here, 'zeros')
    print("HONEST HARMONIC COSTS (units of pi; no level indexing)")
    print("  c_* = cost of the FIRST harmonic measured from birth/base/dip anchor")
    print("  buy_* = where a full-pi purchase from that anchor lands (vs g1)")
    for spec in SPECS:
        if spec.q == 1:
            continue                            # principal chi: captured sum diverges
        path = os.path.join(zeros_dir, f"{spec.label}.txt")
        zeros = [float(l.split()[1]) for l in open(path) if not l.startswith('#')]
        z_max = zeros[9] + 2.0
        row = CHANNEL_TABLE[spec.label]
        runs = [("default D=1", 1.0),
                (f"{row['src']} row (d={row['helixUnit']:.3f}, e^{row['mode']:.0f})", None)]
        print(f"\n{spec.label}  q={spec.q}  g1={zeros[0]:.4f}")
        for name, dens in runs:
            h = helix_covering(spec.label, z_max, density=dens)
            r = measure_costs(spec, h, zeros_dir)
            d_str = " ".join(f"{d:5.3f}" for d in r["deltas"][:6])
            print(f"  [{name}]  n_int={r['n_int']}")
            print(f"    c_birth={r['c_birth']:7.4f}  c_base={r['c_base']:7.4f}"
                  f"  c_dip={r['c_dip']:7.4f}  (dip at t={r['t_dip']:.2f})")
            print(f"    buy(birth+pi)={r['buy_birth']:8.4f}  buy(dip+pi)={r['buy_dip']:8.4f}"
                  f"  vs g1={r['g1']:.4f}")
            print(f"    delta_2..7 = {d_str}   mean={r['mean_d']:.4f} +/- {r['std_d']:.4f}")
            print(f"    bucket imbalance at zeros: {r['imb']}")


# ===========================================================================
# STANDING GAUGE: the fiber is already harmonic form (measured)
# ===========================================================================
# In ONE fixed gauge per channel -- e^{i(theta(t) + alpha)}, alpha = the root
# number half-phase (measured = ray to ~1e-3 rad) -- the captured fiber
#     u(t) = e^{i theta} sum_n chi(n) amp_n e^{-it log n}
# is REAL to truncation order (R = 0.035-0.041 ~ q/sqrt(N)) over the whole
# window: standing EVERYWHERE on the line, not just at zeros.  Each captured
# term is already a real harmonic  chi(n) amp_n cos(theta - t log n + alpha):
# no conversion from integers to harmonics happens -- the placement IS the
# harmonic decomposition (frequency log n, amplitude 1/R(k_n)).  The sine
# (traveling) channel cancels AS A SUM, and the cancellation is carried by the
# sign ARRANGEMENT alone: shuffling live signs among live positions (same
# masses, same neutral set, same amplitudes) gives R = 0.64-0.70 (isotropic
# phasor).  Nodes of the real wave = the certified zeros (50/50 sign flips).

def standing_test(spec: CharSpec, n_zeros: int = 10, seed: int = 7) -> dict:
    """Standing-gauge metric R (true vs scrambled arrangement) + node check."""
    rng = np.random.default_rng(seed)
    here = os.path.dirname(os.path.abspath(__file__))
    path = os.path.join(here, 'zeros', f"{spec.label}.txt")
    g = [float(l.split()[1]) for l in open(path) if not l.startswith('#')][:n_zeros]
    h = helix_covering(spec.label, g[-1] + 2.0, density=1.0)
    f = BucketedFiber(spec, h)
    ts = np.arange(TWO_PI/spec.q + 0.05, g[-1] + 1.0, 0.05)
    th = np.array([f._theta(float(t)) for t in ts])

    def gauge_R(channel):
        w = channel * f.amp
        F = (w[None, :] * np.exp(-1j*ts[:, None]*f.logn[None, :])).sum(axis=1)
        u = np.exp(1j*th) * F
        a = -0.5*np.angle((u**2).sum())                  # best fixed gauge (closed form)
        out = []
        for aa in (a, a + math.pi/2):
            r = math.sqrt(float((np.imag(np.exp(1j*aa)*u)**2).sum() / (np.abs(u)**2).sum()))
            out.append((aa, r, u))
        return min(out, key=lambda x: x[1])

    a, R, u = gauge_R(f.channel)
    V = np.real(np.exp(1j*a)*u)
    mids = [ts[0]] + [0.5*(g[i]+g[i+1]) for i in range(len(g)-1)] + [g[-1]+0.8]
    sv = [float(np.interp(m, ts, V)) for m in mids]
    flips = sum(1 for i in range(len(sv)-1) if sv[i]*sv[i+1] < 0)
    live = np.abs(f.channel) > 1e-12
    ch = f.channel.copy(); vals = ch[live]; rng.shuffle(vals); ch[live] = vals
    _, Rs, _ = gauge_R(ch)
    da = min(abs(((a - f.ray_offset) + math.pi/2) % math.pi - math.pi/2),
             abs(((a + f.ray_offset) + math.pi/2) % math.pi - math.pi/2))
    return {"label": spec.label, "R_true": R, "R_scrambled": Rs,
            "alpha_vs_ray": da, "flips": flips, "n_zeros": len(g)}


def main_standing():
    print("STANDING GAUGE TEST (R: 0 = pure standing; ~0.7 = isotropic traveling)")
    for spec in SPECS:
        if spec.q == 1:
            continue
        r = standing_test(spec)
        print(f"  {r['label']:18s} R_true={r['R_true']:.4f}  R_scrambled={r['R_scrambled']:.4f}"
              f"  alpha*=ray to {r['alpha_vs_ray']:.4f} rad  flips {r['flips']}/{r['n_zeros']}")


# ===========================================================================
# CHANNEL BREAKOUT: where the standing wave lives among the conductor classes
# ===========================================================================
# Per live class value v (e.g. +1/-1; for order 4 also +/-i), the class phasor
#     u_v(t) = e^{i theta} sum_{chi(n)=v} amp_n e^{-it log n}
# is that class's eaten, phase-weighted amplitude.  Measured (5 channels):
#   - ALONE each class is a traveling spiral (R = 0.63-0.70) that keeps eating
#     with the horizon (carrier grows x1.15-1.38 per x4 integers), dominated by
#     the shared principal/zeta-like carrier (|corr| = 0.71-0.90) that every
#     class holds equally (1/phi(q) of the unsigned sum);
#   - the SIGNED sum annihilates the carrier exactly: horizon-stable (x1.00),
#     standing (R = 0.035), bounded.  The wave is the inter-class difference;
#   - ZEROS are the rendezvous: the class phasors coincide (|u_+ - u_-|/|u| =
#     0.06-0.10 = truncation scale) -- equal eaten amplitude; midpoints are
#     maximal separation.  |standing wave| = the channel separation;
#   - order-4: pair differences lock in quadrature at zeros on average,
#     (u_1 - u_-1) = -i (u_i - u_-i)  (mean -0.11-1.06i; per-zero noisy, 0/0);
#   - the NEUTRAL class has weight 0: eats placement, never amplitude.

def channel_phasors(spec: CharSpec, n_zeros: int = 10, step: float = 0.02):
    """Grid, certified zeros, and per-class phasors u_v(t) for a channel."""
    here = os.path.dirname(os.path.abspath(__file__))
    g = np.array([float(l.split()[1]) for l in
                  open(os.path.join(here, 'zeros', f"{spec.label}.txt"))
                  if not l.startswith('#')][:n_zeros])
    h = helix_covering(spec.label, float(g[-1]) + 2.0, density=1.0)
    f = BucketedFiber(spec, h)
    ts = np.arange(TWO_PI/spec.q + 0.05, float(g[-1]) + 1.0, step)
    ph = np.exp(1j*np.array([f._theta(float(t)) for t in ts]))
    vals = [v for v in (1+0j, 1j, -1+0j, -1j) if np.any(np.isclose(f.channel, v))]
    U = {}
    for v in vals:
        m = np.isclose(f.channel, v)
        U[v] = ph * (f.amp[None, m] * np.exp(-1j*ts[:, None]*f.logn[None, m])).sum(axis=1)
    return ts, g, vals, U


# ===========================================================================
# THE FULL OBJECT PIPE -- and the amplitude-law discrimination it produced
# ===========================================================================
# GeometricFiber reads EVERY captured number off the object: amplitude from the
# placed radii (as before), the bridge phase from the object's own measured
# unwound arc  t*log(s_n/U), s_n = A*arc0(k_n)  (matches log n to 1.8e-15 --
# the placement is exact), heights through projection A (|z|).  Run under the
# configured table rows (1.0-2.5M integers):
#   - NODES and SELF-INTERFERENCE are placement-robust: sign flips 50/50 for
#     the full wave AND for the 2-5 mode head; fold corr 0.98-0.99.
#   - STANDING PURITY is amplitude-law sensitive: R = 0.37-0.43 (vs 0.035 at
#     default placement), because the rows' long linear bottoms (n <~ A/(2piU):
#     61 / 302 / 932 / 13856 integers) give amp = 1/R(k) ~ 1/n there instead of
#     n^(-1/2) -- exactly where the head lives.
# DISCRIMINATION: two geometric amplitude readouts coincide in the spiral
# regime and differ on the bottom:  1/R(k_n) (instantaneous radius)  vs
# 1/sqrt(s_n/U) (unwound arc -- the area law).  The clean standing wave
# (R = 0.035, zero off-zero crossings) is the ARC/AREA law, which equals
# n^(-1/2) on EVERY configuration (config-invariant).  Reading: the rows
# govern the budget/cost geometry (C); the wave's amplitude is carried by the
# unwound length, not the instantaneous radius.

class GeometricFiber(BucketedFiber):
    """Fiber with the phase read off the object's own unwound arc (the bridge
    log of the MEASURED arc, not of the integer label)."""
    def _capture(self):
        super()._capture()
        from helix3d import _arc0
        p = self.helix.params
        s = p.radial * _arc0(self.helix.k)
        logn_geom = np.log(s / p.spacing)
        self.logn_resid = float(np.max(np.abs(logn_geom - self.logn)))
        self.logn = logn_geom


def helix_covering_pitched(label: str, z_max: float) -> Helix:
    """PITCH-CORRECTED configuration (Sam, 2026-06-11: "we have our pitch wrong").

    The two measured constraints fix the geometry jointly:
      (1) amplitude law: 1/R must be the area law n^(-1/2) from the FIRST
          integer => spiral regime immediately => radial slope A = U;
      (2) the channel's cost coefficient C (table row) is data-pinned and
          n(z) = C z^2 must be preserved  =>  pitch P = sqrt(pi / C).
    The pitch carries ALL the channel dependence (P = e^{-mode/2} (pi/d)^{3/2}):
    richer channels coil flatter -- pitch is the accumulation-velocity dial.
    """
    row = CHANNEL_TABLE[label]
    U = math.pi / row["helixUnit"]
    C = math.exp(row["mode"]) * math.pi / U ** 3        # the row's density coeff
    P = math.sqrt(math.pi / C)
    n_need = int(C * z_max ** 2 * 1.03) + 16
    h = Helix(HelixParams(radial=U, pitch=P, spacing=U, n_integers=n_need))
    assert float(h.z[-1]) >= z_max, f"coverage short: {h.z[-1]:.2f} < {z_max}"
    return h


# ===========================================================================
# THE TIGHTENING COIL: loop counter = zero counter (item 3)
# ===========================================================================
# The geometry the odd-number ladder demands (measured: d_m = (k_m^2 -
# k_{m-1}^2)/(2m-1) = 1.000 +/- 0.004 mean across all six channels, no trend,
# jitter +/-0.33): standard arc placement with A = U (the pitch correction),
# but the HEIGHT map is z(k) = Nsmooth^{-1}(k + c) -- loop k tops out at the
# smooth k-th zero height.  Pitch profile dz/dk = 2 pi / log(q z / 2 pi): the
# coil tightens logarithmically (pitch = quantum / velocity).  Consequences:
#   - one zero per loop ON THE OBJECT (the no-drift series, realized);
#   - material to reach zero m:  n_m = (A pi / U) (m + c)^2  -- the area law
#     in the zero index; harmonic m costs pi*(2m-1) integers exactly in the
#     mean.  Reaching zero 100 takes ~3.3e4 integers (vs ~6.6e7 at constant
#     pitch for chi_3): the coil is the material-efficient chart.
#   - the amplitude readout is UNCHANGED (capture is height-free): the
#     radius-vs-arc choice is a separate, already-settled question (arc law).

def smooth_count(q: int, t):
    """N_smooth(t) = (t/2pi) log(q t/(2 pi e)) -- RvM main term (numpy-safe)."""
    t = np.asarray(t, dtype=float)
    return t/(2*math.pi) * np.log(np.maximum(q*t/(2*math.pi*math.e), 1e-12))

def tightening_coil(label: str, n_integers: int = 250_000):
    """Helix with the tightening-coil height map; returns (helix, z, c).

    The helix's arc placement is standard (A = U from the table row); its z
    array is REPLACED by z(k) = Ninv(k + c), with the single constant c
    calibrated from the channel's certified zeros (mean of m - N(gamma_m)).
    """
    row = CHANNEL_TABLE[label]
    U = math.pi / row["helixUnit"]
    h = Helix(HelixParams(radial=U, pitch=1.0, spacing=U, n_integers=n_integers))
    q = int(label.split("_q")[1])
    here = os.path.dirname(os.path.abspath(__file__))
    g = np.array([float(l.split()[1]) for l in open(os.path.join(here, 'zeros', f"{label}.txt"))
                  if not l.startswith('#')])
    c = float(np.mean(np.arange(1, len(g)+1) - smooth_count(q, g)))
    lo = np.full_like(h.k, 0.5); hi = np.full_like(h.k, 1e7)
    for _ in range(60):                          # vectorized bisection for Ninv
        mid = 0.5*(lo + hi)
        too_low = smooth_count(q, mid) < h.k - c       # solve N(z) = k - c
        lo = np.where(too_low, mid, lo); hi = np.where(too_low, hi, mid)
    z = 0.5*(lo + hi)
    return h, z, c


def main_coil(label: str = "L2_chi3_q3"):
    h, z, c = tightening_coil(label)
    here = os.path.dirname(os.path.abspath(__file__))
    g = np.array([float(l.split()[1]) for l in open(os.path.join(here, 'zeros', f"{label}.txt"))
                  if not l.startswith('#')])
    # (a) one zero per loop on the object: loop index at each certified zero
    q = int(label.split("_q")[1])
    k_at_zero = smooth_count(q, g) + c
    dev = k_at_zero - np.arange(1, len(g)+1)
    # (b) the material ladder off the object: integers consumed per zero
    n_at = np.searchsorted(z, g).astype(float)
    m = np.arange(2, len(g)+1, dtype=float)
    d = (n_at[1:] - n_at[:-1]) / (2*m - 1)
    print(f"{label}: coil with c = {c:+.4f}, {h.params.n_integers} integers reach z = {z[-1]:.1f}")
    print(f"  one-per-loop: max|k(g_m) - m| = {np.abs(dev).max():.3f}  std = {dev.std():.3f}")
    print(f"  material ladder: mean Dn/(2m-1) = {d.mean():.3f}  (predict A*pi/U = {math.pi:.3f})"
          f"  std/mean = {d.std()/d.mean():.3f}")
    print(f"  material to zero 100: {int(n_at[99])} integers (constant-pitch row needs"
          f" ~{int(np.exp(CHANNEL_TABLE[label]['mode'])*math.pi/(math.pi/CHANNEL_TABLE[label]['helixUnit'])**3 * g[99]**2):,})")
