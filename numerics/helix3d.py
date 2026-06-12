"""
helix3d.py -- THE 3D HELIX OBJECT, actually built.

Mirrors the kernel geometry (RequestProject/HelixDefs.lean, HelixArcLength.lean) exactly:

  * the UNWOUND LINE: integer n sits at arc position  s_n = n * U   (even spacing;
    U = integer placement distance -- `placed mode U n k := arc mode k = n*U`),
  * the REWIND: Archimedean spiral, LINEAR radial law  R(k) = A * k  (A = radial
    expansion constant, smooth -- `loopRadius`), angle phi = 2*pi*k, height z = P * k
    (P = pitch, smooth),
  * the PLACEMENT: k(n) solves  A * arc0(k) = n * U  where arc0 is the planar arc
    length -- closed form  arc0(k) = k*sqrt(1+4*pi^2*k^2)/2 + asinh(2*pi*k)/(4*pi).
    Existence/uniqueness is the kernel theorem `HelixArcLength.existsUnique_placed`;
    here it is inverted by Newton with the kernel's sandwich as the seed
    (`radius_theta_sqrtn`: k ~ sqrt(n*U/(A*pi))).

The sqrt(n) frame is EARNED, not assumed: the self-test checks the kernel's two-sided
bound  U/(1+pi) * n  <=  R(k_n)^2 / A  <=  U/pi * n   (`radius_sq_slope_cancels`).

Projections (3D -> collapsed height; the radial coordinate is destroyed, height kept):
  * project_absolute(target)        -> Point3D with height = |z|.
  * project_stacked(z_list, mode)   -> heights under the three stacking conventions
    ('absolute' | 'sum' | 'diff') -- the stacking decision is deliberately deferred;
    all three are exposed so data can decide.

Targets may be any positive real (integers, rational fractions, ...): the target is a
position nu on the unwound line, placed at arc nu * U.

Default build: 250_000 integers.
"""
from __future__ import annotations
from dataclasses import dataclass, field
import math
import numpy as np

TWO_PI = 2.0 * math.pi


@dataclass(frozen=True)
class HelixParams:
    """The construction's constants. Nothing else parametrizes the object."""
    radial: float = 1.0      # A: linear radial slope, R(k) = A*k        (smooth)
    pitch: float = 1.0       # P: height per loop-unit, z(k) = P*k       (smooth)
    spacing: float = 1.0     # U: arc distance between consecutive integers
    n_integers: int = 250_000

    def __post_init__(self):
        if self.radial <= 0 or self.pitch <= 0 or self.spacing <= 0:
            raise ValueError("radial, pitch, spacing must all be positive")
        if self.n_integers < 2:
            raise ValueError("need at least 2 integers on the line")


@dataclass(frozen=True)
class Point3D:
    """A placed point: line position nu, loop parameter k, coordinates, height."""
    nu: float
    k: float
    x: float
    y: float
    z: float
    height: float            # the collapsed-height reading for this projection


def _arc0(k):
    """Slope-free planar arc length of the unit Archimedean spiral (closed form)."""
    c = TWO_PI * k
    return k * np.sqrt(1.0 + c * c) / 2.0 + np.arcsinh(c) / (2.0 * TWO_PI)


def _speed0(k):
    """d(arc0)/dk = sqrt(1 + (2*pi*k)^2)."""
    c = TWO_PI * k
    return np.sqrt(1.0 + c * c)


class Helix:
    """The built 3D object: every integer (and any real target) has its one place.

    Construction is eager: `build()` (called by __init__) solves the placement for
    all n_integers at once and stores the coordinate arrays.
    """

    def __init__(self, params: HelixParams = HelixParams()):
        self.params = params
        self._build()

    # -- placement inversion ------------------------------------------------
    def _solve_k(self, nu):
        """k(nu): A * arc0(k) = nu * U, by Newton from the kernel-sandwich seed.

        Vectorized; nu may be a scalar or array of positive reals.
        """
        p = self.params
        target = np.asarray(nu, dtype=float) * p.spacing / p.radial   # arc0(k) target
        k = np.sqrt(np.maximum(target, 1e-300) / math.pi)             # seed: k ~ sqrt(t/pi)
        for _ in range(40):
            f = _arc0(k) - target
            step = f / _speed0(k)
            k = np.maximum(k - step, 0.0)
            if np.max(np.abs(step)) < 1e-13 * max(1.0, float(np.max(k))):
                break
        return k

    def _build(self):
        p = self.params
        self.n = np.arange(1, p.n_integers + 1, dtype=float)
        self.k = self._solve_k(self.n)
        phi = TWO_PI * self.k
        self.x = p.radial * self.k * np.cos(phi)
        self.y = p.radial * self.k * np.sin(phi)
        self.z = p.pitch * self.k

    # -- the honest API -----------------------------------------------------
    def point(self, nu: float) -> Point3D:
        """Place ANY positive real target (integer, rational, ...) on the helix."""
        if nu <= 0:
            raise ValueError("targets live on the positive line")
        k = float(self._solve_k(nu))
        phi = TWO_PI * k
        p = self.params
        x, y, z = p.radial * k * math.cos(phi), p.radial * k * math.sin(phi), p.pitch * k
        return Point3D(nu=float(nu), k=k, x=x, y=y, z=z, height=abs(z))

    def height_of(self, nu: float) -> float:
        """Collapsed height of a target: |z| (radial information destroyed)."""
        return self.point(nu).height

    # -- projection 1: absolute z -------------------------------------------
    def project_absolute(self, nu: float) -> Point3D:
        """Projection A: each mark's height is its own |z|."""
        return self.point(nu)

    # -- projection 2: stacked ----------------------------------------------
    @staticmethod
    def project_stacked(zs, mode: str = "absolute"):
        """Projection B: heights from a SEQUENCE of marks' z-values.

        mode = 'absolute' : h_j = |z_j|                      (no stacking)
        mode = 'sum'      : h_j = z_1 + z_2 + ... + z_j      (first plus second ...)
        mode = 'diff'     : h_1 = z_1, h_j = z_j - z_{j-1}   (second minus first ...)

        The stacking convention is deliberately undecided; all three are exposed.
        """
        zs = list(map(float, zs))
        if mode == "absolute":
            return [abs(z) for z in zs]
        if mode == "sum":
            out, acc = [], 0.0
            for z in zs:
                acc += z
                out.append(acc)
            return out
        if mode == "diff":
            return [zs[0]] + [zs[j] - zs[j - 1] for j in range(1, len(zs))]
        raise ValueError(f"unknown stacking mode {mode!r}")

    # -- self-tests (kernel laws on the actual object) ----------------------
    def self_test(self) -> dict:
        """Check the built object against the kernel's theorems. Raises on failure."""
        p = self.params
        # (1) placement law: arc(k_n) = n*U  (existsUnique_placed)
        resid = np.max(np.abs(p.radial * _arc0(self.k) - self.n * p.spacing))
        assert resid < 1e-6 * p.spacing * p.n_integers ** 0.5, f"placement residual {resid}"
        # (2) earned sqrt(n): kernel sandwich U/(1+pi)*n <= R^2/A <= U/pi*n for k >= 1
        #     (radius_sq_slope_cancels; lower bound needs k >= 1)
        mask = self.k >= 1.0
        R2_over_A = (p.radial * self.k[mask]) ** 2 / p.radial
        nm = self.n[mask]
        lo_ok = np.all(p.spacing / (1.0 + math.pi) * nm <= R2_over_A * (1 + 1e-12))
        hi_ok = np.all(R2_over_A <= p.spacing / math.pi * nm * (1 + 1e-12))
        assert lo_ok and hi_ok, "kernel radius sandwich violated"
        # (3) strict monotonicity of height in n (the climb never reverses)
        assert np.all(np.diff(self.z) > 0), "height not strictly increasing"
        return {
            "placement_residual": float(resid),
            "sandwich": "U/(1+pi)*n <= R^2/A <= U/pi*n verified for k>=1",
            "monotone": True,
            "n_integers": p.n_integers,
            "z_max": float(self.z[-1]),
            "k_max": float(self.k[-1]),
        }


if __name__ == "__main__":
    h = Helix(HelixParams())
    report = h.self_test()
    print("helix3d self-test PASSED:", report)
    # a rational target, as promised by the API
    pt = h.point(7.5)
    print(f"target 7.5 -> k={pt.k:.6f} (x,y,z)=({pt.x:+.4f},{pt.y:+.4f},{pt.z:.4f}) height={pt.height:.4f}")
    # stacking conventions on the first three integer marks
    zs = [h.point(n).z for n in (1, 2, 3)]
    for m in ("absolute", "sum", "diff"):
        print(f"stacked[{m}] of z(1..3) = {Helix.project_stacked(zs, m)}")
