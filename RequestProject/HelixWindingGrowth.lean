import Mathlib

/-!
# The helix winding-growth — continuous 3-D geometry, log-free, one fitted parameter

The smoothed/continuous helix, at loop parameter `k`:

* **radius**  `R(k) = e^{mode}·k`  — linear (Archimedean): each loop *adds* `e^{mode}`, no compounding;
* **angle**   `φ(k) = 2π·k`        — one full turn per loop (frozen);
* **height**  `z(k) = U·k`         — pitch `U` = change in height per loop.

The **only fitted parameter is the pitch `U`**; the radial law (linear, slope `e^{mode}`) and the
per-loop angle (`2π`) are **frozen**. There is **no `log`** here: the helix is the *argument* of `log`,
not built from it — every `exp` is of the angle or of the constant `mode`, never of a scale. The `√n`
/ area law `n ≈ k²` and the `σ = ½` baseline *emerge* from winding an evenly-spaced integer line onto
this linearly-growing radius (a separate, derived brick); they are not put in here.
-/

open Complex Real

namespace HelixWinding

/-- The 2-D plane point at loop parameter `k`: radius `e^{mode}·k` at angle `2πk`. -/
noncomputable def plane (mode k : ℝ) : ℂ :=
  (↑(Real.exp mode * k) : ℂ) * Complex.exp (↑(2 * Real.pi * k) * Complex.I)

/-- The height at loop parameter `k`: `U·k` (pitch `U` per loop). -/
def height (U k : ℝ) : ℝ := U * k

/-- **The continuous 3-D helix** `(plane, height)`. One fitted parameter `U` (pitch); `mode` and the
    per-loop angle `2π` are frozen. Log-free. -/
noncomputable def helix3D (U mode k : ℝ) : ℂ × ℝ := (plane mode k, height U k)

/-- **The radius is exactly `e^{mode}·k`** — the winding contributes unit modulus, so the distance
    from the axis is the linear Archimedean radial law. (For `k ≥ 0`.) -/
theorem norm_plane (mode : ℝ) {k : ℝ} (hk : 0 ≤ k) : ‖plane mode k‖ = Real.exp mode * k := by
  have h1 : ‖Complex.exp (↑(2 * Real.pi * k) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]; simp
  rw [plane, norm_mul, h1, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]

/-- **The height is `U·k`** — linear, pitch `U` per loop. -/
@[simp] theorem height_eq (U k : ℝ) : height U k = U * k := rfl

/-- **One loop advances the height by exactly the pitch `U`.** -/
theorem height_succ (U k : ℝ) : height U (k + 1) = height U k + U := by
  simp [height]; ring

/-- **One loop grows the radius by exactly `e^{mode}`** (the Archimedean step). -/
theorem norm_plane_succ (mode : ℝ) {k : ℝ} (hk : 0 ≤ k) :
    ‖plane mode (k + 1)‖ = ‖plane mode k‖ + Real.exp mode := by
  rw [norm_plane mode hk, norm_plane mode (by linarith)]; ring

/-- **One loop returns to the same angle** (`2π(k+1) = 2πk + 2π`): the plane direction repeats. -/
theorem plane_dir_period (k : ℝ) :
    Complex.exp (↑(2 * Real.pi * (k + 1)) * Complex.I)
      = Complex.exp (↑(2 * Real.pi * k) * Complex.I) := by
  rw [show (↑(2 * Real.pi * (k + 1)) * Complex.I)
      = ↑(2 * Real.pi * k) * Complex.I + 2 * ↑Real.pi * Complex.I by push_cast; ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- The helix is continuous (smoothed). -/
theorem continuous_helix3D (U mode : ℝ) : Continuous (helix3D U mode) := by
  unfold helix3D plane height
  fun_prop

end HelixWinding
