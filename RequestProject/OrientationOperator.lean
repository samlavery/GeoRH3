import Mathlib

/-!
# `i` is an orientation operator, and `i²` is the functional equation

On the centered coordinate `w = ρ − ½` (so a zero `ρ = ½ + α + iγ` has `w = α + iγ`, radial part `α`
and pitch part `γ`), multiplication by `i` is the **orientation operator** `J`:

* `J² = −1` — it's a complex structure;
* `‖J z‖ = ‖z‖` — an isometry (a genuine rotation, not a shear);
* it rotates the **radial** axis onto the **pitch** axis and back with a sign;
* `det J = +1` — orientation‑**preserving**, against conjugation's `det = −1` (orientation‑reversing).

And the structural payoff, compiled:

* `J² = −1` acting on `w = ρ − ½` is exactly `w ↦ −w`, i.e. `ρ ↦ 1 − ρ` — **the functional equation**.

So the FE is not a separate symmetry: it is the orientation operator squared. One quarter‑turn swaps
radial↔pitch; two quarter‑turns is `ρ ↦ 1−ρ`. No RH content — pure structure, axiom‑clean.
-/

open Complex

namespace OrientationOperator

/-- `J² = −1`: `i` is a complex structure (the defining property of an orientation operator). -/
theorem i_complex_structure : Complex.I ^ 2 = -1 := Complex.I_sq

/-- `i` is an isometry — a rotation of the plane, not a shear. -/
theorem i_isometry (z : ℂ) : ‖Complex.I * z‖ = ‖z‖ := by
  rw [norm_mul, Complex.norm_I, one_mul]

/-- `i` rotates the **radial** axis (real part `α`) onto the **pitch** axis (imaginary part `γ`). -/
theorem i_radial_to_pitch (α : ℝ) : Complex.I * (α : ℂ) = α * Complex.I := by ring

/-- …and the pitch axis back onto `−`radial. -/
theorem i_pitch_to_radial (γ : ℝ) : Complex.I * ((γ : ℂ) * Complex.I) = -(γ : ℂ) := by
  have h : Complex.I * ((γ : ℂ) * Complex.I) = (γ : ℂ) * (Complex.I * Complex.I) := by ring
  rw [h, Complex.I_mul_I]; ring

/-- The field norm of `i` over `ℝ` is `1` (it equals `normSq i`). -/
theorem i_norm_eq_one : Algebra.norm ℝ Complex.I = 1 := by
  rw [Algebra.norm_complex_apply, Complex.normSq_I]

/-- **`i` is orientation‑preserving**: the real determinant of multiplication by `i` is `+1`. -/
theorem i_orientation_preserving :
    LinearMap.det (LinearMap.mulLeft ℝ Complex.I) = 1 := by
  rw [show LinearMap.det (LinearMap.mulLeft ℝ Complex.I) = Algebra.norm ℝ Complex.I from rfl,
      i_norm_eq_one]

/-- **Conjugation is orientation‑reversing**: its real determinant is `−1` (the contrast with `i`). -/
theorem conj_orientation_reversing :
    LinearMap.det (↑↑Complex.conjAe : ℂ →ₗ[ℝ] ℂ) = -1 := Complex.det_conjAe

/-- **The headline: `i²` is the functional equation.** On the centered coordinate `w = ρ − ½`,
`I² · w = −w = (1 − ρ) − ½` — the orientation operator squared is exactly `ρ ↦ 1 − ρ`. -/
theorem i_sq_is_functional_equation (ρ : ℂ) :
    Complex.I ^ 2 * (ρ - 1 / 2) = (1 - ρ) - 1 / 2 := by
  rw [Complex.I_sq]; ring

/-- **Bundle.** `i` is an orientation operator (complex structure, isometry, orientation‑preserving),
conjugation is its orientation‑reversing counterpart, and `i²` is the functional equation. -/
theorem i_is_orientation_operator :
    (Complex.I ^ 2 = -1) ∧
    (∀ z : ℂ, ‖Complex.I * z‖ = ‖z‖) ∧
    (LinearMap.det (LinearMap.mulLeft ℝ Complex.I) = 1) ∧
    (LinearMap.det (↑↑Complex.conjAe : ℂ →ₗ[ℝ] ℂ) = -1) ∧
    (∀ ρ : ℂ, Complex.I ^ 2 * (ρ - 1 / 2) = (1 - ρ) - 1 / 2) :=
  ⟨i_complex_structure, i_isometry, i_orientation_preserving,
   conj_orientation_reversing, i_sq_is_functional_equation⟩

end OrientationOperator

#print axioms OrientationOperator.i_sq_is_functional_equation
#print axioms OrientationOperator.i_orientation_preserving
#print axioms OrientationOperator.i_is_orientation_operator
