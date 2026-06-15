import Mathlib
import RequestProject.HelixProjectionZeros

/-!
# The helix lands on the unit circle — the geometric target, unconditional

Consolidation of the geometric statement: the prime winding
`helix_point x = e^{i(π/3)·log x}` is a multiplicative map from `(ℝ₊, ·)` **onto**
the unit circle, with sixth-root (μ₆) structure and `e^6` pitch. The 3D log-spiral
projects onto the 2D unit circle — and covers it.

All unconditional. The one new piece is **surjectivity** (`helix_surjective_onto_circle`):
"lands on the circle" upgraded to "covers the circle."
-/

noncomputable section
open Complex Real

/-- **The winding covers the circle.** Every unit-modulus point is the image of some
    scale `x > 0` under the helix winding — so the image is exactly the unit circle. -/
theorem helix_surjective_onto_circle (z : ℂ) (hz : ‖z‖ = 1) :
    ∃ x : ℝ, 0 < x ∧ helix_point x = z := by
  obtain ⟨θ, hθ⟩ := (Complex.norm_eq_one_iff z).mp hz
  refine ⟨Real.exp (3 * θ / Real.pi), Real.exp_pos _, ?_⟩
  unfold helix_point
  rw [helix_angle_eq, Real.log_exp]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hθ' : (Real.pi / 3) * (3 * θ / Real.pi) = θ := by field_simp
  rw [hθ']; exact hθ

/-- **The helix lands on (and covers) the 2D unit circle — unconditional.**
    Six facts, one statement:
    1. into the circle (`‖·‖ = 1`);
    2. onto the circle (surjective — covers it);
    3. multiplicative (multiplication on `ℝ₊` = angle addition: a group hom to `S¹`);
    4. `e^6` pitch (one full turn per native radial growth `x ↦ e^6 x`);
    5. μ₆ / sixth-root structure (`ω^6=1`, `ω^3=-1`, `|ω|=1`);
    6. Pythagorean energy conservation on the circle (`cos² + sin² = 1`). -/
theorem helix_lands_on_circle :
    (∀ x : ℝ, ‖helix_point x‖ = 1) ∧
    (∀ z : ℂ, ‖z‖ = 1 → ∃ x : ℝ, 0 < x ∧ helix_point x = z) ∧
    (∀ x y : ℝ, 0 < x → 0 < y → helix_point (x * y) = helix_point x * helix_point y) ∧
    (∀ x : ℝ, 0 < x → helix_point (Real.exp 6 * x) = helix_point x) ∧
    (omega ^ 6 = 1 ∧ omega ^ 3 = -1 ∧ ‖omega‖ = 1) ∧
    (∀ x : ℝ, projection_2d_to_1d x ^ 2 + quadrature_loss x ^ 2 = 1) :=
  ⟨helix_point_norm,
   helix_surjective_onto_circle,
   helix_point_mul,
   helix_point_exp_six_mul,
   ⟨omega_pow_six, omega_pow_three, omega_norm⟩,
   circle_pythagorean⟩

end

#print axioms helix_surjective_onto_circle
#print axioms helix_lands_on_circle
