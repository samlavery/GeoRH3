import Mathlib
import RequestProject.HelixEmpiricalCores

/-!
# The 3D helix projects onto the 2D unit circle

Built entirely from my own axiom-clean cores (`HelixEmpiricalCores`, `HelixHalfUnit`),
not from the aristotle infrastructure.

A helix mode `(σ, γ)` at scale `x` is the 3D point
  angular plane : `x^σ · (cos(γ log x), sin(γ log x))`   — the winding
  radial axis   : `σ − ½`                                — distance from the line

* `helix_angular_on_circle`   — the normalized angular projection is ON the unit
  circle (`cos²+sin²=1`), **unconditionally**: the winding only ever projects there.
* `helix_3d_norm_sq`          — `‖3D‖² = x^{2σ} + (σ−½)²`: the 2D-circle radius and the
  radial loss are orthogonal.
* `helix_pure_projection_iff_half` — the projection is *pure* (radial loss `= 0`) iff `σ=½`.
* `helix_projection_unification`   — pure projection ⟺ `σ=½` ⟺ the Möbius/spectral value
  is on the unit circle (`liMap_unit_iff_half`), the same half-unit the scaling forces.
-/

open Real Complex

noncomputable section

namespace HelixProjection

/-- **The winding projects onto the unit circle, unconditionally.** The normalized
    2D angular projection `(cos(γ log x), sin(γ log x))` satisfies `cos² + sin² = 1`. -/
theorem helix_angular_on_circle (γ x : ℝ) :
    Real.cos (γ * Real.log x) ^ 2 + Real.sin (γ * Real.log x) ^ 2 = 1 :=
  Real.cos_sq_add_sin_sq _

/-- **The 3D helix norm splits orthogonally**: the 2D-circle radius² `x^{2σ}` plus the
    radial loss² `(σ−½)²`. -/
theorem helix_3d_norm_sq (σ γ x : ℝ) (hx : 0 < x) :
    (x ^ σ * Real.cos (γ * Real.log x)) ^ 2
      + (x ^ σ * Real.sin (γ * Real.log x)) ^ 2
      + (σ - 1 / 2) ^ 2
    = x ^ (2 * σ) + (σ - 1 / 2) ^ 2 := by
  have hr : (x ^ σ) ^ 2 = x ^ (2 * σ) := by
    rw [sq, ← Real.rpow_add hx, two_mul]
  have key : (x ^ σ * Real.cos (γ * Real.log x)) ^ 2
      + (x ^ σ * Real.sin (γ * Real.log x)) ^ 2 = x ^ (2 * σ) := by
    rw [mul_pow, mul_pow, ← mul_add, helix_angular_on_circle, mul_one, hr]
  linarith [key]

/-- **Pure projection onto the unit circle (zero radial loss) iff `σ = ½`.** -/
theorem helix_pure_projection_iff_half (σ : ℝ) :
    (σ - 1 / 2 = 0) ↔ σ = 1 / 2 := by
  constructor <;> intro h <;> linarith

/-- The Möbius/spectral value sits on the unit circle iff `σ = ½` — straight from the
    derived half-unit core `liMap_unit_iff_half`. -/
theorem helix_spectral_on_circle_iff_half (σ γ : ℝ) (hρ : (⟨σ, γ⟩ : ℂ) ≠ 0) :
    Complex.normSq (1 - 1 / (⟨σ, γ⟩ : ℂ)) = 1 ↔ σ = 1 / 2 := by
  simpa using HelixEmpiricalCores.liMap_unit_iff_half (⟨σ, γ⟩ : ℂ) hρ

/-- **Unification (from my own files): the 3D helix projects PURELY onto the 2D unit
    circle ⟺ `σ = ½` ⟺ the spectral value is on the unit circle.** The radial-loss
    coordinate and the Möbius modulus agree on the half-unit. -/
theorem helix_projection_unification (σ γ : ℝ) (hρ : (⟨σ, γ⟩ : ℂ) ≠ 0) :
    (σ - 1 / 2 = 0) ↔ Complex.normSq (1 - 1 / (⟨σ, γ⟩ : ℂ)) = 1 := by
  rw [helix_pure_projection_iff_half, helix_spectral_on_circle_iff_half σ γ hρ]

end HelixProjection

#print axioms HelixProjection.helix_angular_on_circle
#print axioms HelixProjection.helix_3d_norm_sq
#print axioms HelixProjection.helix_projection_unification
