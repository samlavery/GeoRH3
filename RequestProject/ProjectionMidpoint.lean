import Mathlib
import RequestProject.ConcreteOperators
import RequestProject.Layer1Objects

/-!
# Projection Midpoint: the 1D center is `(1D unit)/2`

The projection cascade `3D → 2D → 1D` (`ConcreteOperators`: `apply_G1`, `apply_G2`,
`apply_cascade`) discards, at the `3D → 2D` step `G₁`, the radial coordinate `σ − 1/2`.
This file ties that `1/2` to the unit `U`: it is the geometric midpoint `U/2`, the fixed
point of the functional-equation reflection `σ ↦ U − σ`, with `U = Layer1.U = 1`.

The trivial involution/midpoint algebra is re-derived inline to avoid a name clash
between `CoordinateInvariance` and `HelixRoundTrip`. All results are unconditional
(axioms: `propext`, `Classical.choice`, `Quot.sound`).
-/

noncomputable section

open Real Complex

namespace ProjectionMidpoint

/-! ## Part 1: the 1D reflection and its fixed point (any unit `U`) -/

/-- The functional-equation reflection `σ ↦ U − σ` has unique fixed point the geometric
    midpoint `U/2`, in any unit `U`. Pure algebra. -/
theorem reflection_fixed_point (U σ : ℝ) : U - σ = σ ↔ σ = U / 2 := by
  constructor <;> intro h <;> linarith

/-- The midpoint of the interval `[0, U]` is `U/2`. -/
theorem interval_midpoint_eq (U : ℝ) : (0 + U) / 2 = U / 2 := by ring

/-- The signed distance from `σ` to the unit-`U` midpoint. -/
def radial_at (U σ : ℝ) : ℝ := σ - U / 2

/-- The radial loss vanishes iff `σ` is the geometric midpoint `U/2`. Pure algebra, any unit. -/
theorem radial_at_zero_iff (U σ : ℝ) :
    radial_at U σ = 0 ↔ σ = U / 2 := by
  unfold radial_at; constructor <;> intro h <;> linarith

/-- Radial loss is zero exactly on the reflection's fixed locus. -/
theorem radial_at_zero_iff_fixed (U σ : ℝ) :
    radial_at U σ = 0 ↔ U - σ = σ := by
  rw [radial_at_zero_iff]; exact (reflection_fixed_point U σ).symm

/-! ## Part 2: the repo's unit `U = 1`, so the midpoint is `1/2` -/

/-- The geometric midpoint at the repo's unit `U = Layer1.U = 1` is `1/2`.
    This *derives* the value `1/2` as the unit-halved midpoint. -/
theorem midpoint_eq_half : Layer1.U / 2 = 1 / 2 := by
  unfold Layer1.U; norm_num

/-! ## Part 3: the cascade's radial coordinate IS the distance to the midpoint -/

/-- The `3D → 2D` projection `G₁` discards exactly the radial coordinate. -/
theorem G1_discards_radial (v : HelixVector) : (apply_G1 v).radial = 0 := rfl

/-- The hardcoded radial loss `σ − 1/2` in `zero_embed` is exactly the unit-`U` signed
    distance to the midpoint at the repo's normalization `U = 1`: the "1/2" *is* `U/2`. -/
theorem zero_embed_radial_eq_radial_at (σ γ x : ℝ) :
    (zero_embed σ γ x).radial = radial_at Layer1.U σ := by
  rw [radial_loss_eq]; unfold radial_at Layer1.U; ring

/-- **The projection cascade locates the midpoint.** What the `3D → 2D` step discards from
    a zero's embedding is its signed distance to the geometric midpoint `U/2`; that
    distance is zero exactly when `σ` is the midpoint `U/2 = 1/2`. -/
theorem cascade_midpoint_is_unit_half (σ γ x : ℝ) :
    (zero_embed σ γ x).radial = radial_at Layer1.U σ ∧
    ((zero_embed σ γ x).radial = 0 ↔ σ = Layer1.U / 2) ∧
    Layer1.U / 2 = 1 / 2 := by
  refine ⟨zero_embed_radial_eq_radial_at σ γ x, ?_, midpoint_eq_half⟩
  rw [zero_embed_radial_eq_radial_at]; exact radial_at_zero_iff Layer1.U σ

/-! ## Part 4: coordinate independence — `1/2` is just the unit halved -/

/-- Under any positive rescaling by `u`, the midpoint moves `1/2 ↦ u/2`. So `1/2` carries
    no intrinsic meaning: it is the midpoint of `[0,1]` only because we chose unit `1`. -/
theorem midpoint_scales (u : ℝ) : u * (1 / 2) = u / 2 := by ring

/-! ## Part 5: master statement -/

/-- **Master (unconditional, geometric): the 1D projection midpoint is `(1D unit)/2`.**

    1. the FE reflection `σ ↦ U − σ` has unique fixed point `U/2`, any unit `U`;
    2. that fixed point is the interval midpoint of `[0, U]`;
    3. the cascade's discarded radial coordinate vanishes exactly at `σ = U/2`;
    4. at the repo unit `U = Layer1.U = 1`, the midpoint is `1/2`;
    5. rescaling by `u` sends the midpoint `1/2 ↦ u/2` (so `1/2` is unit-relative). -/
theorem projection_midpoint_is_unit_half :
    (∀ U σ : ℝ, U - σ = σ ↔ σ = U / 2) ∧
    (∀ U : ℝ, (0 + U) / 2 = U / 2) ∧
    (∀ σ γ x : ℝ, (zero_embed σ γ x).radial = 0 ↔ σ = Layer1.U / 2) ∧
    Layer1.U / 2 = 1 / 2 ∧
    (∀ u : ℝ, u * (1 / 2) = u / 2) := by
  refine ⟨reflection_fixed_point, interval_midpoint_eq, ?_, midpoint_eq_half, midpoint_scales⟩
  intro σ γ x
  rw [zero_embed_radial_eq_radial_at]; exact radial_at_zero_iff Layer1.U σ

end ProjectionMidpoint

end
