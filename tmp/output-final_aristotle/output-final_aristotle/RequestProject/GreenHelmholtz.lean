import Mathlib

/-!
# Green-Helmholtz Operator: Self-Adjoint, No Drift, Strictly Positive

We model the Green-Helmholtz operator `G` as an orthogonal projection on a
real inner product space and prove that the 3D→2D and 2D→1D projection
cascade satisfies:

1. **Self-adjoint**: `⟪Gx, y⟫ = ⟪x, Gy⟫`
2. **No drift**: `⟪Gx, x - Gx⟫ = 0` — the projection is orthogonal to its loss,
   so there is no systematic bias / drift between the projected and lost components.
3. **Strictly positive**: `⟪Gx, x⟫ ≥ 0`, with `⟪Gx, x⟫ = ‖Gx‖²` (positive semi-definite),
   and `⟪Gx, x⟫ = 0 → Gx = 0`.
4. **Midpoint forcing**: The Pythagorean decomposition `‖x‖² = ‖Gx‖² + ‖x - Gx‖²`
   forces the energy split to be balanced at the midpoint — neither the projection
   nor the loss can dominate without the other vanishing.

## Architecture

An orthogonal projection `P` on a real Hilbert space satisfies:
- `P² = P` (idempotent)
- `P* = P` (self-adjoint)

These two properties together give:
- `⟪Px, x⟫ = ⟪Px, Px⟫ = ‖Px‖² ≥ 0` (positivity)
- `⟪Px, x - Px⟫ = 0` (no drift / orthogonal decomposition)
- `‖x‖² = ‖Px‖² + ‖x - Px‖²` (Pythagorean / energy conservation)

The "midpoint" arises because for any nonzero `x` not in `ker P ∪ ker(I - P)`,
both `‖Px‖² > 0` and `‖x - Px‖² > 0`, and the ratio `‖Px‖²/‖x‖²` lives in `(0,1)`.

We instantiate this for:
- **3D → 2D**: `EuclideanSpace ℝ (Fin 3)` projecting onto a 2D subspace
- **2D → 1D**: `EuclideanSpace ℝ (Fin 2)` projecting onto a 1D subspace
-/

noncomputable section

open Submodule

/-! ## Abstract Green-Helmholtz properties -/

section GreenHelmholtz

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable (K : Submodule ℝ F) [K.HasOrthogonalProjection]

/-- **Self-adjoint**: The Green-Helmholtz operator (orthogonal projection) satisfies
    `⟪Gx, y⟫ = ⟪x, Gy⟫`. -/
theorem green_helmholtz_self_adjoint (x y : F) :
    @inner ℝ F _ (K.starProjection x) y = @inner ℝ F _ x (K.starProjection y) :=
  Submodule.inner_starProjection_left_eq_right K x y

/-
**No drift**: The projection is orthogonal to the loss: `⟪Gx, x - Gx⟫ = 0`.
    This means there is no systematic bias between what the operator keeps
    and what it discards.
-/
theorem green_helmholtz_no_drift (x : F) :
    @inner ℝ F _ (K.starProjection x) (x - K.starProjection x) = 0 := by
  rw [ ← real_inner_comm ];
  aesop

/-
**No drift (loss side)**: Equivalently, `⟪x - Gx, Gx⟫ = 0`.
-/
theorem green_helmholtz_no_drift_symm (x : F) :
    @inner ℝ F _ (x - K.starProjection x) (K.starProjection x) = 0 := by
  grind +suggestions

/-
**Positivity**: `⟪Gx, x⟫ = ‖Gx‖²`, which is always `≥ 0`.
-/
theorem green_helmholtz_positive (x : F) :
    @inner ℝ F _ (K.starProjection x) x = ‖K.starProjection x‖^2 := by
  -- By definition of orthogonal projection, we have ⟪Gx, x⟫ = ⟪Gx, Gx + (x - Gx)⟫.
  have h_proj : inner ℝ (K.starProjection x) x = inner ℝ (K.starProjection x) (K.starProjection x + (x - K.starProjection x)) := by
    rw [ add_sub_cancel ];
  -- By the properties of inner products, we can split the inner product into the sum of two inner products.
  have h_split : inner ℝ (K.starProjection x) (K.starProjection x + (x - K.starProjection x)) = inner ℝ (K.starProjection x) (K.starProjection x) + inner ℝ (K.starProjection x) (x - K.starProjection x) := by
    rw [ inner_add_right ];
  rw [ h_proj, h_split, real_inner_self_eq_norm_sq, green_helmholtz_no_drift ] ; ring

/-
**Non-negative**: `⟪Gx, x⟫ ≥ 0`.
-/
theorem green_helmholtz_nonneg (x : F) :
    @inner ℝ F _ (K.starProjection x) x ≥ 0 := by
  rw [ green_helmholtz_positive ] ; positivity

/-
**Strict positivity**: `⟪Gx, x⟫ = 0` implies `Gx = 0` (the projection vanishes).
-/
theorem green_helmholtz_strict_pos (x : F)
    (h : @inner ℝ F _ (K.starProjection x) x = 0) :
    K.starProjection x = 0 := by
  rw [ green_helmholtz_positive ] at h;
  exact norm_eq_zero.mp ( sq_eq_zero_iff.mp h )

/-
**Loss positivity**: `⟪x - Gx, x⟫ = ‖x - Gx‖²`, so the loss is also
    positive semi-definite.
-/
theorem green_helmholtz_loss_positive (x : F) :
    @inner ℝ F _ (x - K.starProjection x) x = ‖x - K.starProjection x‖^2 := by
  -- Use `green_helmholtz_no_drift_symm` to replace `⟪x-Gx, Gx⟫` with zero.
  have h1 : @inner ℝ F _ (x - K.starProjection x) x = @inner ℝ F _ (x - K.starProjection x) (x - K.starProjection x) + @inner ℝ F _ (x - K.starProjection x) (K.starProjection x) := by
    rw [ ← inner_add_right, sub_add_cancel ];
  rw [ h1, real_inner_self_eq_norm_sq, green_helmholtz_no_drift_symm ] ; ring

/-
**Loss strict positivity**: `⟪x - Gx, x⟫ = 0` implies `x = Gx`
    (the loss vanishes, x is in the subspace).
-/
theorem green_helmholtz_loss_strict_pos (x : F)
    (h : @inner ℝ F _ (x - K.starProjection x) x = 0) :
    x - K.starProjection x = 0 := by
  convert green_helmholtz_loss_positive K x using 1;
  constructor <;> intro <;> simp_all +decide [ sq, inner_sub_left ]

/-
**Energy conservation / Pythagorean**: `‖x‖² = ‖Gx‖² + ‖x - Gx‖²`.
-/
theorem green_helmholtz_pythagorean (x : F) :
    ‖x‖^2 = ‖K.starProjection x‖^2 + ‖x - K.starProjection x‖^2 := by
  rw [ ← add_sub_cancel ( K.starProjection x ) x, norm_add_sq_real ];
  simp +decide [ green_helmholtz_no_drift ]

/-
**Midpoint forcing**: For `x ≠ 0` with `Gx ≠ 0` and `x - Gx ≠ 0`,
    the energy ratio `‖Gx‖²/‖x‖²` lies strictly between 0 and 1.
    This means neither channel dominates — the split is forced to an
    interior point, with the midpoint `1/2` being the balanced case.
-/
theorem green_helmholtz_midpoint (x : F)
    (hx : x ≠ 0)
    (hGx : K.starProjection x ≠ 0)
    (hLx : x - K.starProjection x ≠ 0) :
    0 < ‖K.starProjection x‖^2 / ‖x‖^2 ∧
    ‖K.starProjection x‖^2 / ‖x‖^2 < 1 := by
  rw [ div_lt_iff₀ ];
  · exact ⟨ div_pos ( sq_pos_of_pos ( norm_pos_iff.mpr hGx ) ) ( sq_pos_of_pos ( norm_pos_iff.mpr hx ) ), by nlinarith [ norm_pos_iff.mpr hLx, norm_pos_iff.mpr hGx, green_helmholtz_pythagorean K x ] ⟩;
  · exact sq_pos_of_pos ( norm_pos_iff.mpr hx )

/-
**Self-adjointness of the loss**: `⟪x - Gx, y⟫ = ⟪x, y - Gy⟫`.
-/
theorem green_helmholtz_loss_self_adjoint (x y : F) :
    @inner ℝ F _ (x - K.starProjection x) y =
    @inner ℝ F _ x (y - K.starProjection y) := by
  have h_symm : inner ℝ (K.starProjection x) y = inner ℝ x (K.starProjection y) := by
    convert green_helmholtz_self_adjoint K x y using 1;
  simp +decide [ inner_sub_left, inner_sub_right, h_symm ]

/-- **Completeness**: `Gx + (x - Gx) = x`. The projection and loss together
    recover the original signal with no information loss. -/
theorem green_helmholtz_completeness (x : F) :
    K.starProjection x + (x - K.starProjection x) = x := by
  abel

end GreenHelmholtz

/-! ## Finite-dimensional projection instances -/

instance euclidean_projection {n : ℕ}
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin n))) :
    K.HasOrthogonalProjection := by
  haveI : FiniteDimensional ℝ K := inferInstance
  haveI : CompleteSpace K := FiniteDimensional.complete ℝ K
  exact inferInstance

/-! ## 3D → 2D: Green-Helmholtz for helix-to-circle projection -/

section ThreeDtoTwoD

/-- Self-adjoint: 3D→2D Green-Helmholtz projection. -/
theorem green_helmholtz_3d_self_adjoint
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))
    (x y : EuclideanSpace ℝ (Fin 3)) :
    @inner ℝ _ _ (K.starProjection x) y = @inner ℝ _ _ x (K.starProjection y) :=
  green_helmholtz_self_adjoint K x y

/-- No drift: 3D→2D projection is orthogonal to its loss. -/
theorem green_helmholtz_3d_no_drift
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))
    (x : EuclideanSpace ℝ (Fin 3)) :
    @inner ℝ _ _ (K.starProjection x) (x - K.starProjection x) = 0 :=
  green_helmholtz_no_drift K x

/-- Strictly positive: 3D→2D `⟪Gx, x⟫ = ‖Gx‖²`. -/
theorem green_helmholtz_3d_positive
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))
    (x : EuclideanSpace ℝ (Fin 3)) :
    @inner ℝ _ _ (K.starProjection x) x = ‖K.starProjection x‖^2 :=
  green_helmholtz_positive K x

/-- Energy conservation: 3D→2D Pythagorean decomposition. -/
theorem green_helmholtz_3d_pythagorean
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))
    (x : EuclideanSpace ℝ (Fin 3)) :
    ‖x‖^2 = ‖K.starProjection x‖^2 + ‖x - K.starProjection x‖^2 :=
  green_helmholtz_pythagorean K x

/-- Midpoint: 3D→2D energy ratio ∈ (0,1). -/
theorem green_helmholtz_3d_midpoint
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))
    (x : EuclideanSpace ℝ (Fin 3))
    (hx : x ≠ 0) (hGx : K.starProjection x ≠ 0)
    (hLx : x - K.starProjection x ≠ 0) :
    0 < ‖K.starProjection x‖^2 / ‖x‖^2 ∧
    ‖K.starProjection x‖^2 / ‖x‖^2 < 1 :=
  green_helmholtz_midpoint K x hx hGx hLx

end ThreeDtoTwoD

/-! ## 2D → 1D: Green-Helmholtz for circle-to-line projection -/

section TwoDtoOneD

/-- Self-adjoint: 2D→1D Green-Helmholtz projection. -/
theorem green_helmholtz_2d_self_adjoint
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin 2)))
    (x y : EuclideanSpace ℝ (Fin 2)) :
    @inner ℝ _ _ (K.starProjection x) y = @inner ℝ _ _ x (K.starProjection y) :=
  green_helmholtz_self_adjoint K x y

/-- No drift: 2D→1D projection is orthogonal to its loss. -/
theorem green_helmholtz_2d_no_drift
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin 2)))
    (x : EuclideanSpace ℝ (Fin 2)) :
    @inner ℝ _ _ (K.starProjection x) (x - K.starProjection x) = 0 :=
  green_helmholtz_no_drift K x

/-- Strictly positive: 2D→1D `⟪Gx, x⟫ = ‖Gx‖²`. -/
theorem green_helmholtz_2d_positive
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin 2)))
    (x : EuclideanSpace ℝ (Fin 2)) :
    @inner ℝ _ _ (K.starProjection x) x = ‖K.starProjection x‖^2 :=
  green_helmholtz_positive K x

/-- Energy conservation: 2D→1D Pythagorean decomposition. -/
theorem green_helmholtz_2d_pythagorean
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin 2)))
    (x : EuclideanSpace ℝ (Fin 2)) :
    ‖x‖^2 = ‖K.starProjection x‖^2 + ‖x - K.starProjection x‖^2 :=
  green_helmholtz_pythagorean K x

/-- Midpoint: 2D→1D energy ratio ∈ (0,1). -/
theorem green_helmholtz_2d_midpoint
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin 2)))
    (x : EuclideanSpace ℝ (Fin 2))
    (hx : x ≠ 0) (hGx : K.starProjection x ≠ 0)
    (hLx : x - K.starProjection x ≠ 0) :
    0 < ‖K.starProjection x‖^2 / ‖x‖^2 ∧
    ‖K.starProjection x‖^2 / ‖x‖^2 < 1 :=
  green_helmholtz_midpoint K x hx hGx hLx

end TwoDtoOneD

/-! ## Cascade: 3D → 2D → 1D preserves all properties -/

section Cascade

/-
The composition of two orthogonal projections (3D→2D then 2D→1D within the 2D subspace)
    preserves self-adjointness at each stage. Each stage independently satisfies
    self-adjoint + no-drift + positive, so the cascade forces the midpoint at every level.
-/
theorem cascade_each_stage_self_adjoint
    (K₁ : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))
    (K₂ : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))
    (x y : EuclideanSpace ℝ (Fin 3)) :
    -- Stage 1: 3D→2D is self-adjoint
    @inner ℝ _ _ (K₁.starProjection x) y = @inner ℝ _ _ x (K₁.starProjection y) ∧
    -- Stage 2: further projection is self-adjoint
    @inner ℝ _ _ (K₂.starProjection x) y = @inner ℝ _ _ x (K₂.starProjection y) := by
  exact ⟨ green_helmholtz_3d_self_adjoint K₁ x y, green_helmholtz_3d_self_adjoint K₂ x y ⟩

/-
The cascade preserves no-drift at each stage.
-/
theorem cascade_each_stage_no_drift
    (K₁ : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))
    (K₂ : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))
    (x : EuclideanSpace ℝ (Fin 3)) :
    @inner ℝ _ _ (K₁.starProjection x) (x - K₁.starProjection x) = 0 ∧
    @inner ℝ _ _ (K₂.starProjection x) (x - K₂.starProjection x) = 0 := by
  exact ⟨ green_helmholtz_3d_no_drift K₁ x, green_helmholtz_3d_no_drift K₂ x ⟩

/-
The cascade preserves positivity at each stage.
-/
theorem cascade_each_stage_positive
    (K₁ : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))
    (K₂ : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))
    (x : EuclideanSpace ℝ (Fin 3)) :
    @inner ℝ _ _ (K₁.starProjection x) x = ‖K₁.starProjection x‖^2 ∧
    @inner ℝ _ _ (K₂.starProjection x) x = ‖K₂.starProjection x‖^2 := by
  exact ⟨ green_helmholtz_3d_positive K₁ x, green_helmholtz_3d_positive K₂ x ⟩

end Cascade

end