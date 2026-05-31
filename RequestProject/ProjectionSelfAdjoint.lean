import Mathlib

/-!
# Self-Adjointness of Projections with Tracked Loss

We prove that orthogonal projections (and their associated "projection losses")
are self-adjoint operators with respect to the inner product. This is formalized
both abstractly for any inner product space and concretely for:

- **3D → 2D**: Projection from `EuclideanSpace ℝ (Fin 3)` to a 2D subspace.
- **2D → 1D**: Projection from `EuclideanSpace ℝ (Fin 2)` to a 1D subspace.

## Key Results

Given a closed subspace `K` with orthogonal projection `P : E → K`, define:
- **Projection**: `P(x) = K.starProjection x` (the component in K)
- **Projection loss**: `x - P(x)` (the component orthogonal to K)

We prove:
1. `projection_self_adjoint`: `⟪P x, y⟫ = ⟪x, P y⟫`
2. `projection_loss_self_adjoint`: `⟪x - P x, y⟫ = ⟪x, y - P y⟫`
3. `projection_loss_self_adjoint'`: `⟪x - P x, y - P y⟫` is symmetric
4. Concrete instantiations for 3D→2D and 2D→1D.

These results answer affirmatively: yes, projection can be proven self-adjoint
when the projection loss is tracked, because both the projection and the loss
are orthogonal projections (onto complementary subspaces) and hence self-adjoint.
-/

noncomputable section

open Submodule

/-! ## Abstract self-adjointness in any inner product space -/

section Abstract

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]

/-- The orthogonal projection is self-adjoint: ⟪P x, y⟫ = ⟪x, P y⟫. -/
theorem projection_self_adjoint (x y : E) :
    @inner 𝕜 E _ (K.starProjection x) y = @inner 𝕜 E _ x (K.starProjection y) :=
  Submodule.inner_starProjection_left_eq_right K x y

/-- The projection loss (x - Px) is self-adjoint: ⟪x - Px, y⟫ = ⟪x, y - Py⟫. -/
theorem projection_loss_self_adjoint (x y : E) :
    @inner 𝕜 E _ (x - K.starProjection x) y =
    @inner 𝕜 E _ x (y - K.starProjection y) := by
  simp [inner_sub_left, inner_sub_right, projection_self_adjoint K x y]

/-- The projection loss is symmetric in both arguments:
    ⟪x - Px, y - Py⟫ = ⟪y - Py, x - Px⟫. This is the inner product symmetry
    restricted to the orthogonal complement. -/
theorem projection_loss_symmetric (x y : E) :
    @inner 𝕜 E _ (x - K.starProjection x) (y - K.starProjection y) =
    starRingEnd 𝕜 (@inner 𝕜 E _ (y - K.starProjection y) (x - K.starProjection x)) := by
  exact (inner_conj_symm _ _).symm

/-- Completeness: the projection and loss together recover the original signal.
    This is the master identity x = Px + (x - Px) in the inner product setting. -/
theorem projection_plus_loss (x : E) :
    K.starProjection x + (x - K.starProjection x) = x := by
  abel

/-
The Pythagorean theorem: ‖x‖² = ‖Px‖² + ‖x - Px‖² because Px ⊥ (x - Px).
-/
theorem projection_pythagorean (x : E) :
    ‖x‖^2 = ‖K.starProjection x‖^2 + ‖x - K.starProjection x‖^2 := by
  grind +suggestions

/-
The loss is orthogonal to the projection: ⟪Px, x - Px⟫ = 0.
-/
theorem projection_orthogonal_to_loss (x : E) :
    @inner 𝕜 E _ (K.starProjection x) (x - K.starProjection x) = 0 := by
  rw [ inner_eq_zero_symm, K.starProjection_inner_eq_zero ];
  exact Submodule.coe_mem _

end Abstract

/-! ## Finite-dimensional instances -/

/-- In finite-dimensional spaces (like EuclideanSpace), every subspace
    has an orthogonal projection. -/
instance euclidean_has_orthogonal_projection {n : ℕ}
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin n))) :
    K.HasOrthogonalProjection := by
  haveI : FiniteDimensional ℝ K := inferInstance
  haveI : CompleteSpace K := FiniteDimensional.complete ℝ K
  exact inferInstance

/-! ## 3D → 2D projection -/

section Projection3Dto2D

/-- Any subspace of ℝ³ admits a self-adjoint orthogonal projection. -/
theorem projection_3d_self_adjoint
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))
    (x y : EuclideanSpace ℝ (Fin 3)) :
    @inner ℝ _ _ (K.starProjection x) y = @inner ℝ _ _ x (K.starProjection y) :=
  projection_self_adjoint K x y

/-- The loss of projecting from 3D to a subspace is self-adjoint. -/
theorem projection_loss_3d_self_adjoint
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))
    (x y : EuclideanSpace ℝ (Fin 3)) :
    @inner ℝ _ _ (x - K.starProjection x) y =
    @inner ℝ _ _ x (y - K.starProjection y) :=
  projection_loss_self_adjoint K x y

/-- Completeness in 3D: projection + loss = original signal. -/
theorem projection_plus_loss_3d
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))
    (x : EuclideanSpace ℝ (Fin 3)) :
    K.starProjection x + (x - K.starProjection x) = x :=
  projection_plus_loss K x

end Projection3Dto2D

/-! ## 2D → 1D projection -/

section Projection2Dto1D

/-- Any subspace of ℝ² admits a self-adjoint orthogonal projection. -/
theorem projection_2d_self_adjoint
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin 2)))
    (x y : EuclideanSpace ℝ (Fin 2)) :
    @inner ℝ _ _ (K.starProjection x) y = @inner ℝ _ _ x (K.starProjection y) :=
  projection_self_adjoint K x y

/-- The loss of projecting from 2D to a subspace is self-adjoint. -/
theorem projection_loss_2d_self_adjoint
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin 2)))
    (x y : EuclideanSpace ℝ (Fin 2)) :
    @inner ℝ _ _ (x - K.starProjection x) y =
    @inner ℝ _ _ x (y - K.starProjection y) :=
  projection_loss_self_adjoint K x y

/-- Completeness in 2D: projection + loss = original signal. -/
theorem projection_plus_loss_2d
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin 2)))
    (x : EuclideanSpace ℝ (Fin 2)) :
    K.starProjection x + (x - K.starProjection x) = x :=
  projection_plus_loss K x

end Projection2Dto1D

end