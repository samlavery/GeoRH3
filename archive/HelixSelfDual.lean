import Mathlib

/-!
# Self-Duality of Helix Operations

We prove that the operations from the mod-6 prime helix decomposition are
**self-dual** (self-adjoint) when the base operator G is self-adjoint on an
inner product space.

## Setup

Given a self-adjoint operator `G` on an inner product space (i.e., `⟪Gx, y⟫ = ⟪x, Gy⟫`),
the helix decomposition uses:
- **G²** (the iterated operator): `x ↦ G(G(x))`
- **Loss**: `x ↦ x - G²(x)`
- **Principal channel**: `(r₁, r₅) ↦ r₁ + r₅`
- **Sign channel**: `(r₁, r₅) ↦ r₁ - r₅`

## Results

1. `G_sq_self_adjoint`: G² is self-adjoint if G is.
2. `loss_self_adjoint`: The loss `x - G²(x)` is self-adjoint if G is.
3. `principal_inner_symm` / `sign_inner_symm`: The channels preserve conjugate symmetry.
4. `cross_channel_duality`: The principal/sign decomposition respects the inner product.
5. Real-case specializations with idempotent projections.

These show the helix operations are self-dual in the sense of inner product spaces.
-/

noncomputable section

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-! ## Self-adjointness of iterated operators -/

section SelfAdjointOperators

/-
If G is self-adjoint (⟪Gx, y⟫ = ⟪x, Gy⟫), then G² = G ∘ G is self-adjoint.
-/
theorem G_sq_self_adjoint (G : E →ₗ[𝕜] E)
    (hG : ∀ x y : E, @inner 𝕜 E _ (G x) y = @inner 𝕜 E _ x (G y))
    (x y : E) :
    @inner 𝕜 E _ ((G ∘ₗ G) x) y = @inner 𝕜 E _ x ((G ∘ₗ G) y) := by
  simp +decide only [LinearMap.comp_apply, hG]

/-
The loss operator L(x) = x - G²(x) is self-adjoint when G is self-adjoint.
-/
theorem loss_self_adjoint (G : E →ₗ[𝕜] E)
    (hG : ∀ x y : E, @inner 𝕜 E _ (G x) y = @inner 𝕜 E _ x (G y))
    (x y : E) :
    @inner 𝕜 E _ (x - (G ∘ₗ G) x) y = @inner 𝕜 E _ x (y - (G ∘ₗ G) y) := by
  simp +decide [ inner_sub_left, inner_sub_right, hG ]

/-
The RHS operator R(x) = G²(x) is self-adjoint when G is self-adjoint.
    (Restated from G_sq_self_adjoint for clarity.)
-/
theorem rhs_self_adjoint (G : E →ₗ[𝕜] E)
    (hG : ∀ x y : E, @inner 𝕜 E _ (G x) y = @inner 𝕜 E _ x (G y))
    (x y : E) :
    @inner 𝕜 E _ ((G ∘ₗ G) x) y = @inner 𝕜 E _ x ((G ∘ₗ G) y) := by
  convert G_sq_self_adjoint G hG x y using 1

end SelfAdjointOperators

/-! ## Self-duality of channel operations -/

section ChannelSelfDual

/-
The inner product of principal channels is conjugate-symmetric:
    ⟪r₁ + r₅, s₁ + s₅⟫ = conj ⟪s₁ + s₅, r₁ + r₅⟫.
-/
theorem principal_inner_symm (r₁ r₅ s₁ s₅ : E) :
    @inner 𝕜 E _ (r₁ + r₅) (s₁ + s₅) =
    starRingEnd 𝕜 (@inner 𝕜 E _ (s₁ + s₅) (r₁ + r₅)) := by
  rw [ inner_conj_symm ]

/-
The inner product of sign channels is conjugate-symmetric:
    ⟪r₁ - r₅, s₁ - s₅⟫ = conj ⟪s₁ - s₅, r₁ - r₅⟫.
-/
theorem sign_inner_symm (r₁ r₅ s₁ s₅ : E) :
    @inner 𝕜 E _ (r₁ - r₅) (s₁ - s₅) =
    starRingEnd 𝕜 (@inner 𝕜 E _ (s₁ - s₅) (r₁ - r₅)) := by
  rw [ ← inner_conj_symm ]

/-
Cross-channel inner product decomposes as differences of norms:
    ⟪r₁ + r₅, r₁ - r₅⟫ = ‖r₁‖² - ‖r₅‖² (in the real case).
    In general: ⟪r₁ + r₅, r₁ - r₅⟫ = ⟪r₁, r₁⟫ - ⟪r₅, r₅⟫ + (⟪r₅, r₁⟫ - ⟪r₁, r₅⟫).
-/
theorem cross_channel_duality (r₁ r₅ : E) :
    @inner 𝕜 E _ (r₁ + r₅) (r₁ - r₅) =
    @inner 𝕜 E _ r₁ r₁ - @inner 𝕜 E _ r₅ r₅ +
    (@inner 𝕜 E _ r₅ r₁ - @inner 𝕜 E _ r₁ r₅) := by
  simp +decide [ inner_add_left, inner_sub_left, inner_add_right, inner_sub_right ] ; ring

end ChannelSelfDual

/-! ## Self-duality in the real case -/

section RealCase

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-
In the real case, G² is self-adjoint: ⟪G²x, y⟫ = ⟪x, G²y⟫.
-/
theorem G_sq_self_adjoint_real (G : F →ₗ[ℝ] F)
    (hG : ∀ x y : F, @inner ℝ F _ (G x) y = @inner ℝ F _ x (G y))
    (x y : F) :
    @inner ℝ F _ ((G ∘ₗ G) x) y = @inner ℝ F _ x ((G ∘ₗ G) y) := by
  convert hG _ _ using 1 ; simp +decide [ hG ]

/-
The real loss operator is self-adjoint:
    ⟪x - G²x, y⟫ = ⟪x, y - G²y⟫.
-/
theorem loss_self_adjoint_real (G : F →ₗ[ℝ] F)
    (hG : ∀ x y : F, @inner ℝ F _ (G x) y = @inner ℝ F _ x (G y))
    (x y : F) :
    @inner ℝ F _ (x - (G ∘ₗ G) x) y = @inner ℝ F _ x (y - (G ∘ₗ G) y) := by
  simp +decide [ inner_sub_left, inner_sub_right, hG ]

/-
Cross-channel duality simplifies in the real case:
    ⟪r₁ + r₅, r₁ - r₅⟫ = ‖r₁‖² - ‖r₅‖²
    (the antisymmetric part vanishes since ⟪r₅, r₁⟫ = ⟪r₁, r₅⟫).
-/
theorem cross_channel_real (r₁ r₅ : F) :
    @inner ℝ F _ (r₁ + r₅) (r₁ - r₅) =
    ‖r₁‖^2 - ‖r₅‖^2 := by
  simp +decide [ inner_add_left, inner_sub_right, real_inner_self_eq_norm_sq ];
  rw [ real_inner_comm ] ; ring

/-
When G is idempotent (G² = G, a projection) and self-adjoint,
    the loss operator L(x) = x - G(x) is also idempotent:
    L(L(x)) = L(x), meaning L is itself a projection.
-/
theorem loss_idempotent_of_projection (G : F →ₗ[ℝ] F)
    (hG_sa : ∀ x y : F, @inner ℝ F _ (G x) y = @inner ℝ F _ x (G y))
    (hG_idem : ∀ x : F, G (G x) = G x) (x : F) :
    (x - G x) - G (x - G x) = x - G x := by
  simp +decide [ sub_eq_add_neg, hG_idem ]

/-
Self-adjoint + idempotent implies orthogonality of projection and loss:
    ⟪G²x, x - G²x⟫ = 0.
-/
theorem rhs_orthogonal_loss (G : F →ₗ[ℝ] F)
    (hG_sa : ∀ x y : F, @inner ℝ F _ (G x) y = @inner ℝ F _ x (G y))
    (hG_idem : ∀ x : F, G (G x) = G x) (x : F) :
    @inner ℝ F _ (G (G x)) (x - G (G x)) = 0 := by
  have h₁ := hG_sa x ( G x ) ; have h₂ := hG_sa ( G x ) ( G x ) ; aesop;

end RealCase

end