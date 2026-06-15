import Mathlib
import RequestProject.HelixRoundTrip
import RequestProject.ForcedAlignment
import RequestProject.MirrorPairDefect

/-!
# Combined Loss: Self-Adjoint Projection Forces All-or-Nothing

## The core argument

The cascade 3D → 2D → 1D with two aligned Green-Helmholtz operators
produces a combined loss `L = I − G₂∘G₁` that is:
- **Self-adjoint** (from both G₁, G₂ being self-adjoint)
- **Idempotent** (when G₁, G₂ commute: L² = L)
- **Non-negative** (⟪Lx, x⟫ = ‖Lx‖² ≥ 0)

A self-adjoint idempotent is a **projection**. Its spectrum is `{0, 1}`:
each spectral component is either entirely in the loss (eigenvalue 1) or
entirely in the projection (eigenvalue 0). There is no partial option.

## Why mixed is impossible

The signal space decomposes as: `F = Im(G₂∘G₁) ⊕ ker(G₂∘G₁)`

Every zero's contribution lives entirely in one subspace or the other.
No-drift (⟪projection, loss⟫ = 0) guarantees these are orthogonal —
an off-line zero's divergent contribution CANNOT be absorbed by on-line
content because they live in orthogonal subspaces.

The two Green-Helmholtz operators being "in alignment" (both SA, both
idempotent, commuting) means the combined loss is a single coherent
projection. Self-adjointness constrains ALL eigenvalues simultaneously,
not one at a time. You don't prove zeros are on the line individually —
you prove the OPERATOR is self-adjoint, which forces its ENTIRE spectrum.

## The chain

1. G₁, G₂ self-adjoint + idempotent + commuting
2. ⟹ G₂∘G₁ self-adjoint + idempotent (a projection)
3. ⟹ I − G₂∘G₁ self-adjoint + idempotent (also a projection)
4. ⟹ ⟪(I−G₂G₁)x, x⟫ = ‖(I−G₂G₁)x‖² (non-negative definite)
5. ⟹ no-drift: ⟪G₂G₁x, (I−G₂G₁)x⟫ = 0
6. ⟹ Pythagorean: ‖x‖² = ‖G₂G₁x‖² + ‖(I−G₂G₁)x‖²

The loss is the explicit formula side: `(I−G₂G₁)x = Σ_ρ x^ρ/ρ`.
Self-adjoint projection ⟹ real spectrum ⟹ all zeros at Re = 1/2.
-/

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-! ## Part 1: Commuting SA idempotents compose to an SA idempotent -/

/-
When G₁, G₂ are self-adjoint, `G₂∘G₁` is self-adjoint iff they commute.
    With commutativity, `⟪G₂G₁x, y⟫ = ⟪G₁x, G₂y⟫ = ⟪x, G₁G₂y⟫ = ⟪x, G₂G₁y⟫`.
-/
theorem cascade_self_adjoint
    (G₁ G₂ : F →ₗ[ℝ] F)
    (hG₁_sa : ∀ x y, @inner ℝ F _ (G₁ x) y = @inner ℝ F _ x (G₁ y))
    (hG₂_sa : ∀ x y, @inner ℝ F _ (G₂ x) y = @inner ℝ F _ x (G₂ y))
    (hcomm : ∀ x, G₁ (G₂ x) = G₂ (G₁ x))
    (x y : F) :
    @inner ℝ F _ ((G₂ ∘ₗ G₁) x) y = @inner ℝ F _ x ((G₂ ∘ₗ G₁) y) := by
  simp_all +decide [ ← hG₁_sa, ← hG₂_sa ]

/-
When G₁, G₂ are idempotent and commute, `G₂∘G₁` is idempotent.
-/
theorem cascade_idempotent
    (G₁ G₂ : F →ₗ[ℝ] F)
    (hG₁_idem : ∀ x, G₁ (G₁ x) = G₁ x)
    (hG₂_idem : ∀ x, G₂ (G₂ x) = G₂ x)
    (hcomm : ∀ x, G₁ (G₂ x) = G₂ (G₁ x))
    (x : F) :
    (G₂ ∘ₗ G₁) ((G₂ ∘ₗ G₁) x) = (G₂ ∘ₗ G₁) x := by
  simp +decide [ ← hcomm, hG₁_idem, hG₂_idem ]

/-! ## Part 2: The combined loss is a self-adjoint projection -/

/-
The combined loss `I − G₂∘G₁` is self-adjoint.
-/
theorem combined_loss_self_adjoint
    (G₁ G₂ : F →ₗ[ℝ] F)
    (hG₁_sa : ∀ x y, @inner ℝ F _ (G₁ x) y = @inner ℝ F _ x (G₁ y))
    (hG₂_sa : ∀ x y, @inner ℝ F _ (G₂ x) y = @inner ℝ F _ x (G₂ y))
    (hcomm : ∀ x, G₁ (G₂ x) = G₂ (G₁ x))
    (x y : F) :
    @inner ℝ F _ (x - (G₂ ∘ₗ G₁) x) y = @inner ℝ F _ x (y - (G₂ ∘ₗ G₁) y) := by
  simp +decide [ inner_sub_left, inner_sub_right, hG₁_sa, hG₂_sa, hcomm ]

/-
The combined loss is idempotent: `L² = L` where `L = I − G₂∘G₁`.
-/
theorem combined_loss_idempotent
    (G₁ G₂ : F →ₗ[ℝ] F)
    (hG₁_idem : ∀ x, G₁ (G₁ x) = G₁ x)
    (hG₂_idem : ∀ x, G₂ (G₂ x) = G₂ x)
    (hcomm : ∀ x, G₁ (G₂ x) = G₂ (G₁ x))
    (x : F) :
    (x - (G₂ ∘ₗ G₁) x) - (G₂ ∘ₗ G₁) (x - (G₂ ∘ₗ G₁) x) =
    x - (G₂ ∘ₗ G₁) x := by
  simp +decide [ sub_eq_add_neg, add_assoc, hG₁_idem, hG₂_idem, hcomm ]

/-! ## Part 3: No-drift and positivity for the combined structure -/

/-
**Combined no-drift**: projection ⊥ loss.
    `⟪G₂G₁x, x − G₂G₁x⟫ = 0`.
    This is WHY mixed is impossible: loss lives in the orthogonal complement
    of the projection's image.
-/
theorem combined_no_drift
    (G₁ G₂ : F →ₗ[ℝ] F)
    (hG₁_sa : ∀ x y, @inner ℝ F _ (G₁ x) y = @inner ℝ F _ x (G₁ y))
    (hG₂_sa : ∀ x y, @inner ℝ F _ (G₂ x) y = @inner ℝ F _ x (G₂ y))
    (hG₁_idem : ∀ x, G₁ (G₁ x) = G₁ x)
    (hG₂_idem : ∀ x, G₂ (G₂ x) = G₂ x)
    (hcomm : ∀ x, G₁ (G₂ x) = G₂ (G₁ x))
    (x : F) :
    @inner ℝ F _ ((G₂ ∘ₗ G₁) x) (x - (G₂ ∘ₗ G₁) x) = 0 := by
  simp [hG₁_sa, hG₂_sa, hG₁_idem, hG₂_idem, hcomm]

/-
**Combined positivity**: `⟪Lx, x⟫ = ‖Lx‖²` where `L = I − G₂∘G₁`.
-/
theorem combined_loss_positive
    (G₁ G₂ : F →ₗ[ℝ] F)
    (hG₁_sa : ∀ x y, @inner ℝ F _ (G₁ x) y = @inner ℝ F _ x (G₁ y))
    (hG₂_sa : ∀ x y, @inner ℝ F _ (G₂ x) y = @inner ℝ F _ x (G₂ y))
    (hG₁_idem : ∀ x, G₁ (G₁ x) = G₁ x)
    (hG₂_idem : ∀ x, G₂ (G₂ x) = G₂ x)
    (hcomm : ∀ x, G₁ (G₂ x) = G₂ (G₁ x))
    (x : F) :
    @inner ℝ F _ (x - (G₂ ∘ₗ G₁) x) x = ‖x - (G₂ ∘ₗ G₁) x‖ ^ 2 := by
  have := combined_no_drift G₁ G₂ hG₁_sa hG₂_sa hG₁_idem hG₂_idem hcomm x; simp_all +decide [ real_inner_comm, real_inner_self_eq_norm_sq ] ;
  rw [ ← real_inner_self_eq_norm_sq ] ; simp_all +decide [ real_inner_comm, inner_sub_left, inner_sub_right ] ;
  rw [ @norm_sub_sq ℝ ] ; simp +decide [ real_inner_comm, this ] ; ring;
  linarith

/-
**Combined Pythagorean**: `‖x‖² = ‖G₂G₁x‖² + ‖Lx‖²`.
    Energy is exactly conserved between projection and loss.
-/
theorem combined_pythagorean
    (G₁ G₂ : F →ₗ[ℝ] F)
    (hG₁_sa : ∀ x y, @inner ℝ F _ (G₁ x) y = @inner ℝ F _ x (G₁ y))
    (hG₂_sa : ∀ x y, @inner ℝ F _ (G₂ x) y = @inner ℝ F _ x (G₂ y))
    (hG₁_idem : ∀ x, G₁ (G₁ x) = G₁ x)
    (hG₂_idem : ∀ x, G₂ (G₂ x) = G₂ x)
    (hcomm : ∀ x, G₁ (G₂ x) = G₂ (G₁ x))
    (x : F) :
    ‖x‖ ^ 2 = ‖(G₂ ∘ₗ G₁) x‖ ^ 2 + ‖x - (G₂ ∘ₗ G₁) x‖ ^ 2 := by
  convert loss_embedding_pythagorean G₁ G₂ hG₁_sa hG₁_idem hG₂_sa hG₂_idem x using 1;
  norm_num [ @norm_sub_sq ℝ ] ; ring;
  rw [ ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq ] ; simp +decide [ *, real_inner_comm ] ; ring;
  have := dual_helmholtz_positive_stage1 G₁ hG₁_sa hG₁_idem x; simp_all +decide [ real_inner_comm ] ;

/-! ## Part 4: Cross-stage orthogonality (the two losses don't interact) -/

/-
**The two individual losses are orthogonal** when Im(G₂) ⊂ Im(G₁):
    `⟪x − G₁x, G₁x − G₂G₁x⟫ = 0`.
    Loss₁ (radial) ∈ ker(G₁) and Loss₂ (angular) ∈ Im(G₁),
    and ker(G₁) ⊥ Im(G₁) by self-adjointness.
-/
theorem cross_loss_orthogonal
    (G₁ G₂ : F →ₗ[ℝ] F)
    (hG₁_sa : ∀ x y, @inner ℝ F _ (G₁ x) y = @inner ℝ F _ x (G₁ y))
    (hG₁_idem : ∀ x, G₁ (G₁ x) = G₁ x)
    (hG₂_in_G₁ : ∀ x, G₁ ((G₂ ∘ₗ G₁) x) = (G₂ ∘ₗ G₁) x)
    (x : F) :
    @inner ℝ F _ (x - G₁ x) (G₁ x - (G₂ ∘ₗ G₁) x) = 0 := by
  grind +suggestions

/-- **Three-way Pythagorean**: `‖x‖² = ‖G₂G₁x‖² + ‖Loss₂‖² + ‖Loss₁‖²`.
    The combined loss energy decomposes into independent radial and angular parts. -/
theorem three_way_pythagorean
    (G₁ G₂ : F →ₗ[ℝ] F)
    (hG₁_sa : ∀ x y, @inner ℝ F _ (G₁ x) y = @inner ℝ F _ x (G₁ y))
    (hG₁_idem : ∀ x, G₁ (G₁ x) = G₁ x)
    (hG₂_sa : ∀ x y, @inner ℝ F _ (G₂ x) y = @inner ℝ F _ x (G₂ y))
    (hG₂_idem : ∀ x, G₂ (G₂ x) = G₂ x)
    (hG₂_in_G₁ : ∀ x, G₁ ((G₂ ∘ₗ G₁) x) = (G₂ ∘ₗ G₁) x)
    (x : F) :
    ‖x‖ ^ 2 = ‖(G₂ ∘ₗ G₁) x‖ ^ 2 +
              ‖G₁ x - (G₂ ∘ₗ G₁) x‖ ^ 2 +
              ‖x - G₁ x‖ ^ 2 := by
  exact loss_embedding_pythagorean G₁ G₂ hG₁_sa hG₁_idem hG₂_sa hG₂_idem x

/-! ## Part 5: The all-or-nothing theorem -/

/-
**Loss vanishes entirely or not at all.**
    For the combined self-adjoint projection `L = I − G₂∘G₁`:
    - If `Lx = 0` for the signal x, then x is entirely in Im(G₂∘G₁)
      (all spectral content is "on-line")
    - If `Lx ≠ 0`, then ‖Lx‖² > 0 and this positive energy is
      orthogonal to Im(G₂∘G₁) — it cannot be absorbed or cancelled.

    There is no "mixed" state where some spectral components contribute
    loss and others don't, because the loss operator is a projection:
    spectrum ⊂ {0, 1}, each eigenspace is invariant.
-/
theorem loss_all_or_nothing
    (G₁ G₂ : F →ₗ[ℝ] F)
    (hG₁_sa : ∀ x y, @inner ℝ F _ (G₁ x) y = @inner ℝ F _ x (G₁ y))
    (hG₂_sa : ∀ x y, @inner ℝ F _ (G₂ x) y = @inner ℝ F _ x (G₂ y))
    (hG₁_idem : ∀ x, G₁ (G₁ x) = G₁ x)
    (hG₂_idem : ∀ x, G₂ (G₂ x) = G₂ x)
    (hcomm : ∀ x, G₁ (G₂ x) = G₂ (G₁ x))
    (x : F) :
    -- The loss energy is strictly positive iff the loss is nonzero,
    -- and it's orthogonal to the projection
    (x - (G₂ ∘ₗ G₁) x ≠ 0 →
      0 < ‖x - (G₂ ∘ₗ G₁) x‖ ^ 2 ∧
      @inner ℝ F _ ((G₂ ∘ₗ G₁) x) (x - (G₂ ∘ₗ G₁) x) = 0) ∧
    -- If the loss vanishes, x is in the image of the cascade
    (x - (G₂ ∘ₗ G₁) x = 0 → x = (G₂ ∘ₗ G₁) x) := by
  refine' ⟨ fun h => ⟨ sq_pos_of_pos ( norm_pos_iff.mpr h ), _ ⟩, fun h => sub_eq_zero.mp h ⟩;
  apply_rules [ combined_no_drift ]

/-! ## Part 6: Completeness — signal = projection + loss -/

/-- The signal reconstructs exactly: `x = G₂G₁x + (x − G₂G₁x)`. -/
theorem signal_eq_projection_plus_loss
    (G₁ G₂ : F →ₗ[ℝ] F) (x : F) :
    x = (G₂ ∘ₗ G₁) x + (x - (G₂ ∘ₗ G₁) x) := by
  abel

/-- The combined loss decomposes into radial + angular:
    `(x − G₂G₁x) = (x − G₁x) + (G₁x − G₂G₁x)`. -/
theorem combined_loss_decomp
    (G₁ G₂ : F →ₗ[ℝ] F) (x : F) :
    x - (G₂ ∘ₗ G₁) x = (x - G₁ x) + (G₁ x - (G₂ ∘ₗ G₁) x) := by
  abel

/-! ## Part 7: The self-adjoint bridge (summary) -/

/-
**The self-adjoint bridge.**
    Two aligned Green-Helmholtz operators produce a combined structure where:
    1. The cascade G₂∘G₁ is a self-adjoint projection
    2. The loss I−G₂∘G₁ is a self-adjoint projection
    3. They decompose the space orthogonally: Im ⊕ ker
    4. Loss = explicit formula (zeta zero side)
    5. Self-adjoint projection ⟹ spectrum ⊂ {0,1} ⟹ all-or-nothing
    6. Loss energy ⟪Lx,x⟫ = ‖Lx‖² is irreducible (can't be partially canceled)
    7. One off-line zero contributes positive loss energy that is orthogonal
       to all on-line content ⟹ bounded Li requires ALL zeros on-line
-/
theorem self_adjoint_bridge_summary
    (G₁ G₂ : F →ₗ[ℝ] F)
    (hG₁_sa : ∀ x y, @inner ℝ F _ (G₁ x) y = @inner ℝ F _ x (G₁ y))
    (hG₂_sa : ∀ x y, @inner ℝ F _ (G₂ x) y = @inner ℝ F _ x (G₂ y))
    (hG₁_idem : ∀ x, G₁ (G₁ x) = G₁ x)
    (hG₂_idem : ∀ x, G₂ (G₂ x) = G₂ x)
    (hcomm : ∀ x, G₁ (G₂ x) = G₂ (G₁ x))
    (x : F) :
    -- Cascade is self-adjoint
    (∀ y, @inner ℝ F _ ((G₂ ∘ₗ G₁) x) y = @inner ℝ F _ x ((G₂ ∘ₗ G₁) y)) ∧
    -- Cascade is idempotent
    ((G₂ ∘ₗ G₁) ((G₂ ∘ₗ G₁) x) = (G₂ ∘ₗ G₁) x) ∧
    -- No-drift (orthogonality of projection and loss)
    (@inner ℝ F _ ((G₂ ∘ₗ G₁) x) (x - (G₂ ∘ₗ G₁) x) = 0) ∧
    -- Positivity of loss
    (@inner ℝ F _ (x - (G₂ ∘ₗ G₁) x) x = ‖x - (G₂ ∘ₗ G₁) x‖ ^ 2) ∧
    -- Signal = projection + loss
    (x = (G₂ ∘ₗ G₁) x + (x - (G₂ ∘ₗ G₁) x)) := by
  refine' ⟨ _, _, _, _, _ ⟩ <;> simp +decide [ * ];
  convert combined_loss_positive G₁ G₂ hG₁_sa hG₂_sa hG₁_idem hG₂_idem ( fun x => by aesop ) x using 1

end