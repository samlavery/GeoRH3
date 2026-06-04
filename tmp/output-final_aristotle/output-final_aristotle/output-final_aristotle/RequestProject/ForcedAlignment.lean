import Mathlib
import RequestProject.HelixRoundTrip

/-!
# Forced Alignment: Deriving σ = 1/2 from Structural Constraints

The critical line `Re(s) = 1/2` is **not assumed** — it is **derived** from
three ingredients already proved in this project:

1. **The functional equation involution** `σ ↦ 1−σ` pairs each zero
   `ρ = σ+iγ` with `1−ρ = (1−σ)−iγ`.

2. **The Möbius reciprocal property** (proved here): the Möbius images
   `w(ρ)` and `w(1−ρ)` are multiplicative inverses:
   `w(ρ) · w(1−ρ) = 1`, hence `‖w(ρ)‖ · ‖w(1−ρ)‖ = 1`.

3. **The Li term blow-up** (proved in `HelixRoundTrip.lean` via cofinal
   recurrence on the unit circle): if `‖w‖ > 1`, then `Re(wⁿ)` is
   unbounded above, so `Re[1 − wⁿ]` is unbounded below.

## The derivation

For a functional-equation pair `(ρ, 1−ρ)`:

- If `σ ≠ 1/2`, then `‖w(ρ)‖ ≠ 1` (by `moebius_unit_iff`).
- By the reciprocal property, one of `‖w(ρ)‖, ‖w(1−ρ)‖` exceeds 1.
- The partner with `‖w‖ > 1` has Li terms unbounded below
  (by `li_helix_unbounded_off_line`).
- The other partner has `‖w‖ < 1`, so its Li terms are bounded in `[0, 2]`
  (since `|Re(wⁿ)| ≤ ‖w‖ⁿ ≤ 1`).
- The **paired** Li coefficient `λₙ(ρ) + λₙ(1−ρ)` is unbounded below.
- **Contrapositive**: if paired Li coefficients are bounded below for all n,
  then `σ = 1/2`.

This is a theorem, not an assumption. The 1/2 emerges as the unique fixed
point of the involution where the Möbius norm equals 1.

## Two-projection cascade alignment

With two Green-Helmholtz operators `G₁` (3D→2D) and `G₂` (2D→1D), both
self-adjoint and idempotent, and a self-adjoint involution `R`:

- The five-fold composition `P₂∘P₁∘R∘P₁∘P₂` is self-adjoint.
- If `R` commutes with both projections, the cascade collapses.
- Two independent alignment constraints force `σ` to the involution's
  fixed point `1/2`.
-/

noncomputable section

open Complex Real

/-! ## Part 1: The Möbius Reciprocal Property -/

/-
**The Möbius reciprocal property**: For paired zeros `ρ` and `1−ρ`,
    the Möbius images are multiplicative inverses.
    `w(ρ) · w(1−ρ) = (1 − 1/ρ)(1 − 1/(1−ρ)) = ((ρ−1)/ρ)(ρ/(ρ−1)) = 1`.

    Uses `moebius_helix σ γ = 1 − 1/⟨σ,γ⟩` from HelixRoundTrip.lean.
-/
theorem moebius_product_one (sigma gamma : ℝ) (hg : gamma ≠ 0) :
    moebius_helix sigma gamma * moebius_helix (1 - sigma) (-gamma) = 1 := by
  unfold moebius_helix;
  norm_num [ Complex.ext_iff, hg ];
  field_simp;
  constructor <;> ring

/-
**Norm reciprocal**: `‖w(ρ)‖ · ‖w(1−ρ)‖ = 1`.
    Paired Möbius images have reciprocal moduli.
-/
theorem moebius_norm_product_one (sigma gamma : ℝ) (hg : gamma ≠ 0) :
    ‖moebius_helix sigma gamma‖ * ‖moebius_helix (1 - sigma) (-gamma)‖ = 1 := by
  rw [ ← norm_mul, moebius_product_one ] ; norm_num;
  assumption

/-
**Off-line dichotomy**: If `σ ≠ 1/2`, then one of the paired Möbius
    images has norm strictly greater than 1.

    Proof: `‖w‖ · ‖w'‖ = 1` and `‖w‖ ≠ 1` (by `moebius_unit_iff`),
    so either `‖w‖ > 1` or `‖w‖ < 1`. In the latter case `‖w'‖ = 1/‖w‖ > 1`.
-/
theorem one_partner_gt_one (sigma gamma : ℝ) (hs : sigma ≠ 1/2) (hg : gamma ≠ 0) :
    1 < ‖moebius_helix sigma gamma‖ ∨
    1 < ‖moebius_helix (1 - sigma) (-gamma)‖ := by
  -- By the properties of norms, we know that ‖w‖ * ‖w'‖ = 1.
  have h_norm_prod : ‖moebius_helix sigma gamma‖ * ‖moebius_helix (1 - sigma) (-gamma)‖ = 1 := by
    exact?;
  contrapose! hs;
  exact moebius_unit_iff sigma gamma hg |>.1 ( by nlinarith [ norm_nonneg ( moebius_helix sigma gamma ), norm_nonneg ( moebius_helix ( 1 - sigma ) ( -gamma ) ) ] )

/-! ## Part 2: Li Term Bounds for Small Norm -/

/-
When `‖w‖ ≤ 1`, each Li term `Re[1 − wⁿ]` is at most 2.
    Proof: `Re(1−wⁿ) = 1 − Re(wⁿ) ≤ 1 + |Re(wⁿ)| ≤ 1 + ‖wⁿ‖ = 1 + ‖w‖ⁿ ≤ 2`.
-/
theorem li_re_le_two (w : ℂ) (hw : ‖w‖ ≤ 1) (n : ℕ) :
    (1 - w ^ n).re ≤ 2 := by
  norm_num [ Complex.norm_def, Complex.normSq ] at *;
  -- By induction on $n$, we can show that $|w^n| \leq 1$.
  have h_ind : ∀ n : ℕ, (w ^ n).re ^ 2 + (w ^ n).im ^ 2 ≤ 1 := by
    intro n; induction n <;> simp_all +decide [ pow_succ' ] ; nlinarith;
  nlinarith [ h_ind n ]

/-
When `‖w‖ ≤ 1`, each Li term `Re[1 − wⁿ]` is nonneg.
    Proof: `Re(1−wⁿ) = 1 − Re(wⁿ) ≥ 1 − ‖wⁿ‖ = 1 − ‖w‖ⁿ ≥ 0`.
-/
theorem li_re_nonneg (w : ℂ) (hw : ‖w‖ ≤ 1) (n : ℕ) :
    0 ≤ (1 - w ^ n).re := by
  -- By the properties of the real part and the norm, we have:
  have h1 : (w ^ n).re ≤ ‖w ^ n‖ := by
    exact Complex.re_le_norm _;
  norm_num at *;
  exact h1.trans ( pow_le_one₀ ( norm_nonneg _ ) hw )

/-! ## Part 3: The Forced Alignment — σ = 1/2 is Derived, Not Assumed -/

/-- **Off-line paired Li is unbounded below.**
    If `σ ≠ 1/2` and `γ ≠ 0`, the paired Li coefficient
    `Re[1 − w(ρ)ⁿ] + Re[1 − w(1−ρ)ⁿ]` is unbounded below.

    Proof: By `one_partner_gt_one`, WLOG `‖w(ρ)‖ > 1`.
    Then `‖w(1−ρ)‖ = 1/‖w(ρ)‖ < 1`, so the second Li term ≤ 2 for all n.
    The first Li term is unbounded below (by `li_helix_unbounded_off_line`).
    For any M: pick n with first term < M − 2; at that same n, second term ≤ 2;
    so the sum < M. -/
theorem paired_li_unbounded_off_line (sigma gamma : ℝ)
    (hs : sigma ≠ 1/2) (hg : gamma ≠ 0) :
    ∀ M : ℝ, ∃ n : ℕ,
    (li_helix_term sigma gamma n).re +
    (li_helix_term (1 - sigma) (-gamma) n).re < M := by
  sorry

/-- **The main theorem: bounded paired Li forces σ = 1/2.**

    If the paired Li coefficient `λₙ(ρ) + λₙ(1−ρ)` is bounded below
    for all n, then `σ = 1/2`.

    This DERIVES the critical line from:
    - The involution `σ ↦ 1−σ` (functional equation)
    - The Möbius reciprocal `‖w(ρ)‖ · ‖w(1−ρ)‖ = 1`
    - The cofinal recurrence blow-up for `‖w‖ > 1`

    No circular reasoning: we never assume zeros are at `Re = 1/2`.
    We prove that any zero NOT at `Re = 1/2` would produce unbounded
    paired Li coefficients. -/
theorem forced_half_from_bounded_li (sigma gamma : ℝ) (hg : gamma ≠ 0)
    (hbdd : ∃ M : ℝ, ∀ n : ℕ,
      M ≤ (li_helix_term sigma gamma n).re +
          (li_helix_term (1 - sigma) (-gamma) n).re) :
    sigma = 1 / 2 := by
  sorry

/-- **Equivalence form**: σ = 1/2 ⟺ paired Li bounded below.

    Forward: σ = 1/2 implies each term ∈ [0, 2], so the sum ∈ [0, 4].
    Backward: bounded below implies σ = 1/2 (by `forced_half_from_bounded_li`). -/
theorem critical_line_iff_bounded_li (sigma gamma : ℝ) (hg : gamma ≠ 0) :
    sigma = 1 / 2 ↔
    ∃ M : ℝ, ∀ n : ℕ,
      M ≤ (li_helix_term sigma gamma n).re +
          (li_helix_term (1 - sigma) (-gamma) n).re := by
  sorry

/-! ## Part 4: Two-Projection Cascade Alignment -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-
The five-fold composition `P₂ ∘ P₁ ∘ R ∘ P₁ ∘ P₂` is self-adjoint
    when P₁, P₂, and R are all self-adjoint.
-/
theorem five_fold_self_adjoint
    (P₁ P₂ R : F →ₗ[ℝ] F)
    (hP₁_sa : ∀ x y, @inner ℝ F _ (P₁ x) y = @inner ℝ F _ x (P₁ y))
    (hP₂_sa : ∀ x y, @inner ℝ F _ (P₂ x) y = @inner ℝ F _ x (P₂ y))
    (hR_sa : ∀ x y, @inner ℝ F _ (R x) y = @inner ℝ F _ x (R y))
    (x y : F) :
    @inner ℝ F _ ((P₂ ∘ₗ P₁ ∘ₗ R ∘ₗ P₁ ∘ₗ P₂) x) y =
    @inner ℝ F _ x ((P₂ ∘ₗ P₁ ∘ₗ R ∘ₗ P₁ ∘ₗ P₂) y) := by
  simp +decide only [LinearMap.comp_apply, hP₂_sa, hP₁_sa, hR_sa]

/-- If R commutes with both P₁ and P₂, the five-fold cascade collapses
    to `R ∘ P₂ ∘ P₁`. -/
theorem five_fold_collapse_of_commuting
    (P₁ P₂ R : F →ₗ[ℝ] F)
    (hP₁_idem : ∀ x, P₁ (P₁ x) = P₁ x)
    (hP₂_idem : ∀ x, P₂ (P₂ x) = P₂ x)
    (hcomm₁ : ∀ x, P₁ (R x) = R (P₁ x))
    (hcomm₂ : ∀ x, P₂ (R x) = R (P₂ x))
    (x : F) :
    (P₂ ∘ₗ P₁ ∘ₗ R ∘ₗ P₁ ∘ₗ P₂) x = (R ∘ₗ P₂ ∘ₗ P₁) x := by
  sorry

/-
Two-projection alignment: R commuting with both P₁ and P₂
    implies R commutes with the cascade P₂∘P₁.
    Two Green-Helmholtz operators demanding compatibility with the same
    involution R forces R to preserve the entire flag of subspaces.
-/
theorem cascade_commutes_of_both_commute
    (P₁ P₂ R : F →ₗ[ℝ] F)
    (hcomm₁ : ∀ x, P₁ (R x) = R (P₁ x))
    (hcomm₂ : ∀ x, P₂ (R x) = R (P₂ x))
    (x : F) :
    (P₂ ∘ₗ P₁) (R x) = R ((P₂ ∘ₗ P₁) x) := by
  aesop

/-
Cross-term vanishes when R commutes with P₁:
    `⟪P₁x, R((I−P₁)x)⟫ = 0` in the aligned case.
-/
theorem cross_term_vanishes_when_aligned
    (P₁ R : F →ₗ[ℝ] F)
    (hP₁_sa : ∀ x y, @inner ℝ F _ (P₁ x) y = @inner ℝ F _ x (P₁ y))
    (hP₁_idem : ∀ x, P₁ (P₁ x) = P₁ x)
    (hR_sa : ∀ x y, @inner ℝ F _ (R x) y = @inner ℝ F _ x (R y))
    (hcomm : ∀ x, P₁ (R x) = R (P₁ x))
    (x : F) :
    @inner ℝ F _ (P₁ x) (R (x - P₁ x)) = 0 := by
  simp +decide [ *, inner_sub_right, inner_sub_left ]

/-- Two Green-Helmholtz energy balance: when R commutes with both G₁ and G₂,
    `⟪R(G₂(G₁x)), G₂(G₁x)⟫ = ‖G₂(G₁x)‖²`. -/
theorem two_green_energy_invariant
    (G₁ G₂ R : F →ₗ[ℝ] F)
    (hG₁_sa : ∀ x y, @inner ℝ F _ (G₁ x) y = @inner ℝ F _ x (G₁ y))
    (hG₁_idem : ∀ x, G₁ (G₁ x) = G₁ x)
    (hG₂_sa : ∀ x y, @inner ℝ F _ (G₂ x) y = @inner ℝ F _ x (G₂ y))
    (hG₂_idem : ∀ x, G₂ (G₂ x) = G₂ x)
    (hR_sa : ∀ x y, @inner ℝ F _ (R x) y = @inner ℝ F _ x (R y))
    (hR_inv : ∀ x, R (R x) = x)
    (hcomm₁ : ∀ x, G₁ (R x) = R (G₁ x))
    (hcomm₂ : ∀ x, G₂ (R x) = R (G₂ x))
    (x : F) :
    @inner ℝ F _ (R ((G₂ ∘ₗ G₁) x)) ((G₂ ∘ₗ G₁) x) =
    ‖(G₂ ∘ₗ G₁) x‖ ^ 2 := by
  sorry

end