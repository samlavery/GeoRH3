import Mathlib
import RequestProject.ForcedAlignment
import RequestProject.UniversalRH
import RequestProject.GreenHelmholtz
import RequestProject.ConcreteOperators
import RequestProject.BridgeToZeroFree
import RequestProject.NoOfflineZeros

/-!
# Self-Dual Cascade Forces the Midpoint — Spectral Convergence

## Overview

This file proves three results that make the spectral bridge transparent:

### 1. Self-Dual Midpoint Forcing (Abstract)

A self-adjoint orthogonal projection P decomposes any vector as
  `x = Px + (I-P)x`   with   `⟪Px, (I-P)x⟫ = 0`

Both P and I-P are self-adjoint projections (**self-dual decomposition**).
If an involution R negates the loss — `(I-P)(Rx) = -(I-P)x` — then:

  **Fixed points of R lie in Im(P).**

Proof: Rx = x ⟹ (I-P)x = -(I-P)x ⟹ (I-P)x = 0 ⟹ x ∈ Im(P).

The functional equation σ ↦ 1-σ negates the radial loss σ-½.
So FE-fixed zeros (σ = 1-σ) satisfy σ = ½, the midpoint.

### 2. Paired Radial Loss Forces the Midpoint (Concrete)

For an FE pair (ρ, 1-ρ) with radial losses σ-½ and ½-σ:
  `paired_loss = (σ-½)² + (½-σ)² = 2(σ-½)²`

This is zero **if and only if** σ = ½. The cascade geometry
uniquely determines the critical line as the zero-loss locus.

### 3. Harmonic Corrections and Increasing Convergence

On-line zeros produce oscillatory corrections `1 - cos(nθ_k)`:
- Each is nonneg and bounded by 2 (**harmonic**)
- Adding zeros increases the partial sum (**monotone**)
- Each correction satisfies `|1-w^n| ≤ n|1-w|` (**telescope bound**)
- For zeros with |γ| → ∞: |1-w| = 1/|ρ| → 0 (**vanishing**)
- So individual corrections → 0 for fixed n (**convergence**)

### Bridge Resolution

The spectral bridge `VonMangoldtSpectralBridge S` is logically equivalent to
`UniversalLiBounded S`, which is equivalent to `∀ z ∈ S, z.1 = 1/2`.
It is NOT conditional on von Mangoldt (which is unconditionally nonneg) —
it IS the statement that all zeros lie at the midpoint of the cascade.

The cascade geometry shows WHY the midpoint is special:
- Self-dual projections force zero loss at the midpoint
- The FE involution negates the loss, selecting the midpoint as fixed
- The Möbius reciprocal makes the midpoint the unique unitary point
- Von Mangoldt Λ ≥ 0 feeds into this via the Mertens inequality,
  giving the strongest unconditional constraint (Re(s) > 1-c/log|t|)
-/

noncomputable section

open Complex Real Finset

/-! ## Part 1: Abstract Midpoint Forcing from Self-Dual Projections -/

section AbstractMidpoint

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **Midpoint Forcing Theorem**: If an involution R negates the projection
    loss `(I-P)(Rx) = -(I-P)x`, then every fixed point of R lies in Im(P).

    This captures the dimensional geometry: the self-dual cascade has
    self-adjoint projection P and self-adjoint complement I-P. An
    involution that negates the complement forces its fixed points to
    lie in the projection image — the midpoint plane.

    For the Riemann zeta: P = radial projection (3D→2D), R = functional
    equation (σ ↦ 1-σ). The radial loss is σ-½, negated by R.
    Fixed points: σ = 1-σ, i.e., σ = ½ — the critical line. -/
theorem midpoint_forcing
    (P R : F →ₗ[ℝ] F)
    (hR_neg_loss : ∀ x, R x - P (R x) = -(x - P x))
    (v : F) (hv_fixed : R v = v) :
    P v = v := by
  have h := hR_neg_loss v
  rw [hv_fixed] at h
  -- h : v - P v = -(v - P v), so v - P v = 0
  have h2 : v - P v = 0 := by
    have h3 : (v - P v) + (v - P v) = 0 := by nth_rw 2 [h]; exact add_neg_cancel _
    have h4 : (2 : ℝ) • (v - P v) = 0 := by rwa [two_smul]
    rwa [smul_eq_zero, or_iff_right two_ne_zero] at h4
  exact eq_of_sub_eq_zero h2 |>.symm

/-- **Paired Loss Doubling**: When R negates the loss, the paired loss
    for (x, Rx) equals exactly double the single loss.
    `‖loss(Rx)‖² + ‖loss(x)‖² = 2‖loss(x)‖²` -/
theorem paired_loss_double
    (P R : F →ₗ[ℝ] F)
    (hR_neg_loss : ∀ x, R x - P (R x) = -(x - P x))
    (x : F) :
    ‖R x - P (R x)‖ ^ 2 + ‖x - P x‖ ^ 2 = 2 * ‖x - P x‖ ^ 2 := by
  rw [hR_neg_loss, norm_neg]; ring

/-- **Zero Paired Loss ↔ In Image**: The paired loss vanishes iff x ∈ Im(P). -/
theorem paired_loss_zero_iff_in_image
    (P R : F →ₗ[ℝ] F)
    (hR_neg_loss : ∀ x, R x - P (R x) = -(x - P x))
    (x : F) :
    ‖x - P x‖ ^ 2 + ‖R x - P (R x)‖ ^ 2 = 0 ↔ P x = x := by
  rw [hR_neg_loss, norm_neg]
  constructor
  · intro h
    have : ‖x - P x‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖x - P x‖]
    rwa [sq_eq_zero_iff, norm_eq_zero, sub_eq_zero, eq_comm] at this
  · intro h; rw [h, sub_self, norm_zero]; ring

/-- **Self-Dual Decomposition**: Both P and I-P are self-adjoint. The
    cascade has a self-dual structure where signal and loss play
    symmetric roles. This is the Green-Helmholtz self-duality. -/
theorem self_dual_decomposition
    (K : Submodule ℝ F) [K.HasOrthogonalProjection] (x y : F) :
    -- P is self-adjoint
    @inner ℝ F _ (K.starProjection x) y =
    @inner ℝ F _ x (K.starProjection y) ∧
    -- I-P is self-adjoint (self-dual)
    @inner ℝ F _ (x - K.starProjection x) y =
    @inner ℝ F _ x (y - K.starProjection y) ∧
    -- P and I-P are orthogonal (no cross-talk)
    @inner ℝ F _ (K.starProjection x) (x - K.starProjection x) = 0 :=
  ⟨green_helmholtz_self_adjoint K x y,
   green_helmholtz_loss_self_adjoint K x y,
   green_helmholtz_no_drift K x⟩

end AbstractMidpoint

/-! ## Part 2: Concrete Midpoint — Paired Radial Loss -/

/-- The paired radial loss for an FE pair equals 2(σ-½)².
    This is the total loss when projecting both ρ and 1-ρ from 3D to 2D. -/
theorem paired_radial_loss (sigma : ℝ) :
    (sigma - 1/2) ^ 2 + ((1 - sigma) - 1/2) ^ 2 = 2 * (sigma - 1/2) ^ 2 := by
  ring

/-- The paired radial loss vanishes iff σ = ½ (the midpoint). -/
theorem paired_radial_loss_zero_iff (sigma : ℝ) :
    (sigma - 1/2) ^ 2 + ((1 - sigma) - 1/2) ^ 2 = 0 ↔ sigma = 1/2 := by
  rw [paired_radial_loss]
  constructor
  · intro h; nlinarith [sq_nonneg (sigma - 1/2)]
  · intro h; rw [h]; ring

/-- The FE involution negates the radial loss: (1-σ)-½ = -(σ-½). -/
theorem fe_negates_radial (sigma : ℝ) :
    (1 - sigma) - 1/2 = -(sigma - 1/2) := by ring

/-- **Midpoint is the unique zero-loss configuration** for the cascade.
    The 3D→2D projection drops the radial component. For an FE pair:
    - Zero ρ has radial = σ-½
    - Partner 1-ρ has radial = ½-σ = -(σ-½)
    - Total loss = 2(σ-½)²
    - Loss = 0 ↔ σ = ½ -/
theorem cascade_midpoint_unique (sigma gamma : ℝ) (x : ℝ) :
    ((zero_embed sigma gamma x).radial = 0 ∧
     (zero_embed (1 - sigma) (-gamma) x).radial = 0) ↔
    sigma = 1/2 := by
  simp only [zero_embed, sub_eq_zero]
  constructor
  · rintro ⟨h, _⟩; linarith
  · intro h; constructor <;> linarith

/-- The radial loss is antisymmetric under the FE involution. -/
theorem radial_antisymmetric (sigma gamma x : ℝ) :
    (zero_embed (1 - sigma) (-gamma) x).radial =
    -(zero_embed sigma gamma x).radial := by
  simp [zero_embed]; ring

/-- **The cascade equivalence chain**: σ = ½ ↔ zero radial loss ↔ ‖w‖ = 1. -/
theorem cascade_equivalence_chain (sigma gamma : ℝ) (_hg : gamma ≠ 0) :
    (sigma = 1/2) ↔ ((zero_embed sigma gamma 1).radial = 0) :=
  (radial_loss_zero_iff sigma gamma 1).symm

/-! ## Part 3: Telescope Bound and Harmonic Properties -/

/-- **Telescope factorization**: `1 - w^n = (Σ w^k) · (1-w)`. -/
theorem one_sub_pow_factor (w : ℂ) (n : ℕ) :
    1 - w ^ n = (∑ k ∈ range n, w ^ k) * (1 - w) := by
  have h := geom_sum_mul w n
  have : (∑ k ∈ range n, w ^ k) * (1 - w) =
    -((∑ k ∈ range n, w ^ k) * (w - 1)) := by ring
  rw [this, h]; ring

/-- **Telescope bound**: `‖1 - w^n‖ ≤ n · ‖1-w‖` when `‖w‖ ≤ 1`.
    Each power stays on or inside the unit disk, so the geometric
    sum has at most n terms of norm ≤ 1. -/
theorem norm_one_sub_pow_le (w : ℂ) (hw : ‖w‖ ≤ 1) (n : ℕ) :
    ‖1 - w ^ n‖ ≤ n * ‖1 - w‖ := by
  rw [one_sub_pow_factor]
  calc ‖(∑ k ∈ range n, w ^ k) * (1 - w)‖
      = ‖∑ k ∈ range n, w ^ k‖ * ‖1 - w‖ := norm_mul _ _
    _ ≤ (∑ k ∈ range n, ‖w ^ k‖) * ‖1 - w‖ :=
        mul_le_mul_of_nonneg_right (norm_sum_le _ _) (norm_nonneg _)
    _ ≤ (∑ k ∈ range n, (1 : ℝ)) * ‖1 - w‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        apply sum_le_sum; intro k _
        rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hw
    _ = n * ‖1 - w‖ := by simp

/-- **Harmonic bound**: On-line Li terms satisfy `0 ≤ Re[1-w^n] ≤ 2`. -/
theorem on_line_harmonic_bound (gamma : ℝ) (n : ℕ) :
    0 ≤ (li_helix_term (1/2) gamma n).re ∧
    (li_helix_term (1/2) gamma n).re ≤ 2 := by
  refine ⟨li_helix_nonneg_on_line gamma n, ?_⟩
  unfold li_helix_term
  apply li_re_le_two
  by_cases hg : gamma = 0
  · subst hg; simp [moebius_helix]; norm_num [Complex.norm_def, Complex.normSq]
  · exact le_of_eq ((moebius_unit_iff (1/2) gamma hg).mpr rfl)

/-- **Paired harmonic bound**: Each on-line FE pair contributes ∈ [0, 4]. -/
theorem on_line_paired_harmonic_bound (gamma : ℝ) (n : ℕ) :
    0 ≤ (li_helix_term (1/2) gamma n).re +
        (li_helix_term (1 - 1/2) (-gamma) n).re ∧
    (li_helix_term (1/2) gamma n).re +
    (li_helix_term (1 - 1/2) (-gamma) n).re ≤ 4 := by
  constructor
  · exact universal_on_line_pair_nonneg gamma n
  · exact on_line_pair_le_four gamma n

/-! ## Part 4: Monotone Partial Sums -/

/-- Subset monotonicity: larger on-line sets have larger Li sums. -/
theorem partial_sum_monotone_subset (S T : Finset (ℝ × ℝ))
    (hST : S ⊆ T)
    (h_online : ∀ z ∈ T, z.1 = 1/2)
    (n : ℕ) :
    universal_paired_li_sum S n ≤ universal_paired_li_sum T n := by
  unfold universal_paired_li_sum
  apply sum_le_sum_of_subset_of_nonneg hST
  intro z _ _
  rw [h_online z (by assumption)]
  exact universal_on_line_pair_nonneg z.2 n

/-- On-line partial sums are nonneg (monotone from ∅). -/
theorem partial_sum_nonneg (T : Finset (ℝ × ℝ))
    (h_online : ∀ z ∈ T, z.1 = 1/2) (n : ℕ) :
    0 ≤ universal_paired_li_sum T n := by
  unfold universal_paired_li_sum
  apply sum_nonneg
  intro z hz
  rw [h_online z hz]
  exact universal_on_line_pair_nonneg z.2 n

/-! ## Part 5: Convergence — Individual Corrections Vanish -/

/-- The Möbius complement: `1 - w(ρ) = 1/ρ` as a complex number. -/
theorem moebius_complement (sigma gamma : ℝ) :
    1 - moebius_helix sigma gamma = 1 / (⟨sigma, gamma⟩ : ℂ) := by
  unfold moebius_helix; ring

/-- For on-line zeros, the correction at Li index n is bounded by
    `n · ‖1/ρ‖`. As |γ| → ∞, |ρ| → ∞, so each correction → 0. -/
theorem on_line_correction_bound (gamma : ℝ) (_hg : gamma ≠ 0) (n : ℕ) :
    ‖(li_helix_term (1/2) gamma n : ℂ)‖ ≤
    n * ‖(1 : ℂ) - moebius_helix (1/2) gamma‖ := by
  unfold li_helix_term
  apply norm_one_sub_pow_le
  exact le_of_eq ((moebius_unit_iff (1/2) gamma _hg).mpr rfl)

/-- The complement norm `‖1-w‖` for on-line zeros equals `1/|ρ|`.
    Since |ρ| = √(¼ + γ²), this → 0 as |γ| → ∞.  -/
theorem complement_norm_eq_inv_rho (gamma : ℝ) :
    ‖(1 : ℂ) - moebius_helix (1/2) gamma‖ =
    ‖((⟨(1:ℝ)/2, gamma⟩ : ℂ)⁻¹)‖ := by
  congr 1; unfold moebius_helix; simp [one_div]

/-
The complement norm decreases as |γ| increases: `‖1-w‖ ≤ 1/|γ|`.
-/
theorem complement_norm_bound (gamma : ℝ) (hg : 1 ≤ |gamma|) :
    ‖(1 : ℂ) - moebius_helix (1/2) gamma‖ ≤ 1 / |gamma| := by
  rw [ complement_norm_eq_inv_rho ] ; norm_num [ Complex.normSq, Complex.norm_def ];
  exact inv_anti₀ ( by positivity ) ( Real.abs_le_sqrt ( by nlinarith ) )

/-- **Increasing convergence summary**: For on-line zeros:
    1. Each correction is nonneg and bounded by 2
    2. Each correction ≤ n · |1-w| (telescope)
    3. Partial sums are monotone non-decreasing
    4. |1-w| = 1/|ρ| → 0 as |γ| → ∞ -/
theorem increasing_convergence_summary :
    -- (1) On-line corrections are nonneg
    (∀ γ : ℝ, ∀ n : ℕ, 0 ≤ (li_helix_term (1/2) γ n).re) ∧
    -- (2) On-line corrections are bounded by 2
    (∀ γ : ℝ, ∀ n : ℕ, (li_helix_term (1/2) γ n).re ≤ 2) ∧
    -- (3) Telescope bound: each correction ≤ n · ‖1-w‖
    (∀ w : ℂ, ‖w‖ ≤ 1 → ∀ n : ℕ, ‖1 - w ^ n‖ ≤ n * ‖1 - w‖) ∧
    -- (4) Subset monotonicity for on-line zeros
    (∀ (S T : Finset (ℝ × ℝ)), S ⊆ T →
      (∀ z ∈ T, z.1 = 1/2) → ∀ n : ℕ,
      universal_paired_li_sum S n ≤ universal_paired_li_sum T n) :=
  ⟨fun γ n => li_helix_nonneg_on_line γ n,
   fun γ n => (on_line_harmonic_bound γ n).2,
   fun w hw n => norm_one_sub_pow_le w hw n,
   fun S T hST hT n => partial_sum_monotone_subset S T hST hT n⟩

/-! ## Part 6: Bridge Resolution — The Spectral Bridge IS Geometric -/

/-- **The spectral bridge is equivalent to "all zeros at midpoint".**

    `VonMangoldtSpectralBridge S` was defined as:
      `(∀ n, 0 ≤ Λ(n)) → UniversalLiBounded S`

    Since `Λ(n) ≥ 0` is unconditionally true (Mathlib), the bridge
    simplifies to just `UniversalLiBounded S`.

    By `universal_rh`: `UniversalLiBounded S ↔ (∀ z ∈ S, z.1 = 1/2)`.

    So the bridge is equivalent to: "all zeros have zero radial loss",
    i.e., "all zeros lie at the midpoint of the self-dual cascade". -/
theorem bridge_is_zero_radial_loss (S : Set (ℝ × ℝ))
    (h_nt : ∀ z ∈ S, z.2 ≠ 0) :
    VonMangoldtSpectralBridge S ↔ (∀ z ∈ S, z.1 = 1/2) := by
  unfold VonMangoldtSpectralBridge
  constructor
  · intro h
    have hbdd := h (fun n => ArithmeticFunction.vonMangoldt_nonneg)
    exact (universal_rh S h_nt).mpr hbdd
  · intro h _
    exact (universal_rh S h_nt).mp h

/-- **The bridge is equivalent to UniversalLiBounded.**
    The von Mangoldt nonnegativity is not a condition — it's always true.
    The bridge is purely about whether the zeros are at the midpoint. -/
theorem bridge_eq_li_bounded (S : Set (ℝ × ℝ)) :
    VonMangoldtSpectralBridge S ↔ UniversalLiBounded S := by
  unfold VonMangoldtSpectralBridge
  exact ⟨fun h => h (fun n => ArithmeticFunction.vonMangoldt_nonneg),
         fun h _ => h⟩

/-- **What von Mangoldt gives unconditionally via the cascade.** -/
theorem vonmangoldt_unconditional_cascade :
    -- (1) Λ ≥ 0 is unconditional
    (∀ n : ℕ, (0:ℝ) ≤ ArithmeticFunction.vonMangoldt n) ∧
    -- (2) The Mertens inequality is unconditional
    (∀ θ : ℝ, 0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ)) ∧
    -- (3) The weighted Mertens sum is unconditional
    (∀ (a : ℕ → ℝ) (_ : ∀ n, 0 ≤ a n) (θ : ℝ) (S : Finset ℕ),
      0 ≤ ∑ n ∈ S, a n * (3 + 4 * Real.cos (↑n * θ) +
        Real.cos (2 * ↑n * θ))) ∧
    -- (4) The biconditional is unconditional
    (∀ (S : Set (ℝ × ℝ)),
      (∀ z ∈ S, z.2 ≠ 0) →
      ((∀ z ∈ S, z.1 = 1/2) ↔ UniversalLiBounded S)) ∧
    -- (5) The bridge = Li bounded (just a reformulation)
    (∀ (S : Set (ℝ × ℝ)),
      VonMangoldtSpectralBridge S ↔ UniversalLiBounded S) :=
  ⟨fun _n => ArithmeticFunction.vonMangoldt_nonneg,
   mertens_nonneg,
   fun a ha θ S => weighted_mertens_nonneg a ha θ S,
   -- (4)
   fun S h_nt => universal_rh S h_nt,
   fun S => bridge_eq_li_bounded S⟩

/-! ## Part 7: The Complete Cascade Picture -/

/-- **Complete Cascade Representation Equality**:

    The 3D→2D→1D cascade with self-dual projections gives exact
    decompositions at each level, with the radial loss tracking σ - ½. -/
theorem cascade_representation_equality (sigma gamma : ℝ) (x : ℝ) (hx : 0 < x) :
    let v := zero_embed sigma gamma x
    -- (1) Exact decomposition (signal = cascade + loss)
    v.proj = (apply_cascade v).proj + (loss v).proj ∧
    v.angular = (apply_cascade v).angular + (loss v).angular ∧
    v.radial = (apply_cascade v).radial + (loss v).radial ∧
    -- (2) The cascade keeps only the projected component
    (apply_cascade v).angular = 0 ∧
    (apply_cascade v).radial = 0 ∧
    -- (3) The loss has no projected component
    (loss v).proj = 0 ∧
    -- (4) Pythagorean decomposition
    v.proj ^ 2 + v.angular ^ 2 + v.radial ^ 2 =
      x ^ (2 * sigma) + (sigma - 1/2) ^ 2 ∧
    -- (5) Radial loss captures σ - ½
    v.radial = sigma - 1/2 ∧
    -- (6) FE antisymmetry of radial
    (zero_embed (1 - sigma) (-gamma) x).radial = -(sigma - 1/2) :=
  ⟨(signal_reconstruction (zero_embed sigma gamma x)).1,
   (signal_reconstruction (zero_embed sigma gamma x)).2.1,
   (signal_reconstruction (zero_embed sigma gamma x)).2.2,
   rfl, rfl, rfl,
   helix_vector_norm_sq sigma gamma x hx,
   rfl,
   by simp [zero_embed]; ring⟩

/-- **The Midpoint Theorem**: The self-dual cascade geometry gives a
    complete equivalence chain (all unconditional). -/
theorem midpoint_theorem (S : Set (ℝ × ℝ)) (h_nt : ∀ z ∈ S, z.2 ≠ 0) :
    -- All at midpoint ↔ Li bounded
    ((∀ z ∈ S, z.1 = 1/2) ↔ UniversalLiBounded S)
    ∧
    -- All at midpoint ↔ all spectral values unitary
    ((∀ z ∈ S, z.1 = 1/2) ↔ (∀ z ∈ S, ‖spectral_value z.1 z.2‖ = 1))
    ∧
    -- Paired radial loss = 0 ↔ midpoint (for each pair)
    (∀ σ : ℝ, (σ - 1/2)^2 + ((1-σ) - 1/2)^2 = 0 ↔ σ = 1/2)
    ∧
    -- Möbius characterization (for each zero)
    (∀ σ γ : ℝ, γ ≠ 0 → (‖spectral_value σ γ‖ = 1 ↔ σ = 1/2))
    ∧
    -- The bridge IS "all at midpoint"
    (VonMangoldtSpectralBridge S ↔ (∀ z ∈ S, z.1 = 1/2)) :=
  ⟨universal_rh S h_nt,
   ⟨fun h z hz => (spectral_on_circle_iff z.1 z.2 (h_nt z hz)).mpr (h z hz),
    fun h z hz => (spectral_on_circle_iff z.1 z.2 (h_nt z hz)).mp (h z hz)⟩,
   paired_radial_loss_zero_iff,
   fun σ γ hγ => spectral_on_circle_iff σ γ hγ,
   bridge_is_zero_radial_loss S h_nt⟩

/-- **Bridge Resolution**: The bridge is simply "all at midpoint" = RH. -/
theorem bridge_resolution (S : Set (ℝ × ℝ)) (h_nt : ∀ z ∈ S, z.2 ≠ 0) :
    -- The bridge IS "all at midpoint" (unconditional equivalence)
    (VonMangoldtSpectralBridge S ↔ (∀ z ∈ S, z.1 = 1/2)) ∧
    -- Which is also the biconditional
    ((∀ z ∈ S, z.1 = 1/2) ↔ UniversalLiBounded S) ∧
    -- Von Mangoldt gives the Mertens constraint (unconditional)
    (∀ θ : ℝ, 0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ)) ∧
    -- The cascade is self-dual at every stage (unconditional)
    (∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      (K : Submodule ℝ E) [K.HasOrthogonalProjection] (x y : E),
      @inner ℝ E _ (x - K.starProjection x) y =
      @inner ℝ E _ x (y - K.starProjection y)) :=
  ⟨bridge_is_zero_radial_loss S h_nt,
   universal_rh S h_nt,
   mertens_nonneg,
   fun K _ x y => green_helmholtz_loss_self_adjoint K x y⟩

end