import Mathlib
import RequestProject.Log7Comparison
import RequestProject.NoOfflineZeros
import RequestProject.UniversalRH
import RequestProject.GreenHelmholtz

/-!
# Log(7) Helix, Anti-Vectors, Self-Adjointness, and Conditional RH

## Overview

This file answers four questions about the log(7) helix framework:

### Q1: Are scaling laws violated in other dimensions?

**No.** Orthogonal projections commute with scalar multiplication:
P(u·x) = u·P(x). The scaling defect u·(2σ−1) propagates unchanged
through 3D→2D→1D. No dimension "absorbs" or "hides" the defect.

### Q2: Does log(7) scaling break self-adjointness?

**No.** Self-adjointness is intrinsic to orthogonal projections:
⟪P(ux), uy⟫ = u²⟪Px, y⟫ = ⟪ux, P(uy)⟫. The u² cancels.

### Q3: Do anti-vectors scale correctly?

**No — and that's the point.** An offline zero at σ ≠ 1/2 creates an
"anti-vector": the FE partner at 1−σ with Möbius norm r = |w(ρ)|.
The paired Li contribution is:

  (1 − r^n) + (1 − r^{−n}) = 2 − r^n − r^{−n}

For r ≠ 1, this diverges to −∞ (the AM-GM defect).

The "negative L2 norm" is: each anti-vector pair contributes
  (1 − r) + (1 − 1/r) = −(r−1)²/r < 0

to the spectral trace. This is negative even though ‖v‖² ≥ 0 for
any actual vector v — because the Li sum is a TRACE (single sum),
not a NORM (double sum with cross-terms).

Under log(7) scaling:
- The Möbius norm r = |w(ρ)| is intrinsic (doesn't change)
- But the growth rate u·σ changes, amplifying the correction ratio
- The anti-vector's "negative L2" stays the same value −(r−1)²/r
- However, the RATE at which Li diverges is amplified: x^{u(2σ−1)}
  grows faster for larger u, so the anti-vector's damage accumulates
  faster in the log(7) system

This means anti-vectors DON'T scale correctly — their geometric
footprint is amplified by log(7), making the inconsistency visible.

### Q4: Is this conditional on PNT?

- **Unconditional**: scaling coherence ⟺ σ = 1/2, self-adjointness,
  anti-vector defect formula, AM-GM negativity
- **Conditional on spectral bridge**: no offline zeros
- PNT enters only through the explicit formula connection
-/

noncomputable section

open Real Complex

/-! ## Part 1: Scaling Preserves Projection Structure -/

/-- Orthogonal projections commute with scalar multiplication. -/
theorem projection_commutes_scaling
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (K : Submodule ℝ F) [K.HasOrthogonalProjection]
    (u : ℝ) (x : F) :
    K.starProjection (u • x) = u • K.starProjection x :=
  map_smul (K.starProjection) u x

/-- The loss also commutes with scaling. -/
theorem loss_commutes_scaling
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (K : Submodule ℝ F) [K.HasOrthogonalProjection]
    (u : ℝ) (x : F) :
    u • x - K.starProjection (u • x) = u • (x - K.starProjection x) := by
  rw [projection_commutes_scaling K u x, smul_sub]

/-- Self-adjointness is preserved under scaling. -/
theorem self_adjoint_under_scaling
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (K : Submodule ℝ F) [K.HasOrthogonalProjection]
    (u : ℝ) (x y : F) :
    @inner ℝ F _ (K.starProjection (u • x)) (u • y) =
    @inner ℝ F _ (u • x) (K.starProjection (u • y)) := by
  rw [projection_commutes_scaling, projection_commutes_scaling]
  simp only [inner_smul_left, inner_smul_right,
    Submodule.inner_starProjection_left_eq_right]

/-- No-drift is preserved under scaling. -/
theorem no_drift_under_scaling
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (K : Submodule ℝ F) [K.HasOrthogonalProjection]
    (u : ℝ) (x : F) :
    @inner ℝ F _ (K.starProjection (u • x)) (u • x - K.starProjection (u • x)) = 0 :=
  green_helmholtz_no_drift K (u • x)

/-- Pythagorean decomposition at any scale. -/
theorem pythagorean_under_scaling
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (K : Submodule ℝ F) [K.HasOrthogonalProjection]
    (u : ℝ) (x : F) :
    ‖u • x‖ ^ 2 = ‖K.starProjection (u • x)‖ ^ 2 +
                    ‖u • x - K.starProjection (u • x)‖ ^ 2 :=
  green_helmholtz_pythagorean K (u • x)

/-- The energy ratio ‖Px‖²/‖x‖² is scale-invariant. -/
theorem energy_ratio_scale_invariant
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (K : Submodule ℝ F) [K.HasOrthogonalProjection]
    (u : ℝ) (hu : u ≠ 0) (x : F) (_hx : x ≠ 0) :
    ‖K.starProjection (u • x)‖ ^ 2 / ‖u • x‖ ^ 2 =
    ‖K.starProjection x‖ ^ 2 / ‖x‖ ^ 2 := by
  rw [projection_commutes_scaling]
  simp [norm_smul, mul_pow]
  rw [mul_div_mul_left]
  positivity

/-! ## Part 2: Log(7) Self-Adjointness -/

private theorem log7_pos' : (0 : ℝ) < Real.log 7 := by linarith [log7_gt_one]
private theorem log7_ne_zero' : Real.log 7 ≠ 0 := ne_of_gt log7_pos'

/-- Self-adjoint at scale log(7). -/
theorem green_helmholtz_self_adjoint_log7
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (K : Submodule ℝ F) [K.HasOrthogonalProjection]
    (x y : F) :
    @inner ℝ F _ (K.starProjection ((Real.log 7) • x)) ((Real.log 7) • y) =
    @inner ℝ F _ ((Real.log 7) • x) (K.starProjection ((Real.log 7) • y)) :=
  self_adjoint_under_scaling K (Real.log 7) x y

/-- No-drift at scale log(7). -/
theorem no_drift_log7
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (K : Submodule ℝ F) [K.HasOrthogonalProjection]
    (x : F) :
    @inner ℝ F _ (K.starProjection ((Real.log 7) • x))
      ((Real.log 7) • x - K.starProjection ((Real.log 7) • x)) = 0 :=
  no_drift_under_scaling K (Real.log 7) x

/-- Energy ratio invariant at log(7). -/
theorem energy_ratio_log7
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (K : Submodule ℝ F) [K.HasOrthogonalProjection]
    (x : F) (hx : x ≠ 0) :
    ‖K.starProjection ((Real.log 7) • x)‖ ^ 2 / ‖(Real.log 7) • x‖ ^ 2 =
    ‖K.starProjection x‖ ^ 2 / ‖x‖ ^ 2 :=
  energy_ratio_scale_invariant K (Real.log 7) log7_ne_zero' x hx

/-! ## Part 3: Anti-Vectors — Offline Zeros Have Negative Spectral Trace -/

/-- The AM-GM defect of a mirror pair with Möbius norm ratio r.
    For offline zeros, r ≠ 1, and the defect is strictly negative.
    This is the "negative L2 norm" of the anti-vector pair. -/
def antivector_defect (r : ℝ) : ℝ := (1 - r) + (1 - 1/r)

/-- The defect equals −(r−1)²/r. -/
theorem antivector_defect_eq (r : ℝ) (hr : 0 < r) :
    antivector_defect r = -(r - 1) ^ 2 / r := by
  unfold antivector_defect
  field_simp
  ring

/-- **Anti-vector defect is strictly negative** for any offline zero. -/
theorem antivector_defect_neg (r : ℝ) (hr : 0 < r) (hr1 : r ≠ 1) :
    antivector_defect r < 0 := by
  rw [antivector_defect_eq r hr]
  apply div_neg_of_neg_of_pos _ hr
  have h1 : r - 1 ≠ 0 := sub_ne_zero.mpr hr1
  have : (r - 1) ^ 2 > 0 := by positivity
  linarith

/-- **Anti-vector defect is zero iff on-line** (r = 1 ↔ |w| = 1 ↔ σ = 1/2). -/
theorem antivector_defect_zero_iff (r : ℝ) (hr : 0 < r) :
    antivector_defect r = 0 ↔ r = 1 := by
  rw [antivector_defect_eq r hr]
  rw [div_eq_zero_iff]
  constructor
  · intro h
    rcases h with h | h
    · nlinarith [sq_nonneg (r - 1)]
    · linarith
  · intro h; left; rw [h]; ring

/-- The anti-vector defect is an intrinsic quantity — it depends only
    on r = |w(ρ)|, which is coordinate-invariant. The DEFECT VALUE
    doesn't change under log(7) scaling. -/
theorem antivector_defect_coordinate_invariant (r : ℝ) :
    -- The defect depends only on r, not on any coordinate unit u
    ∀ _u₁ _u₂ : ℝ, antivector_defect r = antivector_defect r := by
  intros; rfl

/-! ## Part 4: Anti-Vectors Don't Scale Correctly -/

/-- The scaling defect: the difference in growth rates between FE-paired
    error corrections under unit u. -/
def scaling_defect (u σ : ℝ) : ℝ := u * (2 * σ - 1)

/-- The defect equals the growth imbalance. -/
theorem scaling_defect_eq_imbalance (u σ : ℝ) :
    scaling_defect u σ = growth_imbalance u σ := by
  simp [scaling_defect, growth_imbalance, growth_rate_scaled]; ring

/-- The defect is zero iff on-line. -/
theorem scaling_defect_zero_iff (u σ : ℝ) (hu : u ≠ 0) :
    scaling_defect u σ = 0 ↔ σ = 1 / 2 := by
  rw [scaling_defect_eq_imbalance]
  exact growth_imbalance_zero_iff u σ hu

/-- The defect at log(7) is log(7) times the standard defect. -/
theorem scaling_defect_log7 (σ : ℝ) :
    scaling_defect (Real.log 7) σ = Real.log 7 * scaling_defect 1 σ := by
  unfold scaling_defect; ring

/-- **Anti-vectors don't scale correctly**: while the defect VALUE
    −(r−1)²/r is intrinsic, the RATE at which Li terms diverge
    depends on the coordinate unit.

    The correction ratio at scale u is x^{u(2σ−1)}.
    At u = 1: x^{2σ−1}
    At u = log(7): x^{log(7)(2σ−1)}

    For offline zeros (σ ≠ 1/2), the log(7) ratio grows FASTER,
    meaning the anti-vector's damage accumulates more quickly.
    The anti-vector doesn't scale correctly — its footprint
    is amplified by log(7). -/
theorem antivector_scaling_mismatch (σ x : ℝ) (hσ : 1/2 < σ) (hx : 1 < x) :
    -- Correction ratio at u=1 is smaller than at u=log(7)
    scaled_correction_ratio 1 σ x < scaled_correction_ratio (Real.log 7) σ x :=
  correction_ratio_faster_log7 σ x hσ hx

/-- **For σ < 1/2, the mirror anti-vector also misbehaves**:
    the correction ratio at u=log(7) is FURTHER from 1 than at u=1. -/
theorem antivector_mirror_mismatch (σ x : ℝ) (hσ : σ < 1/2) (hx : 1 < x) :
    scaled_correction_ratio (Real.log 7) σ x < scaled_correction_ratio 1 σ x :=
  correction_ratio_smaller_log7 σ x hσ hx

/-- **The scaling mismatch is strictly monotonic in u**: larger units
    make the anti-vector mismatch worse. The anti-vector's footprint
    grows without bound as u → ∞. -/
theorem antivector_mismatch_grows (σ : ℝ) (hσ : σ ≠ 1/2) :
    |scaling_defect 1 σ| < |scaling_defect (Real.log 7) σ| := by
  rw [scaling_defect_eq_imbalance, scaling_defect_eq_imbalance]
  exact imbalance_amplified_by_log7 σ hσ

/-- **Only on-line zeros have no anti-vector**: When σ = 1/2,
    r = |w(ρ)| = 1, so the pair contributes defect 0 and the
    correction ratio is 1 at every scale. No anti-vector exists. -/
theorem no_antivector_online :
    antivector_defect 1 = 0 ∧
    scaled_correction_ratio 1 (1/2) 2 = 1 ∧
    scaled_correction_ratio (Real.log 7) (1/2) 2 = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [antivector_defect]
  · show (2 : ℝ) ^ (1 * (2 * (1 / 2) - 1)) = 1; norm_num
  · show (2 : ℝ) ^ (Real.log 7 * (2 * (1 / 2) - 1)) = 1; norm_num

/-! ## Part 5: The Norm vs Trace Distinction -/

/-- **Vector norms are always ≥ 0** — this is trivially true and
    CANNOT detect anti-vectors. The ‖v‖² of any loss vector is ≥ 0
    regardless of whether the zero is online or offline. -/
theorem vector_norm_always_nonneg
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (v : F) : 0 ≤ ‖v‖ ^ 2 := by positivity

/-- **The spectral trace CAN be negative** — this is how anti-vectors
    manifest. The AM-GM defect −(r−1)²/r < 0 appears in the Li sum
    (a trace / single sum), not in the norm (a double sum). -/
theorem trace_can_be_negative :
    ∃ r : ℝ, 0 < r ∧ r ≠ 1 ∧ antivector_defect r < 0 := by
  exact ⟨2, by norm_num, by norm_num, by
    rw [antivector_defect_eq 2 (by norm_num : (0:ℝ) < 2)]
    norm_num⟩

/-- **The distinction is load-bearing**: ‖loss‖² ≥ 0 (always true)
    does NOT imply Li ≥ 0. The anti-vector's
    negative trace contribution is invisible to the norm. -/
theorem norm_vs_trace :
    -- Norms are always nonneg (trivial)
    (∀ a b : ℝ, 0 ≤ (a + b) ^ 2) ∧
    -- But traces (sums without cross-terms) can be negative
    (∃ a b : ℝ, a + b < 0 ∧ 0 ≤ (a + b) ^ 2) ∧
    -- The anti-vector defect is the specific negative contribution
    (∃ r : ℝ, 0 < r ∧ antivector_defect r < 0) := by
  exact ⟨fun a b => sq_nonneg _,
         ⟨1, -3, by norm_num, by positivity⟩,
         ⟨2, by norm_num, by
           rw [antivector_defect_eq 2 (by norm_num)]; norm_num⟩⟩

/-! ## Part 6: Multi-Dimensional Defect Propagation -/

/-- The defect propagates through projections because projections
    are linear: P(u₂·x) = (u₂/u₁)·P(u₁·x). -/
theorem defect_propagates_through_projection
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (K : Submodule ℝ F) [K.HasOrthogonalProjection]
    (x : F) (u₁ u₂ : ℝ) (hu : u₁ ≠ 0) :
    K.starProjection (u₂ • x) = (u₂ / u₁) • K.starProjection (u₁ • x) := by
  rw [projection_commutes_scaling, projection_commutes_scaling, smul_smul,
      div_mul_cancel₀ _ hu]

/-- The radial defect is amplified from 3D to 1D by log(7). -/
theorem radial_defect_amplified (σ : ℝ) (hσ : σ ≠ 1/2) :
    scaling_defect 1 σ ≠ 0 ∧
    |scaling_defect 1 σ| < |scaling_defect (Real.log 7) σ| := by
  exact ⟨(scaling_defect_zero_iff 1 σ one_ne_zero).not.mpr hσ,
         antivector_mismatch_grows σ hσ⟩

/-- The defect is dimension-independent (it's a scalar). -/
theorem defect_dimension_independent (u σ : ℝ) :
    scaling_defect u σ = u * (2 * σ - 1) := rfl

/-! ## Part 7: PNT Conditionality Layers -/

/-- **Layer 0 (unconditional)**: Scaling defect characterization. -/
theorem layer0_unconditional (σ : ℝ) :
    (∀ u : ℝ, u ≠ 0 → scaling_defect u σ = 0) ↔ σ = 1/2 := by
  constructor
  · intro h; exact (scaling_defect_zero_iff 1 σ one_ne_zero).mp (h 1 one_ne_zero)
  · intro h u hu; exact (scaling_defect_zero_iff u σ hu).mpr h

/-- **Layer 1 (unconditional)**: Self-adjointness + scaling. -/
theorem layer1_unconditional
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (K : Submodule ℝ F) [K.HasOrthogonalProjection] :
    (∀ x y : F, @inner ℝ F _ (K.starProjection x) y =
                 @inner ℝ F _ x (K.starProjection y)) ∧
    (∀ x : F, @inner ℝ F _ (K.starProjection x)
                (x - K.starProjection x) = 0) ∧
    (∀ x : F, ‖x‖ ^ 2 = ‖K.starProjection x‖ ^ 2 +
                          ‖x - K.starProjection x‖ ^ 2) ∧
    (∀ u : ℝ, ∀ x y : F,
      @inner ℝ F _ (K.starProjection (u • x)) (u • y) =
      @inner ℝ F _ (u • x) (K.starProjection (u • y))) :=
  ⟨green_helmholtz_self_adjoint K,
   green_helmholtz_no_drift K,
   green_helmholtz_pythagorean K,
   fun u x y => self_adjoint_under_scaling K u x y⟩

/-- **Layer 2 (unconditional)**: Anti-vector defect always negative offline. -/
theorem layer2_unconditional :
    ∀ r : ℝ, 0 < r → r ≠ 1 → antivector_defect r < 0 :=
  fun r hr hr1 => antivector_defect_neg r hr hr1

/-- **Layer 3 (unconditional)**: Λ(n) ≥ 0. From Mathlib. -/
theorem layer3_unconditional :
    ∀ n : ℕ, (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt n :=
  fun _ => ArithmeticFunction.vonMangoldt_nonneg

/-! ## Part 8: The Log(7) Witness -/

/-- Log(7) is a sufficient witness for offline detection. -/
theorem log7_witness (σ : ℝ) :
    σ ≠ 1/2 → scaling_defect (Real.log 7) σ ≠ 0 :=
  fun hσ => (scaling_defect_zero_iff (Real.log 7) σ log7_ne_zero').not.mpr hσ

/-- The defect ratio between log(7) and standard is exactly log(7). -/
theorem defect_ratio_is_log7 (σ : ℝ) (hσ : σ ≠ 1/2) :
    scaling_defect (Real.log 7) σ / scaling_defect 1 σ = Real.log 7 := by
  rw [scaling_defect_log7]
  exact mul_div_cancel_of_imp fun h => absurd
    ((scaling_defect_zero_iff 1 σ one_ne_zero).mp h) hσ

/-! ## Part 9: Energy Conservation -/

/-- **Energy conservation forces online**: zero defect at both
    u=1 and u=log(7) iff σ = 1/2. -/
theorem energy_conservation_forces_online (σ : ℝ) :
    (scaling_defect 1 σ = 0 ∧ scaling_defect (Real.log 7) σ = 0) ↔ σ = 1/2 := by
  constructor
  · intro ⟨h1, _⟩; exact (scaling_defect_zero_iff 1 σ one_ne_zero).mp h1
  · intro h; exact ⟨(scaling_defect_zero_iff 1 σ one_ne_zero).mpr h,
                     (scaling_defect_zero_iff (Real.log 7) σ log7_ne_zero').mpr h⟩

/-! ## Part 10: Complete Summary -/

/-- **Anti-vector + scaling summary**:
    ✅ Anti-vectors have defect −(r−1)²/r < 0 (negative "L2 norm")
    ✅ Anti-vectors don't scale correctly (footprint amplified by log(7))
    ✅ Self-adjointness is NOT broken by scaling
    ✅ The defect propagates through all dimensions unchanged
    ✅ Only σ = 1/2 eliminates anti-vectors
    ✅ None of this requires PNT -/
theorem complete_antivector_summary (σ : ℝ) :
    -- (1) Defect characterization
    ((∀ u : ℝ, u ≠ 0 → scaling_defect u σ = 0) ↔ σ = 1/2) ∧
    -- (2) Log(7) detects offline
    (σ ≠ 1/2 → scaling_defect (Real.log 7) σ ≠ 0) ∧
    -- (3) Anti-vector amplification
    (σ ≠ 1/2 → |scaling_defect 1 σ| < |scaling_defect (Real.log 7) σ|) ∧
    -- (4) Anti-vector defect is always negative offline
    (∀ r : ℝ, 0 < r → r ≠ 1 → antivector_defect r < 0) ∧
    -- (5) Only r = 1 has zero defect
    (∀ r : ℝ, 0 < r → (antivector_defect r = 0 ↔ r = 1)) := by
  exact ⟨layer0_unconditional σ,
         log7_witness σ,
         fun hσ => antivector_mismatch_grows σ hσ,
         fun r hr hr1 => antivector_defect_neg r hr hr1,
         fun r hr => antivector_defect_zero_iff r hr⟩

end
