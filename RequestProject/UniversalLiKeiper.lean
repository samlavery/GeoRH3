import Mathlib
import RequestProject.ForcedAlignment
import RequestProject.NoOfflineZeros
import RequestProject.HelixConvergence
import RequestProject.FiniteRH
import RequestProject.WeilExplicitBridge

/-!
# Universal Li-Keiper: Unconditional Results Over All Zeros

## Motivation

Previous files established Li-Keiper results for:
- A single zero pair (`ForcedAlignment.lean`)
- Finite collections (`NoOfflineZeros.lean`)
- Infinite sums under summability (`HelixConvergence.lean`)
- Finite partial sums with off-line zeros (`VonMangoldtTaylorBridge.lean`)

This file lifts ALL results to the **universal** setting: infinite sequences
of zeros indexed by `ℕ`, with no finite-set restriction. The key results are:

1. **Universal forward**: If all σ_k = 1/2, then for every n and every K,
   the partial sum is nonneg — unconditionally, for all K at once.

2. **Universal backward**: If ANY single zero has σ_j ≠ 1/2, then the Li
   partial sums are NOT uniformly bounded below — regardless of what the
   other zeros do (on-line, off-line, or mixed).

3. **Universal equivalence**: All zeros on the critical line ⟺ Li partial
   sums uniformly bounded below. No finite-set restriction.

The backward direction uses `first_K_on_line`: for any j, the uniform bound
gives a lower bound on `li_partial_sum Z (j+1) n` for all n, and the native
finite forcing (`finite_rh_indexed`, multi-circle recurrence / expansion-rate
domination) implies `Z.sigma j = 1/2`. No Weil functional enters.
-/

noncomputable section

open Complex Real Filter Finset

/-! ## Part 1: Universal Forward Direction -/

/-- **Universal forward (any K)**: If all zeros are on the critical line,
    the Li partial sum over any K zeros is nonneg for all n. -/
theorem universal_forward_partial (Z : ZetaZeroData)
    (h_all_on : ∀ k, Z.sigma k = 1/2) (K n : ℕ) :
    0 ≤ li_partial_sum Z K n :=
  li_nonneg_from_on_line Z h_all_on K n

/-- **Universal forward (upper bound)**: If all zeros are on the critical
    line, the Li partial sum is bounded above by 4K. -/
theorem universal_forward_upper (Z : ZetaZeroData)
    (h_all_on : ∀ k, Z.sigma k = 1/2) (K n : ℕ) :
    li_partial_sum Z K n ≤ 4 * ↑K :=
  li_partial_sum_on_line_le Z K (fun j _ => h_all_on j) n

/-- **Universal forward (uniform bounds)**: All on-line implies
    LiPartialSumsUniformlyBounded — without any summability hypothesis. -/
theorem universal_forward_bounded (Z : ZetaZeroData)
    (h_all_on : ∀ k, Z.sigma k = 1/2) :
    LiPartialSumsUniformlyBounded Z :=
  ⟨0, fun n K => universal_forward_partial Z h_all_on K n⟩

/-! ## Part 2: Universal Backward Direction -/

/-- **Universal backward**: If ANY zero has σ_j ≠ 1/2, the Li partial sums
    are NOT uniformly bounded below. No restriction on other zeros. -/
theorem universal_backward (Z : ZetaZeroData)
    (j : ℕ) (hj_off : Z.sigma j ≠ 1/2) :
    ¬ LiPartialSumsUniformlyBounded Z := by
  intro ⟨C, hC⟩
  have h_bdd : ∃ C : ℝ, ∀ n : ℕ, C ≤ li_partial_sum Z (j + 1) n :=
    ⟨C, fun n => hC n (j + 1)⟩
  have h_on := first_K_on_line Z (j + 1) h_bdd j (Nat.lt_succ_iff.mpr le_rfl)
  exact hj_off h_on

/-! ## Part 3: Universal Equivalence -/

/-- **Universal Li-Keiper equivalence**: All zeros on the critical line iff
    Li partial sums are uniformly bounded below.
    Unconditional, universal — no finite-set restriction, no summability
    hypothesis, no assumption on other zeros, no Weil functional. -/
theorem universal_li_keiper (Z : ZetaZeroData) :
    (∀ k, Z.sigma k = 1/2) ↔ LiPartialSumsUniformlyBounded Z := by
  constructor
  · exact universal_forward_bounded Z
  · intro hbdd k
    by_contra hk
    exact universal_backward Z k hk hbdd

/-! ## Part 4: Corollaries -/

/-- **Contrapositive form**: NOT all on-line ⟹ NOT bounded below. -/
theorem not_all_on_line_not_bounded (Z : ZetaZeroData)
    (h : ∃ j, Z.sigma j ≠ 1/2) :
    ¬ LiPartialSumsUniformlyBounded Z := by
  obtain ⟨j, hj⟩ := h
  exact universal_backward Z j hj

/-! ## Part 5: Universal Tsum Version (under summability) -/

/-- **Universal tsum forward**: Under summability, if all zeros are on-line,
    the infinite tsum is nonneg — for every n. -/
theorem universal_tsum_nonneg (D : SummableOnLineData) (n : ℕ) :
    0 ≤ ∑' k, ((li_helix_term (1/2) (D.gamma k) n).re +
               (li_helix_term (1/2) (-(D.gamma k)) n).re) :=
  li_tsum_nonneg D n

/-- **Universal tsum bounded**: Under summability, the infinite tsum
    is bounded above by `n² · Σ moebius_diff_sq(γ_k)`. -/
theorem universal_tsum_bounded (D : SummableOnLineData) (n : ℕ) :
    ∑' k, ((li_helix_term (1/2) (D.gamma k) n).re +
           (li_helix_term (1/2) (-(D.gamma k)) n).re) ≤
    ↑n ^ 2 * ∑' k, moebius_diff_sq (D.gamma k) :=
  li_tsum_bounded_above D n

/-! ## Part 6: Partial Sum Monotonicity -/

/-- **Adding an on-line zero increases the partial sum**: Each on-line pair
    contributes ≥ 0. -/
theorem partial_sum_mono_on_line (Z : ZetaZeroData) (K n : ℕ)
    (hK : Z.sigma K = 1/2) :
    li_partial_sum Z K n ≤ li_partial_sum Z (K + 1) n := by
  rw [li_partial_sum_succ]
  linarith [show 0 ≤ (li_helix_term (Z.sigma K) (Z.gamma K) n).re +
    (li_helix_term (1 - Z.sigma K) (-(Z.gamma K)) n).re from by
      rw [hK]; exact on_line_pair_nonneg (Z.gamma K) n]

/-! ## Part 7: Universal Summary -/

/-- **Complete universal characterization**: All three directions in one. -/
theorem universal_characterization (Z : ZetaZeroData) :
    ((∀ k, Z.sigma k = 1/2) → LiPartialSumsUniformlyBounded Z) ∧
    ((∃ j, Z.sigma j ≠ 1/2) → ¬ LiPartialSumsUniformlyBounded Z) ∧
    ((∀ k, Z.sigma k = 1/2) ↔ LiPartialSumsUniformlyBounded Z) :=
  ⟨universal_forward_bounded Z,
   not_all_on_line_not_bounded Z,
   universal_li_keiper Z⟩

end

#print axioms universal_li_keiper
#print axioms universal_characterization
