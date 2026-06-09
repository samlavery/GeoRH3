import Mathlib
import RequestProject.ForcedAlignment
import RequestProject.BridgeToZeroFree

/-!
# No Offline Zeros: Narrowing the Gap

## What Prevents a Proof of No Offline Zeros?

The existing framework proves (for a SINGLE zero ρ = σ+iγ):
- `critical_line_iff_bounded_li`: σ = 1/2 ⟺ paired Li bounded below
- `paired_li_unbounded_off_line`: σ ≠ 1/2 ⟹ paired Li → -∞

This is a theorem about one complex number, not about ζ zeros. To prove
"no offline zeros of ζ", we need to go from individual to collective.

## The Three Obstacles (in order of difficulty)

### Obstacle 1: From One Pair to Finitely Many Pairs
**Status: RESOLVED in this file.**

For a finite collection of zero-pairs where we know some are on-line,
if ANY pair is off-line and the rest are on-line, the total
Li sum is unbounded below. More generally, if the total Li partial sums
are uniformly bounded below and all but one pair are on the line, that
last pair must also be on the line.

### Obstacle 2: From Finitely Many to Infinitely Many
**Status: FORMALIZED AS ASSUMPTION.**

ζ has infinitely many zeros. The Li coefficient is:
  λ_n = Σ_ρ Re[1 - (1-1/ρ)^n]
The sum converges for each n (known fact), but formalizing this requires
analytic number theory infrastructure not in Mathlib.

### Obstacle 3: Proving λ_n ≥ 0 from the Number Theory Side
**Status: OPEN.**

Proving λ_n ≥ 0 requires the Weil explicit formula + positivity of
the full quadratic form.

## What This File Proves

1. On-line pair bounds: each on-line pair contributes in [0, 4]
2. One-offline theorem: one offline pair + on-line rest → total unbounded
3. Uniform bound forces on-line: bounded partial sums + others on-line → all on-line
4. Upper bound on any pair's Li contribution (for future use)
5. Bridge assumptions stated precisely
6. Summary of the irreducible gap
-/

noncomputable section

open Complex Real

/-! ## Part 1: On-Line Pair Bounds -/

/-- Auxiliary: moebius_helix (1/2) γ has norm ≤ 1. -/
theorem moebius_half_norm_le_one (gamma : ℝ) :
    ‖moebius_helix (1/2) gamma‖ ≤ 1 := by
  by_cases hg : gamma = 0
  · simp [moebius_helix, hg, Complex.norm_def, Complex.normSq]; norm_num
  · exact le_of_eq ((moebius_unit_iff (1/2) gamma hg).mpr rfl)

/-- Each on-line pair's Li contribution is bounded above by 4. -/
theorem on_line_pair_bounded (gamma : ℝ) (n : ℕ) :
    (li_helix_term (1/2) gamma n).re +
    (li_helix_term (1 - 1/2) (-gamma) n).re ≤ 4 := by
  have h1 : (li_helix_term (1/2) gamma n).re ≤ 2 :=
    li_re_le_two _ (moebius_half_norm_le_one gamma) n
  have h2 : (li_helix_term (1 - 1/2) (-gamma) n).re ≤ 2 := by
    have : (1 : ℝ) - 1/2 = 1/2 := by norm_num
    rw [this]
    exact li_re_le_two _ (moebius_half_norm_le_one (-gamma)) n
  linarith

/-- Each on-line pair's Li contribution is bounded below by 0. -/
theorem on_line_pair_nonneg (gamma : ℝ) (n : ℕ) :
    0 ≤ (li_helix_term (1/2) gamma n).re +
        (li_helix_term (1 - 1/2) (-gamma) n).re := by
  have h1 := li_helix_nonneg_on_line gamma n
  have h2 : 0 ≤ (li_helix_term (1 - 1/2) (-gamma) n).re := by
    have : (1 : ℝ) - 1/2 = 1/2 := by norm_num
    rw [this]
    exact li_helix_nonneg_on_line (-gamma) n
  linarith

/-! ## Part 2: Finite Collection Results -/

/-- Total paired Li sum over K zero-pairs at index n. -/
def total_paired_li (K : ℕ) (sigmas gammas : Fin K → ℝ) (n : ℕ) : ℝ :=
  ∑ k : Fin K,
    ((li_helix_term (sigmas k) (gammas k) n).re +
     (li_helix_term (1 - sigmas k) (-(gammas k)) n).re)

/-- If all pairs have σ = 1/2, the total Li is in [0, 4K]. -/
theorem total_li_bounded_all_on_line (K : ℕ) (gammas : Fin K → ℝ) (n : ℕ) :
    0 ≤ total_paired_li K (fun _ => 1/2) gammas n ∧
    total_paired_li K (fun _ => 1/2) gammas n ≤ 4 * K := by
  constructor
  · exact Finset.sum_nonneg fun k _ => on_line_pair_nonneg (gammas k) n
  · calc total_paired_li K (fun _ => 1/2) gammas n
        = ∑ k : Fin K, ((li_helix_term (1/2) (gammas k) n).re +
            (li_helix_term (1 - 1/2) (-(gammas k)) n).re) := rfl
      _ ≤ ∑ _k : Fin K, (4 : ℝ) :=
            Finset.sum_le_sum fun k _ => on_line_pair_bounded (gammas k) n
      _ = 4 * K := by simp [Finset.sum_const, nsmul_eq_mul]; ring

/-! ## Part 3: One Off-Line Pair Makes Sums Negative -/

/-- **The one-offline theorem**: For K+1 zero-pairs where the
    first K are on the critical line and pair K is off-line,
    the total Li sum is unbounded below. -/
theorem one_offline_makes_sum_negative
    (K : ℕ) (gammas_on : Fin K → ℝ)
    (sigma_off gamma_off : ℝ)
    (hs_off : sigma_off ≠ 1/2)
    (hg_off : gamma_off ≠ 0) :
    ∀ M : ℝ, ∃ n : ℕ,
      (∑ k : Fin K,
        ((li_helix_term (1/2) (gammas_on k) n).re +
         (li_helix_term (1 - 1/2) (-(gammas_on k)) n).re)) +
      ((li_helix_term sigma_off gamma_off n).re +
       (li_helix_term (1 - sigma_off) (-gamma_off) n).re) < M := by
  intro M
  obtain ⟨n, hn⟩ := paired_li_unbounded_off_line sigma_off gamma_off
    hs_off hg_off (M - 4 * K)
  refine ⟨n, ?_⟩
  have h_ub : ∑ k : Fin K,
      ((li_helix_term (1/2) (gammas_on k) n).re +
       (li_helix_term (1 - 1/2) (-(gammas_on k)) n).re) ≤ 4 * ↑K := by
    calc _ ≤ ∑ _k : Fin K, (4 : ℝ) :=
          Finset.sum_le_sum fun k _ => on_line_pair_bounded (gammas_on k) n
      _ = 4 * K := by simp [Finset.sum_const, nsmul_eq_mul]; ring
  linarith

/-! ## Part 4: ζ Zero Data and Bridge Assumptions -/

/-- The "ζ zero data" — an abstract model of ζ's nontrivial zeros as a
    countable sequence of (σ, γ) pairs. This is a modeling convenience for
    the finite-collection arguments; the zeros themselves are from Mathlib's
    `riemannZeta` (see `VMEFStandalone.NontrivialZeros`). A concrete instance
    can be obtained from `SummableOnLineData.toZetaZeroData` in
    `HelixConvergence.lean`. -/
structure ZetaZeroData where
  /-- The zeros come as a countable sequence of pairs. -/
  sigma : ℕ → ℝ
  gamma : ℕ → ℝ
  /-- All imaginary parts are nonzero (nontrivial zeros). -/
  gamma_ne_zero : ∀ k, gamma k ≠ 0
  /-- All zeros are in the critical strip: 0 < σ < 1. -/
  in_strip : ∀ k, 0 < sigma k ∧ sigma k < 1

/-- The Li sum at index n, truncated to K pairs. -/
def li_partial_sum (Z : ZetaZeroData) (K n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range K,
    ((li_helix_term (Z.sigma k) (Z.gamma k) n).re +
     (li_helix_term (1 - Z.sigma k) (-(Z.gamma k)) n).re)

/-- **Obstacle 2 formalized**: The Li sum converges for each n. -/
def LiSumConverges (Z : ZetaZeroData) : Prop :=
  ∀ n : ℕ, ∃ L : ℝ,
    Filter.Tendsto (fun K => li_partial_sum Z K n) Filter.atTop (nhds L)

/-- A cleaner assumption: partial sums are uniformly bounded below. -/
def LiPartialSumsUniformlyBounded (Z : ZetaZeroData) : Prop :=
  ∃ C : ℝ, ∀ n K : ℕ, C ≤ li_partial_sum Z K n

/-! ## Part 5: The One-Offline-Pair Forcing Theorem -/

/-- **Key theorem**: If there is exactly one off-line pair and all
    others are on the critical line, then the Li partial sums are
    NOT uniformly bounded below. -/
theorem one_offline_breaks_uniform_bound
    (Z : ZetaZeroData)
    (j : ℕ)
    (hj_off : Z.sigma j ≠ 1/2)
    (h_others : ∀ k, k ≠ j → Z.sigma k = 1/2) :
    ¬ LiPartialSumsUniformlyBounded Z := by
  intro ⟨C, hC⟩
  obtain ⟨n, hn⟩ := paired_li_unbounded_off_line (Z.sigma j) (Z.gamma j)
    hj_off (Z.gamma_ne_zero j) (C - 4 * ↑j - 1)
  have h_bound := hC n (j + 1)
  have h_split : li_partial_sum Z (j + 1) n =
    (∑ k ∈ Finset.range j,
      ((li_helix_term (Z.sigma k) (Z.gamma k) n).re +
       (li_helix_term (1 - Z.sigma k) (-(Z.gamma k)) n).re)) +
    ((li_helix_term (Z.sigma j) (Z.gamma j) n).re +
     (li_helix_term (1 - Z.sigma j) (-(Z.gamma j)) n).re) := by
    simp [li_partial_sum, Finset.sum_range_succ]
  rw [h_split] at h_bound
  have h_online : ∑ k ∈ Finset.range j,
      ((li_helix_term (Z.sigma k) (Z.gamma k) n).re +
       (li_helix_term (1 - Z.sigma k) (-(Z.gamma k)) n).re) ≤ 4 * ↑j := by
    calc _ ≤ ∑ _k ∈ Finset.range j, (4 : ℝ) := by
          apply Finset.sum_le_sum
          intro k hk
          rw [h_others k (ne_of_lt (Finset.mem_range.mp hk))]
          exact on_line_pair_bounded (Z.gamma k) n
      _ = 4 * ↑j := by simp [Finset.sum_const, nsmul_eq_mul]; ring
  linarith

/-- **Contrapositive**: If the Li partial sums ARE uniformly bounded below,
    and all zeros except possibly one are on the line, then that
    one must be on the line too. -/
theorem uniform_bound_forces_on_line
    (Z : ZetaZeroData)
    (j : ℕ)
    (h_others : ∀ k, k ≠ j → Z.sigma k = 1/2)
    (h_bdd : LiPartialSumsUniformlyBounded Z) :
    Z.sigma j = 1/2 := by
  by_contra hj
  exact one_offline_breaks_uniform_bound Z j hj h_others h_bdd

/-! ## Part 6: Upper Bound on Any Pair's Li Contribution -/

/-- Any pair's Li contribution is bounded above by 1 + ‖w‖^n.
    This uses -Re(z) ≤ |Re(z)| ≤ ‖z‖. -/
theorem paired_li_bounded_above_by_norm (sigma gamma : ℝ) (n : ℕ) :
    (li_helix_term sigma gamma n).re ≤
    1 + ‖moebius_helix sigma gamma‖ ^ n := by
  unfold li_helix_term
  simp only [Complex.sub_re, Complex.one_re]
  have h := Complex.abs_re_le_norm (moebius_helix sigma gamma ^ n)
  rw [norm_pow] at h
  linarith [abs_le.mp h]

/-! ## Part 7: The Precise Gap Summary -/

/-- **The irreducible hard core.**

    PROVED (unconditional, gap-free):
    1. Individual pair: σ = 1/2 ⟺ paired Li bounded below
    2. On-line pair bounds: contribution ∈ [0, 4]
    3. One offline pair + on-line rest → total unbounded below
    4. Uniform bound on partial sums → forces on-line (when others on-line)
    5. Mertens trick: 3+4cosθ+cos2θ ≥ 0
    6. Von Mangoldt: Λ(n) ≥ 0

    THE GAP (three equivalent formulations):
    A. Prove: Σ_ρ Re[1-(1-1/ρ)^n] ≥ 0 for all n (Li-Keiper positivity)
    B. Prove: Weil quadratic form PSD for all test functions
    C. Prove: zero-free region reaches Re(s) ≥ 1/2

    The gap is NOT in the deductive framework (which correctly reduces
    RH to Li positivity). The gap IS the positivity itself — the passage
    from "Λ(n) ≥ 0" (prime side, proved) to "λ_n ≥ 0" (zero side, RH).

    The explicit formula connects these two sides, but formalizing it
    requires: analytic continuation of ζ, contour integration, and the
    Weil-Guinand trace formula — none of which are in Mathlib. -/
theorem gap_summary :
    (∀ sigma gamma : ℝ, gamma ≠ 0 →
      (sigma = 1/2 ↔ ∃ M : ℝ, ∀ n : ℕ,
        M ≤ (li_helix_term sigma gamma n).re +
            (li_helix_term (1 - sigma) (-gamma) n).re)) ∧
    (∀ theta : ℝ, 0 ≤ 3 + 4 * Real.cos theta + Real.cos (2 * theta)) ∧
    (∀ n : ℕ, (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt n) := by
  exact ⟨fun s g hg => critical_line_iff_bounded_li s g hg,
         fun θ => mertens_nonneg θ,
         fun n => ArithmeticFunction.vonMangoldt_nonneg⟩

end
