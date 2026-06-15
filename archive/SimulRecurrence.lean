import Mathlib
import RequestProject.HelixConvergence
import RequestProject.HelixRoundTrip

/-!
# Simultaneous Recurrence on the Unit Circle (Multi-dimensional Dirichlet Approximation)

For a finite family of unit-circle elements u₁,...,uₖ, we prove that their powers
simultaneously return arbitrarily close to 1, cofinally in ℕ.

The proof uses compactness of the product torus Tᵏ (= product of closed unit balls)
via `IsCompact.tendsto_subseq`, generalizing the 1-dimensional `circle_recurrence`.
-/

noncomputable section

open Complex Filter Metric

/-
Simultaneous recurrence on the unit circle for a finite family.
    Generalizes `circle_recurrence` to any `Fintype`-indexed family.
    Proof: the sequence n ↦ (uᵢⁿ)ᵢ lives in the compact product torus.
    By sequential compactness, two nearby subsequence terms give the period.
-/
theorem simul_circle_recurrence {ι : Type*} [Fintype ι] (u : ι → ℂ) (hu : ∀ i, ‖u i‖ = 1)
    {ε : ℝ} (hε : 0 < ε) : ∃ m : ℕ, 1 ≤ m ∧ ∀ i, ‖(u i) ^ m - 1‖ < ε := by
  by_contra h;
  -- By compactness of the product torus T^k, the sequence (u �_�1^n, ..., u_k^n) � has� a convergent subsequence.
  obtain ⟨a, ha⟩ : ∃ a : ι → ℂ, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Filter.Tendsto (fun n => (fun i => (u i) ^ (φ n))) Filter.atTop (nhds a) := by
    -- The sequence (u_i^n) is contained in the compact set S = { �f� : → | ∀ � i�, f i ∈ closedBall 0 1}.
    have h_seq_in_S : ∀ n, (fun i => (u i) ^ n) ∈ {f : ι → ℂ | ∀ i, f i ∈ Metric.closedBall 0 1} := by
      aesop;
    have h_compact : IsCompact {f : ι → ℂ | ∀ i, f i ∈ Metric.closedBall 0 1} := by
      exact isCompact_pi_infinite fun i => ProperSpace.isCompact_closedBall _ _;
    have := h_compact.isSeqCompact fun n => h_seq_in_S n; aesop;
  -- By the triangle inequality, for any $i$, we have $\ �|�u_i^{φ(K+1)} - u_i^{φ(K)}\| < ε$.
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ k ≥ K, ∀ i, ‖(u i) ^ (ha.choose k) - a i‖ < ε / 2 := by
    obtain ⟨ N, hN ⟩ := Metric.tendsto_atTop.mp ha.choose_spec.2 ( ε / 2 ) ( half_pos hε )
    refine ⟨ N, fun n hn i => ?_ ⟩
    have hd := hN n hn
    rw [ dist_eq_norm ] at hd
    exact lt_of_le_of_lt ( norm_le_pi_norm ( (fun i => u i ^ ha.choose n) - a ) i ) hd
  -- Set $m = ha.choose (K + 1) - ha.choose K$.
  set m := ha.choose (K + 1) - ha.choose K with hm_def;
  -- By the triangle inequality, for any $i$, � we� have $\|u_i^{ha.choose (K + 1)} - u_i^{ha.choose K}\| < ε$.
  have h_triangle : ∀ i, ‖(u i) ^ (ha.choose (K + 1)) - (u i) ^ (ha.choose K)‖ < ε := by
    intro i
    have h_triangle : ‖(u i) ^ (ha.choose (K + 1)) - a i‖ < ε / 2 ∧ ‖(u i) ^ (ha.choose K) - a i‖ < ε / 2 := by
      grind;
    simpa using lt_of_le_of_lt ( norm_sub_le _ _ ) ( add_lt_add h_triangle.1 h_triangle.2 );
  -- Factor: $u_i^{ha.choose (K + 1)} - u_i^{ha.choose K} = u_i^{ha.choose K} � (�u_i^m - 1)$.
  have h_factor : ∀ i, (u i) ^ (ha.choose (K + 1)) - (u i) ^ (ha.choose K) = (u i) ^ (ha.choose K) * ((u i) ^ m - 1) := by
    intro i; rw [ mul_sub, mul_one, ← pow_add, Nat.add_sub_of_le ( ha.choose_spec.1.monotone ( Nat.le_succ _ ) ) ] ;
  refine' h ⟨ m, _, _ ⟩;
  · exact Nat.sub_pos_of_lt ( ha.choose_spec.1 ( Nat.lt_succ_self K ) );
  · intro i; specialize h_triangle i; rw [ h_factor i ] at h_triangle; simp_all +decide ;

/-
Cofinal version of simultaneous recurrence.
    Uses `simul_circle_recurrence` + `pow_sub_one_le'` amplification.
-/
theorem multi_recur_cofinal {ι : Type*} [Fintype ι] (u : ι → ℂ) (hu : ∀ i, ‖u i‖ = 1)
    {ε : ℝ} (hε : 0 < ε) (N : ℕ) : ∃ n, N ≤ n ∧ ∀ i, ‖(u i) ^ n - 1‖ < ε := by
  -- By `simul_circle_recurrence` with ε �'� = ε/(N+1), get m ≥ 1 with ∀ i,(u i)^m - 1‖ < ε/(N+1).
  obtain ⟨m, hm1, hm⟩ : ∃ m : ℕ, 1 ≤ m ∧ ∀ i, ‖(u i) ^ m - 1‖ < ε / (N + 1) := by
    exact simul_circle_recurrence u hu ( by positivity );
  -- Set n = m * (N + 1). Then n � ≥� N (since m ≥ 1).
  use m * (N + 1);
  -- By the public unit-circle power bound: ‖((u i)^m)^(N+1) - 1‖ ≤ (N+1) * ‖(u i)^m - 1‖.
  have h_pow_sub_one_le : ∀ i, ‖(u i) ^ (m * (N + 1)) - 1‖ ≤ (N + 1) * ‖(u i) ^ m - 1‖ := by
    intro i
    have := norm_pow_sub_one_le_unit (u i ^ m) (by
    simp +decide [ hu ]) (N + 1)
    simp_all +decide [ pow_mul ];
  exact ⟨ by nlinarith, fun i => lt_of_le_of_lt ( h_pow_sub_one_le i ) ( by nlinarith [ hm i, mul_div_cancel₀ ε ( by positivity : ( N : ℝ ) + 1 ≠ 0 ) ] ) ⟩

end
