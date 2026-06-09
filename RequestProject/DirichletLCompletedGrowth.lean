import RequestProject.DirichletLHadamard

/-!
# Dirichlet completed-`L` order-1 growth — assembly scaffold (step 1 of the port)

Target (the `xi_order_one_log_bound` analogue, the gate to the summability):

  `∃ C R₀ > 0, ∀ R ≥ R₀, ∀ s, ‖s‖ ≤ R → log(‖Λ(s,χ)‖ + 1) ≤ C·R·log R`.

The ξ proof assembles this from a **compact bound** plus three half-plane sub-bounds (right `Re s > 1`,
strip `0 < Re s ≤ 1`, left `Re s ≤ 0` via FE). This file banks the **compact bound** — clean from
continuity + compactness — and the mechanical **assembly** of the four pieces. The three half-plane
growth sub-bounds (`Λ` Stirling × `L`-bound, reflected by the FE) are the remaining analytic work;
each mirrors a proven ξ lemma and has its inputs in hand (`gamma_stirling_bound`,
`DirichletLGrowth.LFunction_norm_le_of_pos_re`, `completedLFunction_one_sub`).
-/

open Complex

namespace DirichletLHadamard

variable {N : ℕ} [NeZero N]

/-- **Compact bound (the `riemannXi_bounded_on_closedBall` analogue).** `completedLFunction χ` is
    entire, hence continuous, hence bounded on every closed ball. Kernel-clean, self-contained. -/
theorem completedLFunction_bounded_on_closedBall {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (R : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ s ∈ Metric.closedBall (0 : ℂ) R, ‖DirichletCharacter.completedLFunction χ s‖ ≤ M := by
  have hcont : Continuous (DirichletCharacter.completedLFunction χ) :=
    (completedLFunction_differentiable hχ).continuous
  obtain ⟨M, hM⟩ :=
    (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn hcont.continuousOn
  exact ⟨max M 0, le_max_right _ _, fun s hs => le_trans (hM s hs) (le_max_left _ _)⟩

/-- **Order-1 growth from the four pieces (the assembly).** Given the compact bound (proved above,
    here packaged) and the three half-plane log-growth sub-bounds, the completed `L` satisfies the
    order-1 log bound. This is the *mechanical* combination from `xi_order_one_log_bound`; the three
    `hRight`/`hStrip`/`hLeft` hypotheses are the genuine analytic sub-bounds remaining to discharge
    (each with a proven ξ analogue and inputs `gamma_stirling_bound` + `LFunction_norm_le_of_pos_re` +
    FE). -/
theorem completedL_order_one_log_bound_of_subbounds {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1)
    (hStrip : ∃ C > (0:ℝ), ∃ R₀ > (0:ℝ), ∀ s : ℂ, R₀ ≤ ‖s‖ → 0 < s.re → s.re ≤ 1 →
      Real.log (‖DirichletCharacter.completedLFunction χ s‖ + 1) ≤ C * ‖s‖ * Real.log ‖s‖)
    (hRight : ∃ C > (0:ℝ), ∃ R₀ > (0:ℝ), ∀ s : ℂ, R₀ ≤ ‖s‖ → 1 < s.re →
      Real.log (‖DirichletCharacter.completedLFunction χ s‖ + 1) ≤ C * ‖s‖ * Real.log ‖s‖)
    (hLeft : ∃ C > (0:ℝ), ∃ R₀ > (0:ℝ), ∀ s : ℂ, R₀ ≤ ‖s‖ → s.re ≤ 0 →
      Real.log (‖DirichletCharacter.completedLFunction χ s‖ + 1) ≤ C * ‖s‖ * Real.log ‖s‖) :
    ∃ C > (0:ℝ), ∃ R₀ > (0:ℝ), ∀ R, R₀ ≤ R → ∀ s : ℂ, ‖s‖ ≤ R →
      Real.log (‖DirichletCharacter.completedLFunction χ s‖ + 1) ≤ C * R * Real.log R := by
  obtain ⟨C1, hC1, R1, hR1, hB1⟩ := hStrip
  obtain ⟨C2, hC2, R2, hR2, hB2⟩ := hRight
  obtain ⟨C3, hC3, R3, hR3, hB3⟩ := hLeft
  set R_max := max (max R1 R2) (max R3 (Real.exp 1)) with hR_max_def
  have hR_max_pos : 0 < R_max := lt_max_of_lt_right (lt_max_of_lt_right (Real.exp_pos 1))
  obtain ⟨M, hM_nn, hM⟩ := completedLFunction_bounded_on_closedBall hχ R_max
  have hlogM_nn : 0 ≤ Real.log (M + 1) := Real.log_nonneg (by linarith)
  set C := max (max (max C1 C2) C3) (Real.log (M + 1) + 1) with hC_def
  have hC_ge_C1 : C1 ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
  have hC_ge_C2 : C2 ≤ C := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
  have hC_ge_C3 : C3 ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
  have hC_ge_logM : Real.log (M + 1) + 1 ≤ C := le_max_right _ _
  have hC_pos : 0 < C := lt_of_lt_of_le hC1 hC_ge_C1
  refine ⟨C, hC_pos, R_max, hR_max_pos, ?_⟩
  intro R hR s hs
  have hR_exp : Real.exp 1 ≤ R := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hR
  have hR_one : (1 : ℝ) ≤ R :=
    le_trans (by have := Real.exp_one_gt_d9; linarith : (1:ℝ) ≤ Real.exp 1) hR_exp
  have hR_pos : (0:ℝ) < R := lt_of_lt_of_le one_pos hR_one
  have hR_log_ge_1 : (1:ℝ) ≤ Real.log R := by
    have := Real.log_le_log (Real.exp_pos 1) hR_exp; rwa [Real.log_exp] at this
  have hR_log_nn : 0 ≤ Real.log R := le_trans zero_le_one hR_log_ge_1
  have hC_bound_M : Real.log (M + 1) ≤ C * R * Real.log R := by
    calc Real.log (M + 1) ≤ Real.log (M + 1) + 1 := by linarith
      _ ≤ C := hC_ge_logM
      _ = C * 1 * 1 := by ring
      _ ≤ C * R * Real.log R := by
          apply mul_le_mul _ hR_log_ge_1 zero_le_one (by positivity)
          exact mul_le_mul_of_nonneg_left hR_one hC_pos.le
  by_cases h_small : ‖s‖ ≤ R_max
  · have hs_in : s ∈ Metric.closedBall (0 : ℂ) R_max := by
      rw [Metric.mem_closedBall, dist_zero_right]; exact h_small
    exact le_trans (Real.log_le_log (by positivity) (by linarith [hM s hs_in])) hC_bound_M
  · push_neg at h_small
    have hs_nn : 0 < ‖s‖ := lt_trans hR_max_pos h_small
    have hs_one : (1:ℝ) ≤ ‖s‖ :=
      le_trans (by have := Real.exp_one_gt_d9; linarith : (1:ℝ) ≤ Real.exp 1)
        (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) h_small.le)
    have hs_log_nn : 0 ≤ Real.log ‖s‖ := Real.log_nonneg hs_one
    have hmono : ‖s‖ * Real.log ‖s‖ ≤ R * Real.log R :=
      calc ‖s‖ * Real.log ‖s‖
          ≤ ‖s‖ * Real.log R := mul_le_mul_of_nonneg_left (Real.log_le_log hs_nn hs) hs_nn.le
        _ ≤ R * Real.log R := mul_le_mul_of_nonneg_right hs hR_log_nn
    have hs_R1 : R1 ≤ ‖s‖ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) h_small.le
    have hs_R2 : R2 ≤ ‖s‖ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) h_small.le
    have hs_R3 : R3 ≤ ‖s‖ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) h_small.le
    have hfinish : ∀ Ci, Ci ≤ C →
        Real.log (‖DirichletCharacter.completedLFunction χ s‖ + 1) ≤ Ci * ‖s‖ * Real.log ‖s‖ →
        Real.log (‖DirichletCharacter.completedLFunction χ s‖ + 1) ≤ C * R * Real.log R := by
      intro Ci hCi hb
      calc Real.log (‖DirichletCharacter.completedLFunction χ s‖ + 1)
          ≤ Ci * ‖s‖ * Real.log ‖s‖ := hb
        _ ≤ C * ‖s‖ * Real.log ‖s‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCi hs_nn.le) hs_log_nn
        _ ≤ C * (R * Real.log R) := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hmono hC_pos.le
        _ = C * R * Real.log R := by ring
    rcases le_or_gt s.re 0 with hre_neg | hre_pos
    · exact hfinish C3 hC_ge_C3 (hB3 s hs_R3 hre_neg)
    · rcases le_or_gt s.re 1 with hre_le1 | hre_gt1
      · exact hfinish C1 hC_ge_C1 (hB1 s hs_R1 hre_pos hre_le1)
      · exact hfinish C2 hC_ge_C2 (hB2 s hs_R2 hre_gt1)

end DirichletLHadamard

#print axioms DirichletLHadamard.completedLFunction_bounded_on_closedBall
#print axioms DirichletLHadamard.completedL_order_one_log_bound_of_subbounds
