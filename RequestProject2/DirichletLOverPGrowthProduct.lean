import RequestProject.DirichletLOverPGrowthDyadic
import RequestProject.DirichletLProductMult

/-!
# Step B: pointwise mean-type-2 upper bound on the canonical product `LProductMult χ`

Character-`χ` port of `ZD.xiProductMult_pointwise_meanType_bound`. Splits `log‖Prod(z)‖ = Σ_ρ n_ρ
log‖1 + term‖` into near zeros (`‖ρ‖ ≤ ‖z‖`, crude `log ≤ 2‖z‖/‖ρ‖`, summed by the partial-sum bound)
and far zeros (`‖ρ‖ > ‖z‖`, quadratic `log ≤ 3‖z‖²/‖ρ‖²`, summed by the tail bound), giving
`log(‖Prod z‖+1) ≤ C‖z‖log²(‖z‖+2)+D`.
-/

open Complex Set Filter Topology

noncomputable section

namespace DirichletLHadamard

variable {N : ℕ} [NeZero N]

/-- Pointwise mean-type-2 upper bound on `log ‖LProductMult χ (z)‖`. -/
theorem LProductMult_pointwise_meanType_bound {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hχp : χ.IsPrimitive) :
    ∃ C D : ℝ, ∀ z : ℂ,
      Real.log (‖LProductMult χ z‖ + 1) ≤
        C * ‖z‖ * (Real.log (‖z‖ + 2)) ^ 2 + D := by
  obtain ⟨C_tail, hC_tail⟩ := lOrderNat_div_norm_sq_tail_bound hχ hχp
  obtain ⟨C_part, hC_part⟩ := lOrderNat_div_norm_partial_sum_bound hχ hχp
  rcases (isCompact_closedBall (0 : ℂ) 2).bddAbove_image
    (LProductMult_differentiable hχ hχp).continuous.norm.continuousOn with ⟨M₀, hM₀⟩
  set M : ℝ := max M₀ 1
  have hM_ge_1 : 1 ≤ M := le_max_right _ _
  have hM_bd : ∀ s ∈ Metric.closedBall (0:ℂ) 2, ‖LProductMult χ s‖ ≤ M :=
    fun s hs => le_trans (hM₀ ⟨s, hs, rfl⟩) (le_max_left _ _)
  refine ⟨3 * |C_tail| + 2 * |C_part|, Real.log (M + 1) + Real.log 2, fun z => ?_⟩
  have h_C_tail_abs_nn : 0 ≤ |C_tail| := abs_nonneg _
  have h_C_part_abs_nn : 0 ≤ |C_part| := abs_nonneg _
  have hz_nn : 0 ≤ ‖z‖ := norm_nonneg _
  have hlog_z2_nn : 0 ≤ Real.log (‖z‖ + 2) := Real.log_nonneg (by linarith)
  have hlog_z2_sq_nn : 0 ≤ (Real.log (‖z‖ + 2)) ^ 2 := sq_nonneg _
  have hC_combined_nn : 0 ≤ 3 * |C_tail| + 2 * |C_part| := by positivity
  have hM1_pos : 0 < M + 1 := by linarith
  have hlog_M1_nn : 0 ≤ Real.log (M + 1) := Real.log_nonneg (by linarith)
  have hlog2_nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  by_cases hz_small : ‖z‖ ≤ 2
  · have hz_in : z ∈ Metric.closedBall (0:ℂ) 2 := by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hz_small
    have h_P_bd := hM_bd z hz_in
    have hlog_le : Real.log (‖LProductMult χ z‖ + 1) ≤ Real.log (M + 1) := by
      apply Real.log_le_log (by linarith [norm_nonneg (LProductMult χ z)]); linarith
    have h_rhs_nn : 0 ≤ (3 * |C_tail| + 2 * |C_part|) * ‖z‖ * (Real.log (‖z‖ + 2)) ^ 2 := by
      positivity
    linarith
  · have hz_ge_2 : 2 < ‖z‖ := not_le.mp hz_small
    have hz_pos : 0 < ‖z‖ := by linarith
    have hz_ge_2' : (2:ℝ) ≤ ‖z‖ := hz_ge_2.le
    have hlog_z_pos : 0 < Real.log ‖z‖ := Real.log_pos (by linarith)
    have hlog_z_nn : 0 ≤ Real.log ‖z‖ := hlog_z_pos.le
    have hlog_z_le_z2 : Real.log ‖z‖ ≤ Real.log (‖z‖ + 2) :=
      Real.log_le_log hz_pos (by linarith)
    have hlog_z_sq_le_z2_sq : (Real.log ‖z‖)^2 ≤ (Real.log (‖z‖ + 2))^2 := by
      apply sq_le_sq' (by linarith) hlog_z_le_z2
    have hlog_z2_ge_log4 : Real.log 4 ≤ Real.log (‖z‖ + 2) :=
      Real.log_le_log (by norm_num) (by linarith)
    have hlog4_ge_1 : (1:ℝ) ≤ Real.log 4 := by
      have h1 : Real.exp 1 < 4 := by
        have : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
        linarith
      have h2 : Real.log (Real.exp 1) ≤ Real.log 4 := Real.log_le_log (Real.exp_pos _) h1.le
      rw [Real.log_exp] at h2; exact h2
    have hlog_z2_ge_1 : (1:ℝ) ≤ Real.log (‖z‖ + 2) := by linarith
    have hlog_z2_le_sq : Real.log (‖z‖ + 2) ≤ (Real.log (‖z‖ + 2))^2 := by
      have h1 : Real.log (‖z‖+2) * 1 ≤ Real.log (‖z‖+2) * Real.log (‖z‖+2) :=
        mul_le_mul_of_nonneg_left hlog_z2_ge_1 hlog_z2_nn
      have h2 : Real.log (‖z‖+2) * Real.log (‖z‖+2) = (Real.log (‖z‖+2))^2 := by ring
      linarith
    have hlog_z_le_z2_sq : Real.log ‖z‖ ≤ (Real.log (‖z‖ + 2))^2 :=
      le_trans hlog_z_le_z2 hlog_z2_le_sq
    by_cases hz_ntz : z ∈ GRHSpectral.NontrivialZeros χ
    · have h_zero : LProductMult χ z = 0 := LProductMult_zero_of_mem_NontrivialZeros hχ hz_ntz
      rw [h_zero, norm_zero, zero_add, Real.log_one]
      have h_rhs_nn : 0 ≤ (3 * |C_tail| + 2 * |C_part|) * ‖z‖ * (Real.log (‖z‖ + 2)) ^ 2 := by
        positivity
      linarith
    · have h_summ_norm : Summable (fun p : MultiZeroIdx χ => ‖ZD.xiWeierstrassTerm p.1.val z‖) := by
        set Mn : ℝ := ‖z‖ + 1
        have hMn_pos : 0 < Mn := by positivity
        have h_bd := xiWeierstrassTerm_mult_closedBall_bound hχ Mn hMn_pos
        have h_summ := summable_multi_weierstrassTerm_bound hχ hχp Mn hMn_pos
        apply Summable.of_norm_bounded_eventually h_summ
        filter_upwards [h_bd] with p hp
        have h1 := hp z (by rw [Metric.mem_closedBall, dist_zero_right]; linarith)
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]; exact h1
      have h_summ_log := h_summ_norm.summable_log_norm_one_add
      have h_log_eq : Real.log ‖LProductMult χ z‖ =
          ∑' p : MultiZeroIdx χ, Real.log ‖1 + ZD.xiWeierstrassTerm p.1.val z‖ := by
        have h_mult : Multipliable (fun p : MultiZeroIdx χ => 1 + ZD.xiWeierstrassTerm p.1.val z) :=
          LProductMult_multipliable hχ hχp z
        have h_norm : ‖LProductMult χ z‖ =
            ∏' p : MultiZeroIdx χ, ‖1 + ZD.xiWeierstrassTerm p.1.val z‖ := by
          unfold LProductMult; exact h_mult.norm_tprod
        have h_ne : ∀ p : MultiZeroIdx χ, 1 + ZD.xiWeierstrassTerm p.1.val z ≠ 0 := by
          intro p
          have hρ_ne : p.1.val ≠ 0 := by
            intro heq
            have hre : (0 : ℝ) < p.1.val.re := p.1.property.1
            rw [heq] at hre; simp at hre
          have hz_ne : z ≠ p.1.val := fun heq => hz_ntz (heq ▸ p.1.property)
          exact ZD.one_add_xiWeierstrassTerm_ne_zero_of_ne hρ_ne hz_ne
        have h_pos : ∀ p : MultiZeroIdx χ, 0 < ‖1 + ZD.xiWeierstrassTerm p.1.val z‖ :=
          fun p => norm_pos_iff.mpr (h_ne p)
        rw [h_norm]
        have h_exp := Real.rexp_tsum_eq_tprod h_pos h_summ_log
        exact (congrArg Real.log h_exp).symm.trans (Real.log_exp _)
      have h_summ_weighted : Summable (fun ρ : {ρ : ℂ // ρ ∈ GRHSpectral.NontrivialZeros χ} =>
          (lOrderNat χ ρ.val : ℝ) * Real.log ‖1 + ZD.xiWeierstrassTerm ρ.val z‖) := by
        have h := h_summ_log.sigma' (fun _ => Summable.of_finite)
        refine h.congr ?_
        intro ρ
        show (∑' (_c : Fin (lOrderNat χ ρ.val)),
            Real.log ‖1 + ZD.xiWeierstrassTerm ρ.val z‖) = _
        rw [tsum_const, Nat.card_eq_fintype_card, Fintype.card_fin]; ring
      have h_log_eq_ρ :
          (∑' p : MultiZeroIdx χ, Real.log ‖1 + ZD.xiWeierstrassTerm p.1.val z‖) =
          ∑' ρ : {ρ : ℂ // ρ ∈ GRHSpectral.NontrivialZeros χ},
            (lOrderNat χ ρ.val : ℝ) * Real.log ‖1 + ZD.xiWeierstrassTerm ρ.val z‖ := by
        rw [h_summ_log.tsum_sigma' (fun _ => Summable.of_finite)]
        apply tsum_congr
        intro ρ
        show (∑' (_c : Fin (lOrderNat χ ρ.val)),
            Real.log ‖1 + ZD.xiWeierstrassTerm ρ.val z‖) = _
        rw [tsum_const, Nat.card_eq_fintype_card, Fintype.card_fin]; ring
      have h_split := h_summ_weighted.tsum_subtype_add_tsum_subtype_compl
        ({ρ : {ρ : ℂ // ρ ∈ GRHSpectral.NontrivialZeros χ} | ‖ρ.val‖ ≤ ‖z‖} : Set _)
      have h_near_bd :
          (∑' ρ : ({ρ : {ρ : ℂ // ρ ∈ GRHSpectral.NontrivialZeros χ} | ‖ρ.val‖ ≤ ‖z‖} : Set _),
            (lOrderNat χ ρ.val.val : ℝ) *
              Real.log ‖1 + ZD.xiWeierstrassTerm ρ.val.val z‖) ≤
          2 * |C_part| * ‖z‖ * (Real.log ‖z‖)^2 := by
        have h_rhs_nn : 0 ≤ 2 * |C_part| * ‖z‖ * (Real.log ‖z‖)^2 := by positivity
        apply tsum_le_of_sum_le' h_rhs_nn
        intro T
        let T' : Finset {ρ : ℂ // ρ ∈ GRHSpectral.NontrivialZeros χ} := T.image (·.val)
        have hT'_bd : ∀ ρ ∈ T', ‖ρ.val‖ ≤ ‖z‖ := by
          intro ρ hρ
          rw [Finset.mem_image] at hρ
          obtain ⟨x, _, heq⟩ := hρ
          rw [← heq]; exact x.property
        have h_crude : ∀ ρ : {ρ : ℂ // ρ ∈ GRHSpectral.NontrivialZeros χ},
            Real.log ‖1 + ZD.xiWeierstrassTerm ρ.val z‖ ≤ 2 * (‖z‖ / ‖ρ.val‖) := by
          intro ρ
          have hρ_ne : ρ.val ≠ 0 := by
            intro heq
            have hre : (0 : ℝ) < ρ.val.re := ρ.property.1
            rw [heq] at hre; simp at hre
          rw [ZD.one_add_xiWeierstrassTerm]; unfold ZD.xiWeierstrassFactor
          rw [norm_mul, Complex.norm_exp]
          by_cases h_zero : ‖1 - z/ρ.val‖ = 0
          · rw [h_zero, zero_mul, Real.log_zero]; positivity
          · have h1 : 0 < ‖1 - z/ρ.val‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h_zero)
            have h2 : 0 < Real.exp ((z/ρ.val).re) := Real.exp_pos _
            rw [Real.log_mul (ne_of_gt h1) (ne_of_gt h2), Real.log_exp]
            have h_norm_bd : ‖1 - z/ρ.val‖ ≤ 1 + ‖z‖/‖ρ.val‖ := by
              calc ‖1 - z/ρ.val‖ ≤ ‖(1:ℂ)‖ + ‖z/ρ.val‖ := norm_sub_le _ _
                _ = 1 + ‖z‖/‖ρ.val‖ := by rw [norm_one, norm_div]
            have h_log_bd : Real.log ‖1 - z/ρ.val‖ ≤ ‖z‖/‖ρ.val‖ := by
              have hle : Real.log ‖1 - z/ρ.val‖ ≤ Real.log (1 + ‖z‖/‖ρ.val‖) :=
                Real.log_le_log h1 h_norm_bd
              have hlog_sub : Real.log (1 + ‖z‖/‖ρ.val‖) ≤ (1 + ‖z‖/‖ρ.val‖) - 1 :=
                Real.log_le_sub_one_of_pos (by positivity)
              linarith
            have h_re_bd : (z/ρ.val).re ≤ ‖z/ρ.val‖ := Complex.re_le_norm _
            rw [norm_div] at h_re_bd
            linarith
        have h_sum_bd : (∑ x ∈ T, (lOrderNat χ x.val.val : ℝ) *
              Real.log ‖1 + ZD.xiWeierstrassTerm x.val.val z‖) ≤
            ∑ x ∈ T, (lOrderNat χ x.val.val : ℝ) * (2 * (‖z‖ / ‖x.val.val‖)) := by
          apply Finset.sum_le_sum
          intro x _
          have h_n_nn : (0 : ℝ) ≤ (lOrderNat χ x.val.val : ℝ) := Nat.cast_nonneg _
          exact mul_le_mul_of_nonneg_left (h_crude x.val) h_n_nn
        have h_sum_eq :
            (∑ x ∈ T, (lOrderNat χ x.val.val : ℝ) * (2 * (‖z‖ / ‖x.val.val‖))) =
            2 * ‖z‖ * (∑ ρ ∈ T', (lOrderNat χ ρ.val : ℝ) / ‖ρ.val‖) := by
          rw [show T' = T.image (Subtype.val : _ → {ρ : ℂ // ρ ∈ GRHSpectral.NontrivialZeros χ})
              from rfl]
          rw [Finset.sum_image]
          · rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring
          · intro x _ y _ h; exact Subtype.ext h
        have hT'_sum : (∑ ρ ∈ T', (lOrderNat χ ρ.val : ℝ) / ‖ρ.val‖) ≤
            C_part * (Real.log ‖z‖)^2 := hC_part ‖z‖ hz_ge_2' T' hT'_bd
        have h_abs : C_part * (Real.log ‖z‖)^2 ≤ |C_part| * (Real.log ‖z‖)^2 :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
        have hT'_sum' : (∑ ρ ∈ T', (lOrderNat χ ρ.val : ℝ) / ‖ρ.val‖) ≤
            |C_part| * (Real.log ‖z‖)^2 := by linarith
        have h_2z_nn : 0 ≤ 2 * ‖z‖ := by linarith
        have h_final : 2 * ‖z‖ * (∑ ρ ∈ T', (lOrderNat χ ρ.val : ℝ) / ‖ρ.val‖) ≤
            2 * ‖z‖ * (|C_part| * (Real.log ‖z‖)^2) :=
          mul_le_mul_of_nonneg_left hT'_sum' h_2z_nn
        calc (∑ x ∈ T, (lOrderNat χ x.val.val : ℝ) *
              Real.log ‖1 + ZD.xiWeierstrassTerm x.val.val z‖)
            ≤ ∑ x ∈ T, (lOrderNat χ x.val.val : ℝ) *
                (2 * (‖z‖ / ‖x.val.val‖)) := h_sum_bd
          _ = 2 * ‖z‖ * (∑ ρ ∈ T', (lOrderNat χ ρ.val : ℝ) / ‖ρ.val‖) := h_sum_eq
          _ ≤ 2 * ‖z‖ * (|C_part| * (Real.log ‖z‖)^2) := h_final
          _ = 2 * |C_part| * ‖z‖ * (Real.log ‖z‖)^2 := by ring
      have h_far_bd :
          (∑' ρ : (({ρ : {ρ : ℂ // ρ ∈ GRHSpectral.NontrivialZeros χ} | ‖ρ.val‖ ≤ ‖z‖}ᶜ : Set _)),
            (lOrderNat χ ρ.val.val : ℝ) *
              Real.log ‖1 + ZD.xiWeierstrassTerm ρ.val.val z‖) ≤
          3 * |C_tail| * ‖z‖ * Real.log ‖z‖ := by
        have h_rhs_nn : 0 ≤ 3 * |C_tail| * ‖z‖ * Real.log ‖z‖ := by positivity
        apply tsum_le_of_sum_le' h_rhs_nn
        intro T
        let T' : Finset {ρ : ℂ // ρ ∈ GRHSpectral.NontrivialZeros χ} := T.image (·.val)
        have hT'_bd : ∀ ρ ∈ T', ‖z‖ < ‖ρ.val‖ := by
          intro ρ hρ
          rw [Finset.mem_image] at hρ
          obtain ⟨x, _, heq⟩ := hρ
          rw [← heq]
          have := x.property
          simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at this
          exact this
        have h_quad : ∀ ρ : {ρ : ℂ // ρ ∈ GRHSpectral.NontrivialZeros χ}, ‖z‖ < ‖ρ.val‖ →
            Real.log ‖1 + ZD.xiWeierstrassTerm ρ.val z‖ ≤ 3 * ‖z‖^2 / ‖ρ.val‖^2 := by
          intro ρ hρ_gt
          have hρ_ne : ρ.val ≠ 0 := by
            intro heq
            have hre : (0 : ℝ) < ρ.val.re := ρ.property.1
            rw [heq] at hre; simp at hre
          have hzρ : ‖z‖ ≤ ‖ρ.val‖ := hρ_gt.le
          have h_term_bd := ZD.norm_xiWeierstrassTerm_le hρ_ne hzρ
          have h_norm_bd :
              ‖1 + ZD.xiWeierstrassTerm ρ.val z‖ ≤ 1 + 3 * ‖z‖^2 / ‖ρ.val‖^2 := by
            calc ‖1 + ZD.xiWeierstrassTerm ρ.val z‖
                ≤ ‖(1:ℂ)‖ + ‖ZD.xiWeierstrassTerm ρ.val z‖ := norm_add_le _ _
              _ = 1 + ‖ZD.xiWeierstrassTerm ρ.val z‖ := by rw [norm_one]
              _ ≤ 1 + 3 * ‖z‖^2 / ‖ρ.val‖^2 := by linarith
          by_cases h_zero : ‖1 + ZD.xiWeierstrassTerm ρ.val z‖ = 0
          · rw [h_zero, Real.log_zero]; positivity
          · have hpos : 0 < ‖1 + ZD.xiWeierstrassTerm ρ.val z‖ :=
              lt_of_le_of_ne (norm_nonneg _) (Ne.symm h_zero)
            have h_rhs_pos : 0 < 1 + 3 * ‖z‖^2 / ‖ρ.val‖^2 := by positivity
            have h_log_le : Real.log ‖1 + ZD.xiWeierstrassTerm ρ.val z‖ ≤
                Real.log (1 + 3 * ‖z‖^2 / ‖ρ.val‖^2) := Real.log_le_log hpos h_norm_bd
            have h_log_lt : Real.log (1 + 3 * ‖z‖^2 / ‖ρ.val‖^2) ≤
                3 * ‖z‖^2 / ‖ρ.val‖^2 := by
              have := Real.log_le_sub_one_of_pos h_rhs_pos
              linarith
            linarith
        have h_sum_bd : (∑ x ∈ T, (lOrderNat χ x.val.val : ℝ) *
              Real.log ‖1 + ZD.xiWeierstrassTerm x.val.val z‖) ≤
            ∑ x ∈ T, (lOrderNat χ x.val.val : ℝ) * (3 * ‖z‖^2 / ‖x.val.val‖^2) := by
          apply Finset.sum_le_sum
          intro x _
          have h_n_nn : (0 : ℝ) ≤ (lOrderNat χ x.val.val : ℝ) := Nat.cast_nonneg _
          have hx_prop : ‖z‖ < ‖x.val.val‖ := by
            have := x.property
            simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at this
            exact this
          exact mul_le_mul_of_nonneg_left (h_quad x.val hx_prop) h_n_nn
        have h_sum_eq :
            (∑ x ∈ T, (lOrderNat χ x.val.val : ℝ) * (3 * ‖z‖^2 / ‖x.val.val‖^2)) =
            3 * ‖z‖^2 * (∑ ρ ∈ T', (lOrderNat χ ρ.val : ℝ) / ‖ρ.val‖^2) := by
          rw [show T' = T.image (Subtype.val : _ → {ρ : ℂ // ρ ∈ GRHSpectral.NontrivialZeros χ})
              from rfl]
          rw [Finset.sum_image]
          · rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring
          · intro x _ y _ h; exact Subtype.ext h
        have hT'_sum : (∑ ρ ∈ T', (lOrderNat χ ρ.val : ℝ) / ‖ρ.val‖^2) ≤
            C_tail * Real.log ‖z‖ / ‖z‖ := hC_tail ‖z‖ hz_ge_2' T' hT'_bd
        have h_abs : C_tail * Real.log ‖z‖ / ‖z‖ ≤ |C_tail| * Real.log ‖z‖ / ‖z‖ := by
          have h_factor_nn : 0 ≤ Real.log ‖z‖ / ‖z‖ := by positivity
          have : C_tail * (Real.log ‖z‖ / ‖z‖) ≤ |C_tail| * (Real.log ‖z‖ / ‖z‖) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) h_factor_nn
          have h1 : C_tail * Real.log ‖z‖ / ‖z‖ = C_tail * (Real.log ‖z‖ / ‖z‖) := by ring
          have h2 : |C_tail| * Real.log ‖z‖ / ‖z‖ = |C_tail| * (Real.log ‖z‖ / ‖z‖) := by ring
          linarith
        have hT'_sum' : (∑ ρ ∈ T', (lOrderNat χ ρ.val : ℝ) / ‖ρ.val‖^2) ≤
            |C_tail| * Real.log ‖z‖ / ‖z‖ := by linarith
        have h_3z2_nn : 0 ≤ 3 * ‖z‖^2 := by positivity
        have h_final : 3 * ‖z‖^2 * (∑ ρ ∈ T', (lOrderNat χ ρ.val : ℝ) / ‖ρ.val‖^2) ≤
            3 * ‖z‖^2 * (|C_tail| * Real.log ‖z‖ / ‖z‖) :=
          mul_le_mul_of_nonneg_left hT'_sum' h_3z2_nn
        have hz_ne : ‖z‖ ≠ 0 := ne_of_gt hz_pos
        have h_simplify : 3 * ‖z‖^2 * (|C_tail| * Real.log ‖z‖ / ‖z‖) =
            3 * |C_tail| * ‖z‖ * Real.log ‖z‖ := by field_simp
        calc (∑ x ∈ T, (lOrderNat χ x.val.val : ℝ) *
              Real.log ‖1 + ZD.xiWeierstrassTerm x.val.val z‖)
            ≤ ∑ x ∈ T, (lOrderNat χ x.val.val : ℝ) *
                (3 * ‖z‖^2 / ‖x.val.val‖^2) := h_sum_bd
          _ = 3 * ‖z‖^2 * (∑ ρ ∈ T', (lOrderNat χ ρ.val : ℝ) / ‖ρ.val‖^2) := h_sum_eq
          _ ≤ 3 * ‖z‖^2 * (|C_tail| * Real.log ‖z‖ / ‖z‖) := h_final
          _ = 3 * |C_tail| * ‖z‖ * Real.log ‖z‖ := h_simplify
      have h_log_P_bd : Real.log ‖LProductMult χ z‖ ≤
          2 * |C_part| * ‖z‖ * (Real.log ‖z‖)^2 +
            3 * |C_tail| * ‖z‖ * Real.log ‖z‖ := by
        rw [h_log_eq, h_log_eq_ρ, ← h_split]
        exact add_le_add h_near_bd h_far_bd
      have h_z_bd :
          2 * |C_part| * ‖z‖ * (Real.log ‖z‖)^2 +
            3 * |C_tail| * ‖z‖ * Real.log ‖z‖ ≤
          (3 * |C_tail| + 2 * |C_part|) * ‖z‖ * (Real.log (‖z‖ + 2))^2 := by
        have h1 : 2 * |C_part| * ‖z‖ * (Real.log ‖z‖)^2 ≤
            2 * |C_part| * ‖z‖ * (Real.log (‖z‖ + 2))^2 := by
          have h_coeff_nn : 0 ≤ 2 * |C_part| * ‖z‖ := by positivity
          exact mul_le_mul_of_nonneg_left hlog_z_sq_le_z2_sq h_coeff_nn
        have h2 : 3 * |C_tail| * ‖z‖ * Real.log ‖z‖ ≤
            3 * |C_tail| * ‖z‖ * (Real.log (‖z‖ + 2))^2 := by
          have h_coeff_nn : 0 ≤ 3 * |C_tail| * ‖z‖ := by positivity
          exact mul_le_mul_of_nonneg_left hlog_z_le_z2_sq h_coeff_nn
        have h_expand : (3 * |C_tail| + 2 * |C_part|) * ‖z‖ * (Real.log (‖z‖ + 2))^2 =
            2 * |C_part| * ‖z‖ * (Real.log (‖z‖ + 2))^2 +
            3 * |C_tail| * ‖z‖ * (Real.log (‖z‖ + 2))^2 := by ring
        linarith
      have hP_nn : 0 ≤ ‖LProductMult χ z‖ := norm_nonneg _
      rcases le_or_gt ‖LProductMult χ z‖ 1 with hP_small | hP_big
      · have : Real.log (‖LProductMult χ z‖ + 1) ≤ Real.log 2 := by
          apply Real.log_le_log (by linarith) (by linarith)
        have h_rhs_nn :
            0 ≤ (3 * |C_tail| + 2 * |C_part|) * ‖z‖ * (Real.log (‖z‖ + 2))^2 := by
          positivity
        linarith
      · have hP_pos : 0 < ‖LProductMult χ z‖ := by linarith
        have : Real.log (‖LProductMult χ z‖ + 1) ≤ Real.log (2 * ‖LProductMult χ z‖) := by
          apply Real.log_le_log (by linarith) (by linarith)
        have h_log_2P :
            Real.log (2 * ‖LProductMult χ z‖) = Real.log 2 + Real.log ‖LProductMult χ z‖ :=
          Real.log_mul (by norm_num) (ne_of_gt hP_pos)
        linarith

end DirichletLHadamard
