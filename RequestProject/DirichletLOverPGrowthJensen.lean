import RequestProject.DirichletLOverPGrowthProduct
import RequestProject.DirichletLProductMultOrder

/-!
# Step C: Jensen's formula applied to `LProductMult χ`

Character-`χ` port of `ZD.xiProductMult_circleAverage_log_eq`, `xiProductMult_jensen_rhs_upper`,
`xiProductMult_jensen_rhs_nonneg`. `LProductMult χ` is entire with value `1` at `0`; Jensen gives the
circle-average of `log‖Prod‖` as the multiplicity-weighted `Σ_ρ n_ρ log(R/‖ρ‖)`, bounded above by
`C·R·log²R` (zero-count) and below by `0`.
-/

open Complex Set Filter Topology MeasureTheory

noncomputable section

namespace DirichletLHadamard

variable {N : ℕ} [NeZero N]

/-- Jensen's formula for `LProductMult χ` at center `0`. -/
theorem LProductMult_circleAverage_log_eq {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hχp : χ.IsPrimitive) :
    ∀ R : ℝ, 0 < R →
      Real.circleAverage (fun z => Real.log ‖LProductMult χ z‖) 0 R =
        ∑ᶠ u : ℂ,
          (MeromorphicOn.divisor (LProductMult χ) (Metric.closedBall 0 |R|) u : ℝ) *
            Real.log (R * ‖u‖⁻¹) := by
  intro R hR
  have hR_ne : R ≠ 0 := ne_of_gt hR
  have h0_in : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) |R| := by
    rw [Metric.mem_closedBall]; simp [abs_of_pos hR, hR.le]
  have h_anal_0 : AnalyticAt ℂ (LProductMult χ) 0 :=
    (LProductMult_differentiable hχ hχp).analyticAt 0
  have h_xi0 : LProductMult χ 0 = 1 := by
    unfold LProductMult
    simp [ZD.xiWeierstrassTerm, ZD.xiWeierstrassFactor]
  have h_ne_0 : LProductMult χ 0 ≠ 0 := by rw [h_xi0]; exact one_ne_zero
  have h_mero : MeromorphicOn (LProductMult χ) (Metric.closedBall 0 |R|) :=
    fun z _ => ((LProductMult_differentiable hχ hχp).analyticAt z).meromorphicAt
  have h_order_0 : analyticOrderAt (LProductMult χ) 0 = 0 :=
    h_anal_0.analyticOrderAt_eq_zero.mpr h_ne_0
  have h_div_0 : (MeromorphicOn.divisor (LProductMult χ) (Metric.closedBall 0 |R|)) 0 = 0 := by
    rw [MeromorphicOn.divisor_apply h_mero h0_in]
    rw [h_anal_0.meromorphicOrderAt_eq, h_order_0]; rfl
  have h_trail : meromorphicTrailingCoeffAt (LProductMult χ) 0 = 1 := by
    have := AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero h_anal_0 h_ne_0
    rw [this, h_xi0]
  have h_jensen := MeromorphicOn.circleAverage_log_norm hR_ne h_mero
  rw [h_jensen]
  have h_rewrite : (fun u : ℂ =>
        (MeromorphicOn.divisor (LProductMult χ) (Metric.closedBall 0 |R|) u : ℝ) *
          Real.log (R * ‖(0 : ℂ) - u‖⁻¹)) =
      (fun u : ℂ =>
        (MeromorphicOn.divisor (LProductMult χ) (Metric.closedBall 0 |R|) u : ℝ) *
          Real.log (R * ‖u‖⁻¹)) := by
    funext u
    congr 2
    rw [zero_sub, norm_neg]
  rw [h_rewrite, h_div_0, h_trail]
  simp

/-- Upper bound on the Jensen RHS: `∑_{ρ ∈ closedBall 0 R} n_ρ · log(R/‖ρ‖) ≤ O(R log² R)`. -/
theorem LProductMult_jensen_rhs_upper {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hχp : χ.IsPrimitive) :
    ∃ C D : ℝ, ∀ R : ℝ, 1 ≤ R →
      ∑ᶠ u : ℂ,
        (MeromorphicOn.divisor (LProductMult χ) (Metric.closedBall 0 |R|) u : ℝ) *
          Real.log (R * ‖u‖⁻¹) ≤
        C * R * (Real.log R) ^ 2 + D := by
  obtain ⟨C₀, hC₀_pos, R₀, hR₀_pos, hWB⟩ := completedL_weighted_zero_count_disk_bound hχ hχp
  have hN₁_fin : (GRHSpectral.NontrivialZeros χ ∩ Metric.closedBall (0 : ℂ) 1).Finite :=
    NontrivialZeros_inter_closedBall_finite hχ 1
  have hN_R₀_fin : (GRHSpectral.NontrivialZeros χ ∩ Metric.closedBall (0 : ℂ) R₀).Finite :=
    NontrivialZeros_inter_closedBall_finite hχ R₀
  classical
  set A_N₁ : ℝ := ∑ ρ ∈ hN₁_fin.toFinset, (lOrderNat χ ρ : ℝ) * |Real.log ‖ρ‖| with hA_def
  set N_M : ℝ := ∑ ρ ∈ hN₁_fin.toFinset, (lOrderNat χ ρ : ℝ) with hNM_def
  set B_R₀ : ℝ := ∑ ρ ∈ hN_R₀_fin.toFinset,
    (lOrderNat χ ρ : ℝ) * (max (Real.log R₀) 0 + |Real.log ‖ρ‖|) with hB_def
  have hA_nn : 0 ≤ A_N₁ :=
    Finset.sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)
  have hN_M_nn : 0 ≤ N_M := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hB_nn : 0 ≤ B_R₀ := by
    apply Finset.sum_nonneg; intro ρ _
    apply mul_nonneg (Nat.cast_nonneg _)
    have h1 : 0 ≤ max (Real.log R₀) 0 := le_max_right _ _
    have h2 : 0 ≤ |Real.log ‖ρ‖| := abs_nonneg _
    linarith
  refine ⟨C₀ + N_M, A_N₁ + N_M + B_R₀, fun R hR => ?_⟩
  have hR_pos : 0 < R := by linarith
  have habs : |R| = R := abs_of_pos hR_pos
  have hlog_R_nn : 0 ≤ Real.log R := Real.log_nonneg hR
  have hS'_spec : ∀ u : ℂ, u ∈ (NontrivialZeros_inter_closedBall_finite hχ R).toFinset ↔
      u ∈ GRHSpectral.NontrivialZeros χ ∩ Metric.closedBall (0 : ℂ) R :=
    fun u => Set.Finite.mem_toFinset _
  have h_finset_eq :
    ∑ᶠ u : ℂ,
      (MeromorphicOn.divisor (LProductMult χ) (Metric.closedBall 0 |R|) u : ℝ) *
        Real.log (R * ‖u‖⁻¹) =
    ∑ ρ ∈ (NontrivialZeros_inter_closedBall_finite hχ R).toFinset,
      (lOrderNat χ ρ : ℝ) * Real.log (R * ‖ρ‖⁻¹) := by
    set f : ℂ → ℝ := fun u =>
      (MeromorphicOn.divisor (LProductMult χ) (Metric.closedBall 0 |R|) u : ℝ) *
        Real.log (R * ‖u‖⁻¹)
    have hmero : MeromorphicOn (LProductMult χ) (Metric.closedBall 0 |R|) :=
      fun z _ => ((LProductMult_differentiable hχ hχp).analyticAt z).meromorphicAt
    have h_supp_subset : Function.support f ⊆
        ↑((NontrivialZeros_inter_closedBall_finite hχ R).toFinset) := by
      intro u hu
      simp only [Function.mem_support] at hu
      have h1 : ((MeromorphicOn.divisor (LProductMult χ) (Metric.closedBall 0 |R|)) u : ℝ) ≠ 0 := by
        intro hz; apply hu; show _ * _ = (0 : ℝ); rw [hz, zero_mul]
      have hmem : u ∈ Metric.closedBall (0 : ℂ) |R| := by
        by_contra h; apply h1
        have := Function.locallyFinsuppWithin.apply_eq_zero_of_notMem
          (MeromorphicOn.divisor (LProductMult χ) (Metric.closedBall 0 |R|)) h
        simp [this]
      have h_anal_u : AnalyticAt ℂ (LProductMult χ) u :=
        (LProductMult_differentiable hχ hχp).analyticAt u
      have h_nz : LProductMult χ u = 0 := by
        by_contra hne; apply h1
        rw [MeromorphicOn.divisor_apply hmero hmem, h_anal_u.meromorphicOrderAt_eq]
        rw [h_anal_u.analyticOrderAt_eq_zero.mpr hne]; simp
      have h_NT : u ∈ GRHSpectral.NontrivialZeros χ := (LProductMult_eq_zero_iff hχ hχp u).mp h_nz
      have hmem' : u ∈ Metric.closedBall (0 : ℂ) R := by rwa [habs] at hmem
      exact (hS'_spec u).mpr ⟨h_NT, hmem'⟩
    rw [finsum_eq_sum_of_support_subset f h_supp_subset]
    apply Finset.sum_congr rfl
    intro ρ hρ
    have hρ' := (hS'_spec ρ).mp hρ
    obtain ⟨hρ_NT, hρ_ball⟩ := hρ'
    have hmem : ρ ∈ Metric.closedBall (0 : ℂ) |R| := by rw [habs]; exact hρ_ball
    have h_anal_ρ : AnalyticAt ℂ (LProductMult χ) ρ :=
      (LProductMult_differentiable hχ hχp).analyticAt ρ
    have h_div_eq :
        ((MeromorphicOn.divisor (LProductMult χ) (Metric.closedBall 0 |R|)) ρ : ℝ) =
          (lOrderNat χ ρ : ℝ) := by
      rw [MeromorphicOn.divisor_apply hmero hmem, h_anal_ρ.meromorphicOrderAt_eq]
      rw [analyticOrderAt_LProductMult_eq_lOrderNat hχ hχp hρ_NT]; simp
    show ((MeromorphicOn.divisor (LProductMult χ) (Metric.closedBall 0 |R|)) ρ : ℝ) *
        Real.log (R * ‖ρ‖⁻¹) = (lOrderNat χ ρ : ℝ) * Real.log (R * ‖ρ‖⁻¹)
    rw [h_div_eq]
  rw [h_finset_eq]
  by_cases hR_ge : R₀ ≤ R
  · rw [← Finset.sum_filter_add_sum_filter_not
      (NontrivialZeros_inter_closedBall_finite hχ R).toFinset (fun ρ => ‖ρ‖ ≤ 1)]
    have h_small_subset :
        ((NontrivialZeros_inter_closedBall_finite hχ R).toFinset).filter (fun ρ => ‖ρ‖ ≤ 1) ⊆
          hN₁_fin.toFinset := by
      intro ρ hρ
      rw [Finset.mem_filter] at hρ
      obtain ⟨hρ_mem, h_small⟩ := hρ
      have hρ' := (hS'_spec ρ).mp hρ_mem
      rw [Set.Finite.mem_toFinset]
      exact ⟨hρ'.1, by rw [Metric.mem_closedBall, dist_zero_right]; exact h_small⟩
    have h_small_term_bd : ∀ ρ ∈ ((NontrivialZeros_inter_closedBall_finite hχ R).toFinset).filter
          (fun ρ => ‖ρ‖ ≤ 1),
        (lOrderNat χ ρ : ℝ) * Real.log (R * ‖ρ‖⁻¹) ≤
        (lOrderNat χ ρ : ℝ) * Real.log R + (lOrderNat χ ρ : ℝ) * |Real.log ‖ρ‖| := by
      intro ρ hρ
      rw [Finset.mem_filter] at hρ
      obtain ⟨hρ_mem, _⟩ := hρ
      have hρ' := (hS'_spec ρ).mp hρ_mem
      obtain ⟨hNT, _⟩ := hρ'
      have hρ_ne : ρ ≠ 0 := by
        intro h; rw [h] at hNT; have := hNT.1; simp at this
      have hρ_pos : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ_ne
      have hρ_inv_pos : 0 < ‖ρ‖⁻¹ := inv_pos.mpr hρ_pos
      have h_log_mul : Real.log (R * ‖ρ‖⁻¹) = Real.log R + Real.log ‖ρ‖⁻¹ :=
        Real.log_mul (ne_of_gt hR_pos) (ne_of_gt hρ_inv_pos)
      have h_log_inv : Real.log ‖ρ‖⁻¹ = -Real.log ‖ρ‖ := Real.log_inv _
      have h_xi_nn : (0 : ℝ) ≤ (lOrderNat χ ρ : ℝ) := Nat.cast_nonneg _
      have h_abs : -Real.log ‖ρ‖ ≤ |Real.log ‖ρ‖| := neg_le_abs _
      rw [h_log_mul, h_log_inv]
      have : Real.log R + -Real.log ‖ρ‖ ≤ Real.log R + |Real.log ‖ρ‖| := by linarith
      have := mul_le_mul_of_nonneg_left this h_xi_nn
      linarith
    have h_small_sum_bd := Finset.sum_le_sum h_small_term_bd
    have h_small_split :
      ∑ ρ ∈ ((NontrivialZeros_inter_closedBall_finite hχ R).toFinset).filter (fun ρ => ‖ρ‖ ≤ 1),
        ((lOrderNat χ ρ : ℝ) * Real.log R + (lOrderNat χ ρ : ℝ) * |Real.log ‖ρ‖|) =
      (∑ ρ ∈ ((NontrivialZeros_inter_closedBall_finite hχ R).toFinset).filter (fun ρ => ‖ρ‖ ≤ 1),
        (lOrderNat χ ρ : ℝ)) * Real.log R +
      (∑ ρ ∈ ((NontrivialZeros_inter_closedBall_finite hχ R).toFinset).filter (fun ρ => ‖ρ‖ ≤ 1),
        (lOrderNat χ ρ : ℝ) * |Real.log ‖ρ‖|) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    have h_wN_small_le :
        (∑ ρ ∈ ((NontrivialZeros_inter_closedBall_finite hχ R).toFinset).filter
           (fun ρ => ‖ρ‖ ≤ 1), (lOrderNat χ ρ : ℝ)) ≤ N_M := by
      rw [hNM_def]
      apply Finset.sum_le_sum_of_subset_of_nonneg h_small_subset
      intros; exact Nat.cast_nonneg _
    have h_wA_small_le :
        (∑ ρ ∈ ((NontrivialZeros_inter_closedBall_finite hχ R).toFinset).filter
           (fun ρ => ‖ρ‖ ≤ 1), (lOrderNat χ ρ : ℝ) * |Real.log ‖ρ‖|) ≤ A_N₁ := by
      rw [hA_def]
      apply Finset.sum_le_sum_of_subset_of_nonneg h_small_subset
      intros; exact mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)
    have h_big_term_bd : ∀ ρ ∈ ((NontrivialZeros_inter_closedBall_finite hχ R).toFinset).filter
          (fun ρ => ¬(‖ρ‖ ≤ 1)),
        (lOrderNat χ ρ : ℝ) * Real.log (R * ‖ρ‖⁻¹) ≤
        (lOrderNat χ ρ : ℝ) * Real.log R := by
      intro ρ hρ
      rw [Finset.mem_filter] at hρ
      obtain ⟨hρ_mem, h_not_small⟩ := hρ
      have h_gt : 1 < ‖ρ‖ := not_le.mp h_not_small
      have hρ' := (hS'_spec ρ).mp hρ_mem
      obtain ⟨hNT, _⟩ := hρ'
      have hρ_ne : ρ ≠ 0 := by
        intro h; rw [h] at hNT; have := hNT.1; simp at this
      have hρ_pos : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ_ne
      have hρ_inv_pos : 0 < ‖ρ‖⁻¹ := inv_pos.mpr hρ_pos
      have h_log_mul : Real.log (R * ‖ρ‖⁻¹) = Real.log R + Real.log ‖ρ‖⁻¹ :=
        Real.log_mul (ne_of_gt hR_pos) (ne_of_gt hρ_inv_pos)
      have h_log_inv : Real.log ‖ρ‖⁻¹ = -Real.log ‖ρ‖ := Real.log_inv _
      have h_log_ρ_pos : 0 < Real.log ‖ρ‖ := Real.log_pos h_gt
      have h_xi_nn : (0 : ℝ) ≤ (lOrderNat χ ρ : ℝ) := Nat.cast_nonneg _
      rw [h_log_mul, h_log_inv]
      have : Real.log R + -Real.log ‖ρ‖ ≤ Real.log R := by linarith
      have := mul_le_mul_of_nonneg_left this h_xi_nn
      linarith
    have h_big_sum_bd := Finset.sum_le_sum h_big_term_bd
    have h_big_factor :
        ∑ ρ ∈ ((NontrivialZeros_inter_closedBall_finite hχ R).toFinset).filter
          (fun ρ => ¬(‖ρ‖ ≤ 1)), (lOrderNat χ ρ : ℝ) * Real.log R =
        (∑ ρ ∈ ((NontrivialZeros_inter_closedBall_finite hχ R).toFinset).filter
          (fun ρ => ¬(‖ρ‖ ≤ 1)), (lOrderNat χ ρ : ℝ)) * Real.log R := by
      rw [← Finset.sum_mul]
    have h_sum_attach :
        (∑ ρ ∈ (NontrivialZeros_inter_closedBall_finite hχ R).toFinset, (lOrderNat χ ρ : ℝ)) =
        ∑ ρ ∈ (NontrivialZeros_inter_closedBall_finite hχ R).toFinset.attach.image
          (fun ρ : {x // x ∈ (NontrivialZeros_inter_closedBall_finite hχ R).toFinset} =>
            (⟨ρ.val, ((hS'_spec ρ.val).mp ρ.property).1⟩ :
              {ρ : ℂ // ρ ∈ GRHSpectral.NontrivialZeros χ})),
          (lOrderNat χ ρ.val : ℝ) := by
      rw [Finset.sum_image
        (f := fun ρ : {ρ : ℂ // ρ ∈ GRHSpectral.NontrivialZeros χ} => (lOrderNat χ ρ.val : ℝ))
        (g := fun ρ : {x // x ∈ (NontrivialZeros_inter_closedBall_finite hχ R).toFinset} =>
          (⟨ρ.val, ((hS'_spec ρ.val).mp ρ.property).1⟩ :
            {ρ : ℂ // ρ ∈ GRHSpectral.NontrivialZeros χ}))
        (s := (NontrivialZeros_inter_closedBall_finite hχ R).toFinset.attach)
        (?_)]
      · exact (Finset.sum_attach _ _).symm
      · intro a _ b _ hab
        exact Subtype.ext (Subtype.mk.injEq _ _ _ _ |>.mp hab)
    set S_attach : Finset {ρ : ℂ // ρ ∈ GRHSpectral.NontrivialZeros χ} :=
      (NontrivialZeros_inter_closedBall_finite hχ R).toFinset.attach.image
        (fun ρ : {x // x ∈ (NontrivialZeros_inter_closedBall_finite hχ R).toFinset} =>
          (⟨ρ.val, ((hS'_spec ρ.val).mp ρ.property).1⟩ :
            {ρ : ℂ // ρ ∈ GRHSpectral.NontrivialZeros χ})) with hSa_def
    have hS_attach_bd : ∀ ρ ∈ S_attach, ‖ρ.val‖ ≤ R := by
      intro ρ hρ
      simp only [hSa_def, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at hρ
      obtain ⟨ρ', hρ', heq⟩ := hρ
      have hρ'' := (hS'_spec ρ').mp hρ'
      have : ρ' ∈ Metric.closedBall (0 : ℂ) R := hρ''.2
      rw [Metric.mem_closedBall, dist_zero_right] at this
      rw [← heq]; exact this
    have hWB_R := hWB R hR_ge S_attach hS_attach_bd
    rw [← h_sum_attach] at hWB_R
    have h_big_weight_le :
        (∑ ρ ∈ ((NontrivialZeros_inter_closedBall_finite hχ R).toFinset).filter
          (fun ρ => ¬(‖ρ‖ ≤ 1)), (lOrderNat χ ρ : ℝ)) ≤
        ∑ ρ ∈ (NontrivialZeros_inter_closedBall_finite hχ R).toFinset, (lOrderNat χ ρ : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intros; exact Nat.cast_nonneg _
    have h_log_le_sq : Real.log R ≤ R * (Real.log R)^2 + 1 := by
      have h1 : Real.log R ≤ (Real.log R)^2 + 1 := by
        nlinarith [sq_nonneg (Real.log R - 1/2)]
      have h2 : (Real.log R)^2 ≤ R * (Real.log R)^2 := by
        have := mul_le_mul_of_nonneg_right hR (sq_nonneg (Real.log R))
        linarith
      linarith
    have h_big_sum_le_final :
        ∑ ρ ∈ ((NontrivialZeros_inter_closedBall_finite hχ R).toFinset).filter
          (fun ρ => ¬(‖ρ‖ ≤ 1)),
          (lOrderNat χ ρ : ℝ) * Real.log (R * ‖ρ‖⁻¹) ≤
        C₀ * R * Real.log R * Real.log R := by
      calc ∑ ρ ∈ ((NontrivialZeros_inter_closedBall_finite hχ R).toFinset).filter
            (fun ρ => ¬(‖ρ‖ ≤ 1)),
            (lOrderNat χ ρ : ℝ) * Real.log (R * ‖ρ‖⁻¹)
          ≤ ∑ ρ ∈ ((NontrivialZeros_inter_closedBall_finite hχ R).toFinset).filter
            (fun ρ => ¬(‖ρ‖ ≤ 1)), (lOrderNat χ ρ : ℝ) * Real.log R := h_big_sum_bd
        _ = _ := h_big_factor
        _ ≤ (∑ ρ ∈ (NontrivialZeros_inter_closedBall_finite hχ R).toFinset,
              (lOrderNat χ ρ : ℝ)) * Real.log R :=
            mul_le_mul_of_nonneg_right h_big_weight_le hlog_R_nn
        _ ≤ C₀ * R * Real.log R * Real.log R :=
            mul_le_mul_of_nonneg_right hWB_R hlog_R_nn
    have h_small_sum_le_final :
        ∑ ρ ∈ ((NontrivialZeros_inter_closedBall_finite hχ R).toFinset).filter
          (fun ρ => ‖ρ‖ ≤ 1),
          (lOrderNat χ ρ : ℝ) * Real.log (R * ‖ρ‖⁻¹) ≤
        N_M * Real.log R + A_N₁ := by
      calc _ ≤ _ := h_small_sum_bd
        _ = _ := h_small_split
        _ ≤ N_M * Real.log R + A_N₁ := by
            have := mul_le_mul_of_nonneg_right h_wN_small_le hlog_R_nn
            linarith
    have hC₀_sq : C₀ * R * Real.log R * Real.log R = C₀ * R * (Real.log R)^2 := by ring
    have h_NM_logR : N_M * Real.log R ≤ N_M * R * (Real.log R)^2 + N_M := by
      have := mul_le_mul_of_nonneg_left h_log_le_sq hN_M_nn
      nlinarith
    linarith
  · push_neg at hR_ge
    have hR_lt : R < R₀ := hR_ge
    have hR_le : R ≤ R₀ := hR_lt.le
    have h_S_subset : (NontrivialZeros_inter_closedBall_finite hχ R).toFinset ⊆
        hN_R₀_fin.toFinset := by
      intro ρ hρ
      have hρ' := (hS'_spec ρ).mp hρ
      rw [Set.Finite.mem_toFinset]
      refine ⟨hρ'.1, ?_⟩
      have := hρ'.2
      rw [Metric.mem_closedBall, dist_zero_right] at this ⊢
      linarith
    have h_term_bd : ∀ ρ ∈ (NontrivialZeros_inter_closedBall_finite hχ R).toFinset,
        (lOrderNat χ ρ : ℝ) * Real.log (R * ‖ρ‖⁻¹) ≤
        (lOrderNat χ ρ : ℝ) * (max (Real.log R₀) 0 + |Real.log ‖ρ‖|) := by
      intro ρ hρ
      have hρ' := (hS'_spec ρ).mp hρ
      obtain ⟨hNT, _⟩ := hρ'
      have hρ_ne : ρ ≠ 0 := by
        intro h; rw [h] at hNT; have := hNT.1; simp at this
      have hρ_pos : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ_ne
      have hρ_inv_pos : 0 < ‖ρ‖⁻¹ := inv_pos.mpr hρ_pos
      have h_log_mul : Real.log (R * ‖ρ‖⁻¹) = Real.log R + Real.log ‖ρ‖⁻¹ :=
        Real.log_mul (ne_of_gt hR_pos) (ne_of_gt hρ_inv_pos)
      have h_log_inv : Real.log ‖ρ‖⁻¹ = -Real.log ‖ρ‖ := Real.log_inv _
      have h_xi_nn : (0 : ℝ) ≤ (lOrderNat χ ρ : ℝ) := Nat.cast_nonneg _
      have h_abs : -Real.log ‖ρ‖ ≤ |Real.log ‖ρ‖| := neg_le_abs _
      have h_log_R_le : Real.log R ≤ Real.log R₀ := Real.log_le_log hR_pos hR_le
      have h_log_R₀_le_max : Real.log R₀ ≤ max (Real.log R₀) 0 := le_max_left _ _
      rw [h_log_mul, h_log_inv]
      have h_ineq : Real.log R + -Real.log ‖ρ‖ ≤ max (Real.log R₀) 0 + |Real.log ‖ρ‖| := by linarith
      have := mul_le_mul_of_nonneg_left h_ineq h_xi_nn
      linarith
    have h_sum_le_B :
        ∑ ρ ∈ (NontrivialZeros_inter_closedBall_finite hχ R).toFinset,
          (lOrderNat χ ρ : ℝ) * Real.log (R * ‖ρ‖⁻¹) ≤ B_R₀ := by
      calc _ ≤ ∑ ρ ∈ (NontrivialZeros_inter_closedBall_finite hχ R).toFinset,
              (lOrderNat χ ρ : ℝ) * (max (Real.log R₀) 0 + |Real.log ‖ρ‖|) :=
            Finset.sum_le_sum h_term_bd
        _ ≤ ∑ ρ ∈ hN_R₀_fin.toFinset,
              (lOrderNat χ ρ : ℝ) * (max (Real.log R₀) 0 + |Real.log ‖ρ‖|) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg h_S_subset
            intro ρ _ _
            apply mul_nonneg (Nat.cast_nonneg _)
            have h1 : 0 ≤ max (Real.log R₀) 0 := le_max_right _ _
            have h2 : 0 ≤ |Real.log ‖ρ‖| := abs_nonneg _
            linarith
        _ = B_R₀ := hB_def.symm
    have hC_R_logSq_nn : 0 ≤ (C₀ + N_M) * R * (Real.log R)^2 := by
      apply mul_nonneg
      · exact mul_nonneg (by linarith [hC₀_pos, hN_M_nn]) hR_pos.le
      · exact sq_nonneg _
    linarith

/-- The Jensen RHS is nonnegative. -/
theorem LProductMult_jensen_rhs_nonneg {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hχp : χ.IsPrimitive) :
    ∀ R : ℝ, 1 ≤ R →
      0 ≤ ∑ᶠ u : ℂ,
        (MeromorphicOn.divisor (LProductMult χ) (Metric.closedBall 0 |R|) u : ℝ) *
          Real.log (R * ‖u‖⁻¹) := by
  intro R hR
  have hR_pos : 0 < R := by linarith
  have h_anal : AnalyticOnNhd ℂ (LProductMult χ) (Metric.closedBall 0 |R|) := by
    intro z _
    exact (LProductMult_differentiable hχ hχp).analyticAt z
  have h_div_nn :
      0 ≤ MeromorphicOn.divisor (LProductMult χ) (Metric.closedBall 0 |R|) :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg h_anal
  refine finsum_nonneg fun u => ?_
  by_cases hu : u ∈ Metric.closedBall (0 : ℂ) |R|
  · have hu_norm : ‖u‖ ≤ R := by
      have : ‖u‖ ≤ |R| := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hu
      rwa [abs_of_pos hR_pos] at this
    have h_div_u_nn :
        (0 : ℤ) ≤ MeromorphicOn.divisor (LProductMult χ) (Metric.closedBall 0 |R|) u :=
      h_div_nn u
    have h_div_u_real_nn :
        (0 : ℝ) ≤ (MeromorphicOn.divisor (LProductMult χ)
          (Metric.closedBall 0 |R|) u : ℝ) := by exact_mod_cast h_div_u_nn
    have h_log_nn : 0 ≤ Real.log (R * ‖u‖⁻¹) := by
      by_cases hu_zero : u = 0
      · subst hu_zero
        simp
      · have hu_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu_zero
        have h_arg_ge_one : 1 ≤ R * ‖u‖⁻¹ := by
          rw [le_mul_inv_iff₀ hu_pos]
          linarith
        exact Real.log_nonneg h_arg_ge_one
    exact mul_nonneg h_div_u_real_nn h_log_nn
  · have h_zero :
        MeromorphicOn.divisor (LProductMult χ) (Metric.closedBall 0 |R|) u = 0 :=
      Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu
    simp [h_zero]

end DirichletLHadamard
