import RequestProject.DirichletLZeroCount

/-!
# Dyadic weighted-zero-moduli bounds for Dirichlet `L` (Step B prep)

Character-`χ` port of `ZD.xiOrderNat_div_norm_sq_tail_bound` and
`ZD.xiOrderNat_div_norm_partial_sum_bound`. Both follow the dyadic-shell template using the zero-count
bound `completedL_weighted_zero_count_disk_bound` and the summability
`summable_lOrderNat_div_norm_sq_nontrivialZeros`.

**One genuine adaptation** vs. the ζ proof: ζ's nontrivial zeros satisfy `|Im ρ| ≥ 2` (so `‖ρ‖ ≥ 2`),
which is FALSE for Dirichlet `L` (low-lying zeros). The partial-sum bound therefore splits at
`max(2, R₀)` and absorbs the finitely many small zeros (`‖ρ‖ ≤ max(2,R₀)`) into the finite constant
`M_low`, rather than assuming `‖ρ‖ ≥ 2` for every zero.
-/

open Complex Set Filter Topology

noncomputable section

namespace DirichletLHadamard

variable {N : ℕ} [NeZero N]

/-- **Tail**: `∑_{‖ρ‖ > R} n_ρ / ‖ρ‖² ≤ C · log R / R`. Dyadic shells `2^k R < ‖ρ‖ ≤ 2^{k+1} R`. -/
theorem lOrderNat_div_norm_sq_tail_bound {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hχp : χ.IsPrimitive) :
    ∃ C : ℝ, ∀ R : ℝ, 2 ≤ R →
      ∀ (S : Finset {ρ : ℂ // ρ ∈ GRHSpectral.NontrivialZeros χ}),
        (∀ ρ ∈ S, R < ‖ρ.val‖) →
        (∑ ρ ∈ S, (lOrderNat χ ρ.val : ℝ) / ‖ρ.val‖ ^ 2) ≤ C * Real.log R / R := by
  obtain ⟨C₀, hC₀_pos, R₀, hR₀_pos, hWB⟩ := completedL_weighted_zero_count_disk_bound hχ hχp
  have hSumm := summable_lOrderNat_div_norm_sq_nontrivialZeros hχ hχp
  set T_glob : ℝ := ∑' ρ : {ρ : ℂ // ρ ∈ GRHSpectral.NontrivialZeros χ},
      (lOrderNat χ ρ.val : ℝ) / ‖ρ.val‖ ^ 2 with hT_def
  have hT_nn : 0 ≤ T_glob := by
    rw [hT_def]; exact tsum_nonneg (fun ρ => by positivity)
  have h_summ_geom : Summable (fun k : ℕ => ((k : ℝ) + 2) / 2^k) := by
    have h1 : Summable (fun k : ℕ => (k : ℝ) * (1/2)^k) := by
      have := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
        (show ‖(1/2:ℝ)‖ < 1 by rw [Real.norm_eq_abs]; norm_num)
      exact this.congr (fun k => by simp [pow_one])
    have h2 : Summable (fun k : ℕ => (1/2 : ℝ)^k) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    have h_sum : Summable (fun k : ℕ => (k : ℝ) * (1/2)^k + 2 * (1/2 : ℝ)^k) :=
      h1.add (h2.mul_left 2)
    convert h_sum using 1
    funext k
    have h_eq : (1/2 : ℝ)^k = 1/2^k := by rw [div_pow, one_pow]
    rw [h_eq]; field_simp
  set S_geom : ℝ := ∑' k : ℕ, ((k : ℝ) + 2) / 2^k with hSgeom_def
  have hSgeom_nn : 0 ≤ S_geom := tsum_nonneg (fun k => by positivity)
  set R_fence : ℝ := max 2 R₀ with hRf_def
  have hRf_ge_two : (2 : ℝ) ≤ R_fence := le_max_left _ _
  have hRf_ge_R₀ : R₀ ≤ R_fence := le_max_right _ _
  have hRf_pos : 0 < R_fence := by linarith
  set C_dyad : ℝ := 2 * C₀ * S_geom with hCd_def
  have hCd_nn : 0 ≤ C_dyad := by rw [hCd_def]; positivity
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set C_glob : ℝ := T_glob * R_fence / Real.log 2 with hCg_def
  have hCg_nn : 0 ≤ C_glob := by rw [hCg_def]; positivity
  set C : ℝ := C_glob + C_dyad with hC_def
  refine ⟨C, ?_⟩
  intro R hR S hS_far
  have hR_pos : 0 < R := by linarith
  have hlog_R_pos : 0 < Real.log R := Real.log_pos (by linarith)
  have hlog_R_nn : 0 ≤ Real.log R := hlog_R_pos.le
  have hlog2_le_logR : Real.log 2 ≤ Real.log R := Real.log_le_log (by norm_num) hR
  have hlog2_nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h_sum_nn : 0 ≤ ∑ ρ ∈ S, (lOrderNat χ ρ.val : ℝ) / ‖ρ.val‖ ^ 2 :=
    Finset.sum_nonneg (fun ρ _ => by positivity)
  have h_sum_le_T : (∑ ρ ∈ S, (lOrderNat χ ρ.val : ℝ) / ‖ρ.val‖ ^ 2) ≤ T_glob := by
    rw [hT_def]; exact Summable.sum_le_tsum _ (fun i _ => by positivity) hSumm
  by_cases hR_case : R_fence ≤ R
  · have hR_ge_R₀ : R₀ ≤ R := le_trans hRf_ge_R₀ hR_case
    let kf : {ρ : ℂ // ρ ∈ GRHSpectral.NontrivialZeros χ} → ℕ := fun ρ =>
      if h : (1 : ℝ) ≤ ‖ρ.val‖ / R
      then (exists_nat_pow_near h (by norm_num : (1:ℝ) < 2)).choose
      else 0
    have h_kf_prop :
        ∀ ρ ∈ S, (2 : ℝ) ^ kf ρ * R ≤ ‖ρ.val‖ ∧ ‖ρ.val‖ < (2 : ℝ) ^ (kf ρ + 1) * R := by
      intro ρ hρ
      have hgt : R < ‖ρ.val‖ := hS_far ρ hρ
      have h_ratio : 1 ≤ ‖ρ.val‖ / R := by
        rw [le_div_iff₀ hR_pos]; linarith
      simp only [kf, dif_pos h_ratio]
      have ⟨h1, h2⟩ := (exists_nat_pow_near h_ratio (by norm_num : (1:ℝ) < 2)).choose_spec
      refine ⟨?_, ?_⟩
      · rwa [le_div_iff₀ hR_pos] at h1
      · rwa [div_lt_iff₀ hR_pos] at h2
    set K_max : ℕ := S.sup kf + 1 with hKmax_def
    have h_kf_le : ∀ ρ ∈ S, kf ρ < K_max := fun ρ hρ => by
      have := Finset.le_sup (f := kf) hρ
      omega
    have h_per_elem :
        ∀ ρ ∈ S,
          (lOrderNat χ ρ.val : ℝ) / ‖ρ.val‖ ^ 2 ≤
          (lOrderNat χ ρ.val : ℝ) / ((2 : ℝ) ^ kf ρ * R) ^ 2 := by
      intro ρ hρ
      have ⟨h_lb, _⟩ := h_kf_prop ρ hρ
      have h_sq_pos : (0 : ℝ) < ((2 : ℝ) ^ kf ρ * R) ^ 2 := by positivity
      have hρ_pos : 0 < ‖ρ.val‖ := by linarith [hS_far ρ hρ]
      have hρ_sq_pos : (0 : ℝ) < ‖ρ.val‖ ^ 2 := by positivity
      have h_sq_le : ((2 : ℝ) ^ kf ρ * R) ^ 2 ≤ ‖ρ.val‖ ^ 2 :=
        pow_le_pow_left₀ (by positivity) h_lb 2
      apply div_le_div_of_nonneg_left (by positivity) h_sq_pos h_sq_le
    have h_shell_bound : ∀ k : ℕ,
        (∑ ρ ∈ S.filter (fun ρ => kf ρ = k), (lOrderNat χ ρ.val : ℝ)) ≤
        C₀ * ((2 : ℝ) ^ (k + 1) * R) * Real.log ((2 : ℝ) ^ (k + 1) * R) := by
      intro k
      have hR_target_ge : R₀ ≤ (2 : ℝ) ^ (k + 1) * R := by
        have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := one_le_pow₀ (by norm_num)
        have : R ≤ (2 : ℝ) ^ (k + 1) * R := by nlinarith
        linarith
      apply hWB ((2 : ℝ) ^ (k + 1) * R) hR_target_ge
      intro ρ hρ
      simp only [Finset.mem_filter] at hρ
      have ⟨_, h_ub⟩ := h_kf_prop ρ hρ.1
      rw [hρ.2] at h_ub
      linarith
    have h_shell_bound_scaled : ∀ k : ℕ,
        (∑ ρ ∈ S.filter (fun ρ => kf ρ = k), (lOrderNat χ ρ.val : ℝ)) / ((2:ℝ)^k * R)^2 ≤
        2 * C₀ * Real.log R / R * ((k + 2 : ℝ) / 2^k) := by
      intro k
      set x : ℝ := ∑ ρ ∈ S.filter (fun ρ => kf ρ = k), (lOrderNat χ ρ.val : ℝ)
      have hx_nn : 0 ≤ x := Finset.sum_nonneg (fun ρ _ => Nat.cast_nonneg _)
      have h_bd : x ≤ C₀ * ((2:ℝ)^(k+1) * R) * Real.log ((2:ℝ)^(k+1) * R) := h_shell_bound k
      have h_log_expand : Real.log ((2:ℝ)^(k+1) * R) = (k+1 : ℝ) * Real.log 2 + Real.log R := by
        rw [Real.log_mul (by positivity) (by linarith)]
        rw [Real.log_pow]; push_cast; ring
      have h_log_le : (k+1 : ℝ) * Real.log 2 + Real.log R ≤ (k+2) * Real.log R := by
        have hk_nn : 0 ≤ (k+1 : ℝ) := by positivity
        nlinarith
      have h_bd' : x ≤ C₀ * ((2:ℝ)^(k+1) * R) * ((k+2 : ℝ) * Real.log R) := by
        rw [h_log_expand] at h_bd
        have h_pos : 0 ≤ C₀ * ((2:ℝ)^(k+1) * R) := by positivity
        calc x ≤ C₀ * ((2:ℝ)^(k+1) * R) * ((k+1 : ℝ) * Real.log 2 + Real.log R) := h_bd
          _ ≤ C₀ * ((2:ℝ)^(k+1) * R) * ((k+2 : ℝ) * Real.log R) :=
              mul_le_mul_of_nonneg_left h_log_le h_pos
      have h2R_sq_pos : (0 : ℝ) < ((2 : ℝ) ^ k * R) ^ 2 := by positivity
      calc x / ((2:ℝ)^k * R)^2
          ≤ C₀ * ((2:ℝ)^(k+1) * R) * ((k+2 : ℝ) * Real.log R) / ((2:ℝ)^k * R)^2 := by gcongr
        _ = 2 * C₀ * Real.log R / R * ((k + 2 : ℝ) / 2^k) := by
            have h2k1 : (2 : ℝ) ^ (k+1) = 2 * (2:ℝ)^k := by rw [pow_succ]; ring
            rw [h2k1]; field_simp
    have h_dyad_sum :
        (∑ ρ ∈ S, (lOrderNat χ ρ.val : ℝ) / ‖ρ.val‖ ^ 2) ≤
        C_dyad * Real.log R / R := by
      calc (∑ ρ ∈ S, (lOrderNat χ ρ.val : ℝ) / ‖ρ.val‖ ^ 2)
          ≤ ∑ ρ ∈ S, (lOrderNat χ ρ.val : ℝ) / ((2 : ℝ) ^ kf ρ * R) ^ 2 :=
            Finset.sum_le_sum h_per_elem
        _ = ∑ k ∈ Finset.range K_max,
              ∑ ρ ∈ S.filter (fun ρ => kf ρ = k),
                (lOrderNat χ ρ.val : ℝ) / ((2 : ℝ) ^ kf ρ * R) ^ 2 := by
            rw [← Finset.sum_fiberwise_of_maps_to
              (t := Finset.range K_max) (g := kf)
              (f := fun ρ => (lOrderNat χ ρ.val : ℝ) / ((2 : ℝ) ^ kf ρ * R) ^ 2)]
            intro ρ hρ
            exact Finset.mem_range.mpr (h_kf_le ρ hρ)
        _ = ∑ k ∈ Finset.range K_max,
              (∑ ρ ∈ S.filter (fun ρ => kf ρ = k), (lOrderNat χ ρ.val : ℝ)) /
                ((2 : ℝ) ^ k * R) ^ 2 := by
            apply Finset.sum_congr rfl; intro k _
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl; intro ρ hρ
            simp only [Finset.mem_filter] at hρ
            rw [hρ.2]
        _ ≤ ∑ k ∈ Finset.range K_max,
              2 * C₀ * Real.log R / R * ((k + 2 : ℝ) / 2^k) :=
            Finset.sum_le_sum (fun k _ => h_shell_bound_scaled k)
        _ = 2 * C₀ * Real.log R / R * ∑ k ∈ Finset.range K_max, ((k : ℝ) + 2) / 2^k := by
            rw [← Finset.mul_sum]
        _ ≤ 2 * C₀ * Real.log R / R * S_geom := by
            have h_nn : ∀ k : ℕ, 0 ≤ ((k : ℝ) + 2) / 2^k := fun k => by positivity
            have h_bd : (∑ k ∈ Finset.range K_max, ((k : ℝ) + 2) / 2^k) ≤ S_geom :=
              Summable.sum_le_tsum _ (fun i _ => h_nn i) h_summ_geom
            have h_outer_nn : 0 ≤ 2 * C₀ * Real.log R / R := by positivity
            exact mul_le_mul_of_nonneg_left h_bd h_outer_nn
        _ = C_dyad * Real.log R / R := by rw [hCd_def]; ring
    have h_expand : C * Real.log R / R = C_glob * Real.log R / R + C_dyad * Real.log R / R := by
      rw [hC_def]; ring
    have h_glob_nn : 0 ≤ C_glob * Real.log R / R := by positivity
    linarith
  · push_neg at hR_case
    have hR_lt_Rf : R < R_fence := hR_case
    have hR_le_Rf : R ≤ R_fence := hR_lt_Rf.le
    have h_Rf_logR_ge : R * Real.log 2 ≤ R_fence * Real.log R := by
      have h1 : R * Real.log 2 ≤ R * Real.log R :=
        mul_le_mul_of_nonneg_left hlog2_le_logR hR_pos.le
      have h2 : R * Real.log R ≤ R_fence * Real.log R :=
        mul_le_mul_of_nonneg_right hR_le_Rf hlog_R_nn
      linarith
    have h_Cg : C_glob * Real.log R / R = T_glob * R_fence * Real.log R / (Real.log 2 * R) := by
      rw [hCg_def]; ring
    have h_Cg_ge_T : T_glob ≤ C_glob * Real.log R / R := by
      rw [h_Cg]
      have h_div_ge_1 : 1 ≤ R_fence * Real.log R / (Real.log 2 * R) := by
        rw [le_div_iff₀ (by positivity)]; linarith
      calc T_glob = T_glob * 1 := by ring
        _ ≤ T_glob * (R_fence * Real.log R / (Real.log 2 * R)) :=
            mul_le_mul_of_nonneg_left h_div_ge_1 hT_nn
        _ = T_glob * R_fence * Real.log R / (Real.log 2 * R) := by ring
    have h_expand : C * Real.log R / R = C_glob * Real.log R / R + C_dyad * Real.log R / R := by
      rw [hC_def]; ring
    have h_dyad_nn : 0 ≤ C_dyad * Real.log R / R := by positivity
    linarith

/-- **Partial sum**: `∑_{‖ρ‖ ≤ R} n_ρ / ‖ρ‖ ≤ C · (log R)²`. Unlike ζ (whose zeros have `‖ρ‖ ≥ 2`),
the finitely many small Dirichlet-`L` zeros (`‖ρ‖ ≤ max(2,R₀)`) are absorbed into `M_low`. -/
theorem lOrderNat_div_norm_partial_sum_bound {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hχp : χ.IsPrimitive) :
    ∃ C : ℝ, ∀ R : ℝ, 2 ≤ R →
      ∀ (S : Finset {ρ : ℂ // ρ ∈ GRHSpectral.NontrivialZeros χ}),
        (∀ ρ ∈ S, ‖ρ.val‖ ≤ R) →
        (∑ ρ ∈ S, (lOrderNat χ ρ.val : ℝ) / ‖ρ.val‖) ≤ C * (Real.log R) ^ 2 := by
  obtain ⟨C₃, hC₃_pos, R₀_step3, _, hBound⟩ := completedL_weighted_zero_count_disk_bound hχ hχp
  set R_split : ℝ := max 2 R₀_step3 with hRsplit_def
  have hRsplit_ge_2 : (2 : ℝ) ≤ R_split := le_max_left _ _
  have hRsplit_ge_R0 : R₀_step3 ≤ R_split := le_max_right _ _
  set M_low : ℝ :=
    (NontrivialZeros_inter_closedBall_finite hχ R_split).toFinset.sum
      (fun ρ => (lOrderNat χ ρ : ℝ) / ‖ρ‖) with hM_low_def
  have hM_low_nn : 0 ≤ M_low := by
    apply Finset.sum_nonneg; intro ρ _; exact div_nonneg (by positivity) (by positivity)
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hC₃_nn : 0 ≤ C₃ := hC₃_pos.le
  refine ⟨M_low / (Real.log 2)^2 + 18 * C₃ / Real.log 2, ?_⟩
  intro R hR S hS_bd
  have hR_pos : (0 : ℝ) < R := by linarith
  have hR_log_ge_log2 : Real.log 2 ≤ Real.log R := Real.log_le_log (by norm_num) hR
  have hR_log_pos : 0 < Real.log R := lt_of_lt_of_le hlog2_pos hR_log_ge_log2
  have hR_log_nn : 0 ≤ Real.log R := hR_log_pos.le
  rw [← Finset.sum_filter_add_sum_filter_not S (fun ρ => ‖ρ.val‖ ≤ R_split)]
  have h_lo_bound :
      (∑ ρ ∈ S.filter (fun ρ => ‖ρ.val‖ ≤ R_split),
        (lOrderNat χ ρ.val : ℝ) / ‖ρ.val‖) ≤ M_low := by
    rw [hM_low_def,
        show (∑ ρ ∈ S.filter (fun ρ => ‖ρ.val‖ ≤ R_split),
              (lOrderNat χ ρ.val : ℝ) / ‖ρ.val‖) =
            ∑ ρ ∈ (S.filter (fun ρ => ‖ρ.val‖ ≤ R_split)).image Subtype.val,
                (lOrderNat χ ρ : ℝ) / ‖ρ‖ from ?_]
    swap
    · rw [Finset.sum_image]; intro x _ y _ h; exact Subtype.val_injective h
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro ρ hρ
      rcases Finset.mem_image.mp hρ with ⟨ρ', hρ'_in, hρ'_eq⟩
      simp only [Finset.mem_filter] at hρ'_in
      simp only [Set.Finite.mem_toFinset]
      refine ⟨?_, ?_⟩
      · subst hρ'_eq; exact ρ'.property
      · rw [Metric.mem_closedBall, dist_zero_right]; subst hρ'_eq; exact hρ'_in.2
    · intros; positivity
  set S_hi : Finset {ρ : ℂ // ρ ∈ GRHSpectral.NontrivialZeros χ} :=
    S.filter (fun ρ => ¬ ‖ρ.val‖ ≤ R_split) with hShi_def
  have h_hi_gt_Rsplit : ∀ ρ ∈ S_hi, R_split < ‖ρ.val‖ := by
    intro ρ hρ; simp only [hShi_def, Finset.mem_filter, not_le] at hρ; exact hρ.2
  have h_hi_ge_2 : ∀ ρ ∈ S_hi, (2:ℝ) ≤ ‖ρ.val‖ :=
    fun ρ hρ => le_trans hRsplit_ge_2 (h_hi_gt_Rsplit ρ hρ).le
  have h_hi_gt_R0 : ∀ ρ ∈ S_hi, R₀_step3 < ‖ρ.val‖ :=
    fun ρ hρ => lt_of_le_of_lt hRsplit_ge_R0 (h_hi_gt_Rsplit ρ hρ)
  have h_hi_le_R : ∀ ρ ∈ S_hi, ‖ρ.val‖ ≤ R := by
    intro ρ hρ; simp only [hShi_def, Finset.mem_filter] at hρ; exact hS_bd ρ hρ.1
  let kf : {ρ : ℂ // ρ ∈ GRHSpectral.NontrivialZeros χ} → ℕ := fun ρ =>
    if h : (1 : ℝ) ≤ ‖ρ.val‖ / 2
    then (exists_nat_pow_near h (by norm_num : (1:ℝ) < 2)).choose
    else 0
  have h_kf_spec : ∀ ρ ∈ S_hi,
      (2 : ℝ) ^ (kf ρ) ≤ ‖ρ.val‖ / 2 ∧ ‖ρ.val‖ / 2 < (2 : ℝ) ^ (kf ρ + 1) := by
    intro ρ hρ
    have h2 := h_hi_ge_2 ρ hρ
    have h1 : (1 : ℝ) ≤ ‖ρ.val‖ / 2 := by linarith
    simp only [kf, dif_pos h1]
    exact (exists_nat_pow_near h1 (by norm_num : (1:ℝ) < 2)).choose_spec
  have h_norm_ge : ∀ ρ ∈ S_hi, (2 : ℝ) ^ (kf ρ + 1) ≤ ‖ρ.val‖ := by
    intro ρ hρ; have ⟨h1, _⟩ := h_kf_spec ρ hρ; rw [pow_succ]; linarith
  have h_norm_lt : ∀ ρ ∈ S_hi, ‖ρ.val‖ < (2 : ℝ) ^ (kf ρ + 2) := by
    intro ρ hρ
    have ⟨_, h2⟩ := h_kf_spec ρ hρ
    have : ‖ρ.val‖ < 2 * (2 : ℝ) ^ (kf ρ + 1) := by linarith
    rw [pow_succ] at this ⊢; linarith
  set K_max : ℕ := S_hi.sup kf + 1 with hKmax_def
  have h_kf_lt : ∀ ρ ∈ S_hi, kf ρ < K_max := by
    intro ρ hρ; have := Finset.le_sup (f := kf) hρ; omega
  have h_pow_gt_R0 : ∀ ρ ∈ S_hi, R₀_step3 < (2 : ℝ) ^ (kf ρ + 2) :=
    fun ρ hρ => lt_trans (h_hi_gt_R0 ρ hρ) (h_norm_lt ρ hρ)
  have h_kf_log_bd : ∀ ρ ∈ S_hi, ((kf ρ : ℝ) + 1) ≤ Real.log R / Real.log 2 := by
    intro ρ hρ
    have hge := h_norm_ge ρ hρ
    have hle := h_hi_le_R ρ hρ
    have hR_pos' : (0 : ℝ) < (2:ℝ)^(kf ρ + 1) := pow_pos (by norm_num) _
    have h_pow_le_R : (2:ℝ)^(kf ρ + 1) ≤ R := le_trans hge hle
    have h_log_pow_le : Real.log ((2:ℝ)^(kf ρ + 1)) ≤ Real.log R :=
      Real.log_le_log hR_pos' h_pow_le_R
    rw [Real.log_pow] at h_log_pow_le
    push_cast at h_log_pow_le
    rw [le_div_iff₀ hlog2_pos]
    linarith
  have h_sup_bd : ((S_hi.sup kf : ℕ) : ℝ) ≤ Real.log R / Real.log 2 - 1 := by
    by_cases hS : S_hi.Nonempty
    · obtain ⟨m, hm_mem, hm_max⟩ := S_hi.exists_max_image (f := kf) hS
      have h_sup_eq : S_hi.sup kf = kf m :=
        le_antisymm (Finset.sup_le hm_max) (Finset.le_sup hm_mem)
      rw [h_sup_eq]
      have := h_kf_log_bd m hm_mem
      linarith
    · rw [Finset.not_nonempty_iff_eq_empty] at hS
      rw [hS, Finset.sup_empty]; simp
      have h_div_ge_one : (1 : ℝ) ≤ Real.log R / Real.log 2 := by
        rw [le_div_iff₀ hlog2_pos]; linarith
      linarith
  have h_Kmax_le_logR : (K_max : ℝ) ≤ Real.log R / Real.log 2 := by
    rw [hKmax_def]; push_cast; linarith
  have h_hi_bound :
      (∑ ρ ∈ S_hi, (lOrderNat χ ρ.val : ℝ) / ‖ρ.val‖) ≤
      ∑ k ∈ Finset.range K_max, 2 * C₃ * ((k : ℝ) + 2) * Real.log 2 := by
    have h_per_elem : ∀ ρ ∈ S_hi,
        (lOrderNat χ ρ.val : ℝ) / ‖ρ.val‖ ≤
        (lOrderNat χ ρ.val : ℝ) / (2 : ℝ) ^ (kf ρ + 1) := by
      intro ρ hρ
      have h_pow_pos : (0 : ℝ) < (2 : ℝ) ^ (kf ρ + 1) := pow_pos (by norm_num) _
      exact div_le_div_of_nonneg_left (by positivity) h_pow_pos (h_norm_ge ρ hρ)
    calc (∑ ρ ∈ S_hi, (lOrderNat χ ρ.val : ℝ) / ‖ρ.val‖)
        ≤ ∑ ρ ∈ S_hi, (lOrderNat χ ρ.val : ℝ) / (2 : ℝ) ^ (kf ρ + 1) :=
          Finset.sum_le_sum h_per_elem
      _ = ∑ k ∈ Finset.range K_max,
            ∑ ρ ∈ S_hi.filter (fun ρ => kf ρ = k),
              (lOrderNat χ ρ.val : ℝ) / (2 : ℝ) ^ (kf ρ + 1) := by
          rw [← Finset.sum_fiberwise_of_maps_to
            (t := Finset.range K_max) (g := kf)
            (f := fun ρ => (lOrderNat χ ρ.val : ℝ) / (2 : ℝ) ^ (kf ρ + 1))]
          intro ρ hρ
          exact Finset.mem_range.mpr (h_kf_lt ρ hρ)
      _ = ∑ k ∈ Finset.range K_max,
            (∑ ρ ∈ S_hi.filter (fun ρ => kf ρ = k),
                (lOrderNat χ ρ.val : ℝ)) / (2 : ℝ) ^ (k + 1) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro ρ hρ
          simp only [Finset.mem_filter] at hρ
          rw [hρ.2]
      _ ≤ ∑ k ∈ Finset.range K_max,
            (C₃ * (2 : ℝ)^(k+2) * ((k+2 : ℝ) * Real.log 2)) / (2 : ℝ) ^ (k + 1) := by
          apply Finset.sum_le_sum
          intro k _
          have h_pow_pos : (0 : ℝ) < (2 : ℝ) ^ (k + 1) := pow_pos (by norm_num) _
          have h_shell_bd :
              (∑ ρ ∈ S_hi.filter (fun ρ => kf ρ = k), (lOrderNat χ ρ.val : ℝ)) ≤
                C₃ * (2 : ℝ)^(k+2) * ((k+2 : ℝ) * Real.log 2) := by
            by_cases h_empty : (S_hi.filter (fun ρ => kf ρ = k)).Nonempty
            · obtain ⟨ρ₀, hρ₀⟩ := h_empty
              simp only [Finset.mem_filter] at hρ₀
              have hR0_le : R₀_step3 ≤ (2:ℝ)^(k+2) := by
                have := h_pow_gt_R0 ρ₀ hρ₀.1
                rw [hρ₀.2] at this
                exact this.le
              have h_norm_bd : ∀ ρ ∈ S_hi.filter (fun ρ => kf ρ = k),
                  ‖ρ.val‖ ≤ (2:ℝ)^(k+2) := by
                intro ρ hρ
                simp only [Finset.mem_filter] at hρ
                have := h_norm_lt ρ hρ.1
                rw [hρ.2] at this
                exact this.le
              have hApp := hBound ((2:ℝ)^(k+2)) hR0_le
                (S_hi.filter (fun ρ => kf ρ = k)) h_norm_bd
              have h_log_eq : Real.log ((2:ℝ)^(k+2)) = ((k+2 : ℕ) : ℝ) * Real.log 2 :=
                Real.log_pow _ _
              rw [h_log_eq] at hApp
              push_cast at hApp
              exact hApp
            · rw [Finset.not_nonempty_iff_eq_empty] at h_empty
              rw [h_empty]
              simp
              positivity
          apply div_le_div_of_nonneg_right h_shell_bd h_pow_pos.le
      _ = ∑ k ∈ Finset.range K_max, 2 * C₃ * ((k : ℝ) + 2) * Real.log 2 := by
          apply Finset.sum_congr rfl
          intro k _
          have h_pow_succ : (2:ℝ)^(k+2) = 2 * (2:ℝ)^(k+1) := by
            rw [pow_succ]; ring
          rw [h_pow_succ]
          have h_pow_pos : (0 : ℝ) < (2 : ℝ) ^ (k + 1) := pow_pos (by norm_num) _
          field_simp
  have h_sum_bd :
      (∑ k ∈ Finset.range K_max, 2 * C₃ * ((k : ℝ) + 2) * Real.log 2) ≤
      2 * C₃ * Real.log 2 * ((K_max : ℝ) + 2)^2 := by
    have h_gauss : (∑ k ∈ Finset.range K_max, (k : ℝ)) = (K_max * (K_max - 1) : ℝ) / 2 := by
      induction K_max with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        push_cast
        ring
    have h_sum_eq : (∑ k ∈ Finset.range K_max, 2 * C₃ * ((k : ℝ) + 2) * Real.log 2) =
        2 * C₃ * Real.log 2 * (∑ k ∈ Finset.range K_max, ((k : ℝ) + 2)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intros; ring
    have h_sum_shift : (∑ k ∈ Finset.range K_max, ((k : ℝ) + 2)) =
        (∑ k ∈ Finset.range K_max, (k : ℝ)) + 2 * K_max := by
      rw [Finset.sum_add_distrib]
      simp [Finset.sum_const, Finset.card_range]
      ring
    rw [h_sum_eq, h_sum_shift, h_gauss]
    apply mul_le_mul_of_nonneg_left
    · nlinarith [sq_nonneg ((K_max : ℝ)), sq_nonneg ((K_max : ℝ) + 2)]
    · positivity
  have h_Kmax_sq : ((K_max : ℝ) + 2)^2 ≤ 9 * (Real.log R)^2 / (Real.log 2)^2 := by
    have h_three_bd : (K_max : ℝ) + 2 ≤ 3 * Real.log R / Real.log 2 := by
      have h2_le : (2 : ℝ) ≤ 2 * Real.log R / Real.log 2 := by
        rw [le_div_iff₀ hlog2_pos]; linarith
      have h_sum : Real.log R / Real.log 2 + 2 * Real.log R / Real.log 2 =
          3 * Real.log R / Real.log 2 := by
        field_simp; ring
      linarith [h_Kmax_le_logR]
    have h_rhs_nn : 0 ≤ 3 * Real.log R / Real.log 2 := by positivity
    have h_lhs_nn : 0 ≤ (K_max : ℝ) + 2 := by positivity
    have hK_sq : ((K_max : ℝ) + 2)^2 ≤ (3 * Real.log R / Real.log 2)^2 := by
      apply sq_le_sq' _ h_three_bd
      linarith
    have h_sq_eq : (3 * Real.log R / Real.log 2)^2 = 9 * (Real.log R)^2 / (Real.log 2)^2 := by
      field_simp; ring
    linarith
  have h_Mlow_bd : M_low ≤ M_low / (Real.log 2)^2 * (Real.log R)^2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have h_sq_le : (Real.log 2)^2 ≤ (Real.log R)^2 :=
      pow_le_pow_left₀ hlog2_pos.le hR_log_ge_log2 _
    have : M_low * (Real.log 2)^2 ≤ M_low * (Real.log R)^2 :=
      mul_le_mul_of_nonneg_left h_sq_le hM_low_nn
    linarith
  have h_hi_total : (∑ ρ ∈ S_hi, (lOrderNat χ ρ.val : ℝ) / ‖ρ.val‖) ≤
      18 * C₃ / Real.log 2 * (Real.log R)^2 := by
    have h1 : 2 * C₃ * Real.log 2 * ((K_max : ℝ) + 2)^2 ≤
        2 * C₃ * Real.log 2 * (9 * (Real.log R)^2 / (Real.log 2)^2) :=
      mul_le_mul_of_nonneg_left h_Kmax_sq (by positivity)
    have h2 : 2 * C₃ * Real.log 2 * (9 * (Real.log R)^2 / (Real.log 2)^2) =
        18 * C₃ / Real.log 2 * (Real.log R)^2 := by
      field_simp; ring
    linarith [h_hi_bound, h_sum_bd]
  linarith [h_lo_bound, h_hi_total, h_Mlow_bd]

end DirichletLHadamard
