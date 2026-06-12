import RequestProject.DirichletLGrowthComplete
import RequestProject.XiProduct

/-!
# Jensen at `0` for `Λ_χ` and the zero-count bound

Mirrors the ζ apparatus (`xi_jensen_at_zero`, `xi_weighted_zero_count_disk_bound`) for the completed
Dirichlet `L`. The one new ingredient is `Λ_χ(0) ≠ 0`: `rootNumber ≠ 0` (else the FE forces
`Λ_χ(2) = 0`, contradicting `completedLFunction_two_ne_zero`), then the FE at `s = 1` writes `Λ_χ(0)`
as a product of nonzero factors. Then `MeromorphicOn.circleAverage_log_norm` (mathlib) specializes
cleanly (`divisor(0) = 0`, trailing coeff `= Λ_χ(0)`).
-/

open Complex

namespace DirichletLHadamard

variable {N : ℕ} [NeZero N]

/-- **`rootNumber ≠ 0`** (primitive `χ ≠ 1`). If it were `0`, the FE at `s = −1` gives `Λ_χ(2) = 0`. -/
theorem rootNumber_ne_zero {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) :
    χ.rootNumber ≠ 0 := by
  intro hrn
  have h := hχp.completedLFunction_one_sub (-1)
  rw [show (1 : ℂ) - (-1) = 2 by ring, hrn] at h
  simp only [mul_zero, zero_mul] at h
  exact completedLFunction_two_ne_zero hχ h

/-- **`Λ_χ(0) ≠ 0`** (primitive `χ ≠ 1`), via the FE at `s = 1`. -/
theorem completedLFunction_zero_ne_zero {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hχp : χ.IsPrimitive) : DirichletCharacter.completedLFunction χ 0 ≠ 0 := by
  have hχinv : χ⁻¹ ≠ 1 := fun h => hχ (inv_eq_one.mp h)
  have h := hχp.completedLFunction_one_sub 1
  rw [show (1 : ℂ) - 1 = 0 by ring] at h
  rw [h]
  have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  have hNpow : (N : ℂ) ^ ((1 : ℂ) - 1 / 2) ≠ 0 := by
    intro hc; rw [Complex.cpow_eq_zero_iff] at hc; exact hNne hc.1
  have hΛinv1 : DirichletCharacter.completedLFunction χ⁻¹ 1 ≠ 0 := by
    have hrel := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ⁻¹ 1 (Or.inl one_ne_zero)
    have hLne : DirichletCharacter.LFunction χ⁻¹ 1 ≠ 0 :=
      DirichletCharacter.LFunction_ne_zero_of_one_le_re χ⁻¹ (Or.inl hχinv) (by norm_num)
    intro hc; rw [hc, zero_div] at hrel; exact hLne hrel
  exact mul_ne_zero (mul_ne_zero hNpow (rootNumber_ne_zero hχ hχp)) hΛinv1

/-- **Jensen at `0` for `Λ_χ`** — specialization of `MeromorphicOn.circleAverage_log_norm`. -/
theorem completedL_jensen_at_zero {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (hχp : χ.IsPrimitive)
    (R : ℝ) (hR : 0 < R) :
    Real.circleAverage (fun s => Real.log ‖DirichletCharacter.completedLFunction χ s‖) 0 R
      = ∑ᶠ u, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                (Metric.closedBall (0 : ℂ) |R|)) u * Real.log (R * ‖u‖⁻¹)
        + Real.log ‖DirichletCharacter.completedLFunction χ 0‖ := by
  have hR' : R ≠ 0 := hR.ne'
  have hAnal : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall (0 : ℂ) |R|) := fun z _ => completedLFunction_analyticAt hχ z
  have hMero : MeromorphicOn (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall (0 : ℂ) |R|) := hAnal.meromorphicOn
  have hJensen := MeromorphicOn.circleAverage_log_norm hR' hMero
  have h0_mem : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) |R| := by
    simp [Metric.closedBall, abs_of_pos hR, hR.le]
  have hΛ0_analytic : AnalyticAt ℂ (DirichletCharacter.completedLFunction χ) 0 :=
    completedLFunction_analyticAt hχ 0
  have hΛ0ne := completedLFunction_zero_ne_zero hχ hχp
  have hDiv0 : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall (0 : ℂ) |R|)) 0 = 0 := by
    rw [MeromorphicOn.divisor_apply hMero h0_mem]
    have hAnalOrd : analyticOrderAt (DirichletCharacter.completedLFunction χ) 0 = 0 := by
      rw [analyticOrderAt_eq_zero]; right; exact hΛ0ne
    rw [hΛ0_analytic.meromorphicOrderAt_eq, hAnalOrd]; rfl
  have hTrail : meromorphicTrailingCoeffAt (DirichletCharacter.completedLFunction χ) 0
      = DirichletCharacter.completedLFunction χ 0 :=
    hΛ0_analytic.meromorphicTrailingCoeffAt_of_ne_zero hΛ0ne
  rw [hJensen, hDiv0, hTrail]
  push_cast
  simp only [zero_sub, norm_neg]
  ring_nf

/-- **Jensen at any non-vanishing center for `Λ_χ`** — the general-center payment identity: the
    boundary circle-average of `log ‖Λ_χ‖` equals the sum of the modes inside, each priced
    `ord · log (R/dist)`, plus the ground value `log ‖Λ_χ(c)‖`. -/
theorem completedL_jensen_at_center {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    {c : ℂ} (hc : DirichletCharacter.completedLFunction χ c ≠ 0)
    (R : ℝ) (hR : 0 < R) :
    Real.circleAverage (fun s => Real.log ‖DirichletCharacter.completedLFunction χ s‖) c R
      = ∑ᶠ u, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                (Metric.closedBall c |R|)) u * Real.log (R * ‖c - u‖⁻¹)
        + Real.log ‖DirichletCharacter.completedLFunction χ c‖ := by
  have hR' : R ≠ 0 := hR.ne'
  have hAnal : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall c |R|) := fun z _ => completedLFunction_analyticAt hχ z
  have hMero : MeromorphicOn (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall c |R|) := hAnal.meromorphicOn
  have hJensen := MeromorphicOn.circleAverage_log_norm hR' hMero
  have hc_mem : c ∈ Metric.closedBall c |R| := by
    simp [Metric.mem_closedBall]
  have hΛc_analytic : AnalyticAt ℂ (DirichletCharacter.completedLFunction χ) c :=
    completedLFunction_analyticAt hχ c
  have hDiv0 : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall c |R|)) c = 0 := by
    rw [MeromorphicOn.divisor_apply hMero hc_mem]
    have hAnalOrd : analyticOrderAt (DirichletCharacter.completedLFunction χ) c = 0 := by
      rw [analyticOrderAt_eq_zero]
      right
      exact hc
    rw [hΛc_analytic.meromorphicOrderAt_eq, hAnalOrd]
    rfl
  have hTrail : meromorphicTrailingCoeffAt (DirichletCharacter.completedLFunction χ) c
      = DirichletCharacter.completedLFunction χ c :=
    hΛc_analytic.meromorphicTrailingCoeffAt_of_ne_zero hc
  rw [hJensen, hDiv0, hTrail]
  push_cast
  ring_nf

/-- **divisor ≥ 1 at a `Λ_χ`-zero.** -/
theorem completedL_divisor_ge_one_of_zero {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    {CB : Set ℂ} (hMero : MeromorphicOn (DirichletCharacter.completedLFunction χ) CB)
    (ρ : ℂ) (hρ : ρ ∈ CB) (hρ_zero : DirichletCharacter.completedLFunction χ ρ = 0) :
    (1 : ℤ) ≤ MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) CB ρ := by
  have hAnalρ : AnalyticAt ℂ (DirichletCharacter.completedLFunction χ) ρ :=
    completedLFunction_analyticAt hχ ρ
  have hOrd_ne_zero : analyticOrderAt (DirichletCharacter.completedLFunction χ) ρ ≠ 0 := by
    rw [analyticOrderAt_ne_zero]; exact ⟨hAnalρ, hρ_zero⟩
  have hOrd_ne_top : analyticOrderAt (DirichletCharacter.completedLFunction χ) ρ ≠ ⊤ :=
    fun h => completedLFunction_not_eventuallyEq_zero hχ (analyticOrderAt_eq_top.mp h)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℕ∞) = analyticOrderAt (DirichletCharacter.completedLFunction χ) ρ :=
    ENat.ne_top_iff_exists.mp hOrd_ne_top
  have hn_ge : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (fun h => hOrd_ne_zero (by rw [← hn, h]; rfl))
  rw [MeromorphicOn.divisor_apply hMero hρ, hAnalρ.meromorphicOrderAt_eq, ← hn]
  simp; exact hn_ge

/-- **Multiplicity-weighted zero count in a disk** for `Λ_χ`: `Σ_{ρ ∈ S, ‖ρ‖ ≤ R} ord(ρ) ≤ C·R·log R`.
    Jensen-at-`2R` + the order-1 growth, mirroring `xi_weighted_zero_count_disk_bound`. -/
theorem completedL_weighted_zero_count_disk_bound {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hχp : χ.IsPrimitive) :
    ∃ C > (0 : ℝ), ∃ R₀ > (0 : ℝ), ∀ R, R₀ ≤ R →
      ∀ (S : Finset {ρ : ℂ // ρ ∈ GRHSpectral.NontrivialZeros χ}),
        (∀ ρ ∈ S, ‖ρ.val‖ ≤ R) →
        ((∑ ρ ∈ S, (lOrderNat χ ρ.val : ℝ)) ≤ C * R * Real.log R) := by
  obtain ⟨C1, hC1, R1, hR1, hBound1⟩ := completedL_order_one_log_bound hχ hχp
  set c0 : ℝ := Real.log ‖DirichletCharacter.completedLFunction χ 0‖ with hc0
  refine ⟨(4 * C1 + |c0| + 4) / Real.log 2, by positivity, max R1 (Real.exp 1), by positivity, ?_⟩
  intro R hR S hS_bd
  have hR_R1 : R1 ≤ R := le_trans (le_max_left _ _) hR
  have hR_e : Real.exp 1 ≤ R := le_trans (le_max_right _ _) hR
  have hR_pos : 0 < R := lt_of_lt_of_le (Real.exp_pos 1) hR_e
  have hR_ge_one : (1 : ℝ) ≤ R := le_trans (by have := Real.exp_one_gt_d9; linarith) hR_e
  have hR_log_ge_1 : (1 : ℝ) ≤ Real.log R := by
    have := Real.log_le_log (Real.exp_pos 1) hR_e; rwa [Real.log_exp] at this
  have hR_log_nn : 0 ≤ Real.log R := le_trans zero_le_one hR_log_ge_1
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2R_pos : (0 : ℝ) < 2 * R := by linarith
  have h2R_R1 : R1 ≤ 2 * R := by linarith
  have habs2R : |(2 : ℝ) * R| = 2 * R := abs_of_pos h2R_pos
  set CB : Set ℂ := Metric.closedBall (0 : ℂ) (|(2 : ℝ) * R|) with hCB_def
  have hAnal : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) CB :=
    fun z _ => completedLFunction_analyticAt hχ z
  have hMero : MeromorphicOn (DirichletCharacter.completedLFunction χ) CB := hAnal.meromorphicOn
  have hS_sub_CB : ∀ ρ ∈ S, ρ.val ∈ CB := by
    intro ρ hρ
    rw [hCB_def, Metric.mem_closedBall, dist_zero_right, habs2R]; linarith [hS_bd ρ hρ]
  have h_divisor_eq_order : ∀ ρ : {ρ : ℂ // ρ ∈ GRHSpectral.NontrivialZeros χ}, ρ.val ∈ CB →
      (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) CB ρ.val : ℝ)
        = lOrderNat χ ρ.val := by
    intro ρ hρ_cb
    have hAnalρ : AnalyticAt ℂ (DirichletCharacter.completedLFunction χ) ρ.val :=
      completedLFunction_analyticAt hχ ρ.val
    have h_ord_ne_top : analyticOrderAt (DirichletCharacter.completedLFunction χ) ρ.val ≠ ⊤ :=
      fun h => completedLFunction_not_eventuallyEq_zero hχ (analyticOrderAt_eq_top.mp h)
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℕ∞) = analyticOrderAt (DirichletCharacter.completedLFunction χ) ρ.val :=
      ENat.ne_top_iff_exists.mp h_ord_ne_top
    have h_nat_eq : lOrderNat χ ρ.val = n := by
      unfold lOrderNat analyticOrderNatAt; rw [← hn]; simp
    rw [MeromorphicOn.divisor_apply hMero hρ_cb, hAnalρ.meromorphicOrderAt_eq, ← hn]
    simp [h_nat_eq]
  have h_S_sum_eq_divisor :
      (∑ ρ ∈ S, (lOrderNat χ ρ.val : ℝ))
        = ∑ ρ ∈ S, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) CB ρ.val : ℝ) := by
    apply Finset.sum_congr rfl
    intro ρ hρ; exact (h_divisor_eq_order ρ (hS_sub_CB ρ hρ)).symm
  rw [h_S_sum_eq_divisor]
  -- Jensen at 2R
  have hJensen := completedL_jensen_at_zero hχ hχp (2 * R) h2R_pos
  have hAnalSph : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
      (Metric.sphere (0 : ℂ) (|2 * R|)) := fun z _ => completedLFunction_analyticAt hχ z
  have hCI : CircleIntegrable
      (fun s => Real.log ‖DirichletCharacter.completedLFunction χ s‖) 0 (2 * R) :=
    circleIntegrable_log_norm_meromorphicOn hAnalSph.meromorphicOn
  have hCircAvg_le :
      Real.circleAverage (fun s => Real.log ‖DirichletCharacter.completedLFunction χ s‖) 0 (2 * R)
        ≤ C1 * (2 * R) * Real.log (2 * R) := by
    apply Real.circleAverage_mono_on_of_le_circle hCI
    intro s hs
    rw [Metric.mem_sphere, dist_zero_right, habs2R] at hs
    have h_log_le : Real.log ‖DirichletCharacter.completedLFunction χ s‖
        ≤ Real.log (‖DirichletCharacter.completedLFunction χ s‖ + 1) := by
      rcases eq_or_lt_of_le (norm_nonneg (DirichletCharacter.completedLFunction χ s)) with h0 | hpos
      · rw [← h0, Real.log_zero]
        exact Real.log_nonneg (by linarith [norm_nonneg (DirichletCharacter.completedLFunction χ s)])
      · exact Real.log_le_log hpos (by linarith)
    have h_bd := hBound1 (2 * R) h2R_R1 s (le_of_eq hs)
    linarith
  -- full finsum ≤ growth − c0
  have h_full_finsum_bd :
      (∑ᶠ u, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) CB u : ℝ)
            * Real.log (2 * R * ‖u‖⁻¹))
        ≤ C1 * (2 * R) * Real.log (2 * R) - c0 := by
    have h_eq : (∑ᶠ u, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) CB u : ℝ)
        * Real.log (2 * R * ‖u‖⁻¹))
        = Real.circleAverage (fun s => Real.log ‖DirichletCharacter.completedLFunction χ s‖) 0 (2 * R)
          - c0 := by rw [hc0, hJensen]; ring
    rw [h_eq]; linarith
  have hD_nn : ∀ u, 0 ≤ MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) CB u :=
    fun u => MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAnal u
  have h_term_nn : ∀ u, 0 ≤ (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) CB u : ℝ)
      * Real.log (2 * R * ‖u‖⁻¹) := by
    intro u
    by_cases hu : u ∈ CB
    · rw [hCB_def, Metric.mem_closedBall, dist_zero_right, habs2R] at hu
      by_cases hu0 : u = 0
      · simp [hu0, Real.log_zero]
      · have h_norm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
        have hlog_nn : 0 ≤ Real.log (2 * R * ‖u‖⁻¹) := by
          apply Real.log_nonneg
          rw [show (2 * R * ‖u‖⁻¹) = (2 * R) / ‖u‖ from by ring, le_div_iff₀ h_norm_pos]; linarith
        exact mul_nonneg (by exact_mod_cast hD_nn u) hlog_nn
    · have hD0 := (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) CB).apply_eq_zero_of_notMem hu
      simp [hD0]
  have h_S_lower :
      (∑ ρ ∈ S, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) CB ρ.val : ℝ))
          * Real.log 2 ≤
      ∑ ρ ∈ S, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) CB ρ.val : ℝ)
        * Real.log (2 * R * ‖ρ.val‖⁻¹) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro ρ hρ
    have hρ_le_R : ‖ρ.val‖ ≤ R := hS_bd ρ hρ
    have hρ_ne : ρ.val ≠ 0 := by
      intro heq; have hre : (0 : ℝ) < ρ.val.re := ρ.property.1; rw [heq] at hre; simp at hre
    have h_norm_pos : 0 < ‖ρ.val‖ := norm_pos_iff.mpr hρ_ne
    have hlog_ge : Real.log 2 ≤ Real.log (2 * R * ‖ρ.val‖⁻¹) := by
      apply Real.log_le_log (by norm_num)
      rw [show (2 * R * ‖ρ.val‖⁻¹) = (2 * R) / ‖ρ.val‖ from by ring, le_div_iff₀ h_norm_pos]
      nlinarith [hρ_le_R, hR_ge_one]
    exact mul_le_mul_of_nonneg_left hlog_ge (by exact_mod_cast hD_nn ρ.val)
  have h_S_to_finsum :
      (∑ ρ ∈ S, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) CB ρ.val : ℝ)
        * Real.log (2 * R * ‖ρ.val‖⁻¹))
        ≤ ∑ᶠ u, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) CB u : ℝ)
            * Real.log (2 * R * ‖u‖⁻¹) := by
    have h_image : (∑ ρ ∈ S, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) CB ρ.val : ℝ)
          * Real.log (2 * R * ‖ρ.val‖⁻¹))
        = ∑ u ∈ S.image Subtype.val,
            (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) CB u : ℝ)
              * Real.log (2 * R * ‖u‖⁻¹) := by
      rw [Finset.sum_image (fun _ _ _ _ h => Subtype.val_injective h)]
    rw [h_image]
    have h_fs : (Function.support fun u =>
        (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) CB u : ℝ)
          * Real.log (2 * R * ‖u‖⁻¹)).Finite := by
      apply ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) CB).finiteSupport
        (isCompact_closedBall 0 _)).subset
      intro u hu
      simp only [Function.mem_support] at hu ⊢
      intro hd; apply hu; rw [hd]; simp
    rw [finsum_eq_sum _ h_fs]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro u hu
      simp only [Set.Finite.mem_toFinset, Function.mem_support]
      rw [Finset.mem_image] at hu
      obtain ⟨ρ, hρ, rfl⟩ := hu
      have hρ_zero : DirichletCharacter.completedLFunction χ ρ.val = 0 :=
        completedLFunction_eq_zero_of_mem ρ.property
      have h_div_ge_1 : (1 : ℤ) ≤
          MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) CB ρ.val :=
        completedL_divisor_ge_one_of_zero hχ hMero ρ.val (hS_sub_CB ρ hρ) hρ_zero
      intro h_prod_zero
      rcases mul_eq_zero.mp h_prod_zero with hd | hl
      · have hd' : MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) CB ρ.val = 0 := by
          exact_mod_cast hd
        rw [hd'] at h_div_ge_1; norm_num at h_div_ge_1
      · have hρ_le_R : ‖ρ.val‖ ≤ R := hS_bd ρ hρ
        have hρ_ne : ρ.val ≠ 0 := by
          intro heq; have := ρ.property.1; rw [heq] at this; simp at this
        have h_norm_pos : 0 < ‖ρ.val‖ := norm_pos_iff.mpr hρ_ne
        have hlpos : Real.log (2 * R * ‖ρ.val‖⁻¹) > 0 := by
          apply Real.log_pos
          rw [show (2 * R * ‖ρ.val‖⁻¹) = (2 * R) / ‖ρ.val‖ from by ring, lt_div_iff₀ h_norm_pos,
            one_mul]; linarith
        linarith
    · intros; exact h_term_nn _
  have h_chain :
      (∑ ρ ∈ S, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) CB ρ.val : ℝ))
          * Real.log 2 ≤ C1 * (2 * R) * Real.log (2 * R) - c0 :=
    le_trans h_S_lower (le_trans h_S_to_finsum h_full_finsum_bd)
  have h_divide :
      (∑ ρ ∈ S, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) CB ρ.val : ℝ))
        ≤ (C1 * (2 * R) * Real.log (2 * R) - c0) / Real.log 2 :=
    (le_div_iff₀ hlog2_pos).mpr h_chain
  refine le_trans h_divide ?_
  have h_log_2R_le : Real.log (2 * R) ≤ 2 * Real.log R := by
    rw [Real.log_mul (by norm_num) hR_pos.ne']
    have : Real.log 2 ≤ Real.log R := Real.log_le_log (by norm_num)
      (le_trans (by have := Real.exp_one_gt_d9; linarith) hR_e)
    linarith
  have hXRR : (1 : ℝ) ≤ R * Real.log R := by nlinarith [hR_ge_one, hR_log_ge_1]
  have h1 : C1 * (2 * R) * Real.log (2 * R) ≤ 4 * C1 * (R * Real.log R) := by
    calc C1 * (2 * R) * Real.log (2 * R)
        ≤ C1 * (2 * R) * (2 * Real.log R) := by
          apply mul_le_mul_of_nonneg_left h_log_2R_le; positivity
      _ = 4 * C1 * (R * Real.log R) := by ring
  have h2 : -c0 ≤ |c0| * (R * Real.log R) := by
    nlinarith [neg_le_abs c0, abs_nonneg c0, hXRR]
  have h_num : C1 * (2 * R) * Real.log (2 * R) - c0 ≤ (4 * C1 + |c0| + 4) * R * Real.log R := by
    nlinarith [h1, h2, hXRR, hC1]
  calc (C1 * (2 * R) * Real.log (2 * R) - c0) / Real.log 2
      ≤ ((4 * C1 + |c0| + 4) * R * Real.log R) / Real.log 2 :=
        (div_le_div_iff_of_pos_right hlog2_pos).mpr h_num
    _ = (4 * C1 + |c0| + 4) / Real.log 2 * R * Real.log R := by ring

/-- `Λ_χ`-zeros in a closed ball are finite (subset of the divisor's finite support). -/
theorem completedLFunction_zeros_finite_in_closedBall {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (R : ℝ) :
    (Metric.closedBall (0 : ℂ) R ∩ {z | DirichletCharacter.completedLFunction χ z = 0}).Finite := by
  have hMero : MeromorphicOn (DirichletCharacter.completedLFunction χ) (Metric.closedBall (0 : ℂ) R) :=
    (show AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) (Metric.closedBall (0 : ℂ) R)
      from fun z _ => completedLFunction_analyticAt hχ z).meromorphicOn
  have hDiv_fin := (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
    (Metric.closedBall (0 : ℂ) R)).finiteSupport (isCompact_closedBall 0 R)
  apply hDiv_fin.subset
  intro z hz
  have hz_ball : z ∈ Metric.closedBall (0 : ℂ) R := hz.1
  have hz_zero : DirichletCharacter.completedLFunction χ z = 0 := hz.2
  have hAnal : AnalyticAt ℂ (DirichletCharacter.completedLFunction χ) z :=
    completedLFunction_analyticAt hχ z
  have hOrd_ne_zero : analyticOrderAt (DirichletCharacter.completedLFunction χ) z ≠ 0 := by
    rw [analyticOrderAt_ne_zero]; exact ⟨hAnal, hz_zero⟩
  have hOrd_ne_top : analyticOrderAt (DirichletCharacter.completedLFunction χ) z ≠ ⊤ :=
    fun h => completedLFunction_not_eventuallyEq_zero hχ (analyticOrderAt_eq_top.mp h)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℕ∞) = analyticOrderAt (DirichletCharacter.completedLFunction χ) z :=
    ENat.ne_top_iff_exists.mp hOrd_ne_top
  have hn_ne : n ≠ 0 := fun h => hOrd_ne_zero (by rw [← hn, h]; rfl)
  simp only [Function.mem_support]
  rw [MeromorphicOn.divisor_apply hMero hz_ball, hAnal.meromorphicOrderAt_eq, ← hn]
  simp; exact hn_ne

/-- `NontrivialZeros χ ∩ closedBall 0 R` is finite. -/
theorem NontrivialZeros_inter_closedBall_finite {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (R : ℝ) :
    (GRHSpectral.NontrivialZeros χ ∩ Metric.closedBall (0 : ℂ) R).Finite := by
  apply Set.Finite.subset (completedLFunction_zeros_finite_in_closedBall hχ R)
  intro ρ hρ
  exact ⟨hρ.2, completedLFunction_eq_zero_of_mem hρ.1⟩

/-- **Dyadic summability** `Σ_ρ ord(ρ)/‖ρ‖² < ∞` over the nontrivial zeros of `Λ_χ`.
The zero-count bound `N(R) ≤ C·R·log R` (`completedL_weighted_zero_count_disk_bound`), summed
over dyadic shells `2^k ≤ ‖ρ‖ < 2^{k+1}`, gives a `(k+1)/2^k` majorant — summable. Together with
finitely many zeros in `‖ρ‖ < 2^{N+1}` (`NontrivialZeros_inter_closedBall_finite`), the whole series
converges. This is the input to the Weierstrass product / Hadamard factorization. -/
theorem summable_lOrderNat_div_norm_sq_nontrivialZeros {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hχp : χ.IsPrimitive) :
    Summable (fun ρ : {ρ : ℂ // ρ ∈ GRHSpectral.NontrivialZeros χ} =>
      (lOrderNat χ ρ.val : ℝ) / ‖ρ.val‖ ^ 2) := by
  obtain ⟨C₃, hC₃, R₀_step3, hR₀_step3, hBound_step3⟩ :=
    completedL_weighted_zero_count_disk_bound hχ hχp
  set R_th : ℝ := max R₀_step3 2 with hRth_def
  have hRth_ge_R₀ : R₀_step3 ≤ R_th := le_max_left _ _
  have hRth_ge_two : (2 : ℝ) ≤ R_th := le_max_right _ _
  obtain ⟨Nd, hNd⟩ : ∃ Nd : ℕ, R_th ≤ (2 : ℝ) ^ Nd := by
    rcases pow_unbounded_of_one_lt R_th (by norm_num : (1:ℝ) < 2) with ⟨Nd, hNd⟩
    exact ⟨Nd, le_of_lt hNd⟩
  set M_lo : ℝ :=
    (NontrivialZeros_inter_closedBall_finite hχ 2).toFinset.sum
      (fun ρ => (lOrderNat χ ρ : ℝ) / ‖ρ‖ ^ 2) with hM_lo_def
  set M_mid : ℝ :=
    (NontrivialZeros_inter_closedBall_finite hχ ((2 : ℝ) ^ (Nd + 1))).toFinset.sum
      (fun ρ => (lOrderNat χ ρ : ℝ) / ‖ρ‖ ^ 2) with hM_mid_def
  set C_tail : ℝ := 2 * C₃ with hC_tail_def
  refine summable_of_sum_le
    (fun ρ => div_nonneg (by positivity) (by positivity))
    (c := M_lo + M_mid + C_tail * ∑' k : ℕ, (↑k + 1 : ℝ) / 2 ^ k) ?_
  intro u
  rw [← Finset.sum_filter_add_sum_filter_not u (fun ρ => ‖ρ.val‖ < 2)]
  have h_lo_bound :
      (∑ ρ ∈ u.filter (fun ρ => ‖ρ.val‖ < 2),
        (lOrderNat χ ρ.val : ℝ) / ‖ρ.val‖ ^ 2) ≤ M_lo := by
    rw [hM_lo_def]
    rw [show (∑ ρ ∈ u.filter (fun ρ => ‖ρ.val‖ < 2),
          (lOrderNat χ ρ.val : ℝ) / ‖ρ.val‖ ^ 2) =
        ∑ ρ ∈ (u.filter (fun ρ => ‖ρ.val‖ < 2)).image Subtype.val,
            (lOrderNat χ ρ : ℝ) / ‖ρ‖ ^ 2 from ?_]
    swap
    · rw [Finset.sum_image]; intro x _ y _ h; exact Subtype.val_injective h
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro ρ hρ
      rcases Finset.mem_image.mp hρ with ⟨ρ', hρ'_in, hρ'_eq⟩
      simp only [Finset.mem_filter] at hρ'_in
      simp only [Set.Finite.mem_toFinset]
      refine ⟨?_, ?_⟩
      · subst hρ'_eq; exact ρ'.property
      · rw [Metric.mem_closedBall, dist_zero_right]; subst hρ'_eq; linarith [hρ'_in.2]
    · intros; positivity
  rw [← Finset.sum_filter_add_sum_filter_not (u.filter (fun ρ => ¬ ‖ρ.val‖ < 2))
    (fun ρ => ‖ρ.val‖ < (2 : ℝ) ^ (Nd + 1))]
  have h_mid_bound :
      (∑ ρ ∈ (u.filter (fun ρ => ¬ ‖ρ.val‖ < 2)).filter
            (fun ρ => ‖ρ.val‖ < (2 : ℝ) ^ (Nd + 1)),
        (lOrderNat χ ρ.val : ℝ) / ‖ρ.val‖ ^ 2) ≤ M_mid := by
    rw [hM_mid_def]
    rw [show (∑ ρ ∈ (u.filter (fun ρ => ¬ ‖ρ.val‖ < 2)).filter
            (fun ρ => ‖ρ.val‖ < (2 : ℝ) ^ (Nd + 1)),
            (lOrderNat χ ρ.val : ℝ) / ‖ρ.val‖ ^ 2) =
        ∑ ρ ∈ ((u.filter (fun ρ => ¬ ‖ρ.val‖ < 2)).filter
            (fun ρ => ‖ρ.val‖ < (2 : ℝ) ^ (Nd + 1))).image Subtype.val,
            (lOrderNat χ ρ : ℝ) / ‖ρ‖ ^ 2 from ?_]
    swap
    · rw [Finset.sum_image]; intro x _ y _ h; exact Subtype.val_injective h
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro ρ hρ
      rcases Finset.mem_image.mp hρ with ⟨ρ', hρ'_in, hρ'_eq⟩
      simp only [Finset.mem_filter] at hρ'_in
      simp only [Set.Finite.mem_toFinset]
      refine ⟨?_, ?_⟩
      · subst hρ'_eq; exact ρ'.property
      · rw [Metric.mem_closedBall, dist_zero_right]; subst hρ'_eq; linarith [hρ'_in.2]
    · intros; positivity
  have h_hi_bound :
      (∑ ρ ∈ (u.filter (fun ρ => ¬ ‖ρ.val‖ < 2)).filter
            (fun ρ => ¬ ‖ρ.val‖ < (2 : ℝ) ^ (Nd + 1)),
        (lOrderNat χ ρ.val : ℝ) / ‖ρ.val‖ ^ 2) ≤
      C_tail * ∑' k : ℕ, (↑k + 1 : ℝ) / 2 ^ k := by
    set S : Finset {ρ : ℂ // ρ ∈ GRHSpectral.NontrivialZeros χ} :=
      (u.filter (fun ρ => ¬ ‖ρ.val‖ < 2)).filter
        (fun ρ => ¬ ‖ρ.val‖ < (2 : ℝ) ^ (Nd + 1)) with hS_def
    have h_mem : ∀ ρ ∈ S, (2 : ℝ) ^ (Nd + 1) ≤ ‖ρ.val‖ := by
      intro ρ hρ; simp only [hS_def, Finset.mem_filter, not_lt] at hρ; exact hρ.2
    have h_one_le : ∀ ρ ∈ S, (1 : ℝ) ≤ ‖ρ.val‖ := by
      intro ρ hρ
      have hle := h_mem ρ hρ
      have h2N1_ge_one : (1 : ℝ) ≤ (2 : ℝ) ^ (Nd + 1) := one_le_pow₀ (by norm_num)
      linarith
    let kf : {ρ : ℂ // ρ ∈ GRHSpectral.NontrivialZeros χ} → ℕ := fun ρ =>
      if h : (1 : ℝ) ≤ ‖ρ.val‖
      then (exists_nat_pow_near h (by norm_num : (1:ℝ) < 2)).choose
      else 0
    have h_kf_prop :
        ∀ ρ ∈ S, (2 : ℝ) ^ kf ρ ≤ ‖ρ.val‖ ∧ ‖ρ.val‖ < (2 : ℝ) ^ (kf ρ + 1) := by
      intro ρ hρ
      have h := h_one_le ρ hρ
      simp only [kf, dif_pos h]
      exact (exists_nat_pow_near h (by norm_num : (1:ℝ) < 2)).choose_spec
    have h_kf_ge : ∀ ρ ∈ S, Nd + 1 ≤ kf ρ := by
      intro ρ hρ
      have ⟨_, h_lt⟩ := h_kf_prop ρ hρ
      have h_ge := h_mem ρ hρ
      have hlt_pow : (2 : ℝ) ^ (Nd + 1) < (2 : ℝ) ^ (kf ρ + 1) := lt_of_le_of_lt h_ge h_lt
      have := (pow_lt_pow_iff_right₀ (by norm_num : (1:ℝ) < 2)).mp hlt_pow
      omega
    set K_max : ℕ := S.sup kf + 1 with hKmax_def
    have h_kf_le : ∀ ρ ∈ S, kf ρ < K_max := by
      intro ρ hρ; have := Finset.le_sup (f := kf) hρ; omega
    have h_per_elem :
        ∀ ρ ∈ S,
          (lOrderNat χ ρ.val : ℝ) / ‖ρ.val‖ ^ 2 ≤
          (lOrderNat χ ρ.val : ℝ) / (2 : ℝ) ^ (2 * kf ρ) := by
      intro ρ hρ
      have ⟨h_pow_le, _⟩ := h_kf_prop ρ hρ
      have h_one := h_one_le ρ hρ
      have h_pos : (0 : ℝ) < ‖ρ.val‖ := by linarith
      have h_pow_pos : (0 : ℝ) < (2 : ℝ) ^ kf ρ := pow_pos (by norm_num) _
      have h_pow2k_pos : (0 : ℝ) < (2 : ℝ) ^ (2 * kf ρ) := pow_pos (by norm_num) _
      have h_pow2_le : (2 : ℝ) ^ (2 * kf ρ) ≤ ‖ρ.val‖ ^ 2 := by
        rw [show (2 * kf ρ) = (kf ρ) * 2 from by ring, pow_mul]
        exact pow_le_pow_left₀ h_pow_pos.le h_pow_le 2
      apply div_le_div_of_nonneg_left (by positivity) h_pow2k_pos h_pow2_le
    calc (∑ ρ ∈ S, (lOrderNat χ ρ.val : ℝ) / ‖ρ.val‖ ^ 2)
        ≤ ∑ ρ ∈ S, (lOrderNat χ ρ.val : ℝ) / (2 : ℝ) ^ (2 * kf ρ) :=
          Finset.sum_le_sum h_per_elem
      _ = ∑ k ∈ Finset.range K_max,
            ∑ ρ ∈ S.filter (fun ρ => kf ρ = k),
              (lOrderNat χ ρ.val : ℝ) / (2 : ℝ) ^ (2 * kf ρ) := by
          rw [← Finset.sum_fiberwise_of_maps_to
            (t := Finset.range K_max) (g := kf)
            (f := fun ρ => (lOrderNat χ ρ.val : ℝ) / (2 : ℝ) ^ (2 * kf ρ))]
          intro ρ hρ
          exact Finset.mem_range.mpr (h_kf_le ρ hρ)
      _ = ∑ k ∈ Finset.range K_max,
            (∑ ρ ∈ S.filter (fun ρ => kf ρ = k),
                (lOrderNat χ ρ.val : ℝ)) / (2 : ℝ) ^ (2 * k) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro ρ hρ
          simp only [Finset.mem_filter] at hρ
          rw [hρ.2]
      _ ≤ ∑ k ∈ Finset.range K_max,
            (if Nd + 1 ≤ k then C_tail * (k + 1 : ℝ) / 2 ^ k else 0) := by
          apply Finset.sum_le_sum
          intro k _
          by_cases hk_ge : Nd + 1 ≤ k
          · rw [if_pos hk_ge]
            have h_shell_bound :
                (∑ ρ ∈ S.filter (fun ρ => kf ρ = k), (lOrderNat χ ρ.val : ℝ)) ≤
                C₃ * (2 : ℝ) ^ (k + 1) * Real.log ((2 : ℝ) ^ (k + 1)) := by
              have hR_ge : R₀_step3 ≤ (2 : ℝ) ^ (k + 1) := by
                calc R₀_step3 ≤ R_th := hRth_ge_R₀
                  _ ≤ (2 : ℝ) ^ Nd := hNd
                  _ ≤ (2 : ℝ) ^ (k + 1) :=
                      pow_le_pow_right₀ (by norm_num) (by omega)
              apply hBound_step3 ((2 : ℝ) ^ (k + 1)) hR_ge
              intro ρ hρ
              simp only [Finset.mem_filter] at hρ
              have ⟨_, h_lt⟩ := h_kf_prop ρ hρ.1
              rw [hρ.2] at h_lt
              linarith
            have h_log_pow : Real.log ((2 : ℝ) ^ (k + 1)) = (k + 1 : ℝ) * Real.log 2 := by
              rw [Real.log_pow]; push_cast; ring
            have h_pow2k_pos : (0 : ℝ) < (2 : ℝ) ^ (2 * k) := pow_pos (by norm_num) _
            have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
            have hlog2_le_one : Real.log 2 ≤ 1 :=
              (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)).trans (by norm_num)
            calc (∑ ρ ∈ S.filter (fun ρ => kf ρ = k), (lOrderNat χ ρ.val : ℝ))
                    / (2 : ℝ) ^ (2 * k)
                ≤ (C₃ * (2 : ℝ) ^ (k + 1) * Real.log ((2 : ℝ) ^ (k + 1)))
                    / (2 : ℝ) ^ (2 * k) :=
                  div_le_div_of_nonneg_right h_shell_bound h_pow2k_pos.le
              _ ≤ C_tail * (k + 1 : ℝ) / 2 ^ k := by
                rw [h_log_pow, hC_tail_def]
                have h2pk1 : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by
                  rw [pow_succ]; ring
                have h22k : (2 : ℝ) ^ (2 * k) = ((2 : ℝ) ^ k) ^ 2 := by
                  rw [show (2 * k) = k * 2 from by ring, pow_mul]
                have hpk_pos : (0 : ℝ) < (2 : ℝ) ^ k := pow_pos (by norm_num) _
                rw [h2pk1, h22k]
                have h_numer : C₃ * (2 * (2:ℝ) ^ k) * ((↑k + 1) * Real.log 2) =
                    2 * C₃ * ((2:ℝ)^k) * (↑k + 1) * Real.log 2 := by ring
                rw [h_numer]
                have h_num_le : 2 * C₃ * ((2:ℝ)^k) * (↑k + 1) * Real.log 2 ≤
                    2 * C₃ * ((2:ℝ)^k) * (↑k + 1) := by
                  have h_nn : 0 ≤ 2 * C₃ * ((2:ℝ)^k) * (↑k + 1) := by positivity
                  nlinarith [hlog2_le_one, hlog2_pos]
                calc 2 * C₃ * ((2:ℝ)^k) * (↑k + 1) * Real.log 2 / ((2:ℝ)^k)^2
                    ≤ 2 * C₃ * ((2:ℝ)^k) * (↑k + 1) / ((2:ℝ)^k)^2 :=
                      div_le_div_of_nonneg_right h_num_le (by positivity)
                  _ = 2 * C₃ * (↑k + 1) / (2:ℝ)^k := by
                      field_simp
          · rw [if_neg hk_ge]
            have h_filter_empty : S.filter (fun ρ => kf ρ = k) = ∅ := by
              rw [Finset.filter_eq_empty_iff]
              intro ρ hρ heq
              have := h_kf_ge ρ hρ
              omega
            rw [h_filter_empty]
            simp
      _ ≤ ∑ k ∈ Finset.range K_max, C_tail * (k + 1 : ℝ) / 2 ^ k := by
          apply Finset.sum_le_sum
          intro k _
          by_cases hk_ge : Nd + 1 ≤ k
          · rw [if_pos hk_ge]
          · rw [if_neg hk_ge]
            have : 0 ≤ C_tail * (k + 1 : ℝ) / 2 ^ k := by rw [hC_tail_def]; positivity
            linarith
      _ ≤ C_tail * ∑' k : ℕ, ((k : ℝ) + 1) / 2 ^ k := by
          have h_sum_eq :
              (∑ k ∈ Finset.range K_max, C_tail * (k + 1 : ℝ) / 2 ^ k) =
              C_tail * ∑ k ∈ Finset.range K_max, ((k : ℝ) + 1) / 2 ^ k := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intros; ring
          rw [h_sum_eq]
          apply mul_le_mul_of_nonneg_left _ (by rw [hC_tail_def]; positivity)
          have h_summ := ZD.summable_nat_succ_div_two_pow
          have h_nn : ∀ k : ℕ, 0 ≤ ((k : ℝ) + 1) / 2 ^ k := fun k => by positivity
          exact Summable.sum_le_tsum _ (fun i _ => h_nn i) h_summ
  linarith

end DirichletLHadamard

#print axioms DirichletLHadamard.NontrivialZeros_inter_closedBall_finite
#print axioms DirichletLHadamard.summable_lOrderNat_div_norm_sq_nontrivialZeros
#print axioms DirichletLHadamard.rootNumber_ne_zero
#print axioms DirichletLHadamard.completedLFunction_zero_ne_zero
#print axioms DirichletLHadamard.completedL_jensen_at_zero
