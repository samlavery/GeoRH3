import Mathlib

/-!
# Generic constancy of `logDeriv` from order-1 mean-type growth

Function-agnostic extraction of the Borel–Carathéodory / Cauchy argument used in
`WeilHadamardOpenPatch.logDeriv_xiOverP_const_of_growth`: for **any** entire, nowhere-zero
`g : ℂ → ℂ` with order-1 mean-type growth

  `‖g z‖ ≤ exp (C·‖z‖·log(‖z‖+2) + D)`,

the logarithmic derivative `logDeriv g` is **globally constant**. Classical Hadamard constancy: the
entire zero-free `g = exp(h)` has `Re h` mean-type, so `h''≡0` (BC + Cauchy at order 2), i.e. `h` is
affine and `logDeriv g = h'` is constant. Uses only Mathlib (`Complex.borelCaratheodory_zero`,
`Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`, `Differentiable.isExactOn_univ`).

This is the *last* step of the Dirichlet-`L` Hadamard constancy: applied to `Λ_χ / LProductMult χ`,
it yields the constancy `logDeriv Λ_χ − logDeriv(LProductMult χ) = const` once the quotient growth is
in hand.
-/

open Complex Filter Topology

namespace HadamardConst

/-- The mean-type Cauchy majorant `32(1+A+B R log(R+2))/(R−nz)²` tends to `0` as `R → ∞`. -/
private theorem tendsto_meanType_ratio_zero {A B nz : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hnz : 0 ≤ nz) :
    Filter.Tendsto
      (fun R : ℝ => 32 * (1 + A + B * R * Real.log (R + 2)) / (R - nz) ^ 2)
      Filter.atTop (nhds 0) := by
  have h_maj_tend : Filter.Tendsto
      (fun R : ℝ => 128 * (1 + A) / R^2 + 256 * B * Real.log R / R)
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun R : ℝ => 128 * (1 + A) / R^2)
        Filter.atTop (nhds 0) := by
      have hone : Filter.Tendsto (fun R : ℝ => 1 / R^2) Filter.atTop (nhds 0) := by
        have h := @tendsto_pow_neg_atTop ℝ _ _ _ _ _ 2 (by norm_num)
        refine h.congr' ?_
        filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with R _
        rw [zpow_neg, zpow_natCast, inv_eq_one_div]
      have := hone.const_mul (128 * (1 + A))
      simp at this
      refine this.congr' ?_
      filter_upwards with R; ring
    have h2 : Filter.Tendsto (fun R : ℝ => 256 * B * Real.log R / R)
        Filter.atTop (nhds 0) := by
      have hlog : Filter.Tendsto (fun R : ℝ => Real.log R / R)
          Filter.atTop (nhds 0) := by
        have := Real.tendsto_pow_log_div_mul_add_atTop
          (a := (1:ℝ)) (b := 0) (n := 1) (by norm_num)
        simpa using this
      have := hlog.const_mul (256 * B)
      simp at this
      refine this.congr' ?_
      filter_upwards with R; ring
    simpa using h1.add h2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_maj_tend
  · filter_upwards [Filter.eventually_ge_atTop (max 2 (2*nz+1))] with R hR
    apply div_nonneg _ (sq_nonneg _)
    have hR2 : 2 ≤ R := le_trans (le_max_left _ _) hR
    have h_log_Rplus : 0 ≤ Real.log (R + 2) := Real.log_nonneg (by linarith)
    have : 0 ≤ B * R * Real.log (R + 2) :=
      mul_nonneg (mul_nonneg hB (by linarith)) h_log_Rplus
    linarith
  · filter_upwards [Filter.eventually_ge_atTop (max 2 (2*nz+1))] with R hR
    have hR2 : 2 ≤ R := le_trans (le_max_left _ _) hR
    have hR_nz : 2 * nz + 1 ≤ R := le_trans (le_max_right _ _) hR
    have hR_pos : 0 < R := by linarith
    have hR_gt_nz : R > nz := by linarith
    have hR_sub_pos : 0 < R - nz := by linarith
    have h_log_R : 0 < Real.log R := Real.log_pos (by linarith)
    have h_log_Rplus : 0 < Real.log (R + 2) := Real.log_pos (by linarith)
    have h_rmnz_ge : R - nz ≥ R / 2 := by linarith
    have h_sq_bd : (R - nz) ^ 2 ≥ (R / 2) ^ 2 :=
      pow_le_pow_left₀ (by linarith) h_rmnz_ge 2
    have h_denom_bd : (R - nz) ^ 2 ≥ R^2 / 4 := by nlinarith [h_sq_bd]
    have h_log_bd : Real.log (R + 2) ≤ 2 * Real.log R := by
      have h1 : R + 2 ≤ 2 * R := by linarith
      have h2 : Real.log (R + 2) ≤ Real.log (2 * R) :=
        Real.log_le_log (by linarith) h1
      have h3 : Real.log (2 * R) = Real.log 2 + Real.log R :=
        Real.log_mul (by norm_num) (by linarith)
      have h4 : Real.log 2 ≤ Real.log R := Real.log_le_log (by norm_num) hR2
      linarith
    have h_num : 1 + A + B * R * Real.log (R + 2) ≤
        1 + A + 2 * B * R * Real.log R := by
      have : B * R * Real.log (R + 2) ≤ B * R * (2 * Real.log R) := by
        apply mul_le_mul_of_nonneg_left h_log_bd
        exact mul_nonneg hB (by linarith)
      linarith
    have h_num'_nn : 0 ≤ 1 + A + 2 * B * R * Real.log R := by
      have : 0 ≤ 2 * B * R * Real.log R :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hB) (by linarith))
          (le_of_lt h_log_R)
      linarith
    have h_step1 : 32 * (1 + A + B * R * Real.log (R + 2)) / (R - nz) ^ 2 ≤
        32 * (1 + A + 2 * B * R * Real.log R) / (R - nz) ^ 2 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith
    have h_step2 : 32 * (1 + A + 2 * B * R * Real.log R) / (R - nz) ^ 2 ≤
        32 * (1 + A + 2 * B * R * Real.log R) / (R^2/4) := by
      apply div_le_div₀ _ (le_refl _) (by positivity) h_denom_bd
      linarith
    have h_step3 : 32 * (1 + A + 2 * B * R * Real.log R) / (R^2/4) =
        128 * (1 + A) / R^2 + 256 * B * Real.log R / R := by
      have hRne : R ≠ 0 := ne_of_gt hR_pos
      field_simp
      ring
    linarith

/-- **Second-derivative bound from Borel–Carathéodory + Cauchy.** -/
private theorem iteratedDeriv2_bound_of_meanType
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : f 0 = 0)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hgrowth : ∀ z : ℂ, (f z).re ≤ A + B * ‖z‖ * Real.log (‖z‖ + 2))
    (z₀ : ℂ) (R : ℝ) (hR : 3 * (‖z₀‖ + 1) ≤ R) :
    ‖iteratedDeriv 2 f z₀‖ ≤
      32 * (1 + A + B * R * Real.log (R + 2)) / (R - ‖z₀‖) ^ 2 := by
  set nz : ℝ := ‖z₀‖ with hnz_def
  have hnz_nn : 0 ≤ nz := norm_nonneg _
  have hR_pos : 0 < R := by linarith
  have hR_gt_nz : nz + 1 < R := by linarith
  set r : ℝ := (R - nz) / 2 with hr_def
  have hr_pos : 0 < r := by rw [hr_def]; linarith
  have hr_ge_one : 1 ≤ r := by rw [hr_def]; linarith
  set M : ℝ := 1 + A + B * R * Real.log (R + 2) with hM_def
  have hlog_nn : 0 ≤ Real.log (R + 2) := Real.log_nonneg (by linarith)
  have hM_pos : 0 < M := by
    rw [hM_def]
    have : 0 ≤ B * R * Real.log (R + 2) :=
      mul_nonneg (mul_nonneg hB hR_pos.le) hlog_nn
    linarith
  have hz₀_in_ball : z₀ ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_zero_right]; linarith
  have hf_diff_on : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) R) :=
    hf.differentiableOn
  have hf_maps : Set.MapsTo f (Metric.ball (0 : ℂ) R) {w : ℂ | w.re ≤ M} := by
    intro w hw
    have hw_norm : ‖w‖ < R := by
      rw [Metric.mem_ball, dist_zero_right] at hw; exact hw
    have hgw : (f w).re ≤ A + B * ‖w‖ * Real.log (‖w‖ + 2) := hgrowth w
    have h_mono : B * ‖w‖ * Real.log (‖w‖ + 2) ≤ B * R * Real.log (R + 2) := by
      have hwnn : 0 ≤ ‖w‖ := norm_nonneg _
      have h1 : B * ‖w‖ ≤ B * R := mul_le_mul_of_nonneg_left hw_norm.le hB
      have h2 : Real.log (‖w‖ + 2) ≤ Real.log (R + 2) :=
        Real.log_le_log (by linarith) (by linarith)
      have h4 : 0 ≤ Real.log (‖w‖ + 2) := Real.log_nonneg (by linarith)
      calc B * ‖w‖ * Real.log (‖w‖ + 2)
          ≤ B * R * Real.log (‖w‖ + 2) := mul_le_mul_of_nonneg_right h1 h4
        _ ≤ B * R * Real.log (R + 2) :=
            mul_le_mul_of_nonneg_left h2 (mul_nonneg hB hR_pos.le)
    show (f w).re ≤ M
    rw [hM_def]; linarith
  have hBC : ∀ z ∈ Metric.ball (0 : ℂ) R, ‖f z‖ ≤ 2 * M * ‖z‖ / (R - ‖z‖) :=
    fun z hz => Complex.borelCaratheodory_zero hM_pos hf_diff_on hf_maps hR_pos hz hf0
  have h_sphere_bd : ∀ w ∈ Metric.sphere z₀ r, ‖f w‖ ≤ 4 * M := by
    intro w hw
    have hw_dist : ‖w - z₀‖ = r := by rw [← dist_eq_norm]; exact hw
    have hw_norm_le : ‖w‖ ≤ nz + r := by
      calc ‖w‖ = ‖(w - z₀) + z₀‖ := by ring_nf
        _ ≤ ‖w - z₀‖ + ‖z₀‖ := norm_add_le _ _
        _ = r + nz := by rw [hw_dist]
        _ = nz + r := by ring
    have hw_in_ball : w ∈ Metric.ball (0 : ℂ) R := by
      rw [Metric.mem_ball, dist_zero_right]
      have h1 : nz + r = nz + (R - nz) / 2 := by rw [hr_def]
      have h2 : nz + (R - nz) / 2 < R := by linarith
      calc ‖w‖ ≤ nz + r := hw_norm_le
        _ < R := by rw [h1]; exact h2
    have hR_sub_w : r ≤ R - ‖w‖ := by
      have h1 : ‖w‖ ≤ nz + r := hw_norm_le
      have h2 : R - (nz + r) = r := by rw [hr_def]; ring
      linarith
    have hR_sub_pos : 0 < R - ‖w‖ := by linarith
    have hBCw := hBC w hw_in_ball
    have hr_ge_nz : nz ≤ r := by rw [hr_def]; linarith
    have hw_nn : 0 ≤ ‖w‖ := norm_nonneg _
    have h_nzr_nn : 0 ≤ nz + r := by linarith
    have h_step1 : 2 * M * ‖w‖ / (R - ‖w‖) ≤ 2 * M * (nz + r) / r := by
      apply div_le_div₀ _ _ hr_pos hR_sub_w
      · exact mul_nonneg (by linarith [hM_pos]) h_nzr_nn
      · exact mul_le_mul_of_nonneg_left hw_norm_le (by linarith [hM_pos])
    have h_step2 : 2 * M * (nz + r) / r ≤ 4 * M := by
      rw [div_le_iff₀ hr_pos]
      have h : nz + r ≤ 2 * r := by linarith
      calc 2 * M * (nz + r) ≤ 2 * M * (2 * r) :=
            mul_le_mul_of_nonneg_left h (by linarith [hM_pos])
        _ = 4 * M * r := by ring
    linarith [hBCw]
  have h_dcc : DiffContOnCl ℂ f (Metric.ball z₀ r) := hf.diffContOnCl
  have hcauchy : ‖iteratedDeriv 2 f z₀‖ ≤ (2 : ℕ).factorial * (4 * M) / r ^ 2 :=
    Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2 hr_pos h_dcc
      h_sphere_bd
  have h_fact2 : ((2 : ℕ).factorial : ℝ) = 2 := by norm_num
  rw [h_fact2] at hcauchy
  have hr2 : r ^ 2 = (R - nz) ^ 2 / 4 := by rw [hr_def]; ring
  rw [hr2] at hcauchy
  have hfinal : 2 * (4 * M) / ((R - nz) ^ 2 / 4) = 32 * M / (R - nz) ^ 2 := by
    have hRnz_pos : 0 < R - nz := by linarith
    have : (R - nz) ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  rw [hfinal] at hcauchy
  show ‖iteratedDeriv 2 f z₀‖ ≤ 32 * M / (R - nz) ^ 2
  exact hcauchy

/-- **Second derivative vanishes for an entire mean-type function.** -/
private theorem secondDeriv_zero_of_meanType
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : f 0 = 0)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hgrowth : ∀ z : ℂ, (f z).re ≤ A + B * ‖z‖ * Real.log (‖z‖ + 2)) :
    ∀ z₀ : ℂ, iteratedDeriv 2 f z₀ = 0 := by
  intro z₀
  have hnz_nn : 0 ≤ ‖z₀‖ := norm_nonneg _
  have h_bound : ∀ R : ℝ, 3 * (‖z₀‖ + 1) ≤ R →
      ‖iteratedDeriv 2 f z₀‖ ≤
        32 * (1 + A + B * R * Real.log (R + 2)) / (R - ‖z₀‖) ^ 2 :=
    fun R hR => iteratedDeriv2_bound_of_meanType hf hf0 hA hB hgrowth z₀ R hR
  have h_tend : Filter.Tendsto
      (fun R : ℝ => 32 * (1 + A + B * R * Real.log (R + 2)) / (R - ‖z₀‖) ^ 2)
      Filter.atTop (nhds 0) := tendsto_meanType_ratio_zero hA hB hnz_nn
  have h_le_zero : ‖iteratedDeriv 2 f z₀‖ ≤ 0 :=
    ge_of_tendsto h_tend (Filter.eventually_atTop.mpr ⟨3 * (‖z₀‖ + 1), h_bound⟩)
  exact norm_le_zero_iff.mp h_le_zero

/-- **Generic constancy of `logDeriv` from order-1 mean-type growth.** For an entire, nowhere-zero
`g` with `‖g z‖ ≤ exp(C·‖z‖·log(‖z‖+2)+D)`, the logarithmic derivative `logDeriv g` is globally
constant. -/
theorem logDeriv_const_of_growth {g : ℂ → ℂ} (hg_diff : Differentiable ℂ g)
    (hg_ne : ∀ z, g z ≠ 0)
    (hG : ∃ C D : ℝ, ∀ z : ℂ, ‖g z‖ ≤ Real.exp (C * ‖z‖ * Real.log (‖z‖ + 2) + D)) :
    ∃ A : ℂ, ∀ z : ℂ, logDeriv g z = A := by
  obtain ⟨C, D, hG⟩ := hG
  have h_anal : ∀ z, AnalyticAt ℂ g z :=
    fun z => (hg_diff.differentiableOn.analyticOnNhd isOpen_univ) z (Set.mem_univ z)
  have h_log_diff : Differentiable ℂ (logDeriv g) := by
    intro z
    have h_deriv_anal : AnalyticAt ℂ (deriv g) z := (h_anal z).deriv
    have h_ld : AnalyticAt ℂ (logDeriv g) z := by
      simpa [logDeriv] using h_deriv_anal.div (h_anal z) (hg_ne z)
    exact h_ld.differentiableAt
  obtain ⟨g₀, hg₀⟩ : ∃ G : ℂ → ℂ, ∀ z ∈ (Set.univ : Set ℂ),
      HasDerivAt G (logDeriv g z) z :=
    h_log_diff.isExactOn_univ
  set G : ℂ → ℂ := fun z => g₀ z + (Complex.log (g 0) - g₀ 0) with hG_def
  have hG_deriv : ∀ z, HasDerivAt G (logDeriv g z) z := by
    intro z
    have h₀ := hg₀ z (Set.mem_univ z)
    simpa [hG_def] using h₀.add_const (Complex.log (g 0) - g₀ 0)
  have hG_diff : Differentiable ℂ G := fun z => (hG_deriv z).differentiableAt
  have hG_deriv_eq : ∀ z, deriv G z = logDeriv g z := fun z => (hG_deriv z).deriv
  have hG0 : G 0 = Complex.log (g 0) := by simp [hG_def]
  set φ : ℂ → ℂ := fun z => Complex.exp (G z) / g z with hφ_def
  have hφ_deriv_zero : ∀ z, deriv φ z = 0 := by
    intro z
    have h_exp_G_deriv : HasDerivAt (fun w => Complex.exp (G w))
        (Complex.exp (G z) * logDeriv g z) z := by
      have := (hG_deriv z).cexp
      simpa using this
    have h_g_deriv : HasDerivAt g (deriv g z) z := (hg_diff z).hasDerivAt
    have h_div : HasDerivAt φ
        ((Complex.exp (G z) * logDeriv g z * g z -
          Complex.exp (G z) * deriv g z) / (g z)^2) z :=
      h_exp_G_deriv.div h_g_deriv (hg_ne z)
    have h_num_zero :
        Complex.exp (G z) * logDeriv g z * g z -
          Complex.exp (G z) * deriv g z = 0 := by
      have h_eq : logDeriv g z * g z = deriv g z := by
        rw [logDeriv_apply, div_mul_cancel₀ _ (hg_ne z)]
      calc Complex.exp (G z) * logDeriv g z * g z -
            Complex.exp (G z) * deriv g z
          = Complex.exp (G z) * (logDeriv g z * g z) -
              Complex.exp (G z) * deriv g z := by ring
        _ = Complex.exp (G z) * deriv g z -
              Complex.exp (G z) * deriv g z := by rw [h_eq]
        _ = 0 := sub_self _
    rw [h_div.deriv, h_num_zero, zero_div]
  have hφ_diff : Differentiable ℂ φ := by
    intro z
    have h_exp_G_diff : DifferentiableAt ℂ (fun w => Complex.exp (G w)) z :=
      (hG_diff z).cexp
    exact h_exp_G_diff.div (hg_diff z) (hg_ne z)
  have hφ_const : ∀ z, φ z = φ 0 :=
    fun z => is_const_of_deriv_eq_zero hφ_diff hφ_deriv_zero z 0
  have hφ0 : φ 0 = 1 := by
    show Complex.exp (G 0) / g 0 = 1
    rw [hG0, Complex.exp_log (hg_ne 0)]
    exact div_self (hg_ne 0)
  have h_exp_G_eq : ∀ z, Complex.exp (G z) = g z := by
    intro z
    have hφz : Complex.exp (G z) / g z = 1 := by
      rw [show Complex.exp (G z) / g z = φ z from rfl, hφ_const z, hφ0]
    exact (div_eq_one_iff_eq (hg_ne z)).mp hφz
  have h_G_re_bd : ∀ z, (G z).re ≤ C * ‖z‖ * Real.log (‖z‖ + 2) + D := by
    intro z
    have h1 : Real.exp ((G z).re) = ‖g z‖ := by
      rw [← h_exp_G_eq z, Complex.norm_exp]
    have h2 : Real.exp ((G z).re) ≤ Real.exp (C * ‖z‖ * Real.log (‖z‖ + 2) + D) := by
      rw [h1]; exact hG z
    exact (Real.exp_le_exp.mp h2)
  set h : ℂ → ℂ := fun z => G z - G 0 with hh_def
  have hh_diff : Differentiable ℂ h := hG_diff.sub_const _
  have hh_deriv : ∀ z, deriv h z = logDeriv g z := by
    intro z
    have : deriv h z = deriv G z := by simp [hh_def, deriv_sub_const]
    rw [this, hG_deriv_eq]
  have hh0 : h 0 = 0 := by simp [hh_def]
  set A' : ℝ := max 0 (D - (G 0).re) with hA'_def
  set B' : ℝ := max C 0 with hB'_def
  have hA'_nn : 0 ≤ A' := le_max_left _ _
  have hB'_nn : 0 ≤ B' := le_max_right _ _
  have h_h_growth : ∀ z, (h z).re ≤ A' + B' * ‖z‖ * Real.log (‖z‖ + 2) := by
    intro z
    have h_nz : 0 ≤ ‖z‖ := norm_nonneg _
    have h_log_nn : 0 ≤ Real.log (‖z‖ + 2) := Real.log_nonneg (by linarith)
    have h_gz := h_G_re_bd z
    have h_hre : (h z).re = (G z).re - (G 0).re := by simp [hh_def, Complex.sub_re]
    have h_C_le : C * ‖z‖ * Real.log (‖z‖ + 2) ≤ B' * ‖z‖ * Real.log (‖z‖ + 2) := by
      apply mul_le_mul_of_nonneg_right _ h_log_nn
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) h_nz
    have h_D_le : D - (G 0).re ≤ A' := le_max_right _ _
    rw [h_hre]; linarith
  have h_iter2_zero : ∀ z₀, iteratedDeriv 2 h z₀ = 0 :=
    secondDeriv_zero_of_meanType hh_diff hh0 hA'_nn hB'_nn h_h_growth
  have h_deriv_deriv_zero : ∀ z, deriv (deriv h) z = 0 := by
    intro z
    have := h_iter2_zero z
    simpa [iteratedDeriv_succ, iteratedDeriv_zero] using this
  have h_deriv_diff : Differentiable ℂ (deriv h) := by
    have : deriv h = logDeriv g := funext hh_deriv
    rw [this]; exact h_log_diff
  have h_deriv_const : ∀ z, deriv h z = deriv h 0 := by
    intro z
    exact is_const_of_deriv_eq_zero h_deriv_diff h_deriv_deriv_zero z 0
  refine ⟨logDeriv g 0, ?_⟩
  intro z
  have := h_deriv_const z
  rw [hh_deriv z, hh_deriv 0] at this
  exact this

-- ═══════════════════════════════════════════════════════════════════════════
-- § `log²` (mean-type-2) variant
-- ═══════════════════════════════════════════════════════════════════════════

/-- `log²` variant of `tendsto_meanType_ratio_zero`. -/
private theorem tendsto_meanType_ratio_zero_logSq {A B nz : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hnz : 0 ≤ nz) :
    Filter.Tendsto
      (fun R : ℝ => 32 * (1 + A + B * R * (Real.log (R + 2)) ^ 2) / (R - nz) ^ 2)
      Filter.atTop (nhds 0) := by
  have h_maj_tend : Filter.Tendsto
      (fun R : ℝ => 128 * (1 + A) / R^2 + 512 * B * (Real.log R) ^ 2 / R)
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun R : ℝ => 128 * (1 + A) / R^2)
        Filter.atTop (nhds 0) := by
      have hone : Filter.Tendsto (fun R : ℝ => 1 / R^2) Filter.atTop (nhds 0) := by
        have h := @tendsto_pow_neg_atTop ℝ _ _ _ _ _ 2 (by norm_num)
        refine h.congr' ?_
        filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with R _
        rw [zpow_neg, zpow_natCast, inv_eq_one_div]
      have := hone.const_mul (128 * (1 + A))
      simp at this
      refine this.congr' ?_
      filter_upwards with R; ring
    have h2 : Filter.Tendsto (fun R : ℝ => 512 * B * (Real.log R) ^ 2 / R)
        Filter.atTop (nhds 0) := by
      have hlog : Filter.Tendsto (fun R : ℝ => (Real.log R) ^ 2 / R)
          Filter.atTop (nhds 0) := by
        have := Real.tendsto_pow_log_div_mul_add_atTop
          (a := (1:ℝ)) (b := 0) (n := 2) (by norm_num)
        simpa using this
      have := hlog.const_mul (512 * B)
      simp at this
      refine this.congr' ?_
      filter_upwards with R; ring
    simpa using h1.add h2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_maj_tend
  · filter_upwards [Filter.eventually_ge_atTop (max 2 (2*nz+1))] with R hR
    apply div_nonneg _ (sq_nonneg _)
    have hR2 : 2 ≤ R := le_trans (le_max_left _ _) hR
    have h_log_Rplus : 0 ≤ Real.log (R + 2) := Real.log_nonneg (by linarith)
    have h_log_Rplus_sq : 0 ≤ (Real.log (R + 2)) ^ 2 := sq_nonneg _
    have : 0 ≤ B * R * (Real.log (R + 2)) ^ 2 :=
      mul_nonneg (mul_nonneg hB (by linarith)) h_log_Rplus_sq
    linarith
  · filter_upwards [Filter.eventually_ge_atTop (max 2 (2*nz+1))] with R hR
    have hR2 : 2 ≤ R := le_trans (le_max_left _ _) hR
    have hR_nz : 2 * nz + 1 ≤ R := le_trans (le_max_right _ _) hR
    have hR_pos : 0 < R := by linarith
    have hR_gt_nz : R > nz := by linarith
    have hR_sub_pos : 0 < R - nz := by linarith
    have h_log_R : 0 < Real.log R := Real.log_pos (by linarith)
    have h_log_Rplus : 0 < Real.log (R + 2) := Real.log_pos (by linarith)
    have h_rmnz_ge : R - nz ≥ R / 2 := by linarith
    have h_sq_bd : (R - nz) ^ 2 ≥ (R / 2) ^ 2 :=
      pow_le_pow_left₀ (by linarith) h_rmnz_ge 2
    have h_denom_bd : (R - nz) ^ 2 ≥ R^2 / 4 := by nlinarith [h_sq_bd]
    have h_log_bd : Real.log (R + 2) ≤ 2 * Real.log R := by
      have h1 : R + 2 ≤ 2 * R := by linarith
      have h2 : Real.log (R + 2) ≤ Real.log (2 * R) :=
        Real.log_le_log (by linarith) h1
      have h3 : Real.log (2 * R) = Real.log 2 + Real.log R :=
        Real.log_mul (by norm_num) (by linarith)
      have h4 : Real.log 2 ≤ Real.log R := Real.log_le_log (by norm_num) hR2
      linarith
    have h_log_sq_bd : (Real.log (R + 2)) ^ 2 ≤ 4 * (Real.log R) ^ 2 := by
      have h_log_plus_nn : 0 ≤ Real.log (R + 2) := le_of_lt h_log_Rplus
      have h_two_log_nn : 0 ≤ 2 * Real.log R := by linarith
      have : (Real.log (R + 2)) ^ 2 ≤ (2 * Real.log R) ^ 2 :=
        pow_le_pow_left₀ h_log_plus_nn h_log_bd 2
      calc (Real.log (R + 2)) ^ 2 ≤ (2 * Real.log R) ^ 2 := this
        _ = 4 * (Real.log R) ^ 2 := by ring
    have h_num : 1 + A + B * R * (Real.log (R + 2)) ^ 2 ≤
        1 + A + 4 * B * R * (Real.log R) ^ 2 := by
      have : B * R * (Real.log (R + 2)) ^ 2 ≤ B * R * (4 * (Real.log R) ^ 2) := by
        apply mul_le_mul_of_nonneg_left h_log_sq_bd
        exact mul_nonneg hB (by linarith)
      linarith
    have h_num'_nn : 0 ≤ 1 + A + 4 * B * R * (Real.log R) ^ 2 := by
      have hlog_sq_nn : 0 ≤ (Real.log R) ^ 2 := sq_nonneg _
      have : 0 ≤ 4 * B * R * (Real.log R) ^ 2 :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hB) (by linarith)) hlog_sq_nn
      linarith
    have h_step1 : 32 * (1 + A + B * R * (Real.log (R + 2)) ^ 2) / (R - nz) ^ 2 ≤
        32 * (1 + A + 4 * B * R * (Real.log R) ^ 2) / (R - nz) ^ 2 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith
    have h_step2 : 32 * (1 + A + 4 * B * R * (Real.log R) ^ 2) / (R - nz) ^ 2 ≤
        32 * (1 + A + 4 * B * R * (Real.log R) ^ 2) / (R^2/4) := by
      apply div_le_div₀ _ (le_refl _) (by positivity) h_denom_bd
      linarith
    have h_step3 : 32 * (1 + A + 4 * B * R * (Real.log R) ^ 2) / (R^2/4) =
        128 * (1 + A) / R^2 + 512 * B * (Real.log R) ^ 2 / R := by
      have hRne : R ≠ 0 := ne_of_gt hR_pos
      field_simp
      ring
    linarith [h_step1, h_step2, h_step3]

/-- `log²` variant of `iteratedDeriv2_bound_of_meanType`. -/
private theorem iteratedDeriv2_bound_of_meanType_logSq
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : f 0 = 0)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hgrowth : ∀ z : ℂ, (f z).re ≤ A + B * ‖z‖ * (Real.log (‖z‖ + 2)) ^ 2)
    (z₀ : ℂ) (R : ℝ) (hR : 3 * (‖z₀‖ + 1) ≤ R) :
    ‖iteratedDeriv 2 f z₀‖ ≤
      32 * (1 + A + B * R * (Real.log (R + 2)) ^ 2) / (R - ‖z₀‖) ^ 2 := by
  set nz : ℝ := ‖z₀‖ with hnz_def
  have hnz_nn : 0 ≤ nz := norm_nonneg _
  have hR_pos : 0 < R := by linarith
  have hR_gt_nz : nz + 1 < R := by linarith
  set r : ℝ := (R - nz) / 2 with hr_def
  have hr_pos : 0 < r := by rw [hr_def]; linarith
  have hr_ge_one : 1 ≤ r := by rw [hr_def]; linarith
  set M : ℝ := 1 + A + B * R * (Real.log (R + 2)) ^ 2 with hM_def
  have hlog_nn : 0 ≤ Real.log (R + 2) := Real.log_nonneg (by linarith)
  have hlog_sq_nn : 0 ≤ (Real.log (R + 2)) ^ 2 := sq_nonneg _
  have hM_pos : 0 < M := by
    rw [hM_def]
    have : 0 ≤ B * R * (Real.log (R + 2)) ^ 2 :=
      mul_nonneg (mul_nonneg hB hR_pos.le) hlog_sq_nn
    linarith
  have hz₀_in_ball : z₀ ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_zero_right]; linarith
  have hf_diff_on : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) R) := hf.differentiableOn
  have hf_maps : Set.MapsTo f (Metric.ball (0 : ℂ) R) {w : ℂ | w.re ≤ M} := by
    intro w hw
    have hw_norm : ‖w‖ < R := by
      rw [Metric.mem_ball, dist_zero_right] at hw; exact hw
    have hgw : (f w).re ≤ A + B * ‖w‖ * (Real.log (‖w‖ + 2)) ^ 2 := hgrowth w
    have h_mono : B * ‖w‖ * (Real.log (‖w‖ + 2)) ^ 2 ≤ B * R * (Real.log (R + 2)) ^ 2 := by
      have hwnn : 0 ≤ ‖w‖ := norm_nonneg _
      have h1 : B * ‖w‖ ≤ B * R := mul_le_mul_of_nonneg_left hw_norm.le hB
      have h2 : Real.log (‖w‖ + 2) ≤ Real.log (R + 2) :=
        Real.log_le_log (by linarith) (by linarith)
      have h3 : 0 ≤ Real.log (‖w‖ + 2) := Real.log_nonneg (by linarith)
      have h4 : (Real.log (‖w‖ + 2)) ^ 2 ≤ (Real.log (R + 2)) ^ 2 :=
        pow_le_pow_left₀ h3 h2 2
      have h5 : 0 ≤ (Real.log (‖w‖ + 2)) ^ 2 := sq_nonneg _
      calc B * ‖w‖ * (Real.log (‖w‖ + 2)) ^ 2
          ≤ B * R * (Real.log (‖w‖ + 2)) ^ 2 := mul_le_mul_of_nonneg_right h1 h5
        _ ≤ B * R * (Real.log (R + 2)) ^ 2 :=
            mul_le_mul_of_nonneg_left h4 (mul_nonneg hB hR_pos.le)
    show (f w).re ≤ M
    rw [hM_def]; linarith
  have hBC : ∀ z ∈ Metric.ball (0 : ℂ) R, ‖f z‖ ≤ 2 * M * ‖z‖ / (R - ‖z‖) :=
    fun z hz => Complex.borelCaratheodory_zero hM_pos hf_diff_on hf_maps hR_pos hz hf0
  have h_sphere_bd : ∀ w ∈ Metric.sphere z₀ r, ‖f w‖ ≤ 4 * M := by
    intro w hw
    have hw_dist : ‖w - z₀‖ = r := by rw [← dist_eq_norm]; exact hw
    have hw_norm_le : ‖w‖ ≤ nz + r := by
      calc ‖w‖ = ‖(w - z₀) + z₀‖ := by ring_nf
        _ ≤ ‖w - z₀‖ + ‖z₀‖ := norm_add_le _ _
        _ = r + nz := by rw [hw_dist]
        _ = nz + r := by ring
    have hw_in_ball : w ∈ Metric.ball (0 : ℂ) R := by
      rw [Metric.mem_ball, dist_zero_right]
      have h1 : nz + r = nz + (R - nz) / 2 := by rw [hr_def]
      have h2 : nz + (R - nz) / 2 < R := by linarith
      calc ‖w‖ ≤ nz + r := hw_norm_le
        _ < R := by rw [h1]; exact h2
    have hR_sub_w : r ≤ R - ‖w‖ := by
      have h1 : ‖w‖ ≤ nz + r := hw_norm_le
      have h2 : R - (nz + r) = r := by rw [hr_def]; ring
      linarith
    have hR_sub_pos : 0 < R - ‖w‖ := by linarith
    have hBCw := hBC w hw_in_ball
    have hr_ge_nz : nz ≤ r := by rw [hr_def]; linarith
    have hw_nn : 0 ≤ ‖w‖ := norm_nonneg _
    have h_nzr_nn : 0 ≤ nz + r := by linarith
    have h_step1 : 2 * M * ‖w‖ / (R - ‖w‖) ≤ 2 * M * (nz + r) / r := by
      apply div_le_div₀ _ _ hr_pos hR_sub_w
      · exact mul_nonneg (by linarith [hM_pos]) h_nzr_nn
      · exact mul_le_mul_of_nonneg_left hw_norm_le (by linarith [hM_pos])
    have h_step2 : 2 * M * (nz + r) / r ≤ 4 * M := by
      rw [div_le_iff₀ hr_pos]
      have h : nz + r ≤ 2 * r := by linarith
      calc 2 * M * (nz + r) ≤ 2 * M * (2 * r) :=
            mul_le_mul_of_nonneg_left h (by linarith [hM_pos])
        _ = 4 * M * r := by ring
    linarith [hBCw]
  have h_dcc : DiffContOnCl ℂ f (Metric.ball z₀ r) := hf.diffContOnCl
  have hcauchy : ‖iteratedDeriv 2 f z₀‖ ≤ (2 : ℕ).factorial * (4 * M) / r ^ 2 :=
    Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2 hr_pos h_dcc h_sphere_bd
  have h_fact2 : ((2 : ℕ).factorial : ℝ) = 2 := by norm_num
  rw [h_fact2] at hcauchy
  have hr2 : r ^ 2 = (R - nz) ^ 2 / 4 := by rw [hr_def]; ring
  rw [hr2] at hcauchy
  have hfinal : 2 * (4 * M) / ((R - nz) ^ 2 / 4) = 32 * M / (R - nz) ^ 2 := by
    have hRnz_pos : 0 < R - nz := by linarith
    have : (R - nz) ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  rw [hfinal] at hcauchy
  show ‖iteratedDeriv 2 f z₀‖ ≤ 32 * M / (R - nz) ^ 2
  exact hcauchy

/-- `log²` variant of `secondDeriv_zero_of_meanType`. -/
private theorem secondDeriv_zero_of_meanType_logSq
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : f 0 = 0)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hgrowth : ∀ z : ℂ, (f z).re ≤ A + B * ‖z‖ * (Real.log (‖z‖ + 2)) ^ 2) :
    ∀ z₀ : ℂ, iteratedDeriv 2 f z₀ = 0 := by
  intro z₀
  have hnz_nn : 0 ≤ ‖z₀‖ := norm_nonneg _
  have h_bound : ∀ R : ℝ, 3 * (‖z₀‖ + 1) ≤ R →
      ‖iteratedDeriv 2 f z₀‖ ≤
        32 * (1 + A + B * R * (Real.log (R + 2)) ^ 2) / (R - ‖z₀‖) ^ 2 :=
    fun R hR => iteratedDeriv2_bound_of_meanType_logSq hf hf0 hA hB hgrowth z₀ R hR
  have h_tend : Filter.Tendsto
      (fun R : ℝ => 32 * (1 + A + B * R * (Real.log (R + 2)) ^ 2) / (R - ‖z₀‖) ^ 2)
      Filter.atTop (nhds 0) := tendsto_meanType_ratio_zero_logSq hA hB hnz_nn
  have h_le_zero : ‖iteratedDeriv 2 f z₀‖ ≤ 0 :=
    ge_of_tendsto h_tend (Filter.eventually_atTop.mpr ⟨3 * (‖z₀‖ + 1), h_bound⟩)
  exact norm_le_zero_iff.mp h_le_zero

/-- **Generic constancy of `logDeriv` from order-1 mean-type-2 (`log²`) growth.** -/
theorem logDeriv_const_of_logSqGrowth {g : ℂ → ℂ} (hg_diff : Differentiable ℂ g)
    (hg_ne : ∀ z, g z ≠ 0)
    (hG : ∃ C D : ℝ, ∀ z : ℂ, ‖g z‖ ≤ Real.exp (C * ‖z‖ * (Real.log (‖z‖ + 2)) ^ 2 + D)) :
    ∃ A : ℂ, ∀ z : ℂ, logDeriv g z = A := by
  obtain ⟨C, D, hG⟩ := hG
  have h_anal : ∀ z, AnalyticAt ℂ g z :=
    fun z => (hg_diff.differentiableOn.analyticOnNhd isOpen_univ) z (Set.mem_univ z)
  have h_log_diff : Differentiable ℂ (logDeriv g) := by
    intro z
    have h_deriv_anal : AnalyticAt ℂ (deriv g) z := (h_anal z).deriv
    have h_ld : AnalyticAt ℂ (logDeriv g) z := by
      simpa [logDeriv] using h_deriv_anal.div (h_anal z) (hg_ne z)
    exact h_ld.differentiableAt
  obtain ⟨g₀, hg₀⟩ : ∃ G : ℂ → ℂ, ∀ z ∈ (Set.univ : Set ℂ),
      HasDerivAt G (logDeriv g z) z :=
    h_log_diff.isExactOn_univ
  set G : ℂ → ℂ := fun z => g₀ z + (Complex.log (g 0) - g₀ 0) with hG_def
  have hG_deriv : ∀ z, HasDerivAt G (logDeriv g z) z := by
    intro z
    have h₀ := hg₀ z (Set.mem_univ z)
    simpa [hG_def] using h₀.add_const (Complex.log (g 0) - g₀ 0)
  have hG_diff : Differentiable ℂ G := fun z => (hG_deriv z).differentiableAt
  have hG_deriv_eq : ∀ z, deriv G z = logDeriv g z := fun z => (hG_deriv z).deriv
  have hG0 : G 0 = Complex.log (g 0) := by simp [hG_def]
  set φ : ℂ → ℂ := fun z => Complex.exp (G z) / g z with hφ_def
  have hφ_deriv_zero : ∀ z, deriv φ z = 0 := by
    intro z
    have h_exp_G_deriv : HasDerivAt (fun w => Complex.exp (G w))
        (Complex.exp (G z) * logDeriv g z) z := by
      have := (hG_deriv z).cexp
      simpa using this
    have h_g_deriv : HasDerivAt g (deriv g z) z := (hg_diff z).hasDerivAt
    have h_div : HasDerivAt φ
        ((Complex.exp (G z) * logDeriv g z * g z -
          Complex.exp (G z) * deriv g z) / (g z)^2) z :=
      h_exp_G_deriv.div h_g_deriv (hg_ne z)
    have h_num_zero :
        Complex.exp (G z) * logDeriv g z * g z -
          Complex.exp (G z) * deriv g z = 0 := by
      have h_eq : logDeriv g z * g z = deriv g z := by
        rw [logDeriv_apply, div_mul_cancel₀ _ (hg_ne z)]
      calc Complex.exp (G z) * logDeriv g z * g z -
            Complex.exp (G z) * deriv g z
          = Complex.exp (G z) * (logDeriv g z * g z) -
              Complex.exp (G z) * deriv g z := by ring
        _ = Complex.exp (G z) * deriv g z -
              Complex.exp (G z) * deriv g z := by rw [h_eq]
        _ = 0 := sub_self _
    rw [h_div.deriv, h_num_zero, zero_div]
  have hφ_diff : Differentiable ℂ φ := by
    intro z
    have h_exp_G_diff : DifferentiableAt ℂ (fun w => Complex.exp (G w)) z :=
      (hG_diff z).cexp
    exact h_exp_G_diff.div (hg_diff z) (hg_ne z)
  have hφ_const : ∀ z, φ z = φ 0 :=
    fun z => is_const_of_deriv_eq_zero hφ_diff hφ_deriv_zero z 0
  have hφ0 : φ 0 = 1 := by
    show Complex.exp (G 0) / g 0 = 1
    rw [hG0, Complex.exp_log (hg_ne 0)]
    exact div_self (hg_ne 0)
  have h_exp_G_eq : ∀ z, Complex.exp (G z) = g z := by
    intro z
    have hφz : Complex.exp (G z) / g z = 1 := by
      rw [show Complex.exp (G z) / g z = φ z from rfl, hφ_const z, hφ0]
    exact (div_eq_one_iff_eq (hg_ne z)).mp hφz
  have h_G_re_bd : ∀ z, (G z).re ≤ C * ‖z‖ * (Real.log (‖z‖ + 2)) ^ 2 + D := by
    intro z
    have h1 : Real.exp ((G z).re) = ‖g z‖ := by
      rw [← h_exp_G_eq z, Complex.norm_exp]
    have h2 : Real.exp ((G z).re) ≤ Real.exp (C * ‖z‖ * (Real.log (‖z‖ + 2)) ^ 2 + D) := by
      rw [h1]; exact hG z
    exact (Real.exp_le_exp.mp h2)
  set h : ℂ → ℂ := fun z => G z - G 0 with hh_def
  have hh_diff : Differentiable ℂ h := hG_diff.sub_const _
  have hh_deriv : ∀ z, deriv h z = logDeriv g z := by
    intro z
    have : deriv h z = deriv G z := by simp [hh_def, deriv_sub_const]
    rw [this, hG_deriv_eq]
  have hh0 : h 0 = 0 := by simp [hh_def]
  set A' : ℝ := max 0 (D - (G 0).re) with hA'_def
  set B' : ℝ := max C 0 with hB'_def
  have hA'_nn : 0 ≤ A' := le_max_left _ _
  have hB'_nn : 0 ≤ B' := le_max_right _ _
  have h_h_growth : ∀ z, (h z).re ≤ A' + B' * ‖z‖ * (Real.log (‖z‖ + 2)) ^ 2 := by
    intro z
    have h_nz : 0 ≤ ‖z‖ := norm_nonneg _
    have h_log_sq_nn : 0 ≤ (Real.log (‖z‖ + 2)) ^ 2 := sq_nonneg _
    have h_gz := h_G_re_bd z
    have h_hre : (h z).re = (G z).re - (G 0).re := by simp [hh_def, Complex.sub_re]
    have h_C_le : C * ‖z‖ * (Real.log (‖z‖ + 2)) ^ 2 ≤ B' * ‖z‖ * (Real.log (‖z‖ + 2)) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ h_log_sq_nn
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) h_nz
    have h_D_le : D - (G 0).re ≤ A' := le_max_right _ _
    rw [h_hre]; linarith
  have h_iter2_zero : ∀ z₀, iteratedDeriv 2 h z₀ = 0 :=
    secondDeriv_zero_of_meanType_logSq hh_diff hh0 hA'_nn hB'_nn h_h_growth
  have h_deriv_deriv_zero : ∀ z, deriv (deriv h) z = 0 := by
    intro z
    have := h_iter2_zero z
    simpa [iteratedDeriv_succ, iteratedDeriv_zero] using this
  have h_deriv_diff : Differentiable ℂ (deriv h) := by
    have : deriv h = logDeriv g := funext hh_deriv
    rw [this]; exact h_log_diff
  have h_deriv_const : ∀ z, deriv h z = deriv h 0 := by
    intro z
    exact is_const_of_deriv_eq_zero h_deriv_diff h_deriv_deriv_zero z 0
  refine ⟨logDeriv g 0, ?_⟩
  intro z
  have := h_deriv_const z
  rw [hh_deriv z, hh_deriv 0] at this
  exact this

/-- **Constant log-derivative ⟹ explicit exponential.** If `g` is entire, nowhere zero, and
`logDeriv g ≡ A`, then `g z = g 0 · exp(A·z)`. (Integrating `g'/g = A`.) -/
theorem eq_const_mul_exp_of_logDeriv_const {g : ℂ → ℂ} (hg_diff : Differentiable ℂ g)
    (hg_ne : ∀ z, g z ≠ 0) {A : ℂ} (hA : ∀ z, logDeriv g z = A) :
    ∀ z, g z = g 0 * Complex.exp (A * z) := by
  have hexp_diff : Differentiable ℂ (fun z => Complex.exp (-(A * z))) := by fun_prop
  set h : ℂ → ℂ := fun z => g z * Complex.exp (-(A * z)) with hh_def
  have hderiv0 : ∀ z, deriv h z = 0 := by
    intro z
    have hg' : HasDerivAt g (deriv g z) z := (hg_diff z).hasDerivAt
    have hu : HasDerivAt (fun w => -(A * w)) (-A) z := by
      simpa using ((hasDerivAt_id z).const_mul (-A))
    have he : HasDerivAt (fun w => Complex.exp (-(A * w))) (Complex.exp (-(A * z)) * (-A)) z := by
      simpa using hu.cexp
    have hp : HasDerivAt h
        (deriv g z * Complex.exp (-(A * z)) + g z * (Complex.exp (-(A * z)) * (-A))) z :=
      hg'.mul he
    have hld : deriv g z = A * g z := by
      have h1 := hA z
      rw [logDeriv_apply] at h1
      field_simp [hg_ne z] at h1
      linear_combination h1
    rw [hp.deriv, hld]; ring
  have hconst : ∀ z, h z = h 0 :=
    fun z => is_const_of_deriv_eq_zero (hg_diff.mul hexp_diff) hderiv0 z 0
  intro z
  have hz : g z * Complex.exp (-(A * z)) = g 0 := by
    have hc := hconst z
    simpa [hh_def] using hc
  have e1 : Complex.exp (-(A * z)) * Complex.exp (A * z) = 1 := by
    rw [← Complex.exp_add]; simp
  calc g z = g z * (Complex.exp (-(A * z)) * Complex.exp (A * z)) := by rw [e1]; ring
    _ = (g z * Complex.exp (-(A * z))) * Complex.exp (A * z) := by ring
    _ = g 0 * Complex.exp (A * z) := by rw [hz]

end HadamardConst

#print axioms HadamardConst.logDeriv_const_of_growth
#print axioms HadamardConst.logDeriv_const_of_logSqGrowth
#print axioms HadamardConst.eq_const_mul_exp_of_logDeriv_const
