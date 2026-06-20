import RequestProject.DirichletLOverPGrowthJensen
import RequestProject.DirichletLOverP
import RequestProject.DirichletLGrowthComplete
import RequestProject.DirichletLCompletedGrowth

/-!
# Steps A/D/E/F + Main: unconditional mean-type-2 growth of `LOverP χ = Λ_χ / Prod`

Character-`χ` port of the Nevanlinna/Poisson chain in `ZD.XiOverPGrowth`. Reuses the generic
`ValueDistribution.*` proximity machinery from Mathlib. Produces

  `LOverP_growth_meanType : ∃ C D, ∀ z, ‖LOverP χ z‖ ≤ exp(C‖z‖log²(‖z‖+2)+D)`,

the single growth bound that discharges `HadamardPartialFraction_of_LOverP_logSqGrowth`, making the
Dirichlet-`L` Hadamard partial fraction **unconditional**.
-/

open Complex Set Filter Topology MeasureTheory

noncomputable section

namespace DirichletLHadamard

variable {N : ℕ} [NeZero N]

/-- Nevanlinna proximity `m(R, f) = (1/2π) ∫ log⁺ ‖f(Re^{iθ})‖ dθ`. -/
def proximity (f : ℂ → ℂ) (R : ℝ) : ℝ :=
  Real.circleAverage (fun z => max (Real.log ‖f z‖) 0) 0 R

theorem proximity_nonneg (f : ℂ → ℂ) (R : ℝ) : 0 ≤ proximity f R := by
  unfold proximity
  apply Real.circleAverage_nonneg_of_nonneg
  intro x _
  exact le_max_right _ _

-- Step A: pointwise upper bound on ‖Λ_χ(z)‖ in mean-type-1 form.
theorem completedLFunction_pointwise_meanType_bound {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hχp : χ.IsPrimitive) :
    ∃ C D : ℝ, ∀ z : ℂ,
      Real.log (‖DirichletCharacter.completedLFunction χ z‖ + 1) ≤
        C * ‖z‖ * Real.log (‖z‖ + 2) + D := by
  obtain ⟨C₀, hC₀_pos, R₀, hR₀_pos, hBound⟩ := completedL_order_one_log_bound hχ hχp
  obtain ⟨M, hM_nn, hM⟩ := completedLFunction_bounded_on_closedBall hχ R₀
  refine ⟨C₀, Real.log (M + 1), fun z => ?_⟩
  have hz_nn : 0 ≤ ‖z‖ := norm_nonneg _
  have hlog_z_nn : 0 ≤ Real.log (‖z‖ + 2) := Real.log_nonneg (by linarith)
  have hC₀_nn : 0 ≤ C₀ := le_of_lt hC₀_pos
  have hlogM_nn : 0 ≤ Real.log (M + 1) := Real.log_nonneg (by linarith)
  by_cases hz_small : ‖z‖ ≤ R₀
  · have h_xi_bd : ‖DirichletCharacter.completedLFunction χ z‖ ≤ M := hM z (by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hz_small)
    have h_log_le : Real.log (‖DirichletCharacter.completedLFunction χ z‖ + 1) ≤ Real.log (M + 1) :=
      Real.log_le_log (by positivity) (by linarith)
    have h_lhs_nn : 0 ≤ C₀ * ‖z‖ * Real.log (‖z‖ + 2) :=
      mul_nonneg (mul_nonneg hC₀_nn hz_nn) hlog_z_nn
    linarith
  · have hz_gt : ‖z‖ > R₀ := not_le.mp hz_small
    have hRpos : R₀ ≤ ‖z‖ := le_of_lt hz_gt
    have h_xi_bd := hBound ‖z‖ hRpos z (le_refl _)
    have hz_pos : 0 < ‖z‖ := lt_trans hR₀_pos hz_gt
    have h_log_z_le : Real.log ‖z‖ ≤ Real.log (‖z‖ + 2) :=
      Real.log_le_log hz_pos (by linarith)
    have h1 : C₀ * ‖z‖ * Real.log ‖z‖ ≤ C₀ * ‖z‖ * Real.log (‖z‖ + 2) := by
      apply mul_le_mul_of_nonneg_left h_log_z_le
      exact mul_nonneg hC₀_nn hz_nn
    linarith

-- Step D: m(R, Λ_χ) ≤ O(R log R).
theorem completedLFunction_proximity_bound {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hχp : χ.IsPrimitive) :
    ∃ C D : ℝ, ∀ R : ℝ, 1 ≤ R →
      proximity (DirichletCharacter.completedLFunction χ) R ≤ C * R * Real.log R + D := by
  obtain ⟨C₀, D₀, hBd⟩ := completedLFunction_pointwise_meanType_bound hχ hχp
  refine ⟨2 * |C₀|, D₀ + |C₀| * 2 * Real.log 4, fun R hR => ?_⟩
  have hR_pos : 0 < R := by linarith
  have habs : |R| = R := abs_of_pos hR_pos
  unfold proximity
  have h_ci : CircleIntegrable
      (fun z : ℂ => max (Real.log ‖DirichletCharacter.completedLFunction χ z‖) 0) 0 R := by
    have hMero : MeromorphicOn (DirichletCharacter.completedLFunction χ)
        (Metric.sphere (0 : ℂ) |R|) := fun z _ =>
      ((completedLFunction_differentiable hχ).analyticAt z).meromorphicAt
    have := circleIntegrable_posLog_norm_meromorphicOn
      (f := DirichletCharacter.completedLFunction χ) (c := (0 : ℂ)) (R := R) hMero
    convert this using 1; funext z
    rw [Real.posLog_def, max_comm]; rfl
  have h_sphere_bd : ∀ z ∈ Metric.sphere (0 : ℂ) |R|,
      max (Real.log ‖DirichletCharacter.completedLFunction χ z‖) 0 ≤
        C₀ * R * Real.log (R + 2) + D₀ := by
    intro z hz
    have hz_norm : ‖z‖ = R := by
      rw [habs] at hz
      have : dist z 0 = R := hz
      rwa [dist_zero_right] at this
    have hnn : 0 ≤ ‖DirichletCharacter.completedLFunction χ z‖ := norm_nonneg _
    have h1 : max (Real.log ‖DirichletCharacter.completedLFunction χ z‖) 0 ≤
        Real.log (‖DirichletCharacter.completedLFunction χ z‖ + 1) := by
      rcases le_or_gt ‖DirichletCharacter.completedLFunction χ z‖ 1 with h | h
      · have hlog_nn : 0 ≤ Real.log (‖DirichletCharacter.completedLFunction χ z‖ + 1) :=
          Real.log_nonneg (by linarith)
        have hmax : max (Real.log ‖DirichletCharacter.completedLFunction χ z‖) 0 = 0 := by
          apply max_eq_right; exact Real.log_nonpos hnn h
        rw [hmax]; exact hlog_nn
      · have hlog_nn : 0 ≤ Real.log ‖DirichletCharacter.completedLFunction χ z‖ :=
          Real.log_nonneg h.le
        have hmax : max (Real.log ‖DirichletCharacter.completedLFunction χ z‖) 0 =
            Real.log ‖DirichletCharacter.completedLFunction χ z‖ := max_eq_left hlog_nn
        rw [hmax]
        exact Real.log_le_log (by linarith) (by linarith)
    have h2 := hBd z
    rw [hz_norm] at h2
    linarith
  have h_step1 := Real.circleAverage_mono_on_of_le_circle h_ci h_sphere_bd
  have hC₀_abs_nn : 0 ≤ |C₀| := abs_nonneg _
  have hC₀_le : C₀ ≤ |C₀| := le_abs_self _
  have hR_nn : 0 ≤ R := hR_pos.le
  have hlogR_nn : 0 ≤ Real.log R := Real.log_nonneg hR
  have hlog_R2_nn : 0 ≤ Real.log (R + 2) := Real.log_nonneg (by linarith)
  have hlog_4_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have h_final : C₀ * R * Real.log (R + 2) ≤
      2 * |C₀| * R * Real.log R + |C₀| * 2 * Real.log 4 := by
    rcases le_or_gt R 2 with hR2 | hR2
    · have hR2_bd : R + 2 ≤ 4 := by linarith
      have hR2_pos : 0 < R + 2 := by linarith
      have hlog_R2_le : Real.log (R + 2) ≤ Real.log 4 := Real.log_le_log hR2_pos hR2_bd
      have h_Rle : R ≤ 2 := hR2
      have h1 : C₀ * R * Real.log (R + 2) ≤ |C₀| * R * Real.log (R + 2) := by
        have := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hC₀_le hR_nn) hlog_R2_nn
        linarith
      have h2 : |C₀| * R * Real.log (R + 2) ≤ |C₀| * 2 * Real.log 4 := by
        have hR_bound : R * Real.log (R + 2) ≤ 2 * Real.log 4 := by
          have hR_R2 : R * Real.log (R + 2) ≤ R * Real.log 4 :=
            mul_le_mul_of_nonneg_left hlog_R2_le hR_nn
          have h_R_bound : R * Real.log 4 ≤ 2 * Real.log 4 :=
            mul_le_mul_of_nonneg_right h_Rle hlog_4_pos.le
          linarith
        have := mul_le_mul_of_nonneg_left hR_bound hC₀_abs_nn
        nlinarith
      have h3 : 0 ≤ 2 * |C₀| * R * Real.log R :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC₀_abs_nn) hR_nn) hlogR_nn
      linarith
    · have hR_ge : 2 ≤ R := hR2.le
      have hlog_bd : Real.log (R + 2) ≤ 2 * Real.log R := by
        have h_sq : R + 2 ≤ R ^ 2 := by nlinarith
        have hR2_pos : 0 < R + 2 := by linarith
        have h1 := Real.log_le_log hR2_pos h_sq
        have h2 : Real.log (R ^ 2) = 2 * Real.log R := by
          rw [show (R^2 : ℝ) = R * R from by ring,
              Real.log_mul (ne_of_gt hR_pos) (ne_of_gt hR_pos)]; ring
        linarith
      have h1 : C₀ * R * Real.log (R + 2) ≤ |C₀| * R * Real.log (R + 2) := by
        have := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hC₀_le hR_nn) hlog_R2_nn
        linarith
      have h2 : |C₀| * R * Real.log (R + 2) ≤ |C₀| * R * (2 * Real.log R) := by
        apply mul_le_mul_of_nonneg_left hlog_bd
        exact mul_nonneg hC₀_abs_nn hR_nn
      have h3 : 0 ≤ |C₀| * 2 * Real.log 4 :=
        mul_nonneg (mul_nonneg hC₀_abs_nn (by norm_num)) hlog_4_pos.le
      nlinarith
  linarith

-- Step D: m(R, Prod) ≤ O(R log² R).
theorem LProductMult_proximity_bound {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hχp : χ.IsPrimitive) :
    ∃ C D : ℝ, ∀ R : ℝ, 1 ≤ R →
      proximity (LProductMult χ) R ≤ C * R * (Real.log R) ^ 2 + D := by
  obtain ⟨C₀, D₀, hBd⟩ := LProductMult_pointwise_meanType_bound hχ hχp
  refine ⟨|C₀| * 4, D₀ + |C₀| * 2 * (Real.log 4)^2, fun R hR => ?_⟩
  have hR_pos : 0 < R := by linarith
  have habs : |R| = R := abs_of_pos hR_pos
  unfold proximity
  have h_ci : CircleIntegrable (fun z : ℂ => max (Real.log ‖LProductMult χ z‖) 0) 0 R := by
    have hMero : MeromorphicOn (LProductMult χ) (Metric.sphere (0 : ℂ) |R|) := fun z _ =>
      ((LProductMult_differentiable hχ hχp).analyticAt z).meromorphicAt
    have := circleIntegrable_posLog_norm_meromorphicOn (f := LProductMult χ)
      (c := (0 : ℂ)) (R := R) hMero
    convert this using 1; funext z
    rw [Real.posLog_def, max_comm]; rfl
  have h_sphere_bd : ∀ z ∈ Metric.sphere (0 : ℂ) |R|,
      max (Real.log ‖LProductMult χ z‖) 0 ≤ C₀ * R * (Real.log (R + 2))^2 + D₀ := by
    intro z hz
    have hz_norm : ‖z‖ = R := by
      rw [habs] at hz
      have : dist z 0 = R := hz
      rwa [dist_zero_right] at this
    have hnn : 0 ≤ ‖LProductMult χ z‖ := norm_nonneg _
    have h1 : max (Real.log ‖LProductMult χ z‖) 0 ≤ Real.log (‖LProductMult χ z‖ + 1) := by
      rcases le_or_gt ‖LProductMult χ z‖ 1 with h | h
      · have hlog_nn : 0 ≤ Real.log (‖LProductMult χ z‖ + 1) := Real.log_nonneg (by linarith)
        have hmax : max (Real.log ‖LProductMult χ z‖) 0 = 0 := by
          apply max_eq_right; exact Real.log_nonpos hnn h
        rw [hmax]; exact hlog_nn
      · have hlog_nn : 0 ≤ Real.log ‖LProductMult χ z‖ := Real.log_nonneg h.le
        have hmax : max (Real.log ‖LProductMult χ z‖) 0 = Real.log ‖LProductMult χ z‖ :=
          max_eq_left hlog_nn
        rw [hmax]
        exact Real.log_le_log (by linarith) (by linarith)
    have h2 := hBd z
    rw [hz_norm] at h2
    linarith
  have h_step1 := Real.circleAverage_mono_on_of_le_circle h_ci h_sphere_bd
  have hC₀_abs_nn : 0 ≤ |C₀| := abs_nonneg _
  have hC₀_le : C₀ ≤ |C₀| := le_abs_self _
  have hR_nn : 0 ≤ R := hR_pos.le
  have hlogR_nn : 0 ≤ Real.log R := Real.log_nonneg hR
  have hlogR_sq_nn : 0 ≤ (Real.log R)^2 := sq_nonneg _
  have hlog_R2_nn : 0 ≤ Real.log (R + 2) := Real.log_nonneg (by linarith)
  have hlog_R2_sq_nn : 0 ≤ (Real.log (R+2))^2 := sq_nonneg _
  have hlog_4_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlog_4_nn : 0 ≤ Real.log 4 := hlog_4_pos.le
  have hlog_4_sq_nn : 0 ≤ (Real.log 4)^2 := sq_nonneg _
  have h_final : C₀ * R * (Real.log (R + 2))^2 ≤
      |C₀| * 4 * R * (Real.log R)^2 + |C₀| * 2 * (Real.log 4)^2 := by
    rcases le_or_gt R 2 with hR2 | hR2
    · have hR2_bd : R + 2 ≤ 4 := by linarith
      have hR2_pos : 0 < R + 2 := by linarith
      have hlog_R2_le : Real.log (R + 2) ≤ Real.log 4 := Real.log_le_log hR2_pos hR2_bd
      have hlog_R2_sq_le : (Real.log (R+2))^2 ≤ (Real.log 4)^2 := by
        apply sq_le_sq'
        · linarith
        · exact hlog_R2_le
      have h_Rle : R ≤ 2 := hR2
      have h1 : C₀ * R * (Real.log (R+2))^2 ≤ |C₀| * R * (Real.log (R+2))^2 := by
        have ha : C₀ * R ≤ |C₀| * R := mul_le_mul_of_nonneg_right hC₀_le hR_nn
        have := mul_le_mul_of_nonneg_right ha hlog_R2_sq_nn
        linarith
      have h2 : |C₀| * R * (Real.log (R+2))^2 ≤ |C₀| * 2 * (Real.log 4)^2 := by
        have h2a : R * (Real.log (R+2))^2 ≤ 2 * (Real.log 4)^2 := by
          have hR_le : R * (Real.log (R+2))^2 ≤ R * (Real.log 4)^2 :=
            mul_le_mul_of_nonneg_left hlog_R2_sq_le hR_nn
          have h_R_bound : R * (Real.log 4)^2 ≤ 2 * (Real.log 4)^2 :=
            mul_le_mul_of_nonneg_right h_Rle hlog_4_sq_nn
          linarith
        have := mul_le_mul_of_nonneg_left h2a hC₀_abs_nn
        nlinarith
      have h3 : 0 ≤ |C₀| * 4 * R * (Real.log R)^2 := by positivity
      linarith
    · have hR_ge : 2 ≤ R := hR2.le
      have hlog_bd : Real.log (R + 2) ≤ 2 * Real.log R := by
        have h_sq : R + 2 ≤ R ^ 2 := by nlinarith
        have hR2_pos : 0 < R + 2 := by linarith
        have h1 := Real.log_le_log hR2_pos h_sq
        have h2 : Real.log (R ^ 2) = 2 * Real.log R := by
          rw [show (R^2 : ℝ) = R * R from by ring,
              Real.log_mul (ne_of_gt hR_pos) (ne_of_gt hR_pos)]; ring
        linarith
      have hlog_bd_sq : (Real.log (R + 2))^2 ≤ 4 * (Real.log R)^2 := by
        have hle : (Real.log (R+2))^2 ≤ (2 * Real.log R)^2 := by
          apply sq_le_sq'
          · linarith
          · exact hlog_bd
        calc (Real.log (R+2))^2 ≤ (2 * Real.log R)^2 := hle
          _ = 4 * (Real.log R)^2 := by ring
      have h1 : C₀ * R * (Real.log (R+2))^2 ≤ |C₀| * R * (Real.log (R+2))^2 := by
        have ha : C₀ * R ≤ |C₀| * R := mul_le_mul_of_nonneg_right hC₀_le hR_nn
        have := mul_le_mul_of_nonneg_right ha hlog_R2_sq_nn
        linarith
      have h2 : |C₀| * R * (Real.log (R+2))^2 ≤ |C₀| * R * (4 * (Real.log R)^2) := by
        apply mul_le_mul_of_nonneg_left hlog_bd_sq
        exact mul_nonneg hC₀_abs_nn hR_nn
      have h_expand : |C₀| * R * (4 * (Real.log R)^2) = 4 * |C₀| * R * (Real.log R)^2 := by ring
      have h_eq2 : |C₀| * 4 * R * (Real.log R)^2 = 4 * |C₀| * R * (Real.log R)^2 := by ring
      have h3 : 0 ≤ |C₀| * 2 * (Real.log 4)^2 := by positivity
      linarith
  linarith

-- Step D: m(R, 1/Prod) ≤ O(R log² R).
theorem LProductMult_inv_proximity_bound {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hχp : χ.IsPrimitive) :
    ∃ C D : ℝ, ∀ R : ℝ, 1 ≤ R →
      proximity (fun z => (LProductMult χ z)⁻¹) R ≤ C * R * (Real.log R) ^ 2 + D := by
  obtain ⟨C, D, hPbd⟩ := LProductMult_proximity_bound hχ hχp
  refine ⟨C, D, fun R hR => ?_⟩
  have hR_pos : 0 < R := by linarith
  have hmero : Meromorphic (LProductMult χ) := fun z =>
    ((LProductMult_differentiable hχ hχp).analyticAt z).meromorphicAt
  have hid := @ValueDistribution.proximity_sub_proximity_inv_eq_circleAverage (LProductMult χ) hmero
  have hid_R : ValueDistribution.proximity (LProductMult χ) ⊤ R -
      ValueDistribution.proximity (LProductMult χ)⁻¹ ⊤ R =
      Real.circleAverage (fun x => Real.log ‖LProductMult χ x‖) 0 R := by
    have := congrArg (fun f => f R) hid
    simp only [Pi.sub_apply] at this
    exact this
  have hJensen := LProductMult_circleAverage_log_eq hχ hχp R hR_pos
  have hJnn := LProductMult_jensen_rhs_nonneg hχ hχp R hR
  rw [hJensen] at hid_R
  unfold proximity
  have hP_bridge :
    Real.circleAverage (fun z => max (Real.log ‖LProductMult χ z‖) 0) 0 R =
      ValueDistribution.proximity (LProductMult χ) ⊤ R := by
    rw [ValueDistribution.proximity_top]
    simp only [Real.posLog_def]
    congr 1; funext z; exact max_comm _ _
  have hPinv_bridge :
    Real.circleAverage (fun z => max (Real.log ‖(LProductMult χ z)⁻¹‖) 0) 0 R =
      ValueDistribution.proximity (LProductMult χ)⁻¹ ⊤ R := by
    rw [ValueDistribution.proximity_top]
    simp only [Real.posLog_def]
    congr 1; funext z
    show max (Real.log ‖(LProductMult χ z)⁻¹‖) 0 = max 0 (Real.log ‖(LProductMult χ)⁻¹ z‖)
    simp only [Pi.inv_apply]
    exact max_comm _ _
  rw [hPinv_bridge]
  have h_prox_le :
      ValueDistribution.proximity (LProductMult χ)⁻¹ ⊤ R ≤
      ValueDistribution.proximity (LProductMult χ) ⊤ R := by linarith
  have hP_bound : ValueDistribution.proximity (LProductMult χ) ⊤ R ≤
      C * R * (Real.log R)^2 + D := by
    have := hPbd R hR
    unfold proximity at this
    rw [hP_bridge] at this
    exact this
  linarith

-- Step E: m(R, LOverP) ≤ O(R log² R).
theorem LOverP_proximity_bound {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) :
    ∃ C D : ℝ, ∀ R : ℝ, 1 ≤ R →
      proximity (LOverP χ) R ≤ C * R * (Real.log R) ^ 2 + D := by
  obtain ⟨C_xi, D_xi, hXi⟩ := completedLFunction_proximity_bound hχ hχp
  obtain ⟨C_inv, D_inv, hInv⟩ := LProductMult_inv_proximity_bound hχ hχp
  refine ⟨|C_xi| + |C_inv|, |D_xi| + |D_inv| + Real.log 2 + |C_xi| * Real.exp 1,
    fun R hR => ?_⟩
  have hR_pos : 0 < R := by linarith
  have hR_ne : R ≠ 0 := ne_of_gt hR_pos
  have h_codisc : (fun z => DirichletCharacter.completedLFunction χ z * (LProductMult χ z)⁻¹)
      =ᶠ[Filter.codiscrete ℂ] LOverP χ := by
    have hratio : (fun z => DirichletCharacter.completedLFunction χ z / LProductMult χ z)
        =ᶠ[Filter.codiscrete ℂ] LOverP χ := LOverP_eq_ratio_codiscretely hχ hχp
    filter_upwards [hratio] with z hz
    rw [← hz, div_eq_mul_inv]
  unfold proximity
  have h_bridge_xi :
    Real.circleAverage (fun z => max (Real.log ‖DirichletCharacter.completedLFunction χ z‖) 0) 0 R =
      ValueDistribution.proximity (DirichletCharacter.completedLFunction χ) ⊤ R := by
    rw [ValueDistribution.proximity_top]; simp only [Real.posLog_def]
    congr 1; funext z; exact max_comm _ _
  have h_bridge_xiOverP :
    Real.circleAverage (fun z => max (Real.log ‖LOverP χ z‖) 0) 0 R =
      ValueDistribution.proximity (LOverP χ) ⊤ R := by
    rw [ValueDistribution.proximity_top]; simp only [Real.posLog_def]
    congr 1; funext z; exact max_comm _ _
  have h_bridge_Pinv :
    Real.circleAverage (fun z => max (Real.log ‖(LProductMult χ z)⁻¹‖) 0) 0 R =
      ValueDistribution.proximity (LProductMult χ)⁻¹ ⊤ R := by
    rw [ValueDistribution.proximity_top]; simp only [Real.posLog_def]
    congr 1; funext z
    show max (Real.log ‖(LProductMult χ z)⁻¹‖) 0 = max 0 (Real.log ‖(LProductMult χ)⁻¹ z‖)
    simp only [Pi.inv_apply]; exact max_comm _ _
  rw [h_bridge_xiOverP]
  have h_prox_eq : ValueDistribution.proximity (LOverP χ) ⊤ R =
      ValueDistribution.proximity
        (fun z => DirichletCharacter.completedLFunction χ z * (LProductMult χ z)⁻¹) ⊤ R :=
    (ValueDistribution.proximity_congr_codiscrete h_codisc hR_ne).symm
  rw [h_prox_eq]
  have hmero_xi : Meromorphic (DirichletCharacter.completedLFunction χ) := fun z =>
    ((completedLFunction_differentiable hχ).analyticAt z).meromorphicAt
  have hmero_P : Meromorphic (LProductMult χ) := fun z =>
    ((LProductMult_differentiable hχ hχp).analyticAt z).meromorphicAt
  have hmero_Pinv : Meromorphic (LProductMult χ)⁻¹ := hmero_P.inv
  have h_mul : ValueDistribution.proximity
        (DirichletCharacter.completedLFunction χ * (LProductMult χ)⁻¹) ⊤ ≤
      ValueDistribution.proximity (DirichletCharacter.completedLFunction χ) ⊤ +
        ValueDistribution.proximity (LProductMult χ)⁻¹ ⊤ :=
    ValueDistribution.proximity_mul_top_le hmero_xi hmero_Pinv
  have h_mul_R : ValueDistribution.proximity
        (DirichletCharacter.completedLFunction χ * (LProductMult χ)⁻¹) ⊤ R ≤
      ValueDistribution.proximity (DirichletCharacter.completedLFunction χ) ⊤ R +
        ValueDistribution.proximity (LProductMult χ)⁻¹ ⊤ R := by
    have := h_mul R
    simp only [Pi.add_apply] at this
    exact this
  have h_fun_eq : (fun z => DirichletCharacter.completedLFunction χ z * (LProductMult χ z)⁻¹) =
      (DirichletCharacter.completedLFunction χ * (LProductMult χ)⁻¹) := by
    funext z; rfl
  rw [h_fun_eq]
  have hXi_R : ValueDistribution.proximity (DirichletCharacter.completedLFunction χ) ⊤ R ≤
      C_xi * R * Real.log R + D_xi := by
    have := hXi R hR
    unfold proximity at this
    rw [h_bridge_xi] at this; exact this
  have hInv_R : ValueDistribution.proximity (LProductMult χ)⁻¹ ⊤ R ≤
      C_inv * R * (Real.log R)^2 + D_inv := by
    have := hInv R hR
    unfold proximity at this
    rw [h_bridge_Pinv] at this; exact this
  have h_sum : ValueDistribution.proximity
        (DirichletCharacter.completedLFunction χ * (LProductMult χ)⁻¹) ⊤ R ≤
      C_xi * R * Real.log R + D_xi + (C_inv * R * (Real.log R)^2 + D_inv) := by linarith
  have hR_nn : 0 ≤ R := hR_pos.le
  have hlog_R_nn : 0 ≤ Real.log R := Real.log_nonneg hR
  have hC_xi_le : C_xi ≤ |C_xi| := le_abs_self _
  have hC_inv_le : C_inv ≤ |C_inv| := le_abs_self _
  have hCxi_abs_nn : 0 ≤ |C_xi| := abs_nonneg _
  have hCinv_abs_nn : 0 ≤ |C_inv| := abs_nonneg _
  have hlogSq_nn : 0 ≤ (Real.log R)^2 := sq_nonneg _
  have h_RlogR_bd : R * Real.log R ≤ R * (Real.log R)^2 + Real.exp 1 := by
    rcases le_or_gt R (Real.exp 1) with hRe | hRe
    · have hlogR_le : Real.log R ≤ 1 := by
        have := Real.log_le_log hR_pos hRe
        rwa [Real.log_exp] at this
      have h_RlogR_le_e : R * Real.log R ≤ Real.exp 1 * 1 :=
        mul_le_mul hRe hlogR_le hlog_R_nn (Real.exp_pos _).le
      have h_sqR_nn : 0 ≤ R * (Real.log R)^2 := mul_nonneg hR_nn hlogSq_nn
      linarith
    · have hlogR_ge_one : 1 ≤ Real.log R := by
        have := Real.log_le_log (Real.exp_pos 1) hRe.le
        rwa [Real.log_exp] at this
      have hlog_sq : Real.log R ≤ (Real.log R)^2 := by
        have := mul_le_mul_of_nonneg_left hlogR_ge_one hlog_R_nn
        nlinarith
      have h_RlogR : R * Real.log R ≤ R * (Real.log R)^2 :=
        mul_le_mul_of_nonneg_left hlog_sq hR_nn
      have h_exp_nn : 0 ≤ Real.exp 1 := (Real.exp_pos _).le
      linarith
  have h1 : C_xi * R * Real.log R ≤ |C_xi| * R * (Real.log R)^2 + |C_xi| * Real.exp 1 := by
    have h_step_a : C_xi * R * Real.log R ≤ |C_xi| * R * Real.log R := by
      have h_l1 : C_xi * R ≤ |C_xi| * R := mul_le_mul_of_nonneg_right hC_xi_le hR_nn
      exact mul_le_mul_of_nonneg_right h_l1 hlog_R_nn
    have h_step_b : |C_xi| * R * Real.log R ≤ |C_xi| * (R * (Real.log R)^2 + Real.exp 1) := by
      have := mul_le_mul_of_nonneg_left h_RlogR_bd hCxi_abs_nn
      nlinarith
    linarith
  have h2 : C_inv * R * (Real.log R)^2 ≤ |C_inv| * R * (Real.log R)^2 := by
    have h_l1 : C_inv * R ≤ |C_inv| * R := mul_le_mul_of_nonneg_right hC_inv_le hR_nn
    exact mul_le_mul_of_nonneg_right h_l1 hlogSq_nn
  have hlog2_nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hD_xi_le : D_xi ≤ |D_xi| := le_abs_self _
  have hD_inv_le : D_inv ≤ |D_inv| := le_abs_self _
  linarith

-- Step F: Poisson — pointwise bound from proximity.
theorem LOverP_pointwise_log_bound {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) :
    ∃ C D : ℝ, ∀ z : ℂ,
      Real.log ‖LOverP χ z‖ ≤ C * ‖z‖ * (Real.log (‖z‖ + 2)) ^ 2 + D := by
  obtain ⟨Cp, Dp, hProx⟩ := LOverP_proximity_bound hχ hχp
  refine ⟨72 * |Cp|, 48 * |Cp| * (Real.log 3)^2 + 3 * |Dp|, fun z => ?_⟩
  have hLogCont : Continuous (fun z => Real.log ‖LOverP χ z‖) :=
    Continuous.log (continuous_norm.comp (LOverP_differentiable hχ hχp).continuous)
      (fun z => norm_ne_zero_iff.mpr (LOverP_ne_zero hχ hχp z))
  set t := ‖z‖ with ht_def
  have ht_nn : 0 ≤ t := norm_nonneg _
  set R : ℝ := 2 * t + 2 with hR_def
  have hR_pos : 0 < R := by rw [hR_def]; linarith
  have hR_ge_one : 1 ≤ R := by rw [hR_def]; linarith
  have htR : t < R := by rw [hR_def]; linarith
  have hR_sub : R - t = t + 2 := by rw [hR_def]; ring
  have hR_add : R + t = 3*t + 2 := by rw [hR_def]; ring
  have hHarm : InnerProductSpace.HarmonicOnNhd (fun z => Real.log ‖LOverP χ z‖)
      (Metric.closedBall (0:ℂ) R) :=
    fun x _ => (LOverP_analyticAt hχ hχp x).harmonicAt_log_norm (LOverP_ne_zero hχ hχp x)
  have hzB : z ∈ Metric.ball (0:ℂ) R := by
    rw [Metric.mem_ball, dist_zero_right]; exact htR
  have hPoissonEq := hHarm.circleAverage_poissonKernel_smul hzB
  have hPCont : ContinuousOn (fun x => poissonKernel 0 z x) (Metric.sphere (0:ℂ) R) := by
    rw [poissonKernel_eq_re_herglotzRieszKernel]
    refine Complex.continuous_re.continuousOn.comp ?_ (fun _ _ => Set.mem_univ _)
    rw [herglotzRieszKernel_fun_def]
    simp only [sub_zero]
    refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
    intro x hx
    have hxR : ‖x‖ = R := by
      have : dist x 0 = R := hx
      rwa [dist_zero_right] at this
    intro hzero
    have hzw : x = z := by
      have h0 : x - z = 0 := by linear_combination hzero
      linear_combination h0
    rw [hzw] at hxR; linarith
  set M : ℝ := (R + t) / (R - t) with hM_def
  have hR_sub_pos : 0 < R - t := by linarith
  have hR_add_nn : 0 ≤ R + t := by linarith
  have hM_nn : 0 ≤ M := div_nonneg hR_add_nn hR_sub_pos.le
  have hM_le_3 : M ≤ 3 := by
    rw [hM_def, hR_sub, hR_add]
    have h2 : 0 < t + 2 := by linarith
    rw [div_le_iff₀ h2]; linarith
  have hBd : ∀ x ∈ Metric.sphere (0:ℂ) |R|,
      (poissonKernel 0 z • (fun w => Real.log ‖LOverP χ w‖)) x ≤
        M * max (Real.log ‖LOverP χ x‖) 0 := by
    intro x hx
    have hxR : x ∈ Metric.sphere (0:ℂ) R := by
      rw [show |R| = R from abs_of_pos hR_pos] at hx; exact hx
    have hP_le_M : poissonKernel 0 z x ≤ M := by
      rw [poissonKernel_eq_re_herglotzRieszKernel]
      have h := re_herglotzRieszKernel_le (c := (0:ℂ)) (R := R) (z := x) (w := z) hxR hzB
      simp only [Function.comp_apply]
      rw [herglotzRieszKernel_def]
      simpa using h
    have hP_nn : 0 ≤ poissonKernel 0 z x := by
      rw [poissonKernel_eq_re_herglotzRieszKernel]
      have hineq := le_re_herglotzRieszKernel (c := (0:ℂ)) (R := R) (z := x) (w := z) hxR hzB
      simp only [Function.comp_apply]
      rw [herglotzRieszKernel_def]
      have h_lb : 0 ≤ (R - t) / (R + t) :=
        div_nonneg hR_sub_pos.le hR_add_nn
      simp only [sub_zero] at hineq
      simp only [sub_zero]
      linarith
    have hlog_le : Real.log ‖LOverP χ x‖ ≤ max (Real.log ‖LOverP χ x‖) 0 := le_max_left _ _
    show poissonKernel 0 z x * Real.log ‖LOverP χ x‖ ≤ M * max (Real.log ‖LOverP χ x‖) 0
    have hmax_nn : 0 ≤ max (Real.log ‖LOverP χ x‖) 0 := le_max_right _ _
    calc poissonKernel 0 z x * Real.log ‖LOverP χ x‖
        ≤ poissonKernel 0 z x * max (Real.log ‖LOverP χ x‖) 0 :=
          mul_le_mul_of_nonneg_left hlog_le hP_nn
      _ ≤ M * max (Real.log ‖LOverP χ x‖) 0 := mul_le_mul_of_nonneg_right hP_le_M hmax_nn
  have hCI_Plog : CircleIntegrable (poissonKernel 0 z • (fun w => Real.log ‖LOverP χ w‖)) 0 R := by
    refine ContinuousOn.circleIntegrable (hR := hR_pos.le) ?_
    exact ContinuousOn.mul hPCont hLogCont.continuousOn
  have hMero_xi : MeromorphicOn (LOverP χ) (Metric.sphere (0:ℂ) |R|) := fun x _ =>
    (LOverP_analyticAt hχ hχp x).meromorphicAt
  have hCI_posLog : CircleIntegrable (fun w => max (Real.log ‖LOverP χ w‖) 0) 0 R := by
    have := circleIntegrable_posLog_norm_meromorphicOn (f := LOverP χ)
      (c := (0:ℂ)) (R := R) hMero_xi
    convert this using 1; funext w
    rw [Real.posLog_def, max_comm]; rfl
  have hCI_Mpos : CircleIntegrable (fun w => M * max (Real.log ‖LOverP χ w‖) 0) 0 R :=
    hCI_posLog.const_mul M
  have h_ca_mono := Real.circleAverage_mono hCI_Plog hCI_Mpos hBd
  rw [hPoissonEq] at h_ca_mono
  have h_rhs_eq : Real.circleAverage (fun w => M * max (Real.log ‖LOverP χ w‖) 0) 0 R =
      M * proximity (LOverP χ) R := by
    unfold proximity
    have h1 : (fun w => M * max (Real.log ‖LOverP χ w‖) 0) =
        (M • fun w => max (Real.log ‖LOverP χ w‖) 0) := by funext w; rfl
    rw [h1, Real.circleAverage_smul, smul_eq_mul]
  rw [h_rhs_eq] at h_ca_mono
  have hPoisson : Real.log ‖LOverP χ z‖ ≤ M * proximity (LOverP χ) R := h_ca_mono
  have hProxR : proximity (LOverP χ) R ≤ Cp * R * (Real.log R)^2 + Dp := hProx R hR_ge_one
  have hProx_nn : 0 ≤ proximity (LOverP χ) R := proximity_nonneg _ _
  have habsCp : Cp ≤ |Cp| := le_abs_self _
  have habsCp_nn : 0 ≤ |Cp| := abs_nonneg _
  have habsDp : Dp ≤ |Dp| := le_abs_self _
  have habsDp_nn : 0 ≤ |Dp| := abs_nonneg _
  have hlogR_nn : 0 ≤ Real.log R := Real.log_nonneg hR_ge_one
  have hR_nn : 0 ≤ R := hR_pos.le
  have h1 : Real.log ‖LOverP χ z‖ ≤ 3 * proximity (LOverP χ) R := by
    have hProd_le : M * proximity (LOverP χ) R ≤ 3 * proximity (LOverP χ) R :=
      mul_le_mul_of_nonneg_right hM_le_3 hProx_nn
    linarith
  have h2 : proximity (LOverP χ) R ≤ |Cp| * R * (Real.log R)^2 + |Dp| := by
    have h_Cp : Cp * R * (Real.log R)^2 ≤ |Cp| * R * (Real.log R)^2 := by
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right habsCp hR_nn)
        (sq_nonneg (Real.log R))
      linarith
    linarith
  have h3 : Real.log ‖LOverP χ z‖ ≤ 3 * |Cp| * R * (Real.log R)^2 + 3 * |Dp| := by
    have h23 : 3 * proximity (LOverP χ) R ≤ 3 * (|Cp| * R * (Real.log R)^2 + |Dp|) := by
      apply mul_le_mul_of_nonneg_left h2 (by norm_num)
    linarith
  have ht_plus_2_pos : 0 < t + 2 := by linarith
  have hlog_t2_ge_log2 : Real.log 2 ≤ Real.log (t + 2) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlog_t2_nn : 0 ≤ Real.log (t + 2) := Real.log_nonneg (by linarith)
  have hlogR_le : Real.log R ≤ 2 * Real.log (t + 2) := by
    have hR_eq : R = 2 * (t + 1) := by rw [hR_def]; ring
    rw [hR_eq]
    have h2_pos : (0:ℝ) < 2 := by norm_num
    have ht1_pos : 0 < t + 1 := by linarith
    rw [Real.log_mul (ne_of_gt h2_pos) (ne_of_gt ht1_pos)]
    have hlog_t1_le : Real.log (t + 1) ≤ Real.log (t + 2) :=
      Real.log_le_log ht1_pos (by linarith)
    linarith
  have hlogSq_le : (Real.log R)^2 ≤ 4 * (Real.log (t + 2))^2 := by
    have : (Real.log R)^2 ≤ (2 * Real.log (t + 2))^2 := by
      apply sq_le_sq'
      · linarith
      · exact hlogR_le
    calc (Real.log R)^2 ≤ (2 * Real.log (t + 2))^2 := this
      _ = 4 * (Real.log (t + 2))^2 := by ring
  have hR_le : R ≤ 2 * (t + 2) := by rw [hR_def]; linarith
  have hRlogSq_le : R * (Real.log R)^2 ≤
      8 * t * (Real.log (t+2))^2 + 16 * (Real.log (t+2))^2 := by
    have hsq_nn : 0 ≤ (Real.log (t+2))^2 := sq_nonneg _
    have hstep1 : R * (Real.log R)^2 ≤ R * (4 * (Real.log (t+2))^2) :=
      mul_le_mul_of_nonneg_left hlogSq_le hR_nn
    have hstep2 : R * (4 * (Real.log (t+2))^2) ≤ 2*(t+2) * (4 * (Real.log (t+2))^2) := by
      apply mul_le_mul_of_nonneg_right hR_le
      exact mul_nonneg (by norm_num) hsq_nn
    have h_expand : 2*(t+2) * (4 * (Real.log (t+2))^2) =
        8 * t * (Real.log (t+2))^2 + 16 * (Real.log (t+2))^2 := by ring
    linarith
  have hlog_t2_sq_bound : (Real.log (t+2))^2 ≤ t * (Real.log (t+2))^2 + (Real.log 3)^2 := by
    rcases le_or_gt 1 t with ht1 | ht1
    · have : (Real.log (t+2))^2 ≤ t * (Real.log (t+2))^2 := by
        have h := mul_le_mul_of_nonneg_right ht1 (sq_nonneg (Real.log (t+2)))
        linarith
      have hlog3_sq_nn : 0 ≤ (Real.log 3)^2 := sq_nonneg _
      linarith
    · have hlog_le_log3 : Real.log (t+2) ≤ Real.log 3 :=
        Real.log_le_log ht_plus_2_pos (by linarith)
      have hlog_t2_sq_le : (Real.log (t+2))^2 ≤ (Real.log 3)^2 := by
        apply sq_le_sq'
        · have hlog3_nn : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
          linarith
        · exact hlog_le_log3
      have ht_log : 0 ≤ t * (Real.log (t+2))^2 := mul_nonneg ht_nn (sq_nonneg _)
      linarith
  have hRlogSq_simplified : R * (Real.log R)^2 ≤
      24 * t * (Real.log (t+2))^2 + 16 * (Real.log 3)^2 := by
    have h := hlog_t2_sq_bound
    have h16 : 16 * (Real.log (t+2))^2 ≤ 16 * (t * (Real.log (t+2))^2 + (Real.log 3)^2) := by
      apply mul_le_mul_of_nonneg_left h (by norm_num)
    have h16' : 16 * (t * (Real.log (t+2))^2 + (Real.log 3)^2) =
        16 * t * (Real.log (t+2))^2 + 16 * (Real.log 3)^2 := by ring
    linarith
  have h_final_term : 3 * |Cp| * R * (Real.log R)^2 ≤
      72 * |Cp| * t * (Real.log (t+2))^2 + 48 * |Cp| * (Real.log 3)^2 := by
    have h3Cp_nn : 0 ≤ 3 * |Cp| := by positivity
    have := mul_le_mul_of_nonneg_left hRlogSq_simplified h3Cp_nn
    nlinarith [habsCp_nn, sq_nonneg (Real.log (t+2)), sq_nonneg (Real.log 3), ht_nn]
  linarith

/-- **UNCONDITIONAL growth bound** on `LOverP χ`. -/
theorem LOverP_growth_meanType {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) :
    ∃ C D : ℝ, ∀ z : ℂ,
      ‖LOverP χ z‖ ≤ Real.exp (C * ‖z‖ * (Real.log (‖z‖ + 2)) ^ 2 + D) := by
  obtain ⟨C, D, hBound⟩ := LOverP_pointwise_log_bound hχ hχp
  refine ⟨C, D, fun z => ?_⟩
  have h_xi_ne : LOverP χ z ≠ 0 := LOverP_ne_zero hχ hχp z
  have h_pos : 0 < ‖LOverP χ z‖ := norm_pos_iff.mpr h_xi_ne
  have h_logle : Real.log ‖LOverP χ z‖ ≤ C * ‖z‖ * (Real.log (‖z‖ + 2)) ^ 2 + D := hBound z
  have h_exp_mono :
      Real.exp (Real.log ‖LOverP χ z‖) ≤
        Real.exp (C * ‖z‖ * (Real.log (‖z‖ + 2)) ^ 2 + D) :=
    Real.exp_le_exp.mpr h_logle
  rw [Real.exp_log h_pos] at h_exp_mono
  exact h_exp_mono

end DirichletLHadamard

#print axioms DirichletLHadamard.LOverP_growth_meanType
