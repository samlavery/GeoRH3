import RequestProject.DirichletLRightBound

/-!
# `hStrip`: order-1 log bound on `Λ(s,χ)` for `0 < Re s ≤ 1`

Split at `Re s = ½`. Upper half `[½,1]` is `completedL_bound_strip_upper` (direct). Lower half `(0,½)`
uses the FE `Λ_χ(s) = N^{½−s}·rootNumber·Λ_{χ⁻¹}(1−s)` with `Re(1−s) ∈ (½,1)`, handing off to
`completedL_bound_strip_upper` for `χ⁻¹`. The `N^{½−s}` factor is now bounded (`½−Re s ∈ (0,½)`).
-/

open Complex

namespace DirichletLHadamard

variable {N : ℕ} [NeZero N]

/-- **Strip lower half `(0,½]`** via the functional equation onto `strip_upper` for `χ⁻¹`. -/
theorem completedL_bound_strip_lower {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) :
    ∃ C > (0 : ℝ), ∃ R₀ > (0 : ℝ), ∀ s : ℂ, R₀ ≤ ‖s‖ → 0 < s.re → s.re ≤ 1 / 2 →
      Real.log (‖DirichletCharacter.completedLFunction χ s‖ + 1) ≤ C * ‖s‖ * Real.log ‖s‖ := by
  have hχinv : χ⁻¹ ≠ 1 := fun h => hχ (inv_eq_one.mp h)
  obtain ⟨Cv, hCv, Rv, hRv, hUpper⟩ := completedL_bound_strip_upper hχinv
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast NeZero.pos N
  have hcN0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast NeZero.one_le)
  have hcR0 : 0 ≤ Real.log (‖χ.rootNumber‖ + 1) :=
    Real.log_nonneg (by have := norm_nonneg χ.rootNumber; linarith)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  refine ⟨2 * Real.log (N : ℝ) + Real.log (‖χ.rootNumber‖ + 1) + 2 * Cv * Real.log 2 + 2 * Cv + 10,
    by nlinarith [hcN0, hcR0, hCv, hlog2], Rv + Real.exp 1 + 1,
    by have := Real.exp_pos 1; linarith, fun s hsR hlo hhi => ?_⟩
  have hexp_le : Real.exp 1 ≤ ‖s‖ := by linarith
  have hsnorm : 0 < ‖s‖ := lt_of_lt_of_le (Real.exp_pos 1) hexp_le
  have hs1 : (1 : ℝ) ≤ ‖s‖ := le_trans (by have := Real.exp_one_gt_d9; linarith) hexp_le
  have hlog1 : (1 : ℝ) ≤ Real.log ‖s‖ := by
    have := Real.log_le_log (Real.exp_pos 1) hexp_le; rwa [Real.log_exp] at this
  have hreabs : -s.re ≤ ‖s‖ := le_trans (neg_le_abs _) (Complex.abs_re_le_norm s)
  have hX1 : (1 : ℝ) ≤ ‖s‖ * Real.log ‖s‖ := by nlinarith
  have hXs : ‖s‖ ≤ ‖s‖ * Real.log ‖s‖ := by nlinarith
  have hFE : DirichletCharacter.completedLFunction χ s
      = (N : ℂ) ^ ((1 : ℂ) / 2 - s) * χ.rootNumber
        * DirichletCharacter.completedLFunction χ⁻¹ (1 - s) := by
    have h := hχp.completedLFunction_one_sub (1 - s)
    rw [show (1 : ℂ) - (1 - s) = s by ring, show (1 - s) - 1 / 2 = (1 : ℂ) / 2 - s by ring] at h
    exact h
  have hNpow : ‖(N : ℂ) ^ ((1 : ℂ) / 2 - s)‖ = (N : ℝ) ^ ((1 : ℝ) / 2 - s.re) := by
    rw [show ((N : ℂ)) = (((N : ℝ)) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos hN0]
    congr 1
    simp [Complex.sub_re, Complex.div_re, Complex.normSq]
  have hAnn : (0 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 - s.re) := Real.rpow_nonneg hN0.le _
  have hRnn : (0 : ℝ) ≤ ‖χ.rootNumber‖ := norm_nonneg _
  have hDnn : (0 : ℝ) ≤ ‖DirichletCharacter.completedLFunction χ⁻¹ (1 - s)‖ := norm_nonneg _
  have hnormΛ : ‖DirichletCharacter.completedLFunction χ s‖
      = (N : ℝ) ^ ((1 : ℝ) / 2 - s.re) * ‖χ.rootNumber‖
        * ‖DirichletCharacter.completedLFunction χ⁻¹ (1 - s)‖ := by
    rw [hFE, norm_mul, norm_mul, hNpow]
  have hsplit : Real.log (‖DirichletCharacter.completedLFunction χ s‖ + 1)
      ≤ Real.log ((N : ℝ) ^ ((1 : ℝ) / 2 - s.re) + 1) + Real.log (‖χ.rootNumber‖ + 1)
        + Real.log (‖DirichletCharacter.completedLFunction χ⁻¹ (1 - s)‖ + 1) := by
    rw [hnormΛ]
    have h1 := GammaBound.log_mul_add_one_le (mul_nonneg hAnn hRnn) hDnn
    have h2 := GammaBound.log_mul_add_one_le hAnn hRnn
    linarith
  have hNA : Real.log ((N : ℝ) ^ ((1 : ℝ) / 2 - s.re) + 1)
      ≤ 2 * (Real.log (N : ℝ) * (‖s‖ * Real.log ‖s‖)) + 1 := by
    have hNterm : Real.log ((N : ℝ) ^ ((1 : ℝ) / 2 - s.re) + 1)
        ≤ ((1 : ℝ) / 2 - s.re) * Real.log (N : ℝ) + 1 := by
      apply GammaBound.log_add_one_le hAnn (mul_nonneg (by linarith) hcN0)
      rw [Real.log_rpow hN0]
    have hle : (1 : ℝ) / 2 - s.re ≤ 2 * ‖s‖ := by linarith [hreabs, hs1]
    have hstep1 : ((1 : ℝ) / 2 - s.re) * Real.log (N : ℝ) ≤ (2 * ‖s‖) * Real.log (N : ℝ) :=
      mul_le_mul_of_nonneg_right hle hcN0
    have hstep2 : Real.log (N : ℝ) * ‖s‖ ≤ Real.log (N : ℝ) * (‖s‖ * Real.log ‖s‖) :=
      mul_le_mul_of_nonneg_left hXs hcN0
    nlinarith [hNterm, hstep1, hstep2]
  have hRA : Real.log (‖χ.rootNumber‖ + 1)
      ≤ Real.log (‖χ.rootNumber‖ + 1) * (‖s‖ * Real.log ‖s‖) := by nlinarith [hcR0, hX1]
  have h1s_ge : ‖s‖ - 1 ≤ ‖1 - s‖ := by
    have h1 : ‖s‖ - ‖(1 : ℂ)‖ ≤ ‖1 - s‖ := by
      rw [show (1 : ℂ) - s = -(s - 1) by ring, norm_neg]; exact norm_sub_norm_le s 1
    rw [norm_one] at h1; linarith
  have hRe1s_lo : 1 / 2 ≤ (1 - s).re := by rw [Complex.sub_re, Complex.one_re]; linarith
  have hRe1s_hi : (1 - s).re ≤ 1 := by rw [Complex.sub_re, Complex.one_re]; linarith
  have hnorm1s : Rv ≤ ‖1 - s‖ := by linarith [Real.exp_pos 1]
  have h1s_pos : 0 < ‖1 - s‖ := lt_of_lt_of_le hRv hnorm1s
  have h1s_one : (1 : ℝ) ≤ ‖1 - s‖ := by have := Real.exp_one_gt_d9; linarith
  have h1s_le : ‖1 - s‖ ≤ 2 * ‖s‖ := by
    have h2 : ‖1 - s‖ ≤ ‖(1 : ℂ)‖ + ‖s‖ := by
      rw [show (1 : ℂ) - s = (1 : ℂ) + (-s) by ring]
      exact le_trans (norm_add_le _ _) (by rw [norm_neg])
    rw [norm_one] at h2; linarith
  have hlog1s : Real.log ‖1 - s‖ ≤ Real.log 2 + Real.log ‖s‖ := by
    calc Real.log ‖1 - s‖ ≤ Real.log (2 * ‖s‖) := Real.log_le_log h1s_pos h1s_le
      _ = Real.log 2 + Real.log ‖s‖ := Real.log_mul (by norm_num) (ne_of_gt hsnorm)
  have hDterm := hUpper (1 - s) hnorm1s hRe1s_lo hRe1s_hi
  have hDA : Real.log (‖DirichletCharacter.completedLFunction χ⁻¹ (1 - s)‖ + 1)
      ≤ 2 * (Cv * Real.log 2 * (‖s‖ * Real.log ‖s‖)) + 2 * (Cv * (‖s‖ * Real.log ‖s‖)) := by
    have hmono : ‖1 - s‖ * Real.log ‖1 - s‖ ≤ 2 * ‖s‖ * (Real.log 2 + Real.log ‖s‖) :=
      mul_le_mul h1s_le hlog1s (Real.log_nonneg h1s_one) (by linarith)
    have hCmono : Cv * (‖1 - s‖ * Real.log ‖1 - s‖)
        ≤ Cv * (2 * ‖s‖ * (Real.log 2 + Real.log ‖s‖)) :=
      mul_le_mul_of_nonneg_left hmono hCv.le
    have hterm1 : Cv * Real.log 2 * ‖s‖ ≤ Cv * Real.log 2 * (‖s‖ * Real.log ‖s‖) :=
      mul_le_mul_of_nonneg_left hXs (mul_nonneg hCv.le hlog2)
    nlinarith [hDterm, hCmono, hterm1]
  nlinarith [hsplit, hNA, hRA, hDA, hX1, hcN0, hcR0, hCv, hlog2]

/-- **`hStrip`.** For `0 < Re s ≤ 1` (primitive `χ ≠ 1`) and `‖s‖ ≥ R₀`,
    `log(‖Λ(s,χ)‖+1) ≤ C·‖s‖·log‖s‖`. Upper half direct, lower half by FE. -/
theorem completedL_bound_strip {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) :
    ∃ C > (0 : ℝ), ∃ R₀ > (0 : ℝ), ∀ s : ℂ, R₀ ≤ ‖s‖ → 0 < s.re → s.re ≤ 1 →
      Real.log (‖DirichletCharacter.completedLFunction χ s‖ + 1) ≤ C * ‖s‖ * Real.log ‖s‖ := by
  obtain ⟨Cu, hCu, Ru, hRu, hUpper⟩ := completedL_bound_strip_upper hχ
  obtain ⟨Cl, hCl, Rl, hRl, hLower⟩ := completedL_bound_strip_lower hχ hχp
  refine ⟨max Cu Cl, lt_of_lt_of_le hCu (le_max_left _ _), max Ru Rl,
    lt_of_lt_of_le hRu (le_max_left _ _), fun s hsR hlo hhi => ?_⟩
  have hLnn : 0 ≤ Real.log (‖DirichletCharacter.completedLFunction χ s‖ + 1) :=
    Real.log_nonneg (by have := norm_nonneg (DirichletCharacter.completedLFunction χ s); linarith)
  by_cases hcase : 1 / 2 ≤ s.re
  · have hb := hUpper s (le_trans (le_max_left _ _) hsR) hcase hhi
    have hX0 : 0 ≤ ‖s‖ * Real.log ‖s‖ := by nlinarith [hb, hLnn, hCu]
    nlinarith [hb, hX0, le_max_left Cu Cl]
  · push_neg at hcase
    have hb := hLower s (le_trans (le_max_right _ _) hsR) hlo (le_of_lt hcase)
    have hX0 : 0 ≤ ‖s‖ * Real.log ‖s‖ := by nlinarith [hb, hLnn, hCl]
    nlinarith [hb, hX0, le_max_right Cu Cl]

end DirichletLHadamard

#print axioms DirichletLHadamard.completedL_bound_strip_lower
#print axioms DirichletLHadamard.completedL_bound_strip
