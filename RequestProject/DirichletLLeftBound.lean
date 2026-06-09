import RequestProject.DirichletLRightBound

/-!
# `hLeft`: order-1 log bound on `Λ(s,χ)` for `Re s ≤ 0`, via the functional equation

`Λ_χ(s) = N^{½−s}·rootNumber(χ)·Λ_{χ⁻¹}(1−s)` (FE at `1−s`). For `Re s ≤ 0`, `Re(1−s) ≥ 1`, so the
right factor is governed by `completedL_bound_right` for `χ⁻¹`. The `N^{½−s}` factor and the fixed
constant `‖rootNumber‖` are absorbed into `C·‖s‖·log‖s‖`.
-/

open Complex

namespace DirichletLHadamard

variable {N : ℕ} [NeZero N]

/-- **`hLeft`.** For `Re s ≤ 0` (primitive `χ ≠ 1`) and `‖s‖ ≥ R₀`,
    `log(‖Λ(s,χ)‖+1) ≤ C·‖s‖·log‖s‖`. -/
theorem completedL_bound_left {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) :
    ∃ C > (0 : ℝ), ∃ R₀ > (0 : ℝ), ∀ s : ℂ, R₀ ≤ ‖s‖ → s.re ≤ 0 →
      Real.log (‖DirichletCharacter.completedLFunction χ s‖ + 1) ≤ C * ‖s‖ * Real.log ‖s‖ := by
  have hχinv : χ⁻¹ ≠ 1 := fun h => hχ (inv_eq_one.mp h)
  obtain ⟨C₁, hC₁, R₁, hR₁, hRight⟩ := completedL_bound_right hχinv
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast NeZero.pos N
  have hcN0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast NeZero.one_le)
  have hcR0 : 0 ≤ Real.log (‖χ.rootNumber‖ + 1) :=
    Real.log_nonneg (by have := norm_nonneg χ.rootNumber; linarith)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  refine ⟨2 * Real.log (N : ℝ) + Real.log (‖χ.rootNumber‖ + 1) + 2 * C₁ * Real.log 2 + 2 * C₁ + 10,
    by nlinarith [hcN0, hcR0, hC₁, hlog2], R₁ + Real.exp 1 + 1,
    by have := Real.exp_pos 1; linarith, fun s hsR hsre => ?_⟩
  -- basics
  have hexp_le : Real.exp 1 ≤ ‖s‖ := by linarith
  have hsnorm : 0 < ‖s‖ := lt_of_lt_of_le (Real.exp_pos 1) hexp_le
  have hs1 : (1 : ℝ) ≤ ‖s‖ := le_trans (by have := Real.exp_one_gt_d9; linarith) hexp_le
  have hlog1 : (1 : ℝ) ≤ Real.log ‖s‖ := by
    have := Real.log_le_log (Real.exp_pos 1) hexp_le; rwa [Real.log_exp] at this
  have hreabs : -s.re ≤ ‖s‖ := le_trans (neg_le_abs _) (Complex.abs_re_le_norm s)
  have hX1 : (1 : ℝ) ≤ ‖s‖ * Real.log ‖s‖ := by nlinarith
  have hXs : ‖s‖ ≤ ‖s‖ * Real.log ‖s‖ := by nlinarith
  -- FE: Λ_χ(s) = N^{½−s}·rootNumber·Λ_{χ⁻¹}(1−s)
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
  -- split into three log terms
  have hsplit : Real.log (‖DirichletCharacter.completedLFunction χ s‖ + 1)
      ≤ Real.log ((N : ℝ) ^ ((1 : ℝ) / 2 - s.re) + 1) + Real.log (‖χ.rootNumber‖ + 1)
        + Real.log (‖DirichletCharacter.completedLFunction χ⁻¹ (1 - s)‖ + 1) := by
    rw [hnormΛ]
    have h1 := GammaBound.log_mul_add_one_le (mul_nonneg hAnn hRnn) hDnn
    have h2 := GammaBound.log_mul_add_one_le hAnn hRnn
    linarith
  -- N term ≤ 2·logN·(‖s‖·log‖s‖) + 1
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
    have hbk : ((1 : ℝ) / 2 - s.re) * Real.log (N : ℝ)
        ≤ 2 * (Real.log (N : ℝ) * (‖s‖ * Real.log ‖s‖)) := by nlinarith [hstep1, hstep2]
    linarith
  -- rootNumber term ≤ cR·(‖s‖·log‖s‖)
  have hRA : Real.log (‖χ.rootNumber‖ + 1)
      ≤ Real.log (‖χ.rootNumber‖ + 1) * (‖s‖ * Real.log ‖s‖) := by nlinarith [hcR0, hX1]
  -- D term via hRight at 1−s
  have h1s_ge : ‖s‖ - 1 ≤ ‖1 - s‖ := by
    have h1 : ‖s‖ - ‖(1 : ℂ)‖ ≤ ‖1 - s‖ := by
      rw [show (1 : ℂ) - s = -(s - 1) by ring, norm_neg]; exact norm_sub_norm_le s 1
    rw [norm_one] at h1; linarith
  have hRe1s : 1 ≤ (1 - s).re := by rw [Complex.sub_re, Complex.one_re]; linarith
  have hnorm1s : R₁ ≤ ‖1 - s‖ := by linarith [Real.exp_pos 1]
  have h1s_pos : 0 < ‖1 - s‖ := lt_of_lt_of_le hR₁ hnorm1s
  have h1s_one : (1 : ℝ) ≤ ‖1 - s‖ := by have := Real.exp_one_gt_d9; linarith
  have h1s_le : ‖1 - s‖ ≤ 2 * ‖s‖ := by
    have h2 : ‖1 - s‖ ≤ ‖(1 : ℂ)‖ + ‖s‖ := by
      rw [show (1 : ℂ) - s = (1 : ℂ) + (-s) by ring]
      exact le_trans (norm_add_le _ _) (by rw [norm_neg])
    rw [norm_one] at h2; linarith
  have hlog1s : Real.log ‖1 - s‖ ≤ Real.log 2 + Real.log ‖s‖ := by
    calc Real.log ‖1 - s‖ ≤ Real.log (2 * ‖s‖) := Real.log_le_log h1s_pos h1s_le
      _ = Real.log 2 + Real.log ‖s‖ := Real.log_mul (by norm_num) (ne_of_gt hsnorm)
  have hDterm := hRight (1 - s) hnorm1s hRe1s
  have hDA : Real.log (‖DirichletCharacter.completedLFunction χ⁻¹ (1 - s)‖ + 1)
      ≤ 2 * (C₁ * Real.log 2 * (‖s‖ * Real.log ‖s‖)) + 2 * (C₁ * (‖s‖ * Real.log ‖s‖)) := by
    have hmono : ‖1 - s‖ * Real.log ‖1 - s‖ ≤ 2 * ‖s‖ * (Real.log 2 + Real.log ‖s‖) :=
      mul_le_mul h1s_le hlog1s (Real.log_nonneg h1s_one) (by linarith)
    have hCmono : C₁ * (‖1 - s‖ * Real.log ‖1 - s‖)
        ≤ C₁ * (2 * ‖s‖ * (Real.log 2 + Real.log ‖s‖)) :=
      mul_le_mul_of_nonneg_left hmono hC₁.le
    have hterm1 : C₁ * Real.log 2 * ‖s‖ ≤ C₁ * Real.log 2 * (‖s‖ * Real.log ‖s‖) :=
      mul_le_mul_of_nonneg_left hXs (mul_nonneg hC₁.le hlog2)
    nlinarith [hDterm, hCmono, hterm1]
  -- assemble (linear in the product atoms)
  nlinarith [hsplit, hNA, hRA, hDA, hX1, hcN0, hcR0, hC₁, hlog2]

end DirichletLHadamard

#print axioms DirichletLHadamard.completedL_bound_left
