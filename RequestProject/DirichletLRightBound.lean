import RequestProject.DirichletLGammaFactor
import RequestProject.DirichletLGrowth

/-!
# `hRight`: order-1 log bound on `Λ(s,χ)` for `Re s > 1`

`Λ = gammaFactor · L`, so `log(‖Λ‖+1) ≤ log(‖gammaFactor‖+1) + log(‖L‖+1)`
(`log_mul_add_one_le`). The first is `log_norm_gammaFactor_le` + `log_add_one_le`; the second is the
polynomial L-bound `LFunction_norm_le_of_pos_re`. Bookkeeping then gives `≤ C·‖s‖·log‖s‖`.
-/

open Complex

namespace DirichletLHadamard

variable {N : ℕ} [NeZero N]

/-- Uniform-`B` form of the `L`-bound (same proof as `LFunction_norm_le_of_pos_re`, `B` hoisted). -/
private theorem L_bound_uniform {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, 0 < s.re →
      ‖DirichletCharacter.LFunction χ s‖ ≤ ‖s‖ * B / s.re := by
  obtain ⟨B, hB0, hB⟩ := chiPartialSum_Icc_bounded hχ
  refine ⟨B, hB0, fun s hs => ?_⟩
  rw [LFunction_eq_mellin hχ hs, norm_mul, ← abelIntegral_eq_mellin]
  calc ‖s‖ * ‖∫ t in Set.Ioi (1 : ℝ), chiSumStep χ t * (t : ℂ) ^ (-(s + 1))‖
      ≤ ‖s‖ * (B / s.re) :=
        mul_le_mul_of_nonneg_left (abelIntegral_norm_le hs hB) (norm_nonneg _)
    _ = ‖s‖ * B / s.re := by ring

/-- **`hRight`.** For `Re s > 1` and `‖s‖ ≥ R₀`, `log(‖Λ(s,χ)‖+1) ≤ C·‖s‖·log‖s‖`. -/
theorem completedL_bound_right {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    ∃ C > (0 : ℝ), ∃ R₀ > (0 : ℝ), ∀ s : ℂ, R₀ ≤ ‖s‖ → 1 ≤ s.re →
      Real.log (‖DirichletCharacter.completedLFunction χ s‖ + 1) ≤ C * ‖s‖ * Real.log ‖s‖ := by
  obtain ⟨B, hB0, hBfun⟩ := L_bound_uniform hχ
  refine ⟨2 * Real.log 2 + Real.log (B + 1) + 6,
    by have h2 := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
       have hB1 := Real.log_nonneg (show (1 : ℝ) ≤ B + 1 by linarith); linarith,
    Real.exp 1, Real.exp_pos 1, fun s hsR hsre => ?_⟩
  -- basic facts
  have hs0re : 0 < s.re := by linarith
  have hsne : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs0re; exact lt_irrefl 0 hs0re
  have hsnorm : 0 < ‖s‖ := norm_pos_iff.mpr hsne
  have hs1 : (1 : ℝ) ≤ ‖s‖ := le_trans (by have := Real.exp_one_gt_d9; linarith) hsR
  have hlog1 : (1 : ℝ) ≤ Real.log ‖s‖ := by
    have := Real.log_le_log (Real.exp_pos 1) hsR; rwa [Real.log_exp] at this
  have hre : s.re ≤ ‖s‖ := Complex.re_le_norm s
  have hγne : χ.gammaFactor s ≠ 0 := gammaFactor_ne_zero hs0re
  have hγnn : 0 ≤ ‖χ.gammaFactor s‖ := norm_nonneg _
  have hLnn : 0 ≤ ‖DirichletCharacter.LFunction χ s‖ := norm_nonneg _
  -- factorization Λ = γ·L, so ‖Λ‖ = ‖γ‖·‖L‖
  have hfact : DirichletCharacter.completedLFunction χ s
      = χ.gammaFactor s * DirichletCharacter.LFunction χ s := by
    have hrel := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inl hsne)
    rw [hrel]; field_simp
  have hnormΛ : ‖DirichletCharacter.completedLFunction χ s‖
      = ‖χ.gammaFactor s‖ * ‖DirichletCharacter.LFunction χ s‖ := by rw [hfact, norm_mul]
  -- split: log(‖Λ‖+1) ≤ log(‖γ‖+1) + log(‖L‖+1)
  have hsplit : Real.log (‖DirichletCharacter.completedLFunction χ s‖ + 1)
      ≤ Real.log (‖χ.gammaFactor s‖ + 1) + Real.log (‖DirichletCharacter.LFunction χ s‖ + 1) := by
    rw [hnormΛ]; exact GammaBound.log_mul_add_one_le hγnn hLnn
  -- γ term: log(‖γ‖+1) ≤ (s.re+1)·log(s.re+1) + 2
  have hG : Real.log (‖χ.gammaFactor s‖ + 1) ≤ (s.re + 1) * Real.log (s.re + 1) + 2 := by
    have hgb := log_norm_gammaFactor_le (χ := χ) (s := s) hsre
    have hGnn : 0 ≤ (s.re + 1) * Real.log (s.re + 1) + 1 := by
      have : 0 ≤ (s.re + 1) * Real.log (s.re + 1) :=
        mul_nonneg (by linarith) (Real.log_nonneg (by linarith))
      linarith
    have := GammaBound.log_add_one_le hγnn hGnn hgb
    linarith
  -- L term: log(‖L‖+1) ≤ log‖s‖ + log(B+1)
  have hLle : ‖DirichletCharacter.LFunction χ s‖ ≤ ‖s‖ * B := by
    have h := hBfun s hs0re
    have : ‖s‖ * B / s.re ≤ ‖s‖ * B := by
      apply div_le_self (by positivity); linarith
    linarith
  have hL : Real.log (‖DirichletCharacter.LFunction χ s‖ + 1) ≤ Real.log ‖s‖ + Real.log (B + 1) := by
    have h1 : ‖DirichletCharacter.LFunction χ s‖ + 1 ≤ ‖s‖ * (B + 1) := by nlinarith
    calc Real.log (‖DirichletCharacter.LFunction χ s‖ + 1)
        ≤ Real.log (‖s‖ * (B + 1)) := Real.log_le_log (by positivity) h1
      _ = Real.log ‖s‖ + Real.log (B + 1) :=
          Real.log_mul (ne_of_gt hsnorm) (by positivity)
  -- (s.re+1)·log(s.re+1) ≤ 2·log2·‖s‖ + 2·‖s‖·log‖s‖
  have hRes : (s.re + 1) * Real.log (s.re + 1) ≤ 2 * Real.log 2 * ‖s‖ + 2 * ‖s‖ * Real.log ‖s‖ := by
    have hb1 : s.re + 1 ≤ 2 * ‖s‖ := by nlinarith
    have hb2 : Real.log (s.re + 1) ≤ Real.log (2 * ‖s‖) :=
      Real.log_le_log (by linarith) hb1
    have hmul : (s.re + 1) * Real.log (s.re + 1) ≤ (2 * ‖s‖) * Real.log (2 * ‖s‖) :=
      mul_le_mul hb1 hb2 (Real.log_nonneg (by linarith)) (by positivity)
    have hexp : Real.log (2 * ‖s‖) = Real.log 2 + Real.log ‖s‖ :=
      Real.log_mul (by norm_num) (ne_of_gt hsnorm)
    have hring : (2 * ‖s‖) * (Real.log 2 + Real.log ‖s‖)
        = 2 * Real.log 2 * ‖s‖ + 2 * ‖s‖ * Real.log ‖s‖ := by ring
    rw [hexp, hring] at hmul; exact hmul
  -- assemble
  have hlogB0 : 0 ≤ Real.log (B + 1) := Real.log_nonneg (by linarith)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith [hsplit, hG, hL, hRes, hlog1, hs1, mul_le_mul_of_nonneg_left hlog1 (le_of_lt hsnorm)]

/-- **Strip upper half `[½,1]`.** `gammaFactor` is bounded by the constant `4` here, and `‖L‖ ≤ 2‖s‖B`
    (`Re s ≥ ½`, no `1/Re s` blowup), so `‖Λ‖ ≤ 8B‖s‖` and `log(‖Λ‖+1) ≤ C·‖s‖·log‖s‖`. -/
theorem completedL_bound_strip_upper {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    ∃ C > (0 : ℝ), ∃ R₀ > (0 : ℝ), ∀ s : ℂ, R₀ ≤ ‖s‖ → 1 / 2 ≤ s.re → s.re ≤ 1 →
      Real.log (‖DirichletCharacter.completedLFunction χ s‖ + 1) ≤ C * ‖s‖ * Real.log ‖s‖ := by
  obtain ⟨B, hB0, hBfun⟩ := L_bound_uniform hχ
  refine ⟨Real.log (8 * B + 1) + 2,
    by have := Real.log_nonneg (show (1 : ℝ) ≤ 8 * B + 1 by linarith); linarith,
    Real.exp 1, Real.exp_pos 1, fun s hsR hlo hhi => ?_⟩
  have hsnorm : 0 < ‖s‖ := lt_of_lt_of_le (Real.exp_pos 1) hsR
  have hs1 : (1 : ℝ) ≤ ‖s‖ := le_trans (by have := Real.exp_one_gt_d9; linarith) hsR
  have hlog1 : (1 : ℝ) ≤ Real.log ‖s‖ := by
    have := Real.log_le_log (Real.exp_pos 1) hsR; rwa [Real.log_exp] at this
  have hX1 : (1 : ℝ) ≤ ‖s‖ * Real.log ‖s‖ := by nlinarith
  have hs0re : 0 < s.re := by linarith
  have hsne : s ≠ 0 := fun hh => by rw [hh, Complex.zero_re] at hs0re; exact lt_irrefl 0 hs0re
  have hγne : χ.gammaFactor s ≠ 0 := gammaFactor_ne_zero hs0re
  have hfact : DirichletCharacter.completedLFunction χ s
      = χ.gammaFactor s * DirichletCharacter.LFunction χ s := by
    have hrel := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inl hsne)
    rw [hrel]; field_simp
  have hγ4 : ‖χ.gammaFactor s‖ ≤ 4 := norm_gammaFactor_le_four hlo hhi
  have hLle : ‖DirichletCharacter.LFunction χ s‖ ≤ 2 * (‖s‖ * B) := by
    have h := hBfun s hs0re
    have hdiv : ‖s‖ * B / s.re ≤ 2 * (‖s‖ * B) := by
      rw [div_le_iff₀ hs0re]
      nlinarith [mul_nonneg (mul_nonneg (norm_nonneg s) hB0)
        (show (0 : ℝ) ≤ 2 * s.re - 1 by linarith)]
    linarith
  have hΛle : ‖DirichletCharacter.completedLFunction χ s‖ ≤ 8 * B * ‖s‖ := by
    rw [hfact, norm_mul]
    calc ‖χ.gammaFactor s‖ * ‖DirichletCharacter.LFunction χ s‖
        ≤ 4 * (2 * (‖s‖ * B)) := mul_le_mul hγ4 hLle (norm_nonneg _) (by norm_num)
      _ = 8 * B * ‖s‖ := by ring
  have hΛ1 : ‖DirichletCharacter.completedLFunction χ s‖ + 1 ≤ (8 * B + 1) * ‖s‖ := by
    nlinarith [hΛle, hs1, mul_nonneg hB0 (le_of_lt hsnorm)]
  have hlog : Real.log (‖DirichletCharacter.completedLFunction χ s‖ + 1)
      ≤ Real.log (8 * B + 1) + Real.log ‖s‖ := by
    calc Real.log (‖DirichletCharacter.completedLFunction χ s‖ + 1)
        ≤ Real.log ((8 * B + 1) * ‖s‖) := Real.log_le_log (by positivity) hΛ1
      _ = Real.log (8 * B + 1) + Real.log ‖s‖ := Real.log_mul (by positivity) (ne_of_gt hsnorm)
  have hlogB0 : 0 ≤ Real.log (8 * B + 1) := Real.log_nonneg (by linarith)
  have h_p1 : Real.log (8 * B + 1) ≤ Real.log (8 * B + 1) * (‖s‖ * Real.log ‖s‖) := by
    nlinarith [hlogB0, hX1]
  have h_p2 : Real.log ‖s‖ ≤ ‖s‖ * Real.log ‖s‖ := by nlinarith [hlog1, hs1]
  nlinarith [hlog, h_p1, h_p2, hX1]

end DirichletLHadamard

#print axioms DirichletLHadamard.completedL_bound_right
#print axioms DirichletLHadamard.completedL_bound_strip_upper
