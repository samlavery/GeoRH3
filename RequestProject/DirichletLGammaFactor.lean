import RequestProject.GammaModulusBound
import RequestProject.DirichletLHadamard

/-!
# `gammaFactor` log-bound for a Dirichlet character

`log ‖χ.gammaFactor s‖ ≤ (Re s + 1)·log(Re s + 1) + 1` for `Re s ≥ 1`. The even/odd `gammaFactor`
is `Gammaℝ s` resp. `Gammaℝ(s+1)`; apply `GammaBound.log_norm_Gammaℝ_le` and monotonicity
(`Re s'/2 ≤ Re s`). This is the Archimedean half of the `hRight` growth bound.
-/

open Complex

namespace DirichletLHadamard

variable {N : ℕ} [NeZero N]

/-- **`gammaFactor` log-bound.** For `Re s ≥ 1`, `log ‖χ.gammaFactor s‖ ≤ (Re s+1)·log(Re s+1) + 1`. -/
theorem log_norm_gammaFactor_le {χ : DirichletCharacter ℂ N} {s : ℂ} (hs : 1 ≤ s.re) :
    Real.log ‖χ.gammaFactor s‖ ≤ (s.re + 1) * Real.log (s.re + 1) + 1 := by
  rcases χ.even_or_odd with h | h
  · rw [h.gammaFactor_def]
    have hmul : (s.re / 2 + 1) * Real.log (s.re / 2 + 1) ≤ (s.re + 1) * Real.log (s.re + 1) :=
      mul_le_mul (by linarith) (Real.log_le_log (by linarith) (by linarith))
        (Real.log_nonneg (by linarith)) (by linarith)
    linarith [GammaBound.log_norm_Gammaℝ_le hs, hmul]
  · rw [h.gammaFactor_def]
    have hs1 : 1 ≤ (s + 1).re := by rw [Complex.add_re, Complex.one_re]; linarith
    have hb := GammaBound.log_norm_Gammaℝ_le hs1
    rw [Complex.add_re, Complex.one_re] at hb
    have hmul : ((s.re + 1) / 2 + 1) * Real.log ((s.re + 1) / 2 + 1)
        ≤ (s.re + 1) * Real.log (s.re + 1) :=
      mul_le_mul (by linarith) (Real.log_le_log (by linarith) (by linarith))
        (Real.log_nonneg (by linarith)) (by linarith)
    linarith [hb, hmul]

/-- **`gammaFactor` constant bound on the strip half `[½,1]`.** For `½ ≤ Re s ≤ 1` the `gammaFactor`
    argument lands in `[¼,1]`, where `Γ ≤ 1/x ≤ 4` (`Gamma_le_inv`) and `π^{−Re/2} ≤ 1`, so
    `‖gammaFactor χ s‖ ≤ 4` — a *constant* (no order-1 needed). This is the Archimedean half of the
    `[½,1]` strip bound. -/
theorem norm_gammaFactor_le_four {χ : DirichletCharacter ℂ N} {s : ℂ}
    (hlo : 1 / 2 ≤ s.re) (hhi : s.re ≤ 1) : ‖χ.gammaFactor s‖ ≤ 4 := by
  have hπ1 : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  rcases χ.even_or_odd with h | h
  · rw [h.gammaFactor_def]
    have hsre0 : (0 : ℝ) < s.re := by linarith
    have hbound := GammaBound.norm_Gammaℝ_le hsre0
    have hπle : Real.pi ^ (-s.re / 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hπ1 (by linarith)
    have hΓle : Real.Gamma (s.re / 2) ≤ 4 := by
      have h1 := GammaBound.Gamma_le_inv (show (0 : ℝ) < s.re / 2 by linarith) (by linarith)
      have h2 : 1 / (s.re / 2) ≤ 4 := by rw [div_le_iff₀ (by linarith)]; linarith
      linarith
    calc ‖Complex.Gammaℝ s‖ ≤ Real.pi ^ (-s.re / 2) * Real.Gamma (s.re / 2) := hbound
      _ ≤ 1 * 4 := mul_le_mul hπle hΓle (Real.Gamma_pos_of_pos (by linarith)).le (by norm_num)
      _ = 4 := by ring
  · rw [h.gammaFactor_def]
    have hsre0 : (0 : ℝ) < (s + 1).re := by rw [Complex.add_re, Complex.one_re]; linarith
    have hbound := GammaBound.norm_Gammaℝ_le hsre0
    have hπle : Real.pi ^ (-(s + 1).re / 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hπ1 (by rw [Complex.add_re, Complex.one_re]; linarith)
    have hΓle : Real.Gamma ((s + 1).re / 2) ≤ 4 := by
      rw [Complex.add_re, Complex.one_re]
      have h1 := GammaBound.Gamma_le_inv (show (0 : ℝ) < (s.re + 1) / 2 by linarith) (by linarith)
      have h2 : 1 / ((s.re + 1) / 2) ≤ 4 := by rw [div_le_iff₀ (by linarith)]; linarith
      linarith
    calc ‖Complex.Gammaℝ (s + 1)‖
        ≤ Real.pi ^ (-(s + 1).re / 2) * Real.Gamma ((s + 1).re / 2) := hbound
      _ ≤ 1 * 4 := mul_le_mul hπle hΓle
            (Real.Gamma_pos_of_pos (by rw [Complex.add_re, Complex.one_re]; linarith)).le
            (by norm_num)
      _ = 4 := by ring

end DirichletLHadamard

#print axioms DirichletLHadamard.log_norm_gammaFactor_le
#print axioms DirichletLHadamard.norm_gammaFactor_le_four
