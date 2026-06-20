import Mathlib
import RequestProject.Chi3CompletedLogDeriv
import RequestProject.ArchimedeanGamma

/-!
# `negCompletedLogDerivChi3 = −Λ′/Λ(s,χ₃)` — the identification (completes `HelixLossχ₃`)

* **#1** `chi3 = χ₃`: the repo function is the Legendre/quadratic character mod 3.
* **#2** the von Mangoldt prime series `= −L′/L(s,χ₃)` (Mathlib `LSeries_twist_vonMangoldt_eq`).
* **#3** assembly: `−L′/L − logDeriv(arch) = −logDeriv(arch·L) = −Λ′/Λ` (using `chi3_arch_logDeriv`).
-/

open Complex DirichletCharacter

namespace ChiThree

/-! ### #1  Character identification `chi3 = χ₃` -/

noncomputable def χ3 : DirichletCharacter ℂ 3 :=
  (quadraticChar (ZMod 3)).ringHomComp (Int.castRingHom ℂ)

theorem χ3_zero : χ3 0 = 0 := by simp [χ3, MulChar.ringHomComp]
theorem χ3_one : χ3 1 = 1 := by simp [χ3, MulChar.ringHomComp]
theorem χ3_two : χ3 2 = -1 := by
  have h : (quadraticChar (ZMod 3)) 2 = (-1 : ℤ) := by decide
  unfold χ3; rw [MulChar.ringHomComp_apply, h]; norm_num

/-- The repo function `chi3` is the Mathlib character `χ₃`. -/
theorem chi3_eq_χ3 (n : ℕ) : chi3 n = χ3 (n : ZMod 3) := by
  have hmod : (n : ZMod 3) = ((n % 3 : ℕ) : ZMod 3) := (ZMod.natCast_mod n 3).symm
  have h3 : n % 3 < 3 := Nat.mod_lt n (by norm_num)
  unfold chi3; rw [hmod]
  interval_cases (n % 3) <;> simp [χ3_zero, χ3_one, χ3_two]

theorem χ3_ne_one : χ3 ≠ 1 := by
  intro h
  have h2 : χ3 2 = 1 := by rw [h]; exact MulChar.one_apply (by decide)
  rw [χ3_two] at h2; norm_num at h2

/-! ### #2  The prime series is `−L′/L(s,χ₃)` -/

theorem chi3_dirichletSeries_eq {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * chi3 n * (n : ℂ) ^ (-s))
      = -deriv (LFunction χ3) s / LFunction χ3 s := by
  rw [DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ3 hs,
      DirichletCharacter.LFunction_eq_LSeries χ3 hs,
      ← DirichletCharacter.LSeries_twist_vonMangoldt_eq χ3 hs, LSeries]
  refine tsum_congr (fun n => ?_)
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term]
  · rw [LSeries.term_of_ne_zero hn, Pi.mul_apply, chi3_eq_χ3, Complex.cpow_neg]
    ring

/-! ### #3  Assembly -/

/-- The standard conductor‑3 / odd completed L‑factor `(3/π)^{(s+1)/2}·Γ((s+1)/2)·L(s,χ₃)`. -/
noncomputable def completedLChi3 (s : ℂ) : ℂ :=
  (3 / Real.pi : ℂ) ^ ((s + 1) / 2) * Complex.Gamma ((s + 1) / 2) * LFunction χ3 s

/-- **The identification.** On `Re s > 1`,
`negCompletedLogDerivChi3 s = −logDeriv(completed L) s = −Λ′/Λ(s,χ₃)`. -/
theorem negCompletedLogDerivChi3_eq_neg_logDeriv {s : ℂ} (hs : 1 < s.re) :
    negCompletedLogDerivChi3 s = -logDeriv completedLChi3 s := by
  have hsre1 : (-1 : ℝ) < s.re := by linarith
  have hgam : 0 < ((s + 1) / 2).re := by
    rw [ArchGamma.div_two_re, Complex.add_re, Complex.one_re]; linarith
  have hc : (3 / Real.pi : ℂ) ≠ 0 := div_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  have hsne1 : s ≠ 1 := fun h => by rw [h] at hs; simp at hs
  have hcpowne : (3 / Real.pi : ℂ) ^ ((s + 1) / 2) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hc]; exact Complex.exp_ne_zero _
  have hAne : (3 / Real.pi : ℂ) ^ ((s + 1) / 2) * Complex.Gamma ((s + 1) / 2) ≠ 0 :=
    mul_ne_zero hcpowne (Complex.Gamma_ne_zero_of_re_pos hgam)
  have hLne : LFunction χ3 s ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ3 (Or.inr hsne1) hs.le
  have hAdiff : DifferentiableAt ℂ
      (fun z => (3 / Real.pi : ℂ) ^ ((z + 1) / 2) * Complex.Gamma ((z + 1) / 2)) s := by
    refine DifferentiableAt.mul (DifferentiableAt.const_cpow (by fun_prop) (Or.inl hc)) ?_
    refine (Complex.differentiableAt_Gamma _ ?_).comp s (by fun_prop)
    intro m hm
    rw [hm] at hgam; simp only [Complex.neg_re, Complex.natCast_re] at hgam
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m; linarith
  have hLdiff : DifferentiableAt ℂ (LFunction χ3) s :=
    DirichletCharacter.differentiableAt_LFunction χ3 s (Or.inl hsne1)
  rw [chi3_completed_logderiv_grammar_Re_gt_one s hs, chi3_dirichletSeries_eq hs]
  show _ = -logDeriv
    (fun z => (3 / Real.pi : ℂ) ^ ((z + 1) / 2) * Complex.Gamma ((z + 1) / 2) * LFunction χ3 z) s
  rw [logDeriv_mul s hAne hLne hAdiff hLdiff,
      ArchGamma.chi3_arch_logDeriv s hsre1, logDeriv_apply]
  ring

end ChiThree

#print axioms ChiThree.chi3_eq_χ3
#print axioms ChiThree.chi3_dirichletSeries_eq
#print axioms ChiThree.negCompletedLogDerivChi3_eq_neg_logDeriv
