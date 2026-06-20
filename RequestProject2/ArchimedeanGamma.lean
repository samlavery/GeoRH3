import Mathlib

open Complex

namespace ArchGamma

/-- **The archimedean completion is Euler's gamma** (the three Mathlib facts, packaged). -/
theorem archimedean_completion_is_euler_gamma :
    (∀ s : ℂ, Complex.Gammaℝ s = (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2)) ∧
    (Complex.digamma = logDeriv Complex.Gamma) ∧
    (Complex.digamma 1 = -(Real.eulerMascheroniConstant : ℂ)) :=
  ⟨Complex.Gammaℝ_def, Complex.digamma_def, Complex.digamma_one⟩

/-- The Euler–Mascheroni constant is exactly minus the archimedean digamma at `1`. -/
theorem eulerGamma_eq_neg_digamma_one :
    (Real.eulerMascheroniConstant : ℂ) = -Complex.digamma 1 := by
  rw [Complex.digamma_one]; ring

/-! ### The archimedean log-derivative through Euler's gamma -/

/-- `logDeriv (exp ∘ h) = h'`. -/
theorem logDeriv_cexp_comp {h : ℂ → ℂ} {h' s : ℂ} (hh : HasDerivAt h h' s) :
    logDeriv (fun z => Complex.exp (h z)) s = h' := by
  rw [logDeriv_apply, hh.cexp.deriv, mul_comm (Complex.exp _), mul_div_assoc,
      div_self (Complex.exp_ne_zero _), mul_one]

/-- `logDeriv (Γ ∘ g) = g' · ψ(g s)`, away from the Γ‑poles. -/
theorem logDeriv_Gamma_comp {g : ℂ → ℂ} {g' s : ℂ} (hg : HasDerivAt g g' s)
    (hne : ∀ m : ℕ, g s ≠ -m) :
    logDeriv (fun z => Complex.Gamma (g z)) s = g' * Complex.digamma (g s) := by
  rw [show (fun z => Complex.Gamma (g z)) = Complex.Gamma ∘ g from rfl,
      logDeriv_comp (Complex.differentiableAt_Gamma _ hne) hg.differentiableAt,
      show logDeriv Complex.Gamma (g s) = Complex.digamma (g s) from rfl, hg.deriv, mul_comm]

/-- `(z/2).re = z.re/2`. -/
theorem div_two_re (s : ℂ) : (s / 2).re = s.re / 2 := by
  rw [Complex.div_re]; simp [Complex.normSq]; ring

/-- **`logDeriv Γℝ`, via Euler's gamma.** `Γℝ(s) = π^{-s/2}·Γ(s/2)` has
`logDeriv Γℝ s = −½·log π + ½·ψ(s/2)` for `Re s > 0` (off the Γ‑poles). -/
theorem logDeriv_GammaR (s : ℂ) (hs : 0 < s.re) :
    logDeriv Complex.Gammaℝ s
      = -(1/2 : ℂ) * Complex.log (Real.pi : ℂ) + (1/2 : ℂ) * Complex.digamma (s / 2) := by
  have hsre : 0 < (s / 2).re := by rw [div_two_re]; linarith
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hΓ : Complex.Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hsre
  have hne : ∀ m : ℕ, s / 2 ≠ -m := by
    intro m hcon; rw [hcon] at hsre
    simp only [Complex.neg_re, Complex.natCast_re] at hsre
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m; linarith
  -- the two factors as functions, with their log-derivatives
  have hcpowfun : (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2))
      = fun z => Complex.exp (Complex.log (Real.pi : ℂ) * (-z / 2)) :=
    funext fun z => Complex.cpow_def_of_ne_zero hπ _
  have hLog1 : logDeriv (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s
      = -(1/2 : ℂ) * Complex.log (Real.pi : ℂ) := by
    rw [hcpowfun]
    refine logDeriv_cexp_comp ?_
    have h1 : HasDerivAt (fun z : ℂ => -z / 2) (-1 / 2 : ℂ) s :=
      ((hasDerivAt_id s).neg).div_const 2
    have h2 := h1.const_mul (Complex.log (Real.pi : ℂ))
    rwa [show Complex.log (Real.pi : ℂ) * (-1 / 2) = -(1/2) * Complex.log (Real.pi : ℂ) by ring] at h2
  have hLog2 : logDeriv (fun z : ℂ => Complex.Gamma (z / 2)) s
      = (1/2 : ℂ) * Complex.digamma (s / 2) := by
    have hg : HasDerivAt (fun z : ℂ => z / 2) (1/2 : ℂ) s := by
      simpa using (hasDerivAt_id s).div_const 2
    exact logDeriv_Gamma_comp hg hne
  have hcpow : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hπ]; exact Complex.exp_ne_zero _
  have hd1 : DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s := by
    rw [hcpowfun]; fun_prop
  have hd2 : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z / 2)) s :=
    (Complex.differentiableAt_Gamma _ hne).comp s (by fun_prop)
  rw [show Complex.Gammaℝ = fun z => (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2) from
        funext Complex.Gammaℝ_def,
      logDeriv_mul s hcpow hΓ hd1 hd2, hLog1, hLog2]

/-- **`logDeriv` of the odd‑character χ₃ completed factor `(3/π)^{(s+1)/2}·Γ((s+1)/2)`** —
the archimedean grammar of `negCompletedLogDerivChi3` — equals `½·log(3/π) + ½·ψ((s+1)/2)`,
for `Re s > -1` (off the Γ‑poles). -/
theorem chi3_arch_logDeriv (s : ℂ) (hs : -1 < s.re) :
    logDeriv (fun z => (3 / Real.pi : ℂ) ^ ((z + 1) / 2) * Complex.Gamma ((z + 1) / 2)) s
      = (1/2 : ℂ) * Complex.log (3 / Real.pi : ℂ) + (1/2 : ℂ) * Complex.digamma ((s + 1) / 2) := by
  have hsre : 0 < ((s + 1) / 2).re := by
    rw [div_two_re, Complex.add_re, Complex.one_re]; linarith
  have hc : (3 / Real.pi : ℂ) ≠ 0 := by
    apply div_ne_zero (by norm_num)
    exact_mod_cast Real.pi_ne_zero
  have hΓ : Complex.Gamma ((s + 1) / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hsre
  have hne : ∀ m : ℕ, (s + 1) / 2 ≠ -m := by
    intro m hcon; rw [hcon] at hsre
    simp only [Complex.neg_re, Complex.natCast_re] at hsre
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m; linarith
  have hcpowfun : (fun z : ℂ => (3 / Real.pi : ℂ) ^ ((z + 1) / 2))
      = fun z => Complex.exp (Complex.log (3 / Real.pi : ℂ) * ((z + 1) / 2)) :=
    funext fun z => Complex.cpow_def_of_ne_zero hc _
  have hLog1 : logDeriv (fun z : ℂ => (3 / Real.pi : ℂ) ^ ((z + 1) / 2)) s
      = (1/2 : ℂ) * Complex.log (3 / Real.pi : ℂ) := by
    rw [hcpowfun]
    refine logDeriv_cexp_comp ?_
    have h1 : HasDerivAt (fun z : ℂ => (z + 1) / 2) (1/2 : ℂ) s := by
      simpa using ((hasDerivAt_id s).add_const 1).div_const 2
    have h2 := h1.const_mul (Complex.log (3 / Real.pi : ℂ))
    rwa [show Complex.log (3 / Real.pi : ℂ) * (1/2) = (1/2) * Complex.log (3 / Real.pi : ℂ) by ring]
      at h2
  have hLog2 : logDeriv (fun z : ℂ => Complex.Gamma ((z + 1) / 2)) s
      = (1/2 : ℂ) * Complex.digamma ((s + 1) / 2) := by
    have hg : HasDerivAt (fun z : ℂ => (z + 1) / 2) (1/2 : ℂ) s := by
      simpa using ((hasDerivAt_id s).add_const 1).div_const 2
    have := logDeriv_Gamma_comp hg (by simpa using hne)
    simpa using this
  have hcpow : (3 / Real.pi : ℂ) ^ ((s + 1) / 2) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hc]; exact Complex.exp_ne_zero _
  have hd1 : DifferentiableAt ℂ (fun z : ℂ => (3 / Real.pi : ℂ) ^ ((z + 1) / 2)) s := by
    rw [hcpowfun]; fun_prop
  have hd2 : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma ((z + 1) / 2)) s :=
    (Complex.differentiableAt_Gamma _ hne).comp s (by fun_prop)
  rw [logDeriv_mul s hcpow hΓ hd1 hd2, hLog1, hLog2]

end ArchGamma

#print axioms ArchGamma.logDeriv_GammaR
#print axioms ArchGamma.chi3_arch_logDeriv
