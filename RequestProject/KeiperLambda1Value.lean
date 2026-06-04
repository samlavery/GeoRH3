import Mathlib
import RequestProject.VonMangoldtEFStandalone

/-!
# The first Keiper–Li coefficient: closed arithmetic form

The Keiper definition of the first Li coefficient is `λ₁ = ξ'/ξ(1)` (the
logarithmic derivative of the completed `ξ` at `s = 1`). This file proves its
**closed arithmetic form**, unconditionally and axiom-clean:

  `λ₁ = ξ'/ξ(1) = 1 + γ/2 − ½·log(4π) ≈ 0.0230957…`

where `γ` is the Euler–Mascheroni constant. This is the arithmetic (prime-side)
value of the same `λ₁` whose zero-side positivity is `KeiperLiPositivity`.

## Mechanism

`ξ` is defined entire as `ξ(s) = (s(s−1)/2)·Λ₀(s) + 1/2` (`Λ₀ =
completedRiemannZeta₀`). Hence:

* `ξ(1) = 1/2` (the polynomial factor `s(s−1)` vanishes at `1`);
* `ξ'(1) = Λ₀(1)/2` — differentiating, the `(s−1)` factor kills the `Λ₀'(1)`
  term, leaving only `½·Λ₀(1)`;
* so `ξ'/ξ(1) = Λ₀(1)`.

The value `Λ₀(1) = 1 + (γ − log 4π)/2` comes from Mathlib's zeta-asymptotics:
`ζ(s) − 1/(Γℝ(s)(s−1)) → (γ − log 4π)/2`, and
`ζ(s) − 1/(Γℝ(s)(s−1)) = (Λ₀(s) − 1/s)/Γℝ(s)`, so multiplying by `Γℝ(s) → 1`
gives `Λ₀(s) − 1/s → (γ − log 4π)/2`, i.e. `Λ₀(1) − 1 = (γ − log 4π)/2`.
The digamma value `ψ(½) = −γ − 2log2` is already baked into Mathlib's constant.
-/

noncomputable section

open Complex Real Filter Topology

namespace VMEFStandalone

/-- `ξ(1) = 1/2` — the polynomial factor `s(s−1)/2` vanishes at `s = 1`. -/
lemma riemannXi_one_eq : riemannXi 1 = 1 / 2 := by
  simp [riemannXi]

/-- `ξ'(1) = Λ₀(1)/2`. Differentiating `ξ(s) = (s(s−1)/2)·Λ₀(s) + 1/2`, the
    `(s−1)` factor zeroes the `Λ₀'(1)` term, leaving only `½·Λ₀(1)`. -/
lemma deriv_riemannXi_one :
    deriv riemannXi 1 = completedRiemannZeta₀ 1 / 2 := by
  have hg : HasDerivAt (fun s : ℂ => s * (s - 1) / 2) (1 / 2) 1 := by
    have h2 : HasDerivAt (fun s : ℂ => s * (s - 1)) 1 1 := by
      simpa using (hasDerivAt_id (1 : ℂ)).mul ((hasDerivAt_id (1 : ℂ)).sub_const 1)
    simpa using h2.div_const 2
  have hΛ : HasDerivAt completedRiemannZeta₀ (deriv completedRiemannZeta₀ 1) 1 :=
    (differentiable_completedZeta₀ 1).hasDerivAt
  have hxi : HasDerivAt riemannXi
      (1 / 2 * completedRiemannZeta₀ 1 + 1 * (1 - 1) / 2 * deriv completedRiemannZeta₀ 1) 1 :=
    (hg.mul hΛ).add_const (1 / 2)
  rw [hxi.deriv]; ring

/-- `Λ₀(1) = 1 + (γ − log 4π)/2`, from Mathlib's zeta-asymptotics at `s = 1`. -/
lemma completedRiemannZeta₀_at_one :
    completedRiemannZeta₀ 1 = 1 + ((eulerMascheroniConstant : ℂ) - Complex.log (4 * π)) / 2 := by
  set L : ℂ := ((eulerMascheroniConstant : ℂ) - Complex.log (4 * π)) / 2 with hL
  have hG1 : (1 : ℂ).Gammaℝ = 1 := by
    rw [Complex.Gammaℝ_def, show (1 : ℂ) / 2 = 1 / 2 by ring, Complex.Gamma_one_half_eq,
      ← Complex.cpow_add _ _ (by exact_mod_cast Real.pi_ne_zero)]; norm_num
  have hGtend : Tendsto (fun s : ℂ => s.Gammaℝ) (𝓝[≠] 1) (𝓝 1) := by
    have hcont : ContinuousAt (fun s : ℂ => s.Gammaℝ) 1 := by
      have h : (fun s : ℂ => s.Gammaℝ) = fun s => ((fun s : ℂ => (s.Gammaℝ)⁻¹) s)⁻¹ := by
        funext s; rw [inv_inv]
      rw [h]
      exact ContinuousAt.inv₀ (differentiable_Gammaℝ_inv 1).continuousAt
        (inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num)))
    have ht : Tendsto (fun s : ℂ => s.Gammaℝ) (𝓝[≠] 1) (𝓝 ((1 : ℂ).Gammaℝ)) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    rwa [hG1] at ht
  have hprod := hGtend.mul ZetaAsymptotics.tendsto_riemannZeta_sub_one_div_Gammaℝ
  rw [one_mul] at hprod
  have hnear : ∀ᶠ s in 𝓝[≠] (1 : ℂ), s ≠ 0 ∧ 0 < s.re := by
    have h0 : ∀ᶠ s in 𝓝 (1 : ℂ), s ≠ 0 := isOpen_ne.mem_nhds (by norm_num)
    have hre : ∀ᶠ s in 𝓝 (1 : ℂ), 0 < s.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num [Complex.one_re])
    exact (h0.and hre).filter_mono nhdsWithin_le_nhds
  have hEq : (fun s : ℂ => s.Gammaℝ * (riemannZeta s - 1 / s.Gammaℝ / (s - 1)))
      =ᶠ[𝓝[≠] 1] (fun s => completedRiemannZeta₀ s - 1 / s) := by
    filter_upwards [self_mem_nhdsWithin, hnear] with s hs1 hs
    obtain ⟨hs0, hsre⟩ := hs
    have hs1' : s ≠ 1 := hs1
    have hGne : s.Gammaℝ ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hsre
    have hs1'' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1'
    have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1')
    rw [riemannZeta_def_of_ne_zero hs0, completedRiemannZeta_eq]
    field_simp
    ring
  have hΛ0sub : Tendsto (fun s : ℂ => completedRiemannZeta₀ s - 1 / s) (𝓝[≠] 1) (𝓝 L) :=
    hprod.congr' hEq
  have hcomb : Tendsto (fun s : ℂ => completedRiemannZeta₀ s - 1 / s) (𝓝[≠] 1)
      (𝓝 (completedRiemannZeta₀ 1 - 1)) := by
    have hΛ0cont : Tendsto completedRiemannZeta₀ (𝓝[≠] 1) (𝓝 (completedRiemannZeta₀ 1)) :=
      (differentiable_completedZeta₀ 1).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hinv : Tendsto (fun s : ℂ => (1 : ℂ) / s) (𝓝[≠] 1) (𝓝 1) := by
      have : ContinuousAt (fun s : ℂ => (1 : ℂ) / s) 1 :=
        ContinuousAt.div continuousAt_const continuousAt_id (by norm_num)
      simpa using this.tendsto.mono_left nhdsWithin_le_nhds
    exact hΛ0cont.sub hinv
  have huniq := tendsto_nhds_unique hcomb hΛ0sub
  linear_combination huniq

/-- **The first Keiper–Li coefficient, closed form (unconditional, axiom-clean).**

  `λ₁ = ξ'/ξ(1) = 1 + γ/2 − ½·log(4π) ≈ 0.0230957…`

This is the arithmetic value of the same `λ₁` whose zero-side positivity
(`Σ_ρ Re(1/ρ) > 0`) is proved in `KeiperLiPositivity`. No RH, no hypotheses. -/
theorem keiperLambda1_value :
    logDeriv riemannXi 1 =
      1 + (eulerMascheroniConstant : ℂ) / 2 - Complex.log (4 * π) / 2 := by
  rw [logDeriv_apply, deriv_riemannXi_one, riemannXi_one_eq, completedRiemannZeta₀_at_one]
  ring

end VMEFStandalone

end

#print axioms VMEFStandalone.keiperLambda1_value
