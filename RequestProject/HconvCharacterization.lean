import RequestProject.FENonExpansionClosure
import RequestProject.HelixReadsGRHZeros
import RequestProject.GRHSpectralCriterion
import Mathlib

open Complex Filter

namespace HconvChar

/-- **What the `hconv` hypothesis actually is.** The radial loss mode `exp((ρ.re−½)θ)` has a finite
limit as the helix winds (`θ→∞`) **iff** `ρ.re ≤ ½`. So the hypothesis
`∀ ρ, CompletedLogDerivPole χ ρ → ∃ L, Tendsto (exp((ρ.re−½)·)) atTop (𝓝 L)` is *exactly* the
zero-free right half-strip `Re ρ ≤ ½` for every nontrivial zero — half of GRH(χ). Unconditional. -/
theorem tendsto_exp_iff_re_le_half (ρ : ℂ) :
    (∃ L : ℝ, Tendsto (fun θ : ℝ => Real.exp ((ρ.re - 1 / 2) * θ)) atTop (nhds L))
      ↔ ρ.re ≤ 1 / 2 := by
  constructor
  · rintro ⟨L, hL⟩
    have h := FEClosure.tendsto_exp_finite_imp_nonpos hL
    linarith
  · intro h
    rcases eq_or_lt_of_le h with heq | hlt
    · refine ⟨1, ?_⟩
      simp only [show ρ.re - 1 / 2 = 0 from by linarith, zero_mul, Real.exp_zero]
      exact tendsto_const_nhds
    · refine ⟨0, ?_⟩
      have h1 : Tendsto (fun θ : ℝ => (1 / 2 - ρ.re) * θ) atTop atTop :=
        Filter.Tendsto.const_mul_atTop (by linarith) Filter.tendsto_id
      have hb : Tendsto (fun θ : ℝ => (ρ.re - 1 / 2) * θ) atTop atBot := by
        have heq : (fun θ : ℝ => (ρ.re - 1 / 2) * θ)
            = (fun θ : ℝ => -((1 / 2 - ρ.re) * θ)) := by funext θ; ring
        rw [heq]; exact Filter.tendsto_neg_atBot_iff.mpr h1
      exact Real.tendsto_exp_atBot.comp hb

/-- **The discharge target, decoded.** Discharging the full hypothesis (for every pole) is, term
for term, `∀ ρ ∈ NontrivialZeros χ, ρ.re ≤ ½` — no χ-zero lies in `½ < Re < 1`. With the functional
equation (`ρ ↦ 1−ρ` a pole too) this upgrades to `ρ.re = ½`: full GRH(χ). -/
theorem hconv_eq_half_strip {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    (∀ ρ : ℂ, HelixReadsGRH.CompletedLogDerivPole χ ρ →
        ∃ L : ℝ, Tendsto (fun θ : ℝ => Real.exp ((ρ.re - 1 / 2) * θ)) atTop (nhds L))
      ↔ (∀ ρ : ℂ, HelixReadsGRH.CompletedLogDerivPole χ ρ → ρ.re ≤ 1 / 2) := by
  constructor
  · intro h ρ hρ; exact (tendsto_exp_iff_re_le_half ρ).mp (h ρ hρ)
  · intro h ρ hρ; exact (tendsto_exp_iff_re_le_half ρ).mpr (h ρ hρ)

end HconvChar

#print axioms HconvChar.tendsto_exp_iff_re_le_half
#print axioms HconvChar.hconv_eq_half_strip
