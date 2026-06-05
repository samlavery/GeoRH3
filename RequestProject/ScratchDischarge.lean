import RequestProject.HelixReadsGRHZeros
import RequestProject.UniversalRH
import RequestProject.Dichotomy
import RequestProject.GRHSpectralCriterion
import Mathlib

open Complex

-- TARGET = the literal `hunitary` of the operator constructor (714/728):
theorem chi3_hunitary (χ₃ : DirichletCharacter ℂ 3) :
    ∀ ρ : ℂ, HelixReadsGRH.CompletedLogDerivPole χ₃ ρ →
      Complex.normSq (SpectralSide.w ρ) = 1 := by
  intro ρ hρ
  -- hρ : CompletedLogDerivPole χ₃ ρ  (defeq  ρ ∈ NontrivialZeros χ₃)
  rw [SpectralSide.w_unit_iff_half ρ (GRHSpectral.nontrivial_ne_zero hρ)]
  -- goal: ρ.re = 1/2
  sorry
