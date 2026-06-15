import RequestProject.SpectralSide
import RequestProject.SelfDual

open Complex

namespace HarmonicMorphism

/-! # The Möbius receiver is a harmonic morphism

A **harmonic morphism** (Fuglede–Ishihara / Baird–Wood) is a map whose pullback sends harmonic
functions to harmonic functions; in two real dimensions that class is **exactly the holomorphic (or
anti-holomorphic) maps** — conformal, harmonic-component-preserving. The Möbius `w(ρ) = 1 − 1/ρ` is
holomorphic away from `0`, hence a harmonic morphism. That is what makes the projection chain legal
(Rule Five, downward inheritance): the harmonic/spectral structure of the strip is carried, *intact*,
onto the self-dual unit circle `|w| = 1`, and the Möbius receiver reads it there. -/

/-- **The Möbius `w` is holomorphic away from `0` — a harmonic morphism.** Complex-differentiable,
    hence conformal with harmonic real/imaginary parts: its pullback preserves harmonic structure. -/
theorem w_isHarmonicMorphism {ρ : ℂ} (hρ : ρ ≠ 0) :
    DifferentiableAt ℂ SpectralSide.w ρ := by
  have : SpectralSide.w = fun z : ℂ => 1 - 1 / z := rfl
  rw [this]
  exact (differentiableAt_const _).sub ((differentiableAt_const _).div differentiableAt_id hρ)

/-- **The self-dual involution is intertwined by the harmonic morphism.** The harmonic morphism `w`
    conjugates the spectral duality `ρ ↦ 1−ρ` into circle inversion `w ↦ w⁻¹` (`SelfDual.w_dual`),
    and the morphism is holomorphic at both `ρ` and its dual `1−ρ`. So the duality acts *through* a
    genuine harmonic morphism — the inheritance of the self-dual structure down the chain is earned,
    not assumed. -/
theorem dual_through_harmonicMorphism {ρ : ℂ} (hρ : ρ ≠ 0) (h1 : (1 : ℂ) - ρ ≠ 0) :
    DifferentiableAt ℂ SpectralSide.w ρ
      ∧ DifferentiableAt ℂ SpectralSide.w (1 - ρ)
      ∧ SpectralSide.w (1 - ρ) = (SpectralSide.w ρ)⁻¹ :=
  ⟨w_isHarmonicMorphism hρ, w_isHarmonicMorphism h1, SelfDual.w_dual ρ hρ h1⟩

end HarmonicMorphism
