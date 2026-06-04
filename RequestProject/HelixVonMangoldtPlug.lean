import Mathlib
import RequestProject.UniversalRH
import RequestProject.HelixLossSpectralIdentification

/-!
# Von Mangoldt positivity plug-in for the helix loss chain

This file records the exact point where `ArithmeticFunction.vonMangoldt_nonneg`
enters the existing helix chain.
-/

noncomputable section

open Complex Real

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-- The concrete Λ input consumed by `VonMangoldtSpectralBridge`. -/
theorem vonMangoldt_nonneg_input :
    ∀ n : ℕ, (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt n :=
  fun _ => ArithmeticFunction.vonMangoldt_nonneg

/-- Λ nonnegativity plugs directly into the spectral bridge and discharges
    the universal paired-Li boundedness output. -/
theorem vonMangoldt_nonneg_plugs_into_spectral_bridge
    (S : Set (ℝ × ℝ))
    (h_bridge : VonMangoldtSpectralBridge S) :
    UniversalLiBounded S :=
  h_bridge vonMangoldt_nonneg_input

/-- Once the bridge has consumed Λ nonnegativity, the universal helix theorem
    returns the half-unit radial coordinate for every nontrivial marker. -/
theorem vonMangoldt_nonneg_forces_half_unit_markers
    (S : Set (ℝ × ℝ))
    (h_nontrivial : ∀ z ∈ S, z.2 ≠ 0)
    (h_bridge : VonMangoldtSpectralBridge S) :
    ∀ z ∈ S, z.1 = 1 / 2 :=
  (universal_rh S h_nontrivial).mpr
    (vonMangoldt_nonneg_plugs_into_spectral_bridge S h_bridge)

/-- The same Λ-fed bridge gives zero radial loss in the concrete helix loss
    projection at every source scale. -/
theorem vonMangoldt_nonneg_forces_loss_radial_zero
    (S : Set (ℝ × ℝ))
    (h_nontrivial : ∀ z ∈ S, z.2 ≠ 0)
    (h_bridge : VonMangoldtSpectralBridge S)
    (z : ℝ × ℝ) (hz : z ∈ S) (x : ℝ) :
    (loss (zero_embed z.1 z.2 x)).radial = 0 := by
  have hz_half := vonMangoldt_nonneg_forces_half_unit_markers S h_nontrivial h_bridge z hz
  dsimp [loss, zero_embed]
  linarith

/-- Λ nonnegativity plus the spectral bridge gives both the radial-loss
    closure and the analytic zero-to-log-derivative-pole identification. -/
theorem vonMangoldt_nonneg_to_loss_zero_and_logDeriv_pole
    (S : Set (ℝ × ℝ))
    (h_nontrivial : ∀ z ∈ S, z.2 ≠ 0)
    (h_bridge : VonMangoldtSpectralBridge S)
    (z : ℝ × ℝ) (hz : z ∈ S) (x : ℝ)
    {f : ℂ → ℂ} {w : ℂ} {n : ℕ}
    (hf : AnalyticAt ℂ f w)
    (hf_order : analyticOrderAt f w = (n : ℕ∞))
    (hn : 1 ≤ n) :
    (loss (zero_embed z.1 z.2 x)).radial = 0 ∧
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g w ∧ g w ≠ 0 ∧
      ∀ᶠ s in nhdsWithin w {w}ᶜ,
        deriv f s / f s = (n : ℂ) * (s - w)⁻¹ + deriv g s / g s :=
  ⟨vonMangoldt_nonneg_forces_loss_radial_zero S h_nontrivial h_bridge z hz x,
   analytic_zero_identifies_logDeriv_pole hf hf_order hn⟩

end
