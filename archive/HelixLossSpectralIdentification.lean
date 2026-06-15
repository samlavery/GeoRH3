import Mathlib
import RequestProject.HelixZeroMode
import RequestProject.ConcreteOperators
import RequestProject.HelixProjectionEigenvalue
import RequestProject.WeilContourMultiplicity

/-!
# Helix loss spectral identification

This file connects the concrete helix loss projection with the spectral
zero-mode language:

* the loss projection stores exactly the radial rate offset and angular
  frequency channel of a zero-mode;
* unit normalized envelope is equivalent to zero radial loss;
* zeros of an analytic function are poles of its logarithmic derivative.
-/

noncomputable section

open Complex Real
open scoped BigOperators

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-- The concrete loss projection reads out the radial offset and angular
    frequency channel of the embedded helix mode. -/
theorem loss_projection_operator_identifies_zero_mode (σ γ x : ℝ) :
    let v := zero_embed σ γ x
    (loss v).proj = 0 ∧
    (loss v).angular = x ^ σ * Real.sin (γ * Real.log x) ∧
    (loss v).radial = σ - 1 / 2 ∧
    ((loss v).radial = 0 ↔ σ = 1 / 2) := by
  dsimp [loss, zero_embed]
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor <;> intro h <;> linarith

/-- For a fitted helix mode, unit normalized envelope is equivalent to zero
    radial loss in the concrete loss projection at any source scale. -/
theorem helix_mode_unitEnvelope_iff_loss_radial_zero (m : HelixMode) (x : ℝ) :
    m.UnitEnvelope ↔ (loss (zero_embed m.radialRate m.frequency x)).radial = 0 := by
  rw [m.unitEnvelope_iff_radialRate_half]
  dsimp [HelixMode.radialRate, HelixMode.frequency, loss, zero_embed]
  constructor <;> intro h <;> linarith

/-- The ζ channel: spectral unit envelope identifies exactly the zero-radial-loss
    modes of the helix loss projection. -/
theorem zeta_loss_projection_spectral_identification
    (m : HelixMode) (x : ℝ) :
    m.UnitEnvelope ↔ (loss (zero_embed m.radialRate m.frequency x)).radial = 0 :=
  helix_mode_unitEnvelope_iff_loss_radial_zero m x

/-- The `χ₃` channel: spectral unit envelope identifies exactly the
    zero-radial-loss modes of the helix loss projection. -/
theorem chi3_loss_projection_spectral_identification
    (m : HelixMode) (x : ℝ) :
    m.UnitEnvelope ↔ (loss (zero_embed m.radialRate m.frequency x)).radial = 0 :=
  helix_mode_unitEnvelope_iff_loss_radial_zero m x

/-- The abstract projection/loss eigenvalue swap used by the helix loss
    operator: an eigenvalue `ev` of `P` is read as eigenvalue `1-ev` by
    the loss operator `I-P`. -/
theorem helix_loss_projection_eigenvalue_swap
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (P : F →ₗ[ℝ] F)
    (hP_idem : ∀ x, P (P x) = P x)
    (x : F) (hx : x ≠ 0) (ev : ℝ) (hev : P x = ev • x) :
    x - P x = (1 - ev) • x :=
  loss_eigenvalue_swap P hP_idem x hx ev hev

/-- Analytic zeros are poles of the logarithmic derivative. This is the
    pole-side spectral identification used by the loss/residue channel. -/
theorem analytic_zero_identifies_logDeriv_pole
    {f : ℂ → ℂ} {w : ℂ} {n : ℕ}
    (hf : AnalyticAt ℂ f w)
    (hf_order : analyticOrderAt f w = (n : ℕ∞))
    (hn : 1 ≤ n) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g w ∧ g w ≠ 0 ∧
      ∀ᶠ z in nhdsWithin w {w}ᶜ,
        deriv f z / f z = (n : ℂ) * (z - w)⁻¹ + deriv g z / g z :=
  ZD.WeilPositivity.Contour.logDeriv_pole_of_order hf hf_order hn

/-- For the zeta function, a zero of order `n ≥ 1` is identified as a pole
    of the logarithmic derivative, with principal part `n/(s-ρ)`. -/
theorem zeta_zero_identifies_logDeriv_pole
    {ρ : ℂ} {n : ℕ}
    (hζ_an : AnalyticAt ℂ riemannZeta ρ)
    (hζ_order : analyticOrderAt riemannZeta ρ = (n : ℕ∞))
    (hn : 1 ≤ n) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g ρ ∧ g ρ ≠ 0 ∧
      ∀ᶠ s in nhdsWithin ρ {ρ}ᶜ,
        deriv riemannZeta s / riemannZeta s =
          (n : ℂ) * (s - ρ)⁻¹ + deriv g s / g s :=
  analytic_zero_identifies_logDeriv_pole hζ_an hζ_order hn

/-- Combined statement: the helix loss projection identifies the mode's
    zero-radial spectral locus, and analytic zero data identifies the
    corresponding logarithmic-derivative pole. -/
theorem helix_spectrally_identifies_loss_zero_and_logDeriv_pole
    (m : HelixMode) (x : ℝ)
    {f : ℂ → ℂ} {w : ℂ} {n : ℕ}
    (hf : AnalyticAt ℂ f w)
    (hf_order : analyticOrderAt f w = (n : ℕ∞))
    (hn : 1 ≤ n) :
    (m.UnitEnvelope ↔ (loss (zero_embed m.radialRate m.frequency x)).radial = 0) ∧
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g w ∧ g w ≠ 0 ∧
      ∀ᶠ z in nhdsWithin w {w}ᶜ,
        deriv f z / f z = (n : ℂ) * (z - w)⁻¹ + deriv g z / g z :=
  ⟨helix_mode_unitEnvelope_iff_loss_radial_zero m x,
   analytic_zero_identifies_logDeriv_pole hf hf_order hn⟩

end
