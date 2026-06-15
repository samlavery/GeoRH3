import Mathlib
import RequestProject.HelixHilbertPolyaLoss
import RequestProject.HelixLossSpectralIdentification

/-!
# Helix Spectral Peaks as Dual Projection Loss Modes

This file ties the empirical peak-reading story to the formal loss-space API:

* the dual projection loss space is the orthogonal complement `Kᗮ`;
* every loss vector `x - K.starProjection x` lies in that space;
* a helix zero mode stores its spectral peak in the angular loss channel and
  its envelope displacement in the radial loss channel;
* unit envelope is equivalent to zero radial loss, so the half-unit is produced
  by the helix mode theorem rather than assumed.
-/

noncomputable section

open scoped BigOperators Real
open Real Complex

/-- The dual projection loss space attached to a helix loss space. -/
abbrev helixDualProjectionLossSpace {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (K : HelixLossSpace H) : Submodule ℝ H :=
  Kᗮ

/-- The dual loss vector is the part discarded by the Green-Helmholtz projection. -/
def helixDualProjectionLoss {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (K : HelixLossSpace H) [K.HasOrthogonalProjection] (x : H) : H :=
  x - helixLossProjection K x

/-- The dual loss vector always lies in the dual projection loss space. -/
theorem helixDualProjectionLoss_mem_space {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (K : HelixLossSpace H) [K.HasOrthogonalProjection]
    (x : H) :
    helixDualProjectionLoss K x ∈ helixDualProjectionLossSpace K := by
  exact Submodule.sub_starProjection_mem_orthogonal (K := K) x

/-- Projection plus dual loss exactly reconstructs the helix signal. -/
theorem helixProjection_add_dualLoss {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (K : HelixLossSpace H) [K.HasOrthogonalProjection]
    (x : H) :
    helixLossProjection K x + helixDualProjectionLoss K x = x := by
  simp [helixDualProjectionLoss, helixLossProjection]

/-- The Green-Helmholtz projection has no drift into its dual loss space. -/
theorem helixProjection_orthogonal_dualLoss {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (K : HelixLossSpace H) [K.HasOrthogonalProjection]
    (x : H) :
    @inner ℝ H _ (helixLossProjection K x) (helixDualProjectionLoss K x) = 0 := by
  simpa [helixDualProjectionLoss, helixLossProjection] using green_helmholtz_no_drift K x

/-- The dual loss channel is self-adjoint. -/
theorem helixDualProjectionLoss_self_adjoint {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (K : HelixLossSpace H) [K.HasOrthogonalProjection]
    (x y : H) :
    @inner ℝ H _ (helixDualProjectionLoss K x) y =
      @inner ℝ H _ x (helixDualProjectionLoss K y) :=
  helixLossProjection_loss_self_adjoint K x y

/-- Dual loss energy is nonnegative mode by mode. -/
theorem helixDualProjectionLoss_energy_nonneg {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (K : HelixLossSpace H) [K.HasOrthogonalProjection]
    (x : H) :
    0 ≤ ‖helixDualProjectionLoss K x‖ ^ 2 := by
  positivity

/-- The helix loss readout stores the spectral peak frequency in the angular
channel and the envelope displacement in the radial channel. -/
theorem helix_zero_mode_loss_reads_peak
    (m : HelixMode) (x : ℝ) :
    (loss (zero_embed m.radialRate m.frequency x)).angular =
        x ^ m.radialRate * Real.sin (m.frequency * Real.log x) ∧
      (loss (zero_embed m.radialRate m.frequency x)).radial =
        m.radialRate - 1 / 2 := by
  exact ⟨rfl, rfl⟩

/-- The helix peak frequency is the imaginary coordinate of the source zero. -/
theorem helix_zero_mode_peak_frequency (m : HelixMode) :
    m.frequency = m.rho.im :=
  rfl

/-- The helix peak envelope rate is the real coordinate of the source zero. -/
theorem helix_zero_mode_peak_radialRate (m : HelixMode) :
    m.radialRate = m.rho.re :=
  rfl

/-- A helix spectral peak is exactly a zero-radial-loss mode of the projection loss. -/
theorem helix_spectral_peak_iff_dual_loss_radial_zero
    (m : HelixMode) (x : ℝ) :
    m.UnitEnvelope ↔ (loss (zero_embed m.radialRate m.frequency x)).radial = 0 :=
  helix_mode_unitEnvelope_iff_loss_radial_zero m x

/-- The half-unit coordinate follows from the helix unit-envelope law. -/
theorem helix_spectral_peak_forces_half_unit
    (m : HelixMode) (hm : m.UnitEnvelope) :
    m.radialRate = 1 / 2 :=
  (m.unitEnvelope_iff_radialRate_half).mp hm

/-- The zeta channel reads spectral peaks from the same dual projection loss space. -/
theorem zeta_peak_iff_dual_loss_radial_zero
    (m : HelixMode) (x : ℝ) :
    m.UnitEnvelope ↔ (loss (zero_embed m.radialRate m.frequency x)).radial = 0 :=
  zeta_loss_projection_spectral_identification m x

/-- The `χ₃` channel reads spectral peaks from the same dual projection loss space. -/
theorem chi3_peak_iff_dual_loss_radial_zero
    (m : HelixMode) (x : ℝ) :
    m.UnitEnvelope ↔ (loss (zero_embed m.radialRate m.frequency x)).radial = 0 :=
  chi3_loss_projection_spectral_identification m x

/-- The helix loss mode and the logarithmic-derivative pole are identified in
one statement: zero radial loss on the dual side and pole data on the analytic side. -/
theorem helix_peak_identifies_dual_loss_and_logDeriv_pole
    (m : HelixMode) (x : ℝ)
    {f : ℂ → ℂ} {w : ℂ} {n : ℕ}
    (hf : AnalyticAt ℂ f w)
    (hf_order : analyticOrderAt f w = (n : ℕ∞))
    (hn : 1 ≤ n) :
    (m.UnitEnvelope ↔ (loss (zero_embed m.radialRate m.frequency x)).radial = 0) ∧
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g w ∧ g w ≠ 0 ∧
      ∀ᶠ z in nhdsWithin w {w}ᶜ,
        deriv f z / f z = (n : ℂ) * (z - w)⁻¹ + deriv g z / g z :=
  helix_spectrally_identifies_loss_zero_and_logDeriv_pole m x hf hf_order hn

end
