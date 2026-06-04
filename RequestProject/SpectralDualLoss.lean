import Mathlib
import RequestProject.SpectralSide
import RequestProject.HelixSpectralPeaksLossSpace

/-!
# Finishing the spectral side: the Möbius value lives in the dual loss space

Wires `SpectralSide.w(ρ) = 1 − 1/ρ` to the dual projection loss space `Kᗮ`
(`HelixSpectralPeaksLossSpace`):

* the spectral value is on the unit circle **iff** the zero's dual loss has zero
  radial component (`spectral_circle_iff_dual_loss_radial_zero`);
* the functional equation `w(ρ)·w(1−ρ)=1` is the **radial reflection** of the dual
  loss (`dual_loss_radial_FE_reflection`);
* the dual loss energy is nonnegative (`spectral_dual_loss_energy_nonneg`).

The two descriptions — the Möbius spectral value and the dual projection loss — are the
same object, so the spectral side closes onto the loss geometry.
-/

noncomputable section
open Complex

/-- The dual projection loss of a zero mode has radial component `ρ.re − ½`. -/
theorem zero_mode_dual_loss_radial (ρ : ℂ) (x : ℝ) :
    (loss (zero_embed ρ.re ρ.im x)).radial = ρ.re - 1 / 2 := rfl

/-- **The Möbius spectral value is on the unit circle iff the dual loss radial vanishes.**
    `SpectralSide.w` and the dual loss space describe the same zero — on the circle is
    exactly zero radial loss. -/
theorem spectral_circle_iff_dual_loss_radial_zero (ρ : ℂ) (hρ : ρ ≠ 0) (x : ℝ) :
    Complex.normSq (SpectralSide.w ρ) = 1 ↔
      (loss (zero_embed ρ.re ρ.im x)).radial = 0 := by
  rw [SpectralSide.w_unit_iff_half ρ hρ, zero_mode_dual_loss_radial]
  constructor <;> intro h <;> linarith

/-- **The functional equation is the radial reflection of the dual loss.** The FE pairs
    `ρ` with `1−ρ` (`w(ρ)·w(1−ρ)=1`); on the dual loss side this is exactly the radial
    component flipping sign. -/
theorem dual_loss_radial_FE_reflection (ρ : ℂ) (x : ℝ) :
    (loss (zero_embed (1 - ρ).re (1 - ρ).im x)).radial =
      -(loss (zero_embed ρ.re ρ.im x)).radial := by
  rw [zero_mode_dual_loss_radial, zero_mode_dual_loss_radial, Complex.sub_re, Complex.one_re]
  ring

/-- **The dual loss energy is nonnegative.** The spectral-loss energy of any mode is a
    genuine norm-square in `Kᗮ`. -/
theorem spectral_dual_loss_energy_nonneg {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (K : HelixLossSpace H) [K.HasOrthogonalProjection] (v : H) :
    0 ≤ ‖helixDualProjectionLoss K v‖ ^ 2 :=
  helixDualProjectionLoss_energy_nonneg K v

/-- **The spectral side, closed onto the loss geometry.** For a zero `ρ` with its
    embedded mode:
    1. on the unit circle ⟺ zero radial loss;
    2. the FE acts as the radial reflection;
    3. the dual loss energy is `≥ 0`. -/
theorem spectral_side_closed_on_dual_loss (ρ : ℂ) (hρ : ρ ≠ 0) (x : ℝ)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (K : HelixLossSpace H) [K.HasOrthogonalProjection] (v : H) :
    (Complex.normSq (SpectralSide.w ρ) = 1 ↔
      (loss (zero_embed ρ.re ρ.im x)).radial = 0) ∧
    ((loss (zero_embed (1 - ρ).re (1 - ρ).im x)).radial =
      -(loss (zero_embed ρ.re ρ.im x)).radial) ∧
    (0 ≤ ‖helixDualProjectionLoss K v‖ ^ 2) :=
  ⟨spectral_circle_iff_dual_loss_radial_zero ρ hρ x,
   dual_loss_radial_FE_reflection ρ x,
   spectral_dual_loss_energy_nonneg K v⟩

end

#print axioms spectral_circle_iff_dual_loss_radial_zero
#print axioms dual_loss_radial_FE_reflection
#print axioms spectral_side_closed_on_dual_loss
