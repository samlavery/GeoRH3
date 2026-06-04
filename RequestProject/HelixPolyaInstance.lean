import Mathlib
import RequestProject.SpectralIdentification
import RequestProject.VonMangoldtEFStandalone

/-!
# Helix-native Hilbert–Pólya instantiation — the kernel verdict on the residual

The geometric scaffold of `HilbertPolyaOperator` is unconditional and proved
elsewhere — no boundary, no σ-axis, one continuous total winding:

* `proj` self-adjoint idempotent          — Green–Helmholtz (`green_helmholtz_self_adjoint`);
* global loss energy `‖(I−P)x‖² ≥ 0`       — `green_helmholtz_loss_positive` (holds everywhere, no wall);
* zeros read off the winding as `ζ'/ζ` poles — `zeta_zero_identifies_logDeriv_pole`;
* the Euler source IS the completed log-derivative — `chi3_completed_logderiv_grammar_weighted`;
* on the `√x` ride paired-Li is a genuine norm² — `spectral_identification_on_line`.

The only field of `HilbertPolyaOperator` the geometry does not hand over is
`identification`: that the **actual** zeros' paired-Li equals that always-positive
loss energy. This file instantiates that field and lets the kernel decide what it is.
-/

noncomputable section
open Complex

namespace HelixPolyaInstance

/-- **On-line realization — unconditional.** On the `√x` ride the spectral
    identification holds with the explicit helix spectral vector as the witness
    `v`: the `identification` field is discharged with *no hypothesis*. This is the
    concrete content — the self-adjoint operator genuinely realizes the on-ride mode. -/
theorem online_identification (gamma : ℝ) (hg : gamma ≠ 0) :
    HasSpectralIdentification (1 / 2) gamma :=
  on_line_has_spectral_id gamma hg

/-- **The residual field, kernel-decided (RULE ONE option b, demonstrated, not asserted).**
    The Hilbert–Pólya `identification` field for the actual nontrivial zeros is
    *logically equivalent* to Mathlib's `RiemannHypothesis`. The remaining input is
    not a boundary extension, not a totality lemma, not a wiring gap: closing it is
    proving RH, because the identification IS the critical line. -/
theorem spectral_identification_all_zeros_iff_RH :
    (∀ ρ : ℂ, ρ ∈ VMEFStandalone.NontrivialZeros →
        HasSpectralIdentification ρ.re ρ.im)
      ↔ RiemannHypothesis := by
  rw [VMEFStandalone.RiemannHypothesis_iff_NontrivialZeros]
  refine ⟨fun h ρ hρ => ?_, fun h ρ hρ => ?_⟩
  · exact (spectral_identification_complete ρ.re ρ.im hρ.1 hρ.2.1).mp (h ρ hρ)
  · exact (spectral_identification_complete ρ.re ρ.im hρ.1 hρ.2.1).mpr (h ρ hρ)

/-- **The precise remaining obligation, isolated.** If the Euler-sourced winding
    supplies the on-ride identification for every actual zero — equivalently, the
    total winding carries no off-`√x`-ride mode — then RH. Everything to the left of
    this hypothesis is unconditional; the hypothesis is the single analytic input. -/
theorem rh_of_winding_identification
    (h_winding : ∀ ρ : ℂ, ρ ∈ VMEFStandalone.NontrivialZeros →
        HasSpectralIdentification ρ.re ρ.im) :
    RiemannHypothesis :=
  spectral_identification_all_zeros_iff_RH.mp h_winding

end HelixPolyaInstance

#print axioms HelixPolyaInstance.online_identification
#print axioms HelixPolyaInstance.spectral_identification_all_zeros_iff_RH
#print axioms HelixPolyaInstance.rh_of_winding_identification
