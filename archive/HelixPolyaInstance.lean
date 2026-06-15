import Mathlib
import RequestProject.SpectralIdentification
import RequestProject.VonMangoldtEFStandalone

/-!
# Helix-native Hilbert–Pólya instantiation

The geometric scaffold of `HilbertPolyaOperator` is unconditional and proved
elsewhere — no boundary, no σ-axis, one continuous total winding:

* `proj` self-adjoint idempotent          — Green–Helmholtz (`green_helmholtz_self_adjoint`);
* global loss energy `‖(I−P)x‖² ≥ 0`       — `green_helmholtz_loss_positive` (holds everywhere, no wall);
* zeros read off the winding as `ζ'/ζ` poles — `zeta_zero_identifies_logDeriv_pole`;
* the Euler source IS the completed log-derivative — `chi3_completed_logderiv_grammar_weighted`;
* on the `√x` ride paired-Li is a genuine norm² — `spectral_identification_on_line`.

`online_identification` realizes the on-ride mode concretely: the self-adjoint operator
genuinely discharges the `identification` field on the `√x` ride, no hypothesis. The
remaining target — the same identification for the *actual* nontrivial zeros — is what to
prove via the winding/energy geometry; the per-zero forcing is `spectral_identification_complete`.
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

end HelixPolyaInstance

#print axioms HelixPolyaInstance.online_identification
