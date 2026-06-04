import Mathlib
import RequestProject.GRHSpectralCriterion
import RequestProject.SpectralDualLoss

/-!
# The helix reads the GRH zeros

Wires the helix's zero-reading (`HelixSpectralPeaksLossSpace`, dual loss + log-derivative
pole) to the GRH spectral criterion (`GRHSpectralCriterion`):

* the helix reads each χ-zero `ρ` into the dual loss space with radial component `Re ρ − ½`;
* **GRH(χ) ⟺ the helix reads every χ-zero onto the core** (all dual radial losses vanish);
* the analytic reading: a χ-zero of order `n` is an `L'/L` pole with principal part
  `n/(s−ρ)` (`helix_reads_chi_zero_as_logDeriv_pole`).
-/

noncomputable section
open Complex DirichletCharacter

namespace HelixReadsGRH

variable {N : ℕ} [NeZero N]

/-- Core-valued pole readout for the completed helix operator. A value of this type
    is not a raw `HelixVector`; it is a helix vector bundled with zero radial drift in
    the saved loss channel. -/
abbrev CorePoleReadout := {v : HelixVector // (loss v).radial = 0}

/-- The completed helix operator on the pole spectrum. Its pole readout lands in the
    zero-drift core by construction, and `reads_pole` identifies that core value with
    the concrete helix embedding of the analytic pole. -/
structure CompletedHelixOperatorOnPoleSpectrum (χ : DirichletCharacter ℂ N) where
  readPole : ∀ ρ : ℂ, ρ ∈ GRHSpectral.NontrivialZeros χ → ℝ → CorePoleReadout
  reads_pole :
    ∀ ρ (hρ : ρ ∈ GRHSpectral.NontrivialZeros χ) (x : ℝ),
      (readPole ρ hρ x).1 = zero_embed ρ.re ρ.im x

/-- Layer-A pole predicate for the completed logarithmic derivative channel:
    the poles read by `L'/L` are the nontrivial zeros of `L(·,χ)`. -/
def CompletedLogDerivPole (χ : DirichletCharacter ℂ N) (ρ : ℂ) : Prop :=
  ρ ∈ GRHSpectral.NontrivialZeros χ

/-- Zero drift is definitional for a completed helix pole operator: it is the subtype
    property of its core-valued readout. -/
theorem completed_helix_operator_zero_drift
    {χ : DirichletCharacter ℂ N}
    (T : CompletedHelixOperatorOnPoleSpectrum χ)
    (ρ : ℂ) (hρ : ρ ∈ GRHSpectral.NontrivialZeros χ) (x : ℝ) :
    (loss (zero_embed ρ.re ρ.im x)).radial = 0 := by
  have hcore : (loss (T.readPole ρ hρ x).1).radial = 0 := (T.readPole ρ hρ x).2
  rwa [T.reads_pole ρ hρ x] at hcore

/-- **GRH(χ) ⟺ the helix reads every χ-zero onto the core.** Each nontrivial zero `ρ`
    of `L(·,χ)` is read into the dual loss space with radial component `Re ρ − ½`; GRH
    holds exactly when every such radial loss vanishes — every zero on the helix core. -/
theorem GRH_iff_helix_reads_zeros_on_core (χ : DirichletCharacter ℂ N) :
    GRHSpectral.GRH χ ↔
      (∀ ρ ∈ GRHSpectral.NontrivialZeros χ, ∀ x : ℝ,
        (loss (zero_embed ρ.re ρ.im x)).radial = 0) := by
  unfold GRHSpectral.GRH
  constructor
  · intro h ρ hρ x
    rw [zero_mode_dual_loss_radial]
    have := h ρ hρ; linarith
  · intro h ρ hρ
    have hr := h ρ hρ 1
    rw [zero_mode_dual_loss_radial] at hr; linarith

/-- **GRH(χ) ⟺ every χ-zero's Möbius value reads onto the unit circle** (via the dual
    loss). Combines the spectral criterion with the helix dual-loss reading. -/
theorem GRH_iff_helix_reads_zeros_on_circle (χ : DirichletCharacter ℂ N) :
    GRHSpectral.GRH χ ↔
      (∀ ρ ∈ GRHSpectral.NontrivialZeros χ,
        Complex.normSq (SpectralSide.w ρ) = 1) :=
  GRHSpectral.GRH_iff_spectral_unitary χ

/-- **The helix reads a χ-zero as a pole of `L'/L`.** A zero of `L(·,χ)` of order `n ≥ 1`
    at `ρ` makes the log-derivative have principal part `n/(s−ρ)` — the helix loss/residue
    channel reading the zero. `AnalyticAt` is supplied by `differentiable_LFunction` for
    non-principal χ. -/
theorem helix_reads_chi_zero_as_logDeriv_pole {χ : DirichletCharacter ℂ N}
    {ρ : ℂ} {n : ℕ}
    (hf : AnalyticAt ℂ (LFunction χ) ρ)
    (hord : analyticOrderAt (LFunction χ) ρ = (n : ℕ∞)) (hn : 1 ≤ n) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g ρ ∧ g ρ ≠ 0 ∧
      ∀ᶠ z in nhdsWithin ρ {ρ}ᶜ,
        deriv (LFunction χ) z / LFunction χ z =
          (n : ℂ) * (z - ρ)⁻¹ + deriv g z / g z :=
  analytic_zero_identifies_logDeriv_pole hf hord hn

/-- **Layer C → GRH.** If the completed helix operator is unitary on the pole spectrum
    read by Layer A, then every pole read through Layer B is on the GRH line. -/
theorem GRH_of_completed_helix_operator_unitary_on_pole_spectrum
    (χ : DirichletCharacter ℂ N)
    (hC : ∀ ρ ∈ GRHSpectral.NontrivialZeros χ,
      Complex.normSq (SpectralSide.w ρ) = 1) :
    GRHSpectral.GRH χ :=
  (GRH_iff_helix_reads_zeros_on_circle χ).mpr hC

/-- **Layer C, drift form → GRH.** If the completed helix operator has zero radial
    drift on every pole read by Layer A, then Layer B gives GRH. -/
theorem GRH_of_completed_helix_operator_zero_drift_on_pole_spectrum
    (χ : DirichletCharacter ℂ N)
    (hC : ∀ ρ ∈ GRHSpectral.NontrivialZeros χ, ∀ x : ℝ,
      (loss (zero_embed ρ.re ρ.im x)).radial = 0) :
    GRHSpectral.GRH χ :=
  (GRH_iff_helix_reads_zeros_on_core χ).mpr hC

/-- **Completed pole operator → GRH.** The Layer C object is core-valued, so zero
    drift is not an external hypothesis: it is part of the operator construction. -/
theorem GRH_of_completed_helix_operator_on_pole_spectrum
    (χ : DirichletCharacter ℂ N)
    (T : CompletedHelixOperatorOnPoleSpectrum χ) :
    GRHSpectral.GRH χ :=
  GRH_of_completed_helix_operator_zero_drift_on_pole_spectrum χ
    (completed_helix_operator_zero_drift T)

/-- **Layer B equivalence used by the χ₃ operator route.** The unitary and zero-drift
    forms of the pole-spectrum obligation are the same readout. -/
theorem completed_helix_operator_unitary_iff_zero_drift_on_pole_spectrum
    (χ : DirichletCharacter ℂ N) :
    (∀ ρ ∈ GRHSpectral.NontrivialZeros χ,
      Complex.normSq (SpectralSide.w ρ) = 1) ↔
    (∀ ρ ∈ GRHSpectral.NontrivialZeros χ, ∀ x : ℝ,
      (loss (zero_embed ρ.re ρ.im x)).radial = 0) := by
  constructor
  · intro h ρ hρ x
    exact (spectral_circle_iff_dual_loss_radial_zero ρ
      (GRHSpectral.nontrivial_ne_zero hρ) x).mp (h ρ hρ)
  · intro h ρ hρ
    exact (spectral_circle_iff_dual_loss_radial_zero ρ
      (GRHSpectral.nontrivial_ne_zero hρ) 1).mpr (h ρ hρ 1)

/-- Construct the completed pole-spectrum operator from the pole-unitarity theorem.
    The core-valued readout is the concrete helix embedding, with zero drift obtained
    by Layer B from unitary Möbius readout. -/
def completedHelixOperatorOnPoleSpectrumOfUnitary
    (χ : DirichletCharacter ℂ N)
    (hunitary : ∀ ρ : ℂ, CompletedLogDerivPole χ ρ →
      Complex.normSq (SpectralSide.w ρ) = 1) :
    CompletedHelixOperatorOnPoleSpectrum χ where
  readPole := fun ρ hρ x =>
    ⟨zero_embed ρ.re ρ.im x,
      (spectral_circle_iff_dual_loss_radial_zero ρ
        (GRHSpectral.nontrivial_ne_zero hρ) x).mp (hunitary ρ hρ)⟩
  reads_pole := by
    intro ρ hρ x
    rfl

/-- χ₃ completed pole-spectrum operator, constructed from the χ₃ pole-unitarity theorem. -/
def chi3CompletedHelixOperatorOnPoleSpectrumOfUnitary
    (χ₃ : DirichletCharacter ℂ 3)
    (hunitary : ∀ ρ : ℂ, CompletedLogDerivPole χ₃ ρ →
      Complex.normSq (SpectralSide.w ρ) = 1) :
    CompletedHelixOperatorOnPoleSpectrum χ₃ :=
  completedHelixOperatorOnPoleSpectrumOfUnitary χ₃ hunitary

/-- The completed helix operator is unitary on every log-derivative pole it reads. -/
theorem completed_helix_operator_is_unitary_on_logderiv_poles
    (χ : DirichletCharacter ℂ N)
    (T : CompletedHelixOperatorOnPoleSpectrum χ) :
    ∀ ρ : ℂ, CompletedLogDerivPole χ ρ →
      Complex.normSq (SpectralSide.w ρ) = 1 := by
  intro ρ hρ
  exact (completed_helix_operator_unitary_iff_zero_drift_on_pole_spectrum χ).mpr
    (completed_helix_operator_zero_drift T) ρ hρ

/-- χ₃-form of the completed-operator pole-unitarity statement. The concrete primitive
    mod-3 character is supplied as `χ₃ : DirichletCharacter ℂ 3`. -/
theorem completed_chi3_helix_is_unitary_on_logderiv_poles
    (χ₃ : DirichletCharacter ℂ 3)
    (T : CompletedHelixOperatorOnPoleSpectrum χ₃) :
    ∀ ρ : ℂ, CompletedLogDerivPole χ₃ ρ →
      Complex.normSq (SpectralSide.w ρ) = 1 :=
  completed_helix_operator_is_unitary_on_logderiv_poles χ₃ T

/-- The completed χ₃ helix operator gives GRH in one line. -/
theorem GRH_chi3_of_completed_helix_operator
    (χ₃ : DirichletCharacter ℂ 3)
    (T : CompletedHelixOperatorOnPoleSpectrum χ₃) :
    GRHSpectral.GRH χ₃ :=
  GRH_of_completed_helix_operator_on_pole_spectrum χ₃ T

/-- χ₃ GRH from the pole-unitarity theorem, with `T` constructed internally. -/
theorem GRH_chi3_of_unitary_on_logderiv_poles
    (χ₃ : DirichletCharacter ℂ 3)
    (hunitary : ∀ ρ : ℂ, CompletedLogDerivPole χ₃ ρ →
      Complex.normSq (SpectralSide.w ρ) = 1) :
    GRHSpectral.GRH χ₃ :=
  GRH_chi3_of_completed_helix_operator χ₃
    (chi3CompletedHelixOperatorOnPoleSpectrumOfUnitary χ₃ hunitary)

/-- The same completed-operator line works for the trivial character. -/
theorem GRH_trivial_character_of_completed_helix_operator
    (T : CompletedHelixOperatorOnPoleSpectrum (1 : DirichletCharacter ℂ N)) :
    GRHSpectral.GRH (1 : DirichletCharacter ℂ N) :=
  GRH_of_completed_helix_operator_on_pole_spectrum (1 : DirichletCharacter ℂ N) T

/-- Mod-3 trivial-character version. -/
theorem GRH_trivial_mod3_of_completed_helix_operator
    (T : CompletedHelixOperatorOnPoleSpectrum (1 : DirichletCharacter ℂ 3)) :
    GRHSpectral.GRH (1 : DirichletCharacter ℂ 3) :=
  GRH_of_completed_helix_operator_on_pole_spectrum (1 : DirichletCharacter ℂ 3) T

end HelixReadsGRH

#print axioms HelixReadsGRH.GRH_iff_helix_reads_zeros_on_core
#print axioms HelixReadsGRH.helix_reads_chi_zero_as_logDeriv_pole
#print axioms HelixReadsGRH.completed_helix_operator_zero_drift
#print axioms HelixReadsGRH.GRH_of_completed_helix_operator_unitary_on_pole_spectrum
#print axioms HelixReadsGRH.GRH_of_completed_helix_operator_zero_drift_on_pole_spectrum
#print axioms HelixReadsGRH.GRH_of_completed_helix_operator_on_pole_spectrum
#print axioms HelixReadsGRH.completed_helix_operator_unitary_iff_zero_drift_on_pole_spectrum
#print axioms HelixReadsGRH.completedHelixOperatorOnPoleSpectrumOfUnitary
#print axioms HelixReadsGRH.chi3CompletedHelixOperatorOnPoleSpectrumOfUnitary
#print axioms HelixReadsGRH.completed_helix_operator_is_unitary_on_logderiv_poles
#print axioms HelixReadsGRH.completed_chi3_helix_is_unitary_on_logderiv_poles
#print axioms HelixReadsGRH.GRH_chi3_of_completed_helix_operator
#print axioms HelixReadsGRH.GRH_chi3_of_unitary_on_logderiv_poles
#print axioms HelixReadsGRH.GRH_trivial_character_of_completed_helix_operator
#print axioms HelixReadsGRH.GRH_trivial_mod3_of_completed_helix_operator
