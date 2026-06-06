import Mathlib
import RequestProject.HelixReadsGRHZeros
import RequestProject.HelixZeroMode
import RequestProject.HelixExplicitFormulaTermByTerm
import RequestProject.FENonExpansionClosure

/-!
# Strict completed helix loss

The completed loss field refuses residual radial warp through the strict generated
mode condition.  The core calculation is unconditional:

`∀ u, ‖sqrtNormalizedZeroMode ρ u‖ = 1` is equivalent to `ρ.re - 1/2 = 0`.

The later pole-spectrum declarations keep the pole/readout data explicit, so the
compiler shows exactly where a completed loss field supplies strict generated
modes for its poles.
-/

noncomputable section

open Complex DirichletCharacter

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace HelixStrictCompletion

variable {N : ℕ} [NeZero N]

/-- The residual radial warp after the built-in half-unit helix normalization. -/
def radialDefect (ρ : ℂ) : ℝ :=
  ρ.re - 1 / 2

/-- A strict completed helix mode has no residual radial envelope at any helix scale. -/
def GeneratedStrictHelixMode (ρ : ℂ) : Prop :=
  ∀ u : ℝ, ‖sqrtNormalizedZeroMode ρ u‖ = 1

/-- Strict generated modes are exactly the half-unit readout. -/
theorem generatedStrictHelixMode_iff_re_half (ρ : ℂ) :
    GeneratedStrictHelixMode ρ ↔ ρ.re = 1 / 2 := by
  unfold GeneratedStrictHelixMode
  exact sqrtNormalizedZeroMode_unit_all_scales_iff ρ

/-- Strict generated modes are exactly zero residual radial defect. -/
theorem generatedStrictHelixMode_iff_radialDefect_zero (ρ : ℂ) :
    GeneratedStrictHelixMode ρ ↔ radialDefect ρ = 0 := by
  rw [generatedStrictHelixMode_iff_re_half]
  unfold radialDefect
  constructor <;> intro h <;> linarith

/-- A strict generated mode has zero residual radial defect. -/
theorem generatedStrictHelixMode_forces_radialDefect_zero (ρ : ℂ)
    (h : GeneratedStrictHelixMode ρ) :
    radialDefect ρ = 0 :=
  (generatedStrictHelixMode_iff_radialDefect_zero ρ).mp h

/-- A strict generated mode is read at the half-unit. -/
theorem generatedStrictHelixMode_forces_re_half (ρ : ℂ)
    (h : GeneratedStrictHelixMode ρ) :
    ρ.re = 1 / 2 :=
  (generatedStrictHelixMode_iff_re_half ρ).mp h

/-- Saved zero radial loss is the same strict generated-mode condition. -/
theorem generatedStrictHelixMode_iff_loss_radial_zero (ρ : ℂ) (x : ℝ) :
    GeneratedStrictHelixMode ρ ↔ (loss (zero_embed ρ.re ρ.im x)).radial = 0 := by
  rw [generatedStrictHelixMode_iff_radialDefect_zero]
  unfold radialDefect
  rw [zero_mode_dual_loss_radial]

/-- Zero saved radial loss generates a strict completed mode. -/
theorem generatedStrictHelixMode_of_loss_radial_zero (ρ : ℂ) (x : ℝ)
    (hzero : (loss (zero_embed ρ.re ρ.im x)).radial = 0) :
    GeneratedStrictHelixMode ρ :=
  (generatedStrictHelixMode_iff_loss_radial_zero ρ x).mpr hzero

/-- A `7/10 + iγ` readout cannot be a strict completed helix mode. -/
theorem not_generatedStrictHelixMode_re_seven_tenths (γ : ℝ) :
    ¬ GeneratedStrictHelixMode (((7 / 10 : ℝ) : ℂ) + (γ : ℂ) * Complex.I) := by
  intro h
  have hhalf :=
    generatedStrictHelixMode_forces_re_half
      (((7 / 10 : ℝ) : ℂ) + (γ : ℂ) * Complex.I) h
  have hre : ((((7 / 10 : ℝ) : ℂ) + (γ : ℂ) * Complex.I).re) = 7 / 10 := by
    simp
  rw [hre] at hhalf
  norm_num at hhalf

/-- A completed loss field is strict on its completed log-derivative pole spectrum. -/
structure StrictCompletedHelixLossField
    (χ : DirichletCharacter ℂ N) (F : ℂ → ℂ) where
  pole_generates_strict_mode :
    ∀ ρ : ℂ, HelixReadsGRH.CompletedLogDerivPole χ ρ → GeneratedStrictHelixMode ρ

/-- Pole predicate for a completed helix loss field, using the repo's completed
    log-derivative pole encoding. -/
def HelixLossPole (χ : DirichletCharacter ℂ N) (_F : ℂ → ℂ) (ρ : ℂ) : Prop :=
  HelixReadsGRH.CompletedLogDerivPole χ ρ

/-- Poles constructed by the Euler-product helix grammar. -/
def ConstructedCompletedHelixPole (χ : DirichletCharacter ℂ N) (ρ : ℂ) : Prop :=
  ρ ∈ HelixReadsGRH.WindingLossSpectrum χ

/-- The completed helix loss pole predicate is the completed log-derivative pole predicate. -/
theorem helixLossPole_iff_completedLogDerivPole
    (χ : DirichletCharacter ℂ N) (F : ℂ → ℂ) (ρ : ℂ) :
    HelixLossPole χ F ρ ↔ HelixReadsGRH.CompletedLogDerivPole χ ρ :=
  Iff.rfl

/-- Completeness: every completed helix loss pole is constructed by the
    Euler-product helix grammar. -/
theorem constructedCompletedHelixPole_of_helixLossPole
    (χ : DirichletCharacter ℂ N) (F : ℂ → ℂ) (ρ : ℂ)
    (hρ : HelixLossPole χ F ρ) :
    ConstructedCompletedHelixPole χ ρ :=
  HelixReadsGRH.euler_grammar_exhausts_pole_spectrum χ ρ hρ

/-- Soundness: every constructed completed helix pole is a completed
    log-derivative pole. -/
theorem helixLossPole_of_constructedCompletedHelixPole
    (χ : DirichletCharacter ℂ N) (F : ℂ → ℂ) (ρ : ℂ)
    (hρ : ConstructedCompletedHelixPole χ ρ) :
    HelixLossPole χ F ρ := by
  unfold HelixLossPole ConstructedCompletedHelixPole at *
  rwa [HelixReadsGRH.windingLossSpectrum_eq_nontrivialZeros χ] at hρ

/-- The commuting square: faithful completed-loss poles and constructed grammar
    poles are the same set. -/
theorem helixLossPoleSpectrum_eq_constructedCompletedHelixPoles
    (χ : DirichletCharacter ℂ N) (F : ℂ → ℂ) :
    {ρ : ℂ | HelixLossPole χ F ρ} = {ρ : ℂ | ConstructedCompletedHelixPole χ ρ} := by
  ext ρ
  exact ⟨constructedCompletedHelixPole_of_helixLossPole χ F ρ,
    helixLossPole_of_constructedCompletedHelixPole χ F ρ⟩

/-- The strict-geometry arrow for a constructed completed helix pole. -/
def StrictGeometryOnConstructedCompletedPoles
    (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ ρ : ℂ, ConstructedCompletedHelixPole χ ρ → GeneratedStrictHelixMode ρ

/-- Strict constructed pole geometry forces zero residual radial defect. -/
theorem constructedCompletedHelixPole_radialDefect_zero_of_strictGeometry
    (χ : DirichletCharacter ℂ N)
    (hstrict : StrictGeometryOnConstructedCompletedPoles χ)
    (ρ : ℂ) (hρ : ConstructedCompletedHelixPole χ ρ) :
    radialDefect ρ = 0 :=
  generatedStrictHelixMode_forces_radialDefect_zero ρ (hstrict ρ hρ)

/-- The closed-form forcing law obtained from the commuting square and strict geometry. -/
theorem helixLossPole_re_half_of_strictGeometry
    (χ : DirichletCharacter ℂ N) (F : ℂ → ℂ)
    (hstrict : StrictGeometryOnConstructedCompletedPoles χ) :
    ∀ ρ : ℂ, HelixLossPole χ F ρ → ρ.re = 1 / 2 := by
  intro ρ hρ
  exact generatedStrictHelixMode_forces_re_half ρ
    (hstrict ρ (constructedCompletedHelixPole_of_helixLossPole χ F ρ hρ))

/-- Raw source-readout unitarity is only phase-valued; by itself it does not
    force the residual radial defect to vanish. -/
theorem sourceWindingLossReadout_unit_does_not_force_re_half :
    ∃ ρ : ℂ,
      ‖(HelixReadsGRH.sourceWindingLossReadout ρ : ℂ)‖ = 1 ∧ ρ.re ≠ 1 / 2 := by
  refine ⟨0, ?_, ?_⟩
  · change ‖(HelixReadsGRH.sourceRadialPitchWinding 0 0 : ℂ)‖ = 1
    exact HelixReadsGRH.sourceRadialPitchWinding_norm 0 0
  · norm_num

/-- Correct endpoint: unit norm of the raw Möbius/spectral value gives a strict
    completed generated mode. -/
theorem generatedStrictHelixMode_of_spectral_w_norm
    (ρ : ℂ) (hρ : ρ ≠ 0) (hunit : ‖SpectralSide.w ρ‖ = 1) :
    GeneratedStrictHelixMode ρ := by
  rw [generatedStrictHelixMode_iff_re_half]
  exact (SpectralSide.w_unit_iff_half ρ hρ).mp (by
    rw [Complex.normSq_eq_norm_sq, hunit]
    norm_num)

/-- Norm-square form of the same endpoint. -/
theorem generatedStrictHelixMode_of_spectral_w_unit
    (ρ : ℂ) (hρ : ρ ≠ 0) (hunit : Complex.normSq (SpectralSide.w ρ) = 1) :
    GeneratedStrictHelixMode ρ := by
  exact (generatedStrictHelixMode_iff_re_half ρ).mpr
    ((SpectralSide.w_unit_iff_half ρ hρ).mp hunit)

/-- Source phase unitarity becomes strict geometry once the source phase is
    identified with the raw Möbius/spectral readout. -/
theorem generatedStrictHelixMode_of_sourceReadout_identifies_spectral_w
    (ρ : ℂ) (hρ : ρ ≠ 0)
    (hread : SpectralSide.w ρ = (HelixReadsGRH.sourceWindingLossReadout ρ : ℂ)) :
    GeneratedStrictHelixMode ρ := by
  refine generatedStrictHelixMode_of_spectral_w_norm ρ hρ ?_
  rw [hread]
  have hpow := HelixReadsGRH.sourceWindingLossReadout_pow_norm ρ 1
  rwa [pow_one] at hpow

/-- The Euler-product source readout fixes the constructed-pole strict-geometry endpoint. -/
theorem strictGeometryOnConstructedCompletedPoles_of_eulerProductHelixSourceReadout
    (χ : DirichletCharacter ℂ N)
    (S : HelixReadsGRH.EulerProductHelixSourceReadout χ) :
    StrictGeometryOnConstructedCompletedPoles χ := by
  intro ρ hρ
  have hpole : HelixReadsGRH.CompletedLogDerivPole χ ρ :=
    helixLossPole_of_constructedCompletedHelixPole χ (fun _ : ℂ => 0) ρ hρ
  have hpow : ‖SpectralSide.w ρ ^ 1‖ = 1 :=
    HelixReadsGRH.eulerProductHelixSourceReadout_w_power_norm_eq_one χ 1 S ρ hρ
  have hhalf : ρ.re = 1 / 2 :=
    SpectralSide.half_of_w_power_norm_eq_one ρ
      (GRHSpectral.nontrivial_ne_zero hpole) 1 (by norm_num) hpow
  exact (generatedStrictHelixMode_iff_re_half ρ).mpr hhalf

/-- The commuting-square forcing law with the Euler-product source-readout endpoint supplied. -/
theorem helixLossPole_re_half_of_eulerProductHelixSourceReadout
    (χ : DirichletCharacter ℂ N) (F : ℂ → ℂ)
    (S : HelixReadsGRH.EulerProductHelixSourceReadout χ) :
    ∀ ρ : ℂ, HelixLossPole χ F ρ → ρ.re = 1 / 2 :=
  helixLossPole_re_half_of_strictGeometry χ F
    (strictGeometryOnConstructedCompletedPoles_of_eulerProductHelixSourceReadout χ S)

/-- FE-completion closure fixes the constructed-pole strict-geometry endpoint. -/
theorem strictGeometryOnConstructedCompletedPoles_of_fe_tends_towards_closure
    (χ : DirichletCharacter ℂ N)
    (hFE : ∀ ρ : ℂ, HelixReadsGRH.CompletedLogDerivPole χ ρ →
        HelixReadsGRH.CompletedLogDerivPole χ (1 - ρ))
    (hconv : ∀ ρ : ℂ, HelixReadsGRH.CompletedLogDerivPole χ ρ →
        ∃ L : ℝ, Filter.Tendsto (fun θ : ℝ => Real.exp ((ρ.re - 1 / 2) * θ))
          Filter.atTop (nhds L)) :
    StrictGeometryOnConstructedCompletedPoles χ := by
  intro ρ hρ
  have hpole : HelixReadsGRH.CompletedLogDerivPole χ ρ :=
    helixLossPole_of_constructedCompletedHelixPole χ (fun _ : ℂ => 0) ρ hρ
  have hhalf : ρ.re = 1 / 2 :=
    FEClosure.fe_tends_towards_closure χ hFE hconv ρ hpole
  exact (generatedStrictHelixMode_iff_re_half ρ).mpr hhalf

/-- The commuting-square forcing law with the FE-completion endpoint supplied. -/
theorem helixLossPole_re_half_of_fe_tends_towards_closure
    (χ : DirichletCharacter ℂ N) (F : ℂ → ℂ)
    (hFE : ∀ ρ : ℂ, HelixReadsGRH.CompletedLogDerivPole χ ρ →
        HelixReadsGRH.CompletedLogDerivPole χ (1 - ρ))
    (hconv : ∀ ρ : ℂ, HelixReadsGRH.CompletedLogDerivPole χ ρ →
        ∃ L : ℝ, Filter.Tendsto (fun θ : ℝ => Real.exp ((ρ.re - 1 / 2) * θ))
          Filter.atTop (nhds L)) :
    ∀ ρ : ℂ, HelixLossPole χ F ρ → ρ.re = 1 / 2 :=
  helixLossPole_re_half_of_strictGeometry χ F
    (strictGeometryOnConstructedCompletedPoles_of_fe_tends_towards_closure χ hFE hconv)

/-- A strict completed loss field has zero residual radial defect at every pole. -/
theorem strict_completed_loss_pole_radialDefect_zero
    (χ : DirichletCharacter ℂ N) (F : ℂ → ℂ)
    (H : StrictCompletedHelixLossField χ F)
    (ρ : ℂ) (hρ : HelixReadsGRH.CompletedLogDerivPole χ ρ) :
    radialDefect ρ = 0 :=
  generatedStrictHelixMode_forces_radialDefect_zero ρ
    (H.pole_generates_strict_mode ρ hρ)

/-- A strict completed loss field reads every pole at the half-unit. -/
theorem strict_completed_loss_pole_re_half
    (χ : DirichletCharacter ℂ N) (F : ℂ → ℂ)
    (H : StrictCompletedHelixLossField χ F)
    (ρ : ℂ) (hρ : HelixReadsGRH.CompletedLogDerivPole χ ρ) :
    ρ.re = 1 / 2 :=
  generatedStrictHelixMode_forces_re_half ρ
    (H.pole_generates_strict_mode ρ hρ)

/-- A strict completed loss field has no completed pole at `7/10 + iγ`. -/
theorem strict_completed_loss_no_re_seven_tenths_pole
    (χ : DirichletCharacter ℂ N) (F : ℂ → ℂ)
    (H : StrictCompletedHelixLossField χ F) (γ : ℝ) :
    ¬ HelixReadsGRH.CompletedLogDerivPole χ
        (((7 / 10 : ℝ) : ℂ) + (γ : ℂ) * Complex.I) := by
  intro hρ
  exact not_generatedStrictHelixMode_re_seven_tenths γ (H.pole_generates_strict_mode _ hρ)

/-- The existing no-radial-drift chain produces strict generated modes on poles. -/
theorem strict_modes_of_no_radial_drift_chain
    (χ : DirichletCharacter ℂ N)
    (D : HelixReadsGRH.PoleHelixNoRadialDriftChain χ) :
    ∀ ρ : ℂ, HelixReadsGRH.CompletedLogDerivPole χ ρ → GeneratedStrictHelixMode ρ := by
  intro ρ hρ
  exact generatedStrictHelixMode_of_loss_radial_zero ρ 1
    (HelixReadsGRH.zero_drift_on_logderiv_poles_of_no_radial_drift_chain χ D ρ hρ 1)

/-- A strict completed loss field built from the existing no-radial-drift chain. -/
def strictCompletedHelixLossFieldOfNoRadialDriftChain
    (χ : DirichletCharacter ℂ N) (F : ℂ → ℂ)
    (D : HelixReadsGRH.PoleHelixNoRadialDriftChain χ) :
    StrictCompletedHelixLossField χ F where
  pole_generates_strict_mode := strict_modes_of_no_radial_drift_chain χ D

/-- Strict completed loss on the pole spectrum gives the spectral GRH predicate. -/
theorem GRH_of_strict_completed_loss_field
    (χ : DirichletCharacter ℂ N) (F : ℂ → ℂ)
    (H : StrictCompletedHelixLossField χ F) :
    GRHSpectral.GRH χ := by
  intro ρ hρ
  exact strict_completed_loss_pole_re_half χ F H ρ hρ

/-- χ₃ strict completed loss field, including the completed grammar identity. -/
structure StrictChi3CompletedHelixLossField
    (χ₃ : DirichletCharacter ℂ 3) (F : ℂ → ℂ) where
  completed_loss : HelixEF.IsCompletedHelixLossChi3 F
  pole_generates_strict_mode :
    ∀ ρ : ℂ, HelixReadsGRH.CompletedLogDerivPole χ₃ ρ → GeneratedStrictHelixMode ρ

/-- Forget the χ₃ grammar field and keep the strict pole-spectrum readout. -/
def StrictChi3CompletedHelixLossField.toStrictCompletedHelixLossField
    {χ₃ : DirichletCharacter ℂ 3} {F : ℂ → ℂ}
    (H : StrictChi3CompletedHelixLossField χ₃ F) :
    StrictCompletedHelixLossField χ₃ F where
  pole_generates_strict_mode := H.pole_generates_strict_mode

/-- Any strict χ₃ completed loss field agrees with `−Λ'/Λχ₃` in the Euler-product half-plane. -/
theorem strict_chi3_completed_loss_eq_negCompletedLogDerivChi3
    (χ₃ : DirichletCharacter ℂ 3) (F : ℂ → ℂ)
    (H : StrictChi3CompletedHelixLossField χ₃ F) :
    ∀ s : ℂ, 1 < s.re → F s = negCompletedLogDerivChi3 s :=
  HelixEF.eq_negCompletedLogDerivChi3_of_isCompletedHelixLoss H.completed_loss

/-- The canonical χ₃ completed grammar plus the no-radial-drift chain is strict on poles. -/
def strictChi3CompletedHelixLossFieldOfNoRadialDriftChain
    (χ₃ : DirichletCharacter ℂ 3)
    (D : HelixReadsGRH.PoleHelixNoRadialDriftChain χ₃) :
    StrictChi3CompletedHelixLossField χ₃ negCompletedLogDerivChi3 where
  completed_loss := HelixEF.negCompletedLogDerivChi3_isCompletedHelixLoss
  pole_generates_strict_mode := strict_modes_of_no_radial_drift_chain χ₃ D

/-- χ₃ GRH from strict completed loss on the pole spectrum. -/
theorem GRH_chi3_of_strict_completed_loss_field
    (χ₃ : DirichletCharacter ℂ 3) (F : ℂ → ℂ)
    (H : StrictChi3CompletedHelixLossField χ₃ F) :
    GRHSpectral.GRH χ₃ :=
  GRH_of_strict_completed_loss_field χ₃ F H.toStrictCompletedHelixLossField

/-- χ₃ GRH from the canonical completed grammar and the existing no-radial-drift chain. -/
theorem GRH_chi3_of_strict_completed_loss_no_radial_drift_chain
    (χ₃ : DirichletCharacter ℂ 3)
    (D : HelixReadsGRH.PoleHelixNoRadialDriftChain χ₃) :
    GRHSpectral.GRH χ₃ :=
  GRH_chi3_of_strict_completed_loss_field χ₃ negCompletedLogDerivChi3
    (strictChi3CompletedHelixLossFieldOfNoRadialDriftChain χ₃ D)

end HelixStrictCompletion

end

#print axioms HelixStrictCompletion.generatedStrictHelixMode_iff_radialDefect_zero
#print axioms HelixStrictCompletion.not_generatedStrictHelixMode_re_seven_tenths
#print axioms HelixStrictCompletion.constructedCompletedHelixPole_of_helixLossPole
#print axioms HelixStrictCompletion.helixLossPole_of_constructedCompletedHelixPole
#print axioms HelixStrictCompletion.helixLossPoleSpectrum_eq_constructedCompletedHelixPoles
#print axioms HelixStrictCompletion.helixLossPole_re_half_of_strictGeometry
#print axioms HelixStrictCompletion.sourceWindingLossReadout_unit_does_not_force_re_half
#print axioms HelixStrictCompletion.generatedStrictHelixMode_of_spectral_w_norm
#print axioms HelixStrictCompletion.generatedStrictHelixMode_of_spectral_w_unit
#print axioms HelixStrictCompletion.generatedStrictHelixMode_of_sourceReadout_identifies_spectral_w
#print axioms HelixStrictCompletion.strictGeometryOnConstructedCompletedPoles_of_eulerProductHelixSourceReadout
#print axioms HelixStrictCompletion.helixLossPole_re_half_of_eulerProductHelixSourceReadout
#print axioms HelixStrictCompletion.strictGeometryOnConstructedCompletedPoles_of_fe_tends_towards_closure
#print axioms HelixStrictCompletion.helixLossPole_re_half_of_fe_tends_towards_closure
#print axioms HelixStrictCompletion.strict_completed_loss_no_re_seven_tenths_pole
#print axioms HelixStrictCompletion.strict_modes_of_no_radial_drift_chain
#print axioms HelixStrictCompletion.GRH_of_strict_completed_loss_field
#print axioms HelixStrictCompletion.strict_chi3_completed_loss_eq_negCompletedLogDerivChi3
#print axioms HelixStrictCompletion.GRH_chi3_of_strict_completed_loss_no_radial_drift_chain
