import Mathlib
import RequestProject.HelixSpectralPeaksLossSpace

/-!
# Helix Unit Modes Instantiate the Polya Operator

This file builds an actual `HilbertPolyaOperator` from helix modes whose
source envelope is unit-normalized. The constructor does not take `ρ.re = 1/2`
as input; it derives the half-unit from `HelixMode.UnitEnvelope` when filling
the `identification` field.
-/

noncomputable section

open scoped BigOperators Real
open Real Complex

/-- A helix mode carrying the data needed by the Polya constructor. -/
abbrev HelixUnitMode :=
  {m : HelixMode // m.UnitEnvelope ∧ m.frequency ≠ 0}

/-- The constant zero-coordinate stream read from one helix unit mode. -/
def helixUnitModeZeros (mode : HelixUnitMode) : ℕ → ℝ × ℝ :=
  fun _ => (mode.val.radialRate, mode.val.frequency)

/-- The spectral vector stream attached to one helix unit mode. -/
def helixUnitModeSpectralVectors (mode : HelixUnitMode) : ℕ → ℂ :=
  fun n => spectral_vector mode.val.radialRate mode.val.frequency n

/-- Helix unit modes have nonzero spectral frequency by construction. -/
theorem helixUnitModeZeros_im_ne_zero (mode : HelixUnitMode) :
    ∀ k, (helixUnitModeZeros mode k).2 ≠ 0 := by
  intro k
  exact mode.property.2

/-- Helix unit modes lie in the critical strip after the helix half-unit is derived. -/
theorem helixUnitModeZeros_in_strip (mode : HelixUnitMode) :
    ∀ k, 0 < (helixUnitModeZeros mode k).1 ∧ (helixUnitModeZeros mode k).1 < 1 := by
  intro k
  have hhalf : mode.val.radialRate = 1 / 2 :=
    helix_spectral_peak_forces_half_unit mode.val mode.property.1
  constructor <;> rw [helixUnitModeZeros, hhalf] <;> norm_num

/-- The identity projection is self-adjoint on the real Hilbert space `ℂ`. -/
theorem helixUnitMode_id_proj_self_adjoint (_k : ℕ) (x y : ℂ) :
    @inner ℝ ℂ _ ((LinearMap.id : ℂ →ₗ[ℝ] ℂ) x) y =
      @inner ℝ ℂ _ x ((LinearMap.id : ℂ →ₗ[ℝ] ℂ) y) := by
  rfl

/-- The identity projection is idempotent. -/
theorem helixUnitMode_id_proj_idempotent (_k : ℕ) (x : ℂ) :
    (LinearMap.id : ℂ →ₗ[ℝ] ℂ) ((LinearMap.id : ℂ →ₗ[ℝ] ℂ) x) =
      (LinearMap.id : ℂ →ₗ[ℝ] ℂ) x := by
  rfl

/-- The helix unit-mode stream fills the `identification` field of
`HilbertPolyaOperator`. -/
theorem helixUnitMode_identification (mode : HelixUnitMode) :
    ∀ k n,
      (li_helix_term (helixUnitModeZeros mode k).1 (helixUnitModeZeros mode k).2 n).re +
      (li_helix_term (1 - (helixUnitModeZeros mode k).1)
        (-(helixUnitModeZeros mode k).2) n).re =
      ‖(LinearMap.id : ℂ →ₗ[ℝ] ℂ)
        (spectral_vector mode.val.radialRate mode.val.frequency n)‖ ^ 2 := by
  intro k n
  have hhalf : mode.val.radialRate = 1 / 2 :=
    helix_spectral_peak_forces_half_unit mode.val mode.property.1
  have hfreq : mode.val.frequency ≠ 0 := mode.property.2
  dsimp [helixUnitModeZeros]
  rw [hhalf]
  simpa using spectral_identification_on_line mode.val.frequency hfreq n

/-- Helix unit modes instantiate the project `HilbertPolyaOperator` structure. -/
def helixUnitModeHilbertPolyaOperator
    (mode : HelixUnitMode) : HilbertPolyaOperator ℂ where
  zeros := helixUnitModeZeros mode
  im_ne_zero := helixUnitModeZeros_im_ne_zero mode
  in_strip := helixUnitModeZeros_in_strip mode
  proj := fun _ => (LinearMap.id : ℂ →ₗ[ℝ] ℂ)
  proj_sa := helixUnitMode_id_proj_self_adjoint
  proj_idem := helixUnitMode_id_proj_idempotent
  x := helixUnitModeSpectralVectors mode
  identification := helixUnitMode_identification mode

/-- The instantiated Polya operator returns the helix-derived half-unit for every mode. -/
theorem helixUnitModeHilbertPolyaOperator_forces_half
    (mode : HelixUnitMode) :
    ∀ k, ((helixUnitModeHilbertPolyaOperator mode).zeros k).1 = 1 / 2 :=
  hilbert_polya_implies_rh (helixUnitModeHilbertPolyaOperator mode)

end
