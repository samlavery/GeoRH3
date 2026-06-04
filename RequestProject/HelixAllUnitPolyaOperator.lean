import Mathlib
import RequestProject.HelixConvergence
import RequestProject.HelixSpectralPeaksLossSpace

/-!
# All Helix Modes as One Polya Operator

This file lifts a family of raw `HelixMode`s into one operator over
`ℓ²(ℕ, ℂ)`. The half-unit is not hidden in a subtype: the constructor takes the
derived statement `∀ k, (modes k).radialRate = 1 / 2` explicitly.
-/

noncomputable section

open scoped BigOperators Real
open Real Complex

/-- The all-mode helix loss Hilbert space. -/
abbrev HelixAllModeSpace := lp (fun _ : ℕ => ℂ) 2

/-- The all-mode spectral vector at coefficient index `n`. -/
def helixAllModeSpectralVector
    (modes : ℕ → HelixMode)
    (hℓ2 : ∀ n : ℕ,
      Memℓp (fun k : ℕ => spectral_vector (modes k).radialRate (modes k).frequency n) 2)
    (n : ℕ) : HelixAllModeSpace :=
  ⟨fun k => spectral_vector (modes k).radialRate (modes k).frequency n, hℓ2 n⟩

/-- The zero-coordinate stream read from all helix modes. -/
def helixAllModeZeros (modes : ℕ → HelixMode) : ℕ → ℝ × ℝ :=
  fun k => ((modes k).radialRate, (modes k).frequency)

/-- Coordinate projection onto the `k`-th helix mode axis in `ℓ²(ℕ, ℂ)`. -/
def helixAllModeProjection (k : ℕ) : HelixAllModeSpace →ₗ[ℝ] HelixAllModeSpace :=
  (lp.lsingle (𝕜 := ℝ) (E := fun _ : ℕ => ℂ) 2 k).comp
    (lp.evalₗ (𝕜 := ℝ) (E := fun _ : ℕ => ℂ) 2 k)

/-- Coordinate projection applies by keeping exactly the `k`-th coordinate. -/
theorem helixAllModeProjection_apply (k : ℕ) (x : HelixAllModeSpace) :
    helixAllModeProjection k x = lp.single 2 k (x k) :=
  rfl

/-- All supplied helix modes have nonzero spectral frequency. -/
theorem helixAllModeZeros_im_ne_zero
    (modes : ℕ → HelixMode) (hfreq : ∀ k, (modes k).frequency ≠ 0) :
    ∀ k, (helixAllModeZeros modes k).2 ≠ 0 := by
  intro k
  exact hfreq k

/-- All supplied helix modes lie in the strip once the helix geometry has derived the half-unit. -/
theorem helixAllModeZeros_in_strip
    (modes : ℕ → HelixMode) (hhalf : ∀ k, (modes k).radialRate = 1 / 2) :
    ∀ k, 0 < (helixAllModeZeros modes k).1 ∧ (helixAllModeZeros modes k).1 < 1 := by
  intro k
  constructor <;> rw [helixAllModeZeros, hhalf k] <;> norm_num

/-- The all-mode coordinate projections are self-adjoint. -/
theorem helixAllModeProjection_self_adjoint (k : ℕ) (x y : HelixAllModeSpace) :
    @inner ℝ HelixAllModeSpace _ (helixAllModeProjection k x) y =
      @inner ℝ HelixAllModeSpace _ x (helixAllModeProjection k y) := by
  rw [helixAllModeProjection_apply, helixAllModeProjection_apply]
  rw [lp.inner_single_left, lp.inner_single_right]

/-- The all-mode coordinate projections are idempotent. -/
theorem helixAllModeProjection_idempotent (k : ℕ) (x : HelixAllModeSpace) :
    helixAllModeProjection k (helixAllModeProjection k x) = helixAllModeProjection k x := by
  rw [helixAllModeProjection_apply, helixAllModeProjection_apply]
  simp

/-- The all-mode vector fills the `HilbertPolyaOperator.identification` field. -/
theorem helixAllMode_identification
    (modes : ℕ → HelixMode)
    (hhalf : ∀ k, (modes k).radialRate = 1 / 2)
    (hfreq : ∀ k, (modes k).frequency ≠ 0)
    (hℓ2 : ∀ n : ℕ,
      Memℓp (fun k : ℕ => spectral_vector (modes k).radialRate (modes k).frequency n) 2) :
    ∀ k n,
      (li_helix_term (helixAllModeZeros modes k).1 (helixAllModeZeros modes k).2 n).re +
      (li_helix_term (1 - (helixAllModeZeros modes k).1)
        (-(helixAllModeZeros modes k).2) n).re =
      ‖helixAllModeProjection k (helixAllModeSpectralVector modes hℓ2 n)‖ ^ 2 := by
  intro k n
  dsimp [helixAllModeZeros]
  rw [hhalf k]
  rw [spectral_identification_on_line (modes k).frequency (hfreq k) n]
  rw [helixAllModeProjection_apply]
  change ‖spectral_vector (1 / 2) (modes k).frequency n‖ ^ 2 =
    ‖lp.single (E := fun _ : ℕ => ℂ) 2 k
      (spectral_vector (modes k).radialRate (modes k).frequency n)‖ ^ 2
  rw [hhalf k]
  rw [lp.norm_single (by norm_num : (0 : ENNReal) < 2)]

/-- Raw helix modes instantiate the project `HilbertPolyaOperator` structure once the
half-unit, nonzero-frequency, and `ℓ²` totality statements are supplied explicitly. -/
def helixAllModeHilbertPolyaOperator
    (modes : ℕ → HelixMode)
    (hhalf : ∀ k, (modes k).radialRate = 1 / 2)
    (hfreq : ∀ k, (modes k).frequency ≠ 0)
    (hℓ2 : ∀ n : ℕ,
      Memℓp (fun k : ℕ => spectral_vector (modes k).radialRate (modes k).frequency n) 2) :
    HilbertPolyaOperator HelixAllModeSpace where
  zeros := helixAllModeZeros modes
  im_ne_zero := helixAllModeZeros_im_ne_zero modes hfreq
  in_strip := helixAllModeZeros_in_strip modes hhalf
  proj := helixAllModeProjection
  proj_sa := helixAllModeProjection_self_adjoint
  proj_idem := helixAllModeProjection_idempotent
  x := helixAllModeSpectralVector modes hℓ2
  identification := helixAllMode_identification modes hhalf hfreq hℓ2

/-- The instantiated all-mode operator returns the explicitly supplied helix half-unit. -/
theorem helixAllModeHilbertPolyaOperator_forces_half
    (modes : ℕ → HelixMode)
    (hhalf : ∀ k, (modes k).radialRate = 1 / 2)
    (hfreq : ∀ k, (modes k).frequency ≠ 0)
    (hℓ2 : ∀ n : ℕ,
      Memℓp (fun k : ℕ => spectral_vector (modes k).radialRate (modes k).frequency n) 2) :
    ∀ k, ((helixAllModeHilbertPolyaOperator modes hhalf hfreq hℓ2).zeros k).1 = 1 / 2 :=
  hilbert_polya_implies_rh (helixAllModeHilbertPolyaOperator modes hhalf hfreq hℓ2)

/-! ## Summable on-line helix data -/

/-- The `k`-th raw helix mode attached to summable on-line zero data. -/
def summableOnLineDataMode (D : SummableOnLineData) (k : ℕ) : HelixMode where
  coeff := 1
  rho := ⟨1 / 2, D.gamma k⟩
  coeff_ne_zero := by norm_num

/-- The half-unit readout for `SummableOnLineData` is visible and definitional. -/
theorem summableOnLineDataMode_half (D : SummableOnLineData) :
    ∀ k, (summableOnLineDataMode D k).radialRate = 1 / 2 := by
  intro k
  rfl

/-- The nonzero-frequency readout for `SummableOnLineData`. -/
theorem summableOnLineDataMode_frequency_ne_zero (D : SummableOnLineData) :
    ∀ k, (summableOnLineDataMode D k).frequency ≠ 0 := by
  intro k
  exact D.gamma_ne_zero k

/-- The spectral-vector coordinates of summable on-line data form an `ℓ²` vector. -/
theorem summableOnLineData_spectralVector_memℓp (D : SummableOnLineData) (n : ℕ) :
    Memℓp (fun k : ℕ => spectral_vector (1 / 2) (D.gamma k) n) 2 := by
  apply memℓp_gen
  have hs := paired_li_summable D n
  refine hs.congr ?_
  intro k
  have hid := spectral_identification_on_line (D.gamma k) (D.gamma_ne_zero k) n
  rw [show (2 : ENNReal).toReal = (2 : ℝ) by norm_num]
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at hid
  simpa using hid

/-- The all-mode `ℓ²` membership for the raw modes read from summable on-line data. -/
theorem summableOnLineDataModes_spectralVector_memℓp
    (D : SummableOnLineData) (n : ℕ) :
    Memℓp (fun k : ℕ =>
      spectral_vector (summableOnLineDataMode D k).radialRate
        (summableOnLineDataMode D k).frequency n) 2 := by
  simpa [summableOnLineDataMode, HelixMode.radialRate, HelixMode.frequency]
    using summableOnLineData_spectralVector_memℓp D n

/-- Summable on-line helix data instantiate the all-mode project operator on `ℓ²(ℕ, ℂ)`. -/
def summableOnLineDataHilbertPolyaOperator
    (D : SummableOnLineData) : HilbertPolyaOperator HelixAllModeSpace :=
  helixAllModeHilbertPolyaOperator
    (summableOnLineDataMode D)
    (summableOnLineDataMode_half D)
    (summableOnLineDataMode_frequency_ne_zero D)
    (summableOnLineDataModes_spectralVector_memℓp D)

/-- The all-mode operator built from summable on-line helix data returns the visible half-unit
for every coordinate. -/
theorem summableOnLineDataHilbertPolyaOperator_forces_half
    (D : SummableOnLineData) :
    ∀ k, ((summableOnLineDataHilbertPolyaOperator D).zeros k).1 = 1 / 2 :=
  hilbert_polya_implies_rh (summableOnLineDataHilbertPolyaOperator D)

end
