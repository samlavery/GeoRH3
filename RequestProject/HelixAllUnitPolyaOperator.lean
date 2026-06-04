import Mathlib
import RequestProject.HelixConvergence
import RequestProject.HelixHalfUnit
import RequestProject.HelixSpectralPeaksLossSpace
import RequestProject.HelixSourceBridge
import RequestProject.ZetaZeroDefs

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

/-- Zero radial loss in the helix projection derives the half-unit directly from the
loss coordinate, without using `UnitEnvelope`. -/
theorem helixMode_half_of_zero_radial_loss
    (m : HelixMode) (x : ℝ)
    (hzero : (loss (zero_embed m.radialRate m.frequency x)).radial = 0) :
    m.radialRate = 1 / 2 := by
  dsimp [loss, zero_embed] at hzero
  linarith

/-- A family of zero-radial-loss helix modes derives the half-unit coordinatewise. -/
theorem helixAllMode_half_of_zero_radial_loss
    (modes : ℕ → HelixMode) (x : ℕ → ℝ)
    (hzero : ∀ k, (loss (zero_embed (modes k).radialRate (modes k).frequency (x k))).radial = 0) :
    ∀ k, (modes k).radialRate = 1 / 2 := by
  intro k
  exact helixMode_half_of_zero_radial_loss (modes k) (x k) (hzero k)

/-- Helix isometry data for a single mode supplies zero radial loss. This is the
operator-side bridge from the intrinsic scaling exponent to the loss coordinate. -/
theorem helixMode_zero_radial_loss_of_isometry
    (m : HelixMode) (f : ℝ → ℝ)
    (hE : 0 < ∫ x in Set.Ioi (0 : ℝ), (f x) ^ 2)
    (hIso : ∀ lam : ℝ, 0 < lam →
      (∫ x in Set.Ioi (0 : ℝ), (lam ^ m.radialRate * f (lam * x)) ^ 2)
        = ∫ x in Set.Ioi (0 : ℝ), (f x) ^ 2)
    (x : ℝ) :
    (loss (zero_embed m.radialRate m.frequency x)).radial = 0 := by
  have hhalf : m.radialRate = 1 / 2 :=
    (HelixHalfUnit.helix_forces_half m.radialRate f hE).mp hIso
  dsimp [loss, zero_embed] at *
  linarith

/-- Coordinatewise helix isometry data supplies the zero-radial-loss input for
the all-mode operator. -/
theorem helixAllMode_zero_radial_loss_of_isometry
    (modes : ℕ → HelixMode) (scale : ℕ → ℝ) (f : ℕ → ℝ → ℝ)
    (hE : ∀ k, 0 < ∫ x in Set.Ioi (0 : ℝ), (f k x) ^ 2)
    (hIso : ∀ k : ℕ, ∀ lam : ℝ, 0 < lam →
      (∫ x in Set.Ioi (0 : ℝ), (lam ^ (modes k).radialRate * f k (lam * x)) ^ 2)
        = ∫ x in Set.Ioi (0 : ℝ), (f k x) ^ 2) :
    ∀ k,
      (loss (zero_embed (modes k).radialRate (modes k).frequency (scale k))).radial = 0 := by
  intro k
  exact helixMode_zero_radial_loss_of_isometry (modes k) (f k) (hE k) (hIso k) (scale k)

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

/-- Raw helix modes instantiate the all-mode operator from zero radial loss. The half-unit
input is derived by `helixAllMode_half_of_zero_radial_loss`. -/
def helixAllModeHilbertPolyaOperatorOfZeroRadialLoss
    (modes : ℕ → HelixMode) (x : ℕ → ℝ)
    (hzero : ∀ k, (loss (zero_embed (modes k).radialRate (modes k).frequency (x k))).radial = 0)
    (hfreq : ∀ k, (modes k).frequency ≠ 0)
    (hℓ2 : ∀ n : ℕ,
      Memℓp (fun k : ℕ => spectral_vector (modes k).radialRate (modes k).frequency n) 2) :
    HilbertPolyaOperator HelixAllModeSpace :=
  helixAllModeHilbertPolyaOperator
    modes
    (helixAllMode_half_of_zero_radial_loss modes x hzero)
    hfreq
    hℓ2

/-- Raw helix modes instantiate the all-mode operator from the helix isometry
bridge. The zero-radial-loss input is derived inside the operator constructor. -/
def helixAllModeHilbertPolyaOperatorOfIsometry
    (modes : ℕ → HelixMode) (scale : ℕ → ℝ) (f : ℕ → ℝ → ℝ)
    (hE : ∀ k, 0 < ∫ x in Set.Ioi (0 : ℝ), (f k x) ^ 2)
    (hIso : ∀ k : ℕ, ∀ lam : ℝ, 0 < lam →
      (∫ x in Set.Ioi (0 : ℝ), (lam ^ (modes k).radialRate * f k (lam * x)) ^ 2)
        = ∫ x in Set.Ioi (0 : ℝ), (f k x) ^ 2)
    (hfreq : ∀ k, (modes k).frequency ≠ 0)
    (hℓ2 : ∀ n : ℕ,
      Memℓp (fun k : ℕ => spectral_vector (modes k).radialRate (modes k).frequency n) 2) :
    HilbertPolyaOperator HelixAllModeSpace :=
  helixAllModeHilbertPolyaOperatorOfZeroRadialLoss
    modes
    scale
    (helixAllMode_zero_radial_loss_of_isometry modes scale f hE hIso)
    hfreq
    hℓ2

/-- The instantiated all-mode operator returns the explicitly supplied helix half-unit. -/
theorem helixAllModeHilbertPolyaOperator_forces_half
    (modes : ℕ → HelixMode)
    (hhalf : ∀ k, (modes k).radialRate = 1 / 2)
    (hfreq : ∀ k, (modes k).frequency ≠ 0)
    (hℓ2 : ∀ n : ℕ,
      Memℓp (fun k : ℕ => spectral_vector (modes k).radialRate (modes k).frequency n) 2) :
    ∀ k, ((helixAllModeHilbertPolyaOperator modes hhalf hfreq hℓ2).zeros k).1 = 1 / 2 :=
  fun k => hhalf k

/-- The zero-radial-loss all-mode operator returns the half-unit derived from the loss
coordinate. -/
theorem helixAllModeHilbertPolyaOperatorOfZeroRadialLoss_forces_half
    (modes : ℕ → HelixMode) (x : ℕ → ℝ)
    (hzero : ∀ k, (loss (zero_embed (modes k).radialRate (modes k).frequency (x k))).radial = 0)
    (hfreq : ∀ k, (modes k).frequency ≠ 0)
    (hℓ2 : ∀ n : ℕ,
      Memℓp (fun k : ℕ => spectral_vector (modes k).radialRate (modes k).frequency n) 2) :
    ∀ k, ((helixAllModeHilbertPolyaOperatorOfZeroRadialLoss modes x hzero hfreq hℓ2).zeros k).1 =
      1 / 2 :=
  helixAllMode_half_of_zero_radial_loss modes x hzero

/-- The raw all-mode operator is self-dual modewise: projection and dual loss are
self-adjoint for every spectral coordinate. -/
theorem helixAllModeHilbertPolyaOperator_self_dual
    (modes : ℕ → HelixMode)
    (hhalf : ∀ k, (modes k).radialRate = 1 / 2)
    (hfreq : ∀ k, (modes k).frequency ≠ 0)
    (hℓ2 : ∀ n : ℕ,
      Memℓp (fun k : ℕ => spectral_vector (modes k).radialRate (modes k).frequency n) 2)
    (k : ℕ) (x y : HelixAllModeSpace) :
    @inner ℝ HelixAllModeSpace _
        ((helixAllModeHilbertPolyaOperator modes hhalf hfreq hℓ2).proj k x) y =
        @inner ℝ HelixAllModeSpace _ x
          ((helixAllModeHilbertPolyaOperator modes hhalf hfreq hℓ2).proj k y) ∧
      @inner ℝ HelixAllModeSpace _
          (x - (helixAllModeHilbertPolyaOperator modes hhalf hfreq hℓ2).proj k x) y =
        @inner ℝ HelixAllModeSpace _ x
          (y - (helixAllModeHilbertPolyaOperator modes hhalf hfreq hℓ2).proj k y) :=
  hilbertPolyaOperator_self_dual (helixAllModeHilbertPolyaOperator modes hhalf hfreq hℓ2)
    k x y

/-- The zero-radial-loss all-mode operator is self-dual modewise. -/
theorem helixAllModeHilbertPolyaOperatorOfZeroRadialLoss_self_dual
    (modes : ℕ → HelixMode) (scale : ℕ → ℝ)
    (hzero : ∀ k,
      (loss (zero_embed (modes k).radialRate (modes k).frequency (scale k))).radial = 0)
    (hfreq : ∀ k, (modes k).frequency ≠ 0)
    (hℓ2 : ∀ n : ℕ,
      Memℓp (fun k : ℕ => spectral_vector (modes k).radialRate (modes k).frequency n) 2)
    (k : ℕ) (x y : HelixAllModeSpace) :
    @inner ℝ HelixAllModeSpace _
        ((helixAllModeHilbertPolyaOperatorOfZeroRadialLoss modes scale hzero hfreq hℓ2).proj k x)
        y =
        @inner ℝ HelixAllModeSpace _ x
          ((helixAllModeHilbertPolyaOperatorOfZeroRadialLoss modes scale hzero hfreq hℓ2).proj k y) ∧
      @inner ℝ HelixAllModeSpace _
          (x -
            (helixAllModeHilbertPolyaOperatorOfZeroRadialLoss modes scale hzero hfreq hℓ2).proj k x)
          y =
        @inner ℝ HelixAllModeSpace _ x
          (y -
            (helixAllModeHilbertPolyaOperatorOfZeroRadialLoss modes scale hzero hfreq hℓ2).proj k y) :=
  hilbertPolyaOperator_self_dual
    (helixAllModeHilbertPolyaOperatorOfZeroRadialLoss modes scale hzero hfreq hℓ2) k x y

/-- The zero-radial-loss all-mode package: the same operator carries the derived half-unit,
self-dual projection/loss channels, and the norm-square spectral identification. -/
theorem helixAllModeHilbertPolyaOperatorOfZeroRadialLoss_package
    (modes : ℕ → HelixMode) (scale : ℕ → ℝ)
    (hzero : ∀ k,
      (loss (zero_embed (modes k).radialRate (modes k).frequency (scale k))).radial = 0)
    (hfreq : ∀ k, (modes k).frequency ≠ 0)
    (hℓ2 : ∀ n : ℕ,
      Memℓp (fun k : ℕ => spectral_vector (modes k).radialRate (modes k).frequency n) 2) :
    let HP := helixAllModeHilbertPolyaOperatorOfZeroRadialLoss modes scale hzero hfreq hℓ2
    (∀ k, (HP.zeros k).1 = 1 / 2) ∧
      (∀ k x y,
        @inner ℝ HelixAllModeSpace _ (HP.proj k x) y =
            @inner ℝ HelixAllModeSpace _ x (HP.proj k y) ∧
          @inner ℝ HelixAllModeSpace _ (x - HP.proj k x) y =
            @inner ℝ HelixAllModeSpace _ x (y - HP.proj k y)) ∧
      (∀ k n,
        (li_helix_term (HP.zeros k).1 (HP.zeros k).2 n).re +
          (li_helix_term (1 - (HP.zeros k).1) (-(HP.zeros k).2) n).re =
        ‖HP.proj k (HP.x n)‖ ^ 2) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · exact helixAllModeHilbertPolyaOperatorOfZeroRadialLoss_forces_half
      modes scale hzero hfreq hℓ2
  · intro k x y
    exact helixAllModeHilbertPolyaOperatorOfZeroRadialLoss_self_dual
      modes scale hzero hfreq hℓ2 k x y
  · intro k n
    exact (helixAllModeHilbertPolyaOperatorOfZeroRadialLoss
      modes scale hzero hfreq hℓ2).identification k n

/-! ## Actual zeta zeros as helix loss modes -/

/-- The canonical subtype of actual nontrivial zeta zeros. -/
abbrev ActualZetaZero := {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}

/-- An actual nontrivial zeta zero, read as a raw helix mode. -/
def actualZetaZeroHelixMode (ρ : ActualZetaZero) : HelixMode where
  coeff := 1
  rho := ρ.1
  coeff_ne_zero := by norm_num

/-- A stream of actual nontrivial zeta zeros, read as raw helix modes. -/
def actualZetaZeroHelixModes (zeros : ℕ → ActualZetaZero) : ℕ → HelixMode :=
  fun k => actualZetaZeroHelixMode (zeros k)

/-- Any project `HilbertPolyaOperator` that has an actual zeta zero at coordinate `k`
identifies that zero's paired-Li coefficient with the coordinate energy. -/
theorem actualZetaZero_pairedLi_eq_lossEnergy_of_HilbertPolyaOperator
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (HP : HilbertPolyaOperator H) (ρ : ℂ) (_hρ : ρ ∈ ZD.NontrivialZeros)
    (k n : ℕ) (hre : (HP.zeros k).1 = ρ.re) (him : (HP.zeros k).2 = ρ.im) :
    (li_helix_term ρ.re ρ.im n).re +
      (li_helix_term (1 - ρ.re) (-ρ.im) n).re =
    ‖HP.proj k (HP.x n)‖ ^ 2 := by
  rw [← hre, ← him]
  exact HP.identification k n

/-- The coordinate energy in the preceding identification is always nonnegative. -/
theorem actualZetaZero_pairedLi_nonneg_of_HilbertPolyaOperator
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (HP : HilbertPolyaOperator H) (ρ : ℂ) (hρ : ρ ∈ ZD.NontrivialZeros)
    (k n : ℕ) (hre : (HP.zeros k).1 = ρ.re) (him : (HP.zeros k).2 = ρ.im) :
    0 ≤ (li_helix_term ρ.re ρ.im n).re +
      (li_helix_term (1 - ρ.re) (-ρ.im) n).re := by
  rw [actualZetaZero_pairedLi_eq_lossEnergy_of_HilbertPolyaOperator
    HP ρ hρ k n hre him]
  positivity

/-- A stream of actual zeta zeros instantiates the all-mode helix operator when its
helix loss readout has zero radial drift and its spectral vector stream is total. -/
def actualZetaZeroHilbertPolyaOperator
    (zeros : ℕ → ActualZetaZero) (scale : ℕ → ℝ)
    (hzero : ∀ k,
      (loss (zero_embed (zeros k).1.re (zeros k).1.im (scale k))).radial = 0)
    (hfreq : ∀ k, (zeros k).1.im ≠ 0)
    (hℓ2 : ∀ n : ℕ,
      Memℓp (fun k : ℕ => spectral_vector (zeros k).1.re (zeros k).1.im n) 2) :
    HilbertPolyaOperator HelixAllModeSpace :=
  helixAllModeHilbertPolyaOperatorOfZeroRadialLoss
    (actualZetaZeroHelixModes zeros)
    scale
    (by
      intro k
      simpa [actualZetaZeroHelixModes, actualZetaZeroHelixMode, HelixMode.radialRate,
        HelixMode.frequency] using hzero k)
    (by
      intro k
      simpa [actualZetaZeroHelixModes, actualZetaZeroHelixMode, HelixMode.frequency]
        using hfreq k)
    (by
      intro n
      simpa [actualZetaZeroHelixModes, actualZetaZeroHelixMode, HelixMode.radialRate,
        HelixMode.frequency] using hℓ2 n)

/-- The helix isometry bridge supplies zero radial loss for actual nontrivial zeta zeros. -/
theorem actualZetaZeros_zero_radial_loss_of_isometry
    (zeros : ℕ → ActualZetaZero) (scale : ℕ → ℝ) (f : ℕ → ℝ → ℝ)
    (hE : ∀ k, 0 < ∫ x in Set.Ioi (0 : ℝ), (f k x) ^ 2)
    (hIso : ∀ k : ℕ, ∀ lam : ℝ, 0 < lam →
      (∫ x in Set.Ioi (0 : ℝ), (lam ^ (zeros k).1.re * f k (lam * x)) ^ 2)
        = ∫ x in Set.Ioi (0 : ℝ), (f k x) ^ 2) :
    ∀ k, (loss (zero_embed (zeros k).1.re (zeros k).1.im (scale k))).radial = 0 := by
  intro k
  exact helixMode_zero_radial_loss_of_isometry
    (actualZetaZeroHelixMode (zeros k))
    (f k)
    (hE k)
    (by
      intro lam hlam
      simpa [actualZetaZeroHelixMode, HelixMode.radialRate] using hIso k lam hlam)
    (scale k)

/-- A stream of actual zeta zeros instantiates the all-mode helix operator from
helix isometry data. The radial-loss bridge is part of this operator constructor. -/
def actualZetaZeroHilbertPolyaOperatorOfIsometry
    (zeros : ℕ → ActualZetaZero) (scale : ℕ → ℝ) (f : ℕ → ℝ → ℝ)
    (hE : ∀ k, 0 < ∫ x in Set.Ioi (0 : ℝ), (f k x) ^ 2)
    (hIso : ∀ k : ℕ, ∀ lam : ℝ, 0 < lam →
      (∫ x in Set.Ioi (0 : ℝ), (lam ^ (zeros k).1.re * f k (lam * x)) ^ 2)
        = ∫ x in Set.Ioi (0 : ℝ), (f k x) ^ 2)
    (hfreq : ∀ k, (zeros k).1.im ≠ 0)
    (hℓ2 : ∀ n : ℕ,
      Memℓp (fun k : ℕ => spectral_vector (zeros k).1.re (zeros k).1.im n) 2) :
    HilbertPolyaOperator HelixAllModeSpace :=
  actualZetaZeroHilbertPolyaOperator zeros scale
    (actualZetaZeros_zero_radial_loss_of_isometry zeros scale f hE hIso)
    hfreq
    hℓ2

/-- From the isometry-built actual-zero operator, paired-Li coefficients are
projection-loss energies. -/
theorem actualZetaZeros_pairedLi_eq_lossEnergy_of_isometry
    (zeros : ℕ → ActualZetaZero) (scale : ℕ → ℝ) (f : ℕ → ℝ → ℝ)
    (hE : ∀ k, 0 < ∫ x in Set.Ioi (0 : ℝ), (f k x) ^ 2)
    (hIso : ∀ k : ℕ, ∀ lam : ℝ, 0 < lam →
      (∫ x in Set.Ioi (0 : ℝ), (lam ^ (zeros k).1.re * f k (lam * x)) ^ 2)
        = ∫ x in Set.Ioi (0 : ℝ), (f k x) ^ 2)
    (hfreq : ∀ k, (zeros k).1.im ≠ 0)
    (hℓ2 : ∀ n : ℕ,
      Memℓp (fun k : ℕ => spectral_vector (zeros k).1.re (zeros k).1.im n) 2) :
    ∀ k n,
      (li_helix_term (zeros k).1.re (zeros k).1.im n).re +
        (li_helix_term (1 - (zeros k).1.re) (-(zeros k).1.im) n).re =
      ‖(actualZetaZeroHilbertPolyaOperatorOfIsometry
          zeros scale f hE hIso hfreq hℓ2).proj k
        ((actualZetaZeroHilbertPolyaOperatorOfIsometry
          zeros scale f hE hIso hfreq hℓ2).x n)‖ ^ 2 := by
  intro k n
  exact (actualZetaZeroHilbertPolyaOperatorOfIsometry
    zeros scale f hE hIso hfreq hℓ2).identification k n

/-- For an actual-zero stream, the paired-Li coefficient is the corresponding
helix loss energy. -/
theorem actualZetaZeros_pairedLi_eq_lossEnergy
    (zeros : ℕ → ActualZetaZero) (scale : ℕ → ℝ)
    (hzero : ∀ k,
      (loss (zero_embed (zeros k).1.re (zeros k).1.im (scale k))).radial = 0)
    (hfreq : ∀ k, (zeros k).1.im ≠ 0)
    (hℓ2 : ∀ n : ℕ,
      Memℓp (fun k : ℕ => spectral_vector (zeros k).1.re (zeros k).1.im n) 2) :
    ∀ k n,
      (li_helix_term (zeros k).1.re (zeros k).1.im n).re +
        (li_helix_term (1 - (zeros k).1.re) (-(zeros k).1.im) n).re =
      ‖(actualZetaZeroHilbertPolyaOperator zeros scale hzero hfreq hℓ2).proj k
        ((actualZetaZeroHilbertPolyaOperator zeros scale hzero hfreq hℓ2).x n)‖ ^ 2 := by
  intro k n
  exact (actualZetaZeroHilbertPolyaOperator zeros scale hzero hfreq hℓ2).identification k n

/-- For an actual-zero stream, the paired-Li coefficient is nonnegative because it
is a helix loss-energy norm-square. -/
theorem actualZetaZeros_pairedLi_nonneg_lossEnergy
    (zeros : ℕ → ActualZetaZero) (scale : ℕ → ℝ)
    (hzero : ∀ k,
      (loss (zero_embed (zeros k).1.re (zeros k).1.im (scale k))).radial = 0)
    (hfreq : ∀ k, (zeros k).1.im ≠ 0)
    (hℓ2 : ∀ n : ℕ,
      Memℓp (fun k : ℕ => spectral_vector (zeros k).1.re (zeros k).1.im n) 2) :
    ∀ k n,
      0 ≤ (li_helix_term (zeros k).1.re (zeros k).1.im n).re +
        (li_helix_term (1 - (zeros k).1.re) (-(zeros k).1.im) n).re := by
  intro k n
  rw [actualZetaZeros_pairedLi_eq_lossEnergy zeros scale hzero hfreq hℓ2 k n]
  positivity

/-- The actual-zero loss-energy package: equality with a norm-square and
nonnegativity are carried by the same helix operator. -/
theorem actualZetaZeros_lossEnergy_package
    (zeros : ℕ → ActualZetaZero) (scale : ℕ → ℝ)
    (hzero : ∀ k,
      (loss (zero_embed (zeros k).1.re (zeros k).1.im (scale k))).radial = 0)
    (hfreq : ∀ k, (zeros k).1.im ≠ 0)
    (hℓ2 : ∀ n : ℕ,
      Memℓp (fun k : ℕ => spectral_vector (zeros k).1.re (zeros k).1.im n) 2) :
    let HP := actualZetaZeroHilbertPolyaOperator zeros scale hzero hfreq hℓ2
    (∀ k n,
      (li_helix_term (zeros k).1.re (zeros k).1.im n).re +
        (li_helix_term (1 - (zeros k).1.re) (-(zeros k).1.im) n).re =
      ‖HP.proj k (HP.x n)‖ ^ 2) ∧
    (∀ k n,
      0 ≤ (li_helix_term (zeros k).1.re (zeros k).1.im n).re +
        (li_helix_term (1 - (zeros k).1.re) (-(zeros k).1.im) n).re) := by
  dsimp only
  exact ⟨actualZetaZeros_pairedLi_eq_lossEnergy zeros scale hzero hfreq hℓ2,
    actualZetaZeros_pairedLi_nonneg_lossEnergy zeros scale hzero hfreq hℓ2⟩

/-- The concrete helix no-radial-defect audit supplies the zero-radial-loss input
needed by the actual-zero all-mode operator. -/
theorem actualZetaZeros_zero_radial_loss_of_helixConstruction
    (zeros : ℕ → ActualZetaZero) (scale : ℕ → ℝ)
    (hconstruct : HelixConstructionNoRadialDriftOnZeros) :
    ∀ k, (loss (zero_embed (zeros k).1.re (zeros k).1.im (scale k))).radial = 0 := by
  intro k
  exact (hconstruct (zeros k).1 (zeros k).2 (scale k)).2.2.2.2

/-- A stream of actual zeta zeros instantiates the all-mode helix operator with
zero radial loss supplied by the helix construction itself. -/
def actualZetaZeroHilbertPolyaOperatorOfHelixConstruction
    (zeros : ℕ → ActualZetaZero) (scale : ℕ → ℝ)
    (hconstruct : HelixConstructionNoRadialDriftOnZeros)
    (hfreq : ∀ k, (zeros k).1.im ≠ 0)
    (hℓ2 : ∀ n : ℕ,
      Memℓp (fun k : ℕ => spectral_vector (zeros k).1.re (zeros k).1.im n) 2) :
    HilbertPolyaOperator HelixAllModeSpace :=
  actualZetaZeroHilbertPolyaOperator zeros scale
    (actualZetaZeros_zero_radial_loss_of_helixConstruction zeros scale hconstruct)
    hfreq
    hℓ2

/-- With zero radial loss supplied by the helix construction, actual zeros' paired-Li
coefficients are the corresponding projection-loss energies. -/
theorem actualZetaZeros_pairedLi_eq_lossEnergy_of_helixConstruction
    (zeros : ℕ → ActualZetaZero) (scale : ℕ → ℝ)
    (hconstruct : HelixConstructionNoRadialDriftOnZeros)
    (hfreq : ∀ k, (zeros k).1.im ≠ 0)
    (hℓ2 : ∀ n : ℕ,
      Memℓp (fun k : ℕ => spectral_vector (zeros k).1.re (zeros k).1.im n) 2) :
    ∀ k n,
      (li_helix_term (zeros k).1.re (zeros k).1.im n).re +
        (li_helix_term (1 - (zeros k).1.re) (-(zeros k).1.im) n).re =
      ‖(actualZetaZeroHilbertPolyaOperatorOfHelixConstruction
          zeros scale hconstruct hfreq hℓ2).proj k
        ((actualZetaZeroHilbertPolyaOperatorOfHelixConstruction
          zeros scale hconstruct hfreq hℓ2).x n)‖ ^ 2 := by
  intro k n
  exact (actualZetaZeroHilbertPolyaOperatorOfHelixConstruction
    zeros scale hconstruct hfreq hℓ2).identification k n

/-- With zero radial loss supplied by the helix construction, actual zeros' paired-Li
coefficients are nonnegative projection-loss energies. -/
theorem actualZetaZeros_pairedLi_nonneg_lossEnergy_of_helixConstruction
    (zeros : ℕ → ActualZetaZero) (scale : ℕ → ℝ)
    (hconstruct : HelixConstructionNoRadialDriftOnZeros)
    (hfreq : ∀ k, (zeros k).1.im ≠ 0)
    (hℓ2 : ∀ n : ℕ,
      Memℓp (fun k : ℕ => spectral_vector (zeros k).1.re (zeros k).1.im n) 2) :
    ∀ k n,
      0 ≤ (li_helix_term (zeros k).1.re (zeros k).1.im n).re +
        (li_helix_term (1 - (zeros k).1.re) (-(zeros k).1.im) n).re := by
  intro k n
  rw [actualZetaZeros_pairedLi_eq_lossEnergy_of_helixConstruction
    zeros scale hconstruct hfreq hℓ2 k n]
  positivity

/-- The construction-derived actual-zero package: the helix construction supplies
zero radial loss, and the operator supplies equality with a nonnegative norm-square. -/
theorem actualZetaZeros_lossEnergy_package_of_helixConstruction
    (zeros : ℕ → ActualZetaZero) (scale : ℕ → ℝ)
    (hconstruct : HelixConstructionNoRadialDriftOnZeros)
    (hfreq : ∀ k, (zeros k).1.im ≠ 0)
    (hℓ2 : ∀ n : ℕ,
      Memℓp (fun k : ℕ => spectral_vector (zeros k).1.re (zeros k).1.im n) 2) :
    let HP := actualZetaZeroHilbertPolyaOperatorOfHelixConstruction
      zeros scale hconstruct hfreq hℓ2
    (∀ k n,
      (li_helix_term (zeros k).1.re (zeros k).1.im n).re +
        (li_helix_term (1 - (zeros k).1.re) (-(zeros k).1.im) n).re =
      ‖HP.proj k (HP.x n)‖ ^ 2) ∧
    (∀ k n,
      0 ≤ (li_helix_term (zeros k).1.re (zeros k).1.im n).re +
        (li_helix_term (1 - (zeros k).1.re) (-(zeros k).1.im) n).re) := by
  dsimp only
  exact ⟨actualZetaZeros_pairedLi_eq_lossEnergy_of_helixConstruction
      zeros scale hconstruct hfreq hℓ2,
    actualZetaZeros_pairedLi_nonneg_lossEnergy_of_helixConstruction
      zeros scale hconstruct hfreq hℓ2⟩

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

/-- The summable on-line data modes have zero radial loss at every source scale. -/
theorem summableOnLineDataMode_zero_radial_loss (D : SummableOnLineData) (x : ℕ → ℝ) :
    ∀ k,
      (loss (zero_embed (summableOnLineDataMode D k).radialRate
        (summableOnLineDataMode D k).frequency (x k))).radial = 0 := by
  intro k
  dsimp [summableOnLineDataMode, HelixMode.radialRate, HelixMode.frequency, loss, zero_embed]
  norm_num

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

/-- Summable on-line helix data instantiate the all-mode operator through zero radial loss. -/
def summableOnLineDataHilbertPolyaOperatorOfZeroRadialLoss
    (D : SummableOnLineData) (x : ℕ → ℝ) : HilbertPolyaOperator HelixAllModeSpace :=
  helixAllModeHilbertPolyaOperatorOfZeroRadialLoss
    (summableOnLineDataMode D)
    x
    (summableOnLineDataMode_zero_radial_loss D x)
    (summableOnLineDataMode_frequency_ne_zero D)
    (summableOnLineDataModes_spectralVector_memℓp D)

/-- The all-mode operator built from summable on-line helix data returns the visible half-unit
for every coordinate. -/
theorem summableOnLineDataHilbertPolyaOperator_forces_half
    (D : SummableOnLineData) :
    ∀ k, ((summableOnLineDataHilbertPolyaOperator D).zeros k).1 = 1 / 2 :=
  summableOnLineDataMode_half D

/-- The all-mode operator built from summable on-line helix data through zero radial loss
returns the half-unit for every coordinate. -/
theorem summableOnLineDataHilbertPolyaOperatorOfZeroRadialLoss_forces_half
    (D : SummableOnLineData) (x : ℕ → ℝ) :
    ∀ k, ((summableOnLineDataHilbertPolyaOperatorOfZeroRadialLoss D x).zeros k).1 = 1 / 2 :=
  helixAllMode_half_of_zero_radial_loss
    (summableOnLineDataMode D)
    x
    (summableOnLineDataMode_zero_radial_loss D x)

/-- The summable on-line all-mode operator is self-dual modewise. -/
theorem summableOnLineDataHilbertPolyaOperatorOfZeroRadialLoss_self_dual
    (D : SummableOnLineData) (scale : ℕ → ℝ)
    (k : ℕ) (x y : HelixAllModeSpace) :
    @inner ℝ HelixAllModeSpace _
        ((summableOnLineDataHilbertPolyaOperatorOfZeroRadialLoss D scale).proj k x) y =
        @inner ℝ HelixAllModeSpace _ x
          ((summableOnLineDataHilbertPolyaOperatorOfZeroRadialLoss D scale).proj k y) ∧
      @inner ℝ HelixAllModeSpace _
          (x - (summableOnLineDataHilbertPolyaOperatorOfZeroRadialLoss D scale).proj k x) y =
        @inner ℝ HelixAllModeSpace _ x
          (y - (summableOnLineDataHilbertPolyaOperatorOfZeroRadialLoss D scale).proj k y) :=
  hilbertPolyaOperator_self_dual
    (summableOnLineDataHilbertPolyaOperatorOfZeroRadialLoss D scale) k x y

/-- The summable on-line zero-radial-loss package: one all-mode operator carries the
half-unit, self-dual projection/loss channels, and norm-square spectral identification. -/
theorem summableOnLineDataHilbertPolyaOperatorOfZeroRadialLoss_package
    (D : SummableOnLineData) (scale : ℕ → ℝ) :
    let HP := summableOnLineDataHilbertPolyaOperatorOfZeroRadialLoss D scale
    (∀ k, (HP.zeros k).1 = 1 / 2) ∧
      (∀ k x y,
        @inner ℝ HelixAllModeSpace _ (HP.proj k x) y =
            @inner ℝ HelixAllModeSpace _ x (HP.proj k y) ∧
          @inner ℝ HelixAllModeSpace _ (x - HP.proj k x) y =
            @inner ℝ HelixAllModeSpace _ x (y - HP.proj k y)) ∧
      (∀ k n,
        (li_helix_term (HP.zeros k).1 (HP.zeros k).2 n).re +
          (li_helix_term (1 - (HP.zeros k).1) (-(HP.zeros k).2) n).re =
        ‖HP.proj k (HP.x n)‖ ^ 2) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · exact summableOnLineDataHilbertPolyaOperatorOfZeroRadialLoss_forces_half D scale
  · intro k x y
    exact summableOnLineDataHilbertPolyaOperatorOfZeroRadialLoss_self_dual D scale k x y
  · intro k n
    exact (summableOnLineDataHilbertPolyaOperatorOfZeroRadialLoss D scale).identification k n

#print axioms helixMode_zero_radial_loss_of_isometry
#print axioms helixAllMode_zero_radial_loss_of_isometry
#print axioms helixAllModeHilbertPolyaOperatorOfIsometry
#print axioms actualZetaZeros_zero_radial_loss_of_isometry
#print axioms actualZetaZeroHilbertPolyaOperatorOfIsometry
#print axioms actualZetaZeros_pairedLi_eq_lossEnergy_of_isometry

end
