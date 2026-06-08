import Mathlib
import RequestProject.GRHSpectralCriterion
import RequestProject.HelixExplicitFormulaTermByTerm
import RequestProject.HelixHalfUnit
import RequestProject.HelixNonClosure
import RequestProject.HelixSourceBridge
import RequestProject.HelixUnitaryOperator
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

/-- The winding value determined by radial expansion `σ` and pitch `γ`. -/
def radialPitchWinding (σ γ : ℝ) : ℂ :=
  (σ : ℂ) + (γ : ℂ) * Complex.I

/-- The winding-loss readout attached to a pole. It keeps the full winding rate:
    radial expansion as the real coordinate and pitch as the imaginary coordinate. -/
def windingLossReadout (ρ : ℂ) : ℂ :=
  radialPitchWinding ρ.re ρ.im

/-- The full-loop winding-loss multiplier for loop exponent `M`. It records the
    radial excess of a zero over the self-dual half-unit after one configured loop. -/
def fullLoopWindingLoss (M : ℝ) (ρ : ℂ) : ℝ :=
  Real.exp (M * (ρ.re - 1 / 2))

/-- The winding-loss spectrum read from the completed log-derivative pole channel. -/
def WindingLossSpectrum (χ : DirichletCharacter ℂ N) : Set ℂ :=
  {z | ∃ ρ : ℂ, CompletedLogDerivPole χ ρ ∧ z = windingLossReadout ρ}

/-- The source helix value determined by radial growth plus pitch. -/
def sourceRadialPitchWinding (σ γ : ℝ) : Circle :=
  helixUnitary (σ + γ)

/-- Winding is radial growth plus pitch, and source multiplication is angular addition. -/
theorem sourceRadialPitchWinding_eq_mul (σ γ : ℝ) :
    sourceRadialPitchWinding σ γ = helixUnitary σ * helixUnitary γ := by
  exact helixUnitary_add σ γ

/-- Complex-coordinate form of radial-growth plus pitch angular addition. -/
theorem sourceRadialPitchWinding_coe_eq_mul (σ γ : ℝ) :
    (sourceRadialPitchWinding σ γ : ℂ) =
      (helixUnitary σ : ℂ) * (helixUnitary γ : ℂ) := by
  rw [sourceRadialPitchWinding_eq_mul]
  rfl

/-- The source winding value determined by radial growth plus pitch is unitary. -/
theorem sourceRadialPitchWinding_norm (σ γ : ℝ) :
    ‖(sourceRadialPitchWinding σ γ : ℂ)‖ = 1 :=
  helixUnitary_norm (σ + γ)

/-- Every finite winding power of the radial-growth-plus-pitch source value is
    unitary. -/
theorem sourceRadialPitchWinding_pow_norm (σ γ : ℝ) (M : ℕ) :
    ‖(sourceRadialPitchWinding σ γ : ℂ) ^ M‖ = 1 :=
  helixUnitary_pow_norm (σ + γ) M

/-- Source-side readout attached to a pole: radial growth plus pitch, valued in
    the unitary helix character. -/
def sourceWindingLossReadout (ρ : ℂ) : Circle :=
  sourceRadialPitchWinding ρ.re ρ.im

/-- A pole's source-side radial-growth-plus-pitch winding readout is unitary. -/
theorem sourceWindingLossReadout_pow_norm (ρ : ℂ) (M : ℕ) :
    ‖(sourceWindingLossReadout ρ : ℂ) ^ M‖ = 1 :=
  sourceRadialPitchWinding_pow_norm ρ.re ρ.im M

/-- Source-side energy is conserved for every zero captured by the winding-loss
    spectrum, unconditionally. -/
theorem windingLossSpectrum_source_energy_conserved
    (χ : DirichletCharacter ℂ N) (M : ℕ) :
    ∀ z ∈ WindingLossSpectrum χ, ‖(sourceWindingLossReadout z : ℂ) ^ M‖ = 1 := by
  intro z _hz
  exact sourceWindingLossReadout_pow_norm z M

/-- χ₃ form: source-side energy is conserved for every captured winding-loss zero. -/
theorem chi3_windingLossSpectrum_source_energy_conserved
    (χ₃ : DirichletCharacter ℂ 3) (M : ℕ) :
    ∀ z ∈ WindingLossSpectrum χ₃, ‖(sourceWindingLossReadout z : ℂ) ^ M‖ = 1 :=
  windingLossSpectrum_source_energy_conserved χ₃ M

/-- Source-side Euler-product coherence for the helix readout.

The Euler product reconstructs logarithmic prime height, multiplication is angular
addition through the `Circle`-valued helix character, and the captured spectral
values are read as values of that correctly parameterized source helix. -/
structure EulerProductHelixSourceReadout (χ : DirichletCharacter ℂ N) where
  prime_weight :
    ∀ {p : ℕ}, p.Prime →
      (∑ d ∈ p.divisors, ArithmeticFunction.vonMangoldt d) = Real.log p
  angular_add :
    ∀ s t : ℝ, helixUnitary (s + t) = helixUnitary s * helixUnitary t
  source_readout :
    ∀ z : ℂ, z ∈ WindingLossSpectrum χ →
      ∃ t : ℝ, SpectralSide.w z = (helixUnitary t : ℂ)

/-- Build the source readout package from the spectral-to-helix readout map; the
    Euler-product prime weights and angular-addition law are already theorems. -/
def eulerProductHelixSourceReadoutOfSourceReadout
    (χ : DirichletCharacter ℂ N)
    (hread : ∀ z : ℂ, z ∈ WindingLossSpectrum χ →
      ∃ t : ℝ, SpectralSide.w z = (helixUnitary t : ℂ)) :
    EulerProductHelixSourceReadout χ where
  prime_weight := fun hp => euler_product_at_prime hp
  angular_add := helixUnitary_add
  source_readout := hread

/-- Source readout into the Euler-product helix gives unit norm for every finite
    winding power on the captured spectrum. -/
theorem eulerProductHelixSourceReadout_w_power_norm_eq_one
    (χ : DirichletCharacter ℂ N) (M : ℕ)
    (S : EulerProductHelixSourceReadout χ) :
    ∀ z ∈ WindingLossSpectrum χ, ‖SpectralSide.w z ^ M‖ = 1 := by
  intro z hz
  rcases S.source_readout z hz with ⟨t, ht⟩
  rw [ht]
  exact helixUnitary_pow_norm t M

/-- The constructed source winding readout is a value of the geometric helix
    unitary, by definition of the source construction. -/
theorem sourceWindingLossReadout_helixUnitary (ρ : ℂ) :
    ∃ t : ℝ, (sourceWindingLossReadout ρ : ℂ) = (helixUnitary t : ℂ) :=
  ⟨ρ.re + ρ.im, rfl⟩

/-- Spectrum form: every constructed source readout on the captured
    winding-loss spectrum is geometric-helix-unitary. -/
theorem windingLossSpectrum_source_helixUnitary_by_construction
    (χ : DirichletCharacter ℂ N) :
    ∀ z : ℂ, z ∈ WindingLossSpectrum χ →
      ∃ t : ℝ, (sourceWindingLossReadout z : ℂ) = (helixUnitary t : ℂ) := by
  intro z _hz
  exact sourceWindingLossReadout_helixUnitary z

/-- χ₃ form of the construction-side source endpoint. -/
theorem chi3_windingLossSpectrum_source_helixUnitary_by_construction
    (χ₃ : DirichletCharacter ℂ 3) :
    ∀ z : ℂ, z ∈ WindingLossSpectrum χ₃ →
      ∃ t : ℝ, (sourceWindingLossReadout z : ℂ) = (helixUnitary t : ℂ) :=
  windingLossSpectrum_source_helixUnitary_by_construction χ₃

/-- Transport the construction-side source readout to the raw Möbius readout
    once the source construction is identified with `SpectralSide.w` on the
    captured spectrum. -/
theorem windingLossSpectrum_raw_w_helixUnitary_of_source_identification
    (χ : DirichletCharacter ℂ N)
    (hidentify : ∀ z : ℂ, z ∈ WindingLossSpectrum χ →
      SpectralSide.w z = (sourceWindingLossReadout z : ℂ)) :
    ∀ z : ℂ, z ∈ WindingLossSpectrum χ →
      ∃ t : ℝ, SpectralSide.w z = (helixUnitary t : ℂ) := by
  intro z hz
  rcases sourceWindingLossReadout_helixUnitary z with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  rw [hidentify z hz, ht]

/-- χ₃ form of the source-to-raw transport endpoint. -/
theorem chi3_windingLossSpectrum_raw_w_helixUnitary_of_source_identification
    (χ₃ : DirichletCharacter ℂ 3)
    (hidentify : ∀ z : ℂ, z ∈ WindingLossSpectrum χ₃ →
      SpectralSide.w z = (sourceWindingLossReadout z : ℂ)) :
    ∀ z : ℂ, z ∈ WindingLossSpectrum χ₃ →
      ∃ t : ℝ, SpectralSide.w z = (helixUnitary t : ℂ) :=
  windingLossSpectrum_raw_w_helixUnitary_of_source_identification χ₃ hidentify

/-- A raw Möbius spectral value is read by the geometric helix unitary exactly
    when it is already on the unit circle. -/
theorem raw_w_helixUnitary_readout_iff_unitary (z : ℂ) :
    (∃ t : ℝ, SpectralSide.w z = (helixUnitary t : ℂ)) ↔
      Complex.normSq (SpectralSide.w z) = 1 := by
  constructor
  · rintro ⟨t, ht⟩
    rw [ht]
    exact Circle.normSq_coe (helixUnitary t)
  · intro hunit
    let wz : Circle := ⟨SpectralSide.w z, by
      change SpectralSide.w z ∈ Metric.sphere (0 : ℂ) 1
      rw [mem_sphere_zero_iff_norm]
      rw [Complex.normSq_eq_norm_sq] at hunit
      nlinarith [norm_nonneg (SpectralSide.w z)]
    ⟩
    rcases helixUnitary_surjective wz with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [ht]

/-- Spectrum form of the raw-readout endpoint. -/
theorem windingLossSpectrum_raw_w_helixUnitary_iff_unitary
    (χ : DirichletCharacter ℂ N) :
    (∀ z : ℂ, z ∈ WindingLossSpectrum χ →
      ∃ t : ℝ, SpectralSide.w z = (helixUnitary t : ℂ)) ↔
    (∀ z : ℂ, z ∈ WindingLossSpectrum χ →
      Complex.normSq (SpectralSide.w z) = 1) := by
  constructor
  · intro hread z hz
    exact (raw_w_helixUnitary_readout_iff_unitary z).mp (hread z hz)
  · intro hunit z hz
    exact (raw_w_helixUnitary_readout_iff_unitary z).mpr (hunit z hz)

/-- χ₃-form of the raw-readout endpoint. -/
theorem chi3_windingLossSpectrum_raw_w_helixUnitary_iff_unitary
    (χ₃ : DirichletCharacter ℂ 3) :
    (∀ z : ℂ, z ∈ WindingLossSpectrum χ₃ →
      ∃ t : ℝ, SpectralSide.w z = (helixUnitary t : ℂ)) ↔
    (∀ z : ℂ, z ∈ WindingLossSpectrum χ₃ →
      Complex.normSq (SpectralSide.w z) = 1) :=
  windingLossSpectrum_raw_w_helixUnitary_iff_unitary χ₃

/-- Build the Euler-product source-readout package from raw unitarity on the
    captured winding-loss spectrum. -/
def eulerProductHelixSourceReadoutOfWindingLossSpectrumUnitary
    (χ : DirichletCharacter ℂ N)
    (hunit : ∀ z : ℂ, z ∈ WindingLossSpectrum χ →
      Complex.normSq (SpectralSide.w z) = 1) :
    EulerProductHelixSourceReadout χ :=
  eulerProductHelixSourceReadoutOfSourceReadout χ
    ((windingLossSpectrum_raw_w_helixUnitary_iff_unitary χ).mpr hunit)

/-- Rebuilding a complex zero from its radial expansion and pitch gives the zero. -/
theorem radialPitchWinding_re_im (ρ : ℂ) :
    radialPitchWinding ρ.re ρ.im = ρ := by
  simp [radialPitchWinding, Complex.re_add_im]

/-- The winding-loss readout is the zero itself, reconstructed from radial expansion
    and pitch. -/
theorem windingLossReadout_eq_zero (ρ : ℂ) :
    windingLossReadout ρ = ρ := by
  exact radialPitchWinding_re_im ρ

/-- Full-loop winding-loss invariance is exactly the half-unit readout. -/
theorem fullLoopWindingLoss_eq_one_iff_half (M : ℝ) (hM : M ≠ 0) (ρ : ℂ) :
    fullLoopWindingLoss M ρ = 1 ↔ ρ.re = 1 / 2 := by
  simpa [fullLoopWindingLoss] using HelixEF.no_radial_drift_iff_half M ρ.re hM

/-- Full-loop winding-loss invariance is exactly raw Möbius unitarity. -/
theorem fullLoopWindingLoss_eq_one_iff_raw_unitary
    (M : ℝ) (hM : M ≠ 0) (ρ : ℂ) (hρ : ρ ≠ 0) :
    fullLoopWindingLoss M ρ = 1 ↔ Complex.normSq (SpectralSide.w ρ) = 1 := by
  rw [fullLoopWindingLoss_eq_one_iff_half M hM ρ, SpectralSide.w_unit_iff_half ρ hρ]

/-- Pythagorean preservation by the first projection is the same as full-loop
    winding-loss invariance for the zero mode. -/
theorem G1_energy_preserved_zero_embed_iff_fullLoopWindingLoss_eq_one
    (M : ℝ) (hM : M ≠ 0) (ρ : ℂ) (x : ℝ) :
    helixEnergy (apply_G1 (zero_embed ρ.re ρ.im x)) =
        helixEnergy (zero_embed ρ.re ρ.im x) ↔
      fullLoopWindingLoss M ρ = 1 := by
  rw [G1_energy_preserved_iff_radial_zero,
    fullLoopWindingLoss_eq_one_iff_half M hM ρ]
  simp [zero_embed]
  constructor <;> intro h <;> linarith

/-- The first projection's Pythagorean energy defect for a zero mode is the
    square of the winding radial excess. -/
theorem G1_energy_defect_zero_embed (ρ : ℂ) (x : ℝ) :
    helixEnergy (zero_embed ρ.re ρ.im x) -
        helixEnergy (apply_G1 (zero_embed ρ.re ρ.im x)) =
      (ρ.re - 1 / 2) ^ 2 := by
  simp [helixEnergy, zero_embed, apply_G1]

/-- FE reflection sends full-loop winding loss to its reciprocal. -/
theorem fullLoopWindingLoss_FE_reciprocal (M : ℝ) (ρ : ℂ) :
    fullLoopWindingLoss M ((1 : ℂ) - ρ) * fullLoopWindingLoss M ρ = 1 := by
  unfold fullLoopWindingLoss
  rw [Complex.sub_re, Complex.one_re]
  have h : M * (1 - ρ.re - 1 / 2) = -(M * (ρ.re - 1 / 2)) := by ring
  rw [h, Real.exp_neg]
  exact inv_mul_cancel₀ (Real.exp_ne_zero _)

/-- The two FE-paired winding losses agree exactly at the half-unit. -/
theorem fullLoopWindingLoss_FE_pair_eq_iff_half (M : ℝ) (hM : M ≠ 0) (ρ : ℂ) :
    fullLoopWindingLoss M ((1 : ℂ) - ρ) = fullLoopWindingLoss M ρ ↔
      ρ.re = 1 / 2 := by
  unfold fullLoopWindingLoss
  rw [Complex.sub_re, Complex.one_re]
  constructor
  · intro h
    have hexp : M * (1 - ρ.re - 1 / 2) = M * (ρ.re - 1 / 2) :=
      Real.exp_injective h
    have hzero : M * (1 - 2 * ρ.re) = 0 := by nlinarith
    rcases mul_eq_zero.mp hzero with hM0 | hcenter
    · exact absurd hM0 hM
    · linarith
  · intro h
    rw [h]
    ring_nf

/-- A completed log-derivative pole's radial/pitch winding value is itself a
    nontrivial zero. -/
theorem radialPitchWinding_mem_nontrivialZeros
    (χ : DirichletCharacter ℂ N) (ρ : ℂ)
    (hρ : CompletedLogDerivPole χ ρ) :
    radialPitchWinding ρ.re ρ.im ∈ GRHSpectral.NontrivialZeros χ := by
  rwa [radialPitchWinding_re_im ρ]

/-- A completed log-derivative pole's winding-loss readout is captured by the
    corresponding nontrivial zero set. -/
theorem windingLossReadout_mem_nontrivialZeros
    (χ : DirichletCharacter ℂ N) (ρ : ℂ)
    (hρ : CompletedLogDerivPole χ ρ) :
    windingLossReadout ρ ∈ GRHSpectral.NontrivialZeros χ := by
  rwa [windingLossReadout_eq_zero ρ]

/-- The completed pole channel's winding-loss spectrum is exactly the nontrivial
    zero set. -/
theorem windingLossSpectrum_eq_nontrivialZeros
    (χ : DirichletCharacter ℂ N) :
    WindingLossSpectrum χ = GRHSpectral.NontrivialZeros χ := by
  ext z
  constructor
  · rintro ⟨ρ, hρ, hz⟩
    rw [hz, windingLossReadout_eq_zero ρ]
    exact hρ
  · intro hz
    exact ⟨z, hz, (windingLossReadout_eq_zero z).symm⟩

/-- The nontrivial zeros are exactly the radial-growth-plus-pitch winding-loss
    values read from the completed pole channel. -/
theorem nontrivialZeros_eq_windingLossSpectrum
    (χ : DirichletCharacter ℂ N) :
    GRHSpectral.NontrivialZeros χ = WindingLossSpectrum χ :=
  (windingLossSpectrum_eq_nontrivialZeros χ).symm

/-- A χ₃ completed pole mode bundles the zero-set membership into the mode. -/
abbrev Chi3PoleMode (χ₃ : DirichletCharacter ℂ 3) :=
  {ρ : ℂ // ρ ∈ GRHSpectral.NontrivialZeros χ₃}

/-- χ₃ form: a pole mode's winding-loss readout is captured by the χ₃ zero set. -/
theorem chi3PoleMode_windingLossReadout_mem_nontrivialZeros
    (χ₃ : DirichletCharacter ℂ 3) (v : Chi3PoleMode χ₃) :
    windingLossReadout v.1 ∈ GRHSpectral.NontrivialZeros χ₃ := by
  rw [windingLossReadout_eq_zero]
  exact v.2

/-- χ₃ form: the winding-loss spectrum read from the log-derivative pole channel
    is exactly the χ₃ zero set. -/
theorem chi3_windingLossSpectrum_eq_nontrivialZeros
    (χ₃ : DirichletCharacter ℂ 3) :
    WindingLossSpectrum χ₃ = GRHSpectral.NontrivialZeros χ₃ :=
  windingLossSpectrum_eq_nontrivialZeros χ₃

/-- χ₃ form: the χ₃ zeros are exactly the radial-growth-plus-pitch winding-loss
    values read from the completed pole channel. -/
theorem chi3_nontrivialZeros_eq_windingLossSpectrum
    (χ₃ : DirichletCharacter ℂ 3) :
    GRHSpectral.NontrivialZeros χ₃ = WindingLossSpectrum χ₃ :=
  nontrivialZeros_eq_windingLossSpectrum χ₃

/-- **Completeness — the Euler‑product helix grammar exhausts the completed pole spectrum.**
Every completed log‑derivative pole (every nontrivial zero of `L(·,χ)`, the poles of `−Λ′/Λ`) is
generated by the grammar: it lies in the winding‑loss spectrum read from the Euler‑product helix.
No pole escapes the grammar. (Dual to soundness: with `windingLossSpectrum_eq_nontrivialZeros` the
two give the exact equality `{completed poles} = grammar spectrum`.) -/
theorem euler_grammar_exhausts_pole_spectrum (χ : DirichletCharacter ℂ N) :
    ∀ ρ : ℂ, CompletedLogDerivPole χ ρ → ρ ∈ WindingLossSpectrum χ := by
  intro ρ hρ
  rw [windingLossSpectrum_eq_nontrivialZeros]
  exact hρ

/-- The completed pole spectrum is **exactly** the Euler‑product grammar's winding‑loss spectrum:
exhaustion (`⊇`) and soundness (`⊆`) together. -/
theorem pole_spectrum_eq_euler_grammar_spectrum (χ : DirichletCharacter ℂ N) :
    {ρ : ℂ | CompletedLogDerivPole χ ρ} = WindingLossSpectrum χ := by
  rw [windingLossSpectrum_eq_nontrivialZeros]; rfl

/-- χ₃ form: the Euler‑product helix grammar exhausts the χ₃ completed pole spectrum. -/
theorem chi3_euler_grammar_exhausts_pole_spectrum (χ₃ : DirichletCharacter ℂ 3) :
    ∀ ρ : ℂ, CompletedLogDerivPole χ₃ ρ → ρ ∈ WindingLossSpectrum χ₃ :=
  euler_grammar_exhausts_pole_spectrum χ₃

/-- The winding determined by a χ₃ pole mode's radial expansion and pitch is
    exactly the pole's complex zero. -/
theorem chi3PoleMode_radialPitchWinding_eq
    (χ₃ : DirichletCharacter ℂ 3) (v : Chi3PoleMode χ₃) :
    radialPitchWinding v.1.re v.1.im = v.1 :=
  radialPitchWinding_re_im v.1

/-- Unconditional χ₃ pole-mode form: once the input is a completed pole mode,
    its radial/pitch winding value is in the χ₃ nontrivial zero set. -/
theorem chi3PoleMode_radialPitchWinding_mem_nontrivialZeros
    (χ₃ : DirichletCharacter ℂ 3) (v : Chi3PoleMode χ₃) :
    radialPitchWinding v.1.re v.1.im ∈ GRHSpectral.NontrivialZeros χ₃ := by
  rw [chi3PoleMode_radialPitchWinding_eq χ₃ v]
  exact v.2

/-- The completed spectral mode attached to a χ₃ pole mode. -/
def chi3PoleModeCompletedSpectralMode
    (χ₃ : DirichletCharacter ℂ 3) (v : Chi3PoleMode χ₃) : Chi3CompletedMode :=
  completedSpectralMode (SpectralSide.w v.1)

/-- Every χ₃ pole mode has an unconditional completed unitary spectral mode. -/
theorem chi3PoleMode_completedSpectralMode_unitary
    (χ₃ : DirichletCharacter ℂ 3) (v : Chi3PoleMode χ₃) :
    Complex.normSq (chi3PoleModeCompletedSpectralMode χ₃ v : ℂ) = 1 :=
  completedSpectralMode_unitary (SpectralSide.w v.1)

/-- The completed χ₃ step preserves the norm of the completed spectral pole mode. -/
theorem chi3PoleMode_completedStep_unitary
    (χ₃ : DirichletCharacter ℂ 3) (v : Chi3PoleMode χ₃) :
    ‖completedStep (chi3PoleModeCompletedSpectralMode χ₃ v)‖ =
      ‖chi3PoleModeCompletedSpectralMode χ₃ v‖ :=
  chi3_completed_helix_step_unitary (chi3PoleModeCompletedSpectralMode χ₃ v)

/-- The completed χ₃ pole mode agrees with the raw Möbius spectral value exactly
    when that raw value was already unit norm. -/
theorem chi3PoleMode_completed_eq_raw_iff_raw_norm_eq_one
    (χ₃ : DirichletCharacter ℂ 3) (v : Chi3PoleMode χ₃) :
    (chi3PoleModeCompletedSpectralMode χ₃ v : ℂ) = SpectralSide.w v.1 ↔
      ‖SpectralSide.w v.1‖ = 1 :=
  completedSpectralMode_eq_raw_iff_norm_eq_one (SpectralSide.w v.1)

/-- A completed log-derivative pole is read in the saved dual-loss channel:
    the zero contributes exactly the radial defect `Re ρ - 1/2`. -/
theorem completed_logDeriv_pole_loss_radial_defect
    (χ : DirichletCharacter ℂ N) (ρ : ℂ)
    (_hρ : CompletedLogDerivPole χ ρ) (x : ℝ) :
    (loss (zero_embed ρ.re ρ.im x)).radial = ρ.re - 1 / 2 :=
  zero_mode_dual_loss_radial ρ x

/-- If the saved radial loss is zero for a χ₃ pole, then the raw Möbius spectral
    value is unitary. -/
theorem chi3_raw_spectral_unitary_of_saved_radial_loss_zero
    (χ₃ : DirichletCharacter ℂ 3) (ρ : ℂ)
    (hρ : CompletedLogDerivPole χ₃ ρ) (x : ℝ)
    (hzero : (loss (zero_embed ρ.re ρ.im x)).radial = 0) :
    Complex.normSq (SpectralSide.w ρ) = 1 :=
  (spectral_circle_iff_dual_loss_radial_zero ρ
    (GRHSpectral.nontrivial_ne_zero hρ) x).mpr hzero

/-- If the source radial coordinate is zero for a χ₃ pole, then the raw Möbius
    spectral value is unitary. -/
theorem chi3_raw_spectral_unitary_of_source_radial_zero
    (χ₃ : DirichletCharacter ℂ 3) (ρ : ℂ)
    (hρ : CompletedLogDerivPole χ₃ ρ) (x : ℝ)
    (hzero : (zero_embed ρ.re ρ.im x).radial = 0) :
    Complex.normSq (SpectralSide.w ρ) = 1 :=
  chi3_raw_spectral_unitary_of_saved_radial_loss_zero χ₃ ρ hρ x (by
    simpa [loss] using hzero)

/-- χ₃ GRH from zero saved radial loss on every log-derivative pole.

    **Costume caveat (CLAUDE.md Rule Two).** The hypothesis
    `(loss (zero_embed ρ.re ρ.im x)).radial = 0` is `rfl`-deep in `σ − ½`: by
    `zero_mode_dual_loss_radial` it unfolds to `ρ.re − ½ = 0`, i.e. `Re ρ = ½`. So the hypothesis
    already *is* "ρ is on the critical line" stated per-zero — discharging it restates the
    conclusion, it does not force it. The genuine, σ-free forcing lives in
    `HelixSource.SourceMode.noDrift` (`HelixSource.lean`), which earns `Re (rate) = 0` from
    loss-norm conservation, independent of σ, and feeds `HelixSource.grh_of_sourceComplete`. -/
theorem GRH_chi3_of_saved_radial_loss_zero
    (χ₃ : DirichletCharacter ℂ 3)
    (hzero : ∀ ρ : ℂ, CompletedLogDerivPole χ₃ ρ → ∀ x : ℝ,
      (loss (zero_embed ρ.re ρ.im x)).radial = 0) :
    GRHSpectral.GRH χ₃ := by
  intro ρ hρ
  have hrad : (loss (zero_embed ρ.re ρ.im 1)).radial = 0 := hzero ρ hρ 1
  rw [zero_mode_dual_loss_radial] at hrad
  linarith

/-- χ₃ GRH from zero source radial coordinate on every log-derivative pole.

    **Costume caveat (CLAUDE.md Rule Two).** The hypothesis `(zero_embed ρ.re ρ.im x).radial = 0`
    is `rfl`-deep in `σ − ½`: `zero_embed` defines `radial := σ − ½` (ConcreteOperators.lean), so
    the hypothesis unfolds to `ρ.re − ½ = 0`, i.e. `Re ρ = ½`. It is the on-line conclusion in
    disguise, not an earned forcing. The earned, σ-free forcing is `HelixSource.SourceMode.noDrift`
    (`Re (rate) = 0` from conservation, independent of σ). -/
theorem GRH_chi3_of_source_radial_zero
    (χ₃ : DirichletCharacter ℂ 3)
    (hzero : ∀ ρ : ℂ, CompletedLogDerivPole χ₃ ρ → ∀ x : ℝ,
      (zero_embed ρ.re ρ.im x).radial = 0) :
    GRHSpectral.GRH χ₃ :=
  GRH_chi3_of_saved_radial_loss_zero χ₃
    (fun ρ hρ x => by simpa [loss] using hzero ρ hρ x)

/-- Pythagorean energy route: if the first projection preserves the helix energy
    of every χ₃ pole mode, then every saved radial loss is zero. -/
theorem chi3_saved_radial_loss_zero_of_G1_energy_preserved
    (χ₃ : DirichletCharacter ℂ 3)
    (henergy : ∀ ρ : ℂ, CompletedLogDerivPole χ₃ ρ → ∀ x : ℝ,
      helixEnergy (apply_G1 (zero_embed ρ.re ρ.im x)) =
        helixEnergy (zero_embed ρ.re ρ.im x)) :
    ∀ ρ : ℂ, CompletedLogDerivPole χ₃ ρ → ∀ x : ℝ,
      (loss (zero_embed ρ.re ρ.im x)).radial = 0 := by
  intro ρ hρ x
  have hrad : (zero_embed ρ.re ρ.im x).radial = 0 :=
    (G1_energy_preserved_iff_radial_zero (zero_embed ρ.re ρ.im x)).mp
      (henergy ρ hρ x)
  simpa [loss] using hrad

/-- χ₃ GRH from Pythagorean energy preservation of the first projection on every pole.

    **Costume caveat (CLAUDE.md Rule Two).** The energy-preservation hypothesis is `rfl`-deep in
    `σ − ½`: the `G₁` energy defect of a zero mode is exactly `(ρ.re − ½)²`
    (`G1_energy_defect_zero_embed`), so "energy preserved" ⟺ `(ρ.re − ½)² = 0` ⟺ `Re ρ = ½`. The
    hypothesis restates the on-line conclusion; it is not an earned forcing. The σ-free forcing
    lives in `HelixSource.SourceMode.noDrift` (`Re (rate) = 0` from conservation, independent of σ). -/
theorem GRH_chi3_of_G1_energy_preserved
    (χ₃ : DirichletCharacter ℂ 3)
    (henergy : ∀ ρ : ℂ, CompletedLogDerivPole χ₃ ρ → ∀ x : ℝ,
      helixEnergy (apply_G1 (zero_embed ρ.re ρ.im x)) =
        helixEnergy (zero_embed ρ.re ρ.im x)) :
    GRHSpectral.GRH χ₃ :=
  GRH_chi3_of_saved_radial_loss_zero χ₃
    (chi3_saved_radial_loss_zero_of_G1_energy_preserved χ₃ henergy)

/-- Geometry-side source data for each completed log-derivative pole: the pole's
    radial exponent is the exponent of a nonzero-energy helix signal whose
    multiplicative dilation action is isometric at every positive scale. -/
structure PoleHelixIsometryData (χ : DirichletCharacter ℂ N) where
  signal : ∀ ρ : ℂ, CompletedLogDerivPole χ ρ → ℝ → ℝ
  positive_energy :
    ∀ ρ (hρ : CompletedLogDerivPole χ ρ),
      0 < ∫ x in Set.Ioi (0 : ℝ), (signal ρ hρ x) ^ 2
  isometry :
    ∀ ρ (hρ : CompletedLogDerivPole χ ρ), ∀ lam : ℝ, 0 < lam →
      (∫ x in Set.Ioi (0 : ℝ), (lam ^ ρ.re * signal ρ hρ (lam * x)) ^ 2)
        = ∫ x in Set.Ioi (0 : ℝ), (signal ρ hρ x) ^ 2

/-- Source-chain no-drift data for the completed log-derivative pole spectrum.
    The source embedding has zero radial coordinate; the imported helix-source
    theorem then proves the retained projections and saved loss do not create
    radial drift. -/
structure PoleHelixNoRadialDriftChain (χ : DirichletCharacter ℂ N) where
  source_no_drift :
    ∀ ρ : ℂ, CompletedLogDerivPole χ ρ → ∀ x : ℝ,
      (zero_embed ρ.re ρ.im x).radial = 0

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
    holds exactly when every such radial loss vanishes — every zero on the helix core.

    **Costume caveat (CLAUDE.md Rule Two).** This is an *equivalence*, and its right-hand side is
    `rfl`-deep in `σ − ½`: by `zero_mode_dual_loss_radial` the radial loss is `ρ.re − ½`, so
    "every radial loss = 0" unfolds to "every `Re ρ = ½`" — literally GRH restated. The bridge
    relabels the conclusion, it does not force it. The earned, σ-free forcing of `Re = ½` is
    `HelixSource.SourceMode.noDrift` (`HelixSource.lean`): conservation ⇒ `Re (rate) = 0`,
    independent of σ. -/
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

/-- If the winding-loss spectrum read from the completed pole channel is unitary,
    then every χ-zero is on the GRH line. -/
theorem GRH_of_windingLossSpectrum_unitary
    (χ : DirichletCharacter ℂ N)
    (hunit : ∀ z ∈ WindingLossSpectrum χ, Complex.normSq (SpectralSide.w z) = 1) :
    GRHSpectral.GRH χ := by
  exact (GRH_iff_helix_reads_zeros_on_circle χ).mpr (by
    intro ρ hρ
    exact hunit ρ (by rwa [windingLossSpectrum_eq_nontrivialZeros χ]))

/-- χ₃ form of the winding-loss spectrum bridge. -/
theorem GRH_chi3_of_windingLossSpectrum_unitary
    (χ₃ : DirichletCharacter ℂ 3)
    (hunit : ∀ z ∈ WindingLossSpectrum χ₃, Complex.normSq (SpectralSide.w z) = 1) :
    GRHSpectral.GRH χ₃ :=
  GRH_of_windingLossSpectrum_unitary χ₃ hunit

/-- A nonzero natural winding power with norm `1` on the captured spectrum
    forces raw Möbius unitarity on that spectrum. -/
theorem windingLossSpectrum_unitary_of_w_power_norm_eq_one
    (χ : DirichletCharacter ℂ N) (M : ℕ) (hM : M ≠ 0)
    (hpow : ∀ z ∈ WindingLossSpectrum χ, ‖SpectralSide.w z ^ M‖ = 1) :
    ∀ z ∈ WindingLossSpectrum χ, Complex.normSq (SpectralSide.w z) = 1 := by
  intro z hz
  exact SpectralSide.w_unit_of_power_norm_eq_one z M hM (hpow z hz)

/-- GRH from unit norm of a nonzero natural winding power on the captured spectrum. -/
theorem GRH_of_windingLossSpectrum_w_power_norm_eq_one
    (χ : DirichletCharacter ℂ N) (M : ℕ) (hM : M ≠ 0)
    (hpow : ∀ z ∈ WindingLossSpectrum χ, ‖SpectralSide.w z ^ M‖ = 1) :
    GRHSpectral.GRH χ :=
  GRH_of_windingLossSpectrum_unitary χ
    (windingLossSpectrum_unitary_of_w_power_norm_eq_one χ M hM hpow)

/-- χ₃ form of the winding-power bridge. -/
theorem GRH_chi3_of_windingLossSpectrum_w_power_norm_eq_one
    (χ₃ : DirichletCharacter ℂ 3) (M : ℕ) (hM : M ≠ 0)
    (hpow : ∀ z ∈ WindingLossSpectrum χ₃, ‖SpectralSide.w z ^ M‖ = 1) :
    GRHSpectral.GRH χ₃ :=
  GRH_of_windingLossSpectrum_w_power_norm_eq_one χ₃ M hM hpow

/-- GRH from Euler-product source readout: once each captured spectral value is
    read as a correctly parameterized source-helix value, source unitarity gives
    the finite winding-power premise and the raw Möbius operator is unitary. -/
theorem GRH_of_eulerProductHelixSourceReadout
    (χ : DirichletCharacter ℂ N) (M : ℕ) (hM : M ≠ 0)
    (S : EulerProductHelixSourceReadout χ) :
    GRHSpectral.GRH χ :=
  GRH_of_windingLossSpectrum_w_power_norm_eq_one χ M hM
    (eulerProductHelixSourceReadout_w_power_norm_eq_one χ M S)

/-- χ₃ form of the Euler-product source-readout bridge. -/
theorem GRH_chi3_of_eulerProductHelixSourceReadout
    (χ₃ : DirichletCharacter ℂ 3) (M : ℕ) (hM : M ≠ 0)
    (S : EulerProductHelixSourceReadout χ₃) :
    GRHSpectral.GRH χ₃ :=
  GRH_of_eulerProductHelixSourceReadout χ₃ M hM S

/-- GRH from the raw Möbius spectral values being read by the geometric helix
    unitary on the captured winding-loss spectrum. -/
theorem GRH_of_windingLossSpectrum_raw_w_helixUnitary
    (χ : DirichletCharacter ℂ N)
    (hread : ∀ z : ℂ, z ∈ WindingLossSpectrum χ →
      ∃ t : ℝ, SpectralSide.w z = (helixUnitary t : ℂ)) :
    GRHSpectral.GRH χ :=
  GRH_of_eulerProductHelixSourceReadout χ 1 (by norm_num)
    (eulerProductHelixSourceReadoutOfSourceReadout χ hread)

/-- χ₃ form of the raw-readout endpoint-to-GRH bridge. -/
theorem GRH_chi3_of_windingLossSpectrum_raw_w_helixUnitary
    (χ₃ : DirichletCharacter ℂ 3)
    (hread : ∀ z : ℂ, z ∈ WindingLossSpectrum χ₃ →
      ∃ t : ℝ, SpectralSide.w z = (helixUnitary t : ℂ)) :
    GRHSpectral.GRH χ₃ :=
  GRH_of_windingLossSpectrum_raw_w_helixUnitary χ₃ hread

/-- Full-loop winding-loss invariance on the captured spectrum is exactly raw
    Möbius unitarity on that same spectrum. -/
theorem windingLossSpectrum_fullLoop_invariant_iff_unitary
    (χ : DirichletCharacter ℂ N) (M : ℝ) (hM : M ≠ 0) :
    (∀ z ∈ WindingLossSpectrum χ, fullLoopWindingLoss M z = 1) ↔
      (∀ z ∈ WindingLossSpectrum χ, Complex.normSq (SpectralSide.w z) = 1) := by
  constructor
  · intro hloop z hz
    have hnz : z ∈ GRHSpectral.NontrivialZeros χ := by
      rwa [windingLossSpectrum_eq_nontrivialZeros χ] at hz
    exact (fullLoopWindingLoss_eq_one_iff_raw_unitary M hM z
      (GRHSpectral.nontrivial_ne_zero hnz)).mp (hloop z hz)
  · intro hunit z hz
    have hnz : z ∈ GRHSpectral.NontrivialZeros χ := by
      rwa [windingLossSpectrum_eq_nontrivialZeros χ] at hz
    exact (fullLoopWindingLoss_eq_one_iff_raw_unitary M hM z
      (GRHSpectral.nontrivial_ne_zero hnz)).mpr (hunit z hz)

/-- Pythagorean preservation by the first projection on the captured spectrum is
    exactly raw Möbius unitarity on that spectrum. -/
theorem windingLossSpectrum_G1_energy_preserved_iff_unitary
    (χ : DirichletCharacter ℂ N) (M : ℝ) (hM : M ≠ 0) :
    (∀ z ∈ WindingLossSpectrum χ, ∀ x : ℝ,
        helixEnergy (apply_G1 (zero_embed z.re z.im x)) =
          helixEnergy (zero_embed z.re z.im x)) ↔
      (∀ z ∈ WindingLossSpectrum χ, Complex.normSq (SpectralSide.w z) = 1) := by
  constructor
  · intro henergy z hz
    have hnz : z ∈ GRHSpectral.NontrivialZeros χ := by
      rwa [windingLossSpectrum_eq_nontrivialZeros χ] at hz
    have hloop : fullLoopWindingLoss M z = 1 :=
      (G1_energy_preserved_zero_embed_iff_fullLoopWindingLoss_eq_one M hM z 1).mp
        (henergy z hz 1)
    exact (fullLoopWindingLoss_eq_one_iff_raw_unitary M hM z
      (GRHSpectral.nontrivial_ne_zero hnz)).mp hloop
  · intro hunit z hz x
    have hnz : z ∈ GRHSpectral.NontrivialZeros χ := by
      rwa [windingLossSpectrum_eq_nontrivialZeros χ] at hz
    have hloop : fullLoopWindingLoss M z = 1 :=
      (fullLoopWindingLoss_eq_one_iff_raw_unitary M hM z
        (GRHSpectral.nontrivial_ne_zero hnz)).mpr (hunit z hz)
    exact (G1_energy_preserved_zero_embed_iff_fullLoopWindingLoss_eq_one M hM z x).mpr
      hloop

/-- GRH from full-loop winding-loss invariance on the captured spectrum. -/
theorem GRH_of_fullLoopWindingLoss_invariant
    (χ : DirichletCharacter ℂ N) (M : ℝ) (hM : M ≠ 0)
    (hloop : ∀ z ∈ WindingLossSpectrum χ, fullLoopWindingLoss M z = 1) :
    GRHSpectral.GRH χ :=
  GRH_of_windingLossSpectrum_unitary χ
    ((windingLossSpectrum_fullLoop_invariant_iff_unitary χ M hM).mp hloop)

/-- χ₃ form: GRH from full-loop winding-loss invariance at the configured
    `M = 6` loop. -/
theorem GRH_chi3_of_fullLoopWindingLoss_invariant
    (χ₃ : DirichletCharacter ℂ 3)
    (hloop : ∀ z ∈ WindingLossSpectrum χ₃, fullLoopWindingLoss 6 z = 1) :
    GRHSpectral.GRH χ₃ :=
  GRH_of_fullLoopWindingLoss_invariant χ₃ 6 (by norm_num) hloop

/-- GRH from Pythagorean preservation by the first projection on the captured
    winding-loss spectrum. -/
theorem GRH_of_G1_energy_preserved_on_windingLossSpectrum
    (χ : DirichletCharacter ℂ N) (M : ℝ) (hM : M ≠ 0)
    (henergy : ∀ z ∈ WindingLossSpectrum χ, ∀ x : ℝ,
      helixEnergy (apply_G1 (zero_embed z.re z.im x)) =
        helixEnergy (zero_embed z.re z.im x)) :
    GRHSpectral.GRH χ :=
  GRH_of_windingLossSpectrum_unitary χ
    ((windingLossSpectrum_G1_energy_preserved_iff_unitary χ M hM).mp henergy)

/-- χ₃ form: GRH from Pythagorean preservation at the configured `M = 6` loop. -/
theorem GRH_chi3_of_G1_energy_preserved_on_windingLossSpectrum
    (χ₃ : DirichletCharacter ℂ 3)
    (henergy : ∀ z ∈ WindingLossSpectrum χ₃, ∀ x : ℝ,
      helixEnergy (apply_G1 (zero_embed z.re z.im x)) =
        helixEnergy (zero_embed z.re z.im x)) :
    GRHSpectral.GRH χ₃ :=
  GRH_of_G1_energy_preserved_on_windingLossSpectrum χ₃ 6 (by norm_num) henergy

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

/-- Per-pole helix isometry data is a source for zero radial drift on the completed
    log-derivative pole spectrum. -/
theorem zero_drift_on_logderiv_poles_of_pole_helix_isometry
    (χ : DirichletCharacter ℂ N)
    (D : PoleHelixIsometryData χ) :
    ∀ ρ : ℂ, CompletedLogDerivPole χ ρ → ∀ x : ℝ,
      (loss (zero_embed ρ.re ρ.im x)).radial = 0 := by
  intro ρ hρ x
  have hhalf : ρ.re = 1 / 2 :=
    (HelixHalfUnit.helix_forces_half ρ.re (D.signal ρ hρ)
      (D.positive_energy ρ hρ)).mp (D.isometry ρ hρ)
  rw [zero_mode_dual_loss_radial]
  linarith

/-- If the source pole readout has zero radial drift, the whole concrete helix
    projection/loss chain has zero drift in every retained and saved radial slot. -/
theorem pole_helix_chain_no_radial_drift_audit
    (χ : DirichletCharacter ℂ N)
    (D : PoleHelixNoRadialDriftChain χ) :
    ∀ ρ : ℂ, CompletedLogDerivPole χ ρ → ∀ x : ℝ,
      let v := zero_embed ρ.re ρ.im x
      v.radial = 0 ∧
      (apply_G1 v).radial = 0 ∧
      (apply_G2 (apply_G1 v)).radial = 0 ∧
      (apply_cascade v).radial = 0 ∧
      (loss v).radial = 0 := by
  intro ρ hρ x
  dsimp
  have hsrc : (zero_embed ρ.re ρ.im x).radial = 0 := D.source_no_drift ρ hρ x
  exact ⟨hsrc,
    (source_no_radial_drift_propagates_through_helix
      (zero_embed ρ.re ρ.im x) hsrc).1,
    (source_no_radial_drift_propagates_through_helix
      (zero_embed ρ.re ρ.im x) hsrc).2.1,
    (source_no_radial_drift_propagates_through_helix
      (zero_embed ρ.re ρ.im x) hsrc).2.2.1,
    (source_no_radial_drift_propagates_through_helix
      (zero_embed ρ.re ρ.im x) hsrc).2.2.2⟩

/-- The retained concrete helix projection chain has zero radial coordinate by
    construction. This does not use pole unitarity, a completed operator, or a
    geometric readout hypothesis. -/
theorem retained_pole_helix_chain_no_radial_drift_by_construction
    (χ : DirichletCharacter ℂ N) :
    ∀ ρ : ℂ, CompletedLogDerivPole χ ρ → ∀ x : ℝ,
      let v := zero_embed ρ.re ρ.im x
      (apply_G1 v).radial = 0 ∧
      (apply_G2 (apply_G1 v)).radial = 0 ∧
      (apply_cascade v).radial = 0 := by
  intro ρ hρ x
  exact dimensional_projections_create_no_radial_drift (zero_embed ρ.re ρ.im x)

/-- The no-drift source chain supplies the saved-loss zero-radial readout used by
    the completed pole-spectrum operator. -/
theorem zero_drift_on_logderiv_poles_of_no_radial_drift_chain
    (χ : DirichletCharacter ℂ N)
    (D : PoleHelixNoRadialDriftChain χ) :
    ∀ ρ : ℂ, CompletedLogDerivPole χ ρ → ∀ x : ℝ,
      (loss (zero_embed ρ.re ρ.im x)).radial = 0 := by
  intro ρ hρ x
  exact (pole_helix_chain_no_radial_drift_audit χ D ρ hρ x).2.2.2.2

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

/-- Construct the completed pole-spectrum operator directly from per-pole helix
    isometry data. This is the non-`hunitary` source constructor. -/
def completedHelixOperatorOnPoleSpectrumOfIsometryData
    (χ : DirichletCharacter ℂ N)
    (D : PoleHelixIsometryData χ) :
    CompletedHelixOperatorOnPoleSpectrum χ where
  readPole := fun ρ hρ x =>
    ⟨zero_embed ρ.re ρ.im x,
      zero_drift_on_logderiv_poles_of_pole_helix_isometry χ D ρ hρ x⟩
  reads_pole := by
    intro ρ hρ x
    rfl

/-- χ₃ completed pole-spectrum operator built directly from per-pole helix
    isometry data. -/
def chi3CompletedHelixOperatorOnPoleSpectrumOfIsometryData
    (χ₃ : DirichletCharacter ℂ 3)
    (D : PoleHelixIsometryData χ₃) :
    CompletedHelixOperatorOnPoleSpectrum χ₃ :=
  completedHelixOperatorOnPoleSpectrumOfIsometryData χ₃ D

/-- Construct the completed pole-spectrum operator directly from the no-drift
    source chain. -/
def completedHelixOperatorOnPoleSpectrumOfNoRadialDriftChain
    (χ : DirichletCharacter ℂ N)
    (D : PoleHelixNoRadialDriftChain χ) :
    CompletedHelixOperatorOnPoleSpectrum χ where
  readPole := fun ρ hρ x =>
    ⟨zero_embed ρ.re ρ.im x,
      zero_drift_on_logderiv_poles_of_no_radial_drift_chain χ D ρ hρ x⟩
  reads_pole := by
    intro ρ hρ x
    rfl

/-- χ₃ completed pole-spectrum operator built directly from the no-drift source chain. -/
def chi3CompletedHelixOperatorOnPoleSpectrumOfNoRadialDriftChain
    (χ₃ : DirichletCharacter ℂ 3)
    (D : PoleHelixNoRadialDriftChain χ₃) :
    CompletedHelixOperatorOnPoleSpectrum χ₃ :=
  completedHelixOperatorOnPoleSpectrumOfNoRadialDriftChain χ₃ D

/-- Geometric bridge from log-derivative poles to the helix unitary character:
    every pole's Möbius spectral value is a value of the already-constructed
    geometric helix unitary. -/
def GeometricHelixUnitaryReadoutOnLogDerivPoles
    (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ ρ : ℂ, CompletedLogDerivPole χ ρ →
    ∃ t : ℝ, SpectralSide.w ρ = (helixUnitary t : ℂ)

/-- Winding-rate version of the geometric readout: every pole's explicit-formula
    winding rate is a value of the already-constructed helix unitary. -/
def Chi3WindingRateReadoutOnLogDerivPoles
    (χ₃ : DirichletCharacter ℂ 3) : Prop :=
  ∀ ρ : ℂ, CompletedLogDerivPole χ₃ ρ →
    ∃ t : ℝ, HelixEF.windRate ρ = (helixUnitary t : ℂ)

/-- The Möbius spectral value and the explicit-formula winding rate are the
    same value away from the zero denominator. -/
theorem spectral_w_eq_windRate (ρ : ℂ) (hρ : ρ ≠ 0) :
    SpectralSide.w ρ = HelixEF.windRate ρ := by
  unfold SpectralSide.w HelixEF.windRate
  field_simp [hρ]

/-- A χ₃ winding-rate readout supplies the geometric Möbius readout directly. -/
theorem geometric_readout_on_logderiv_poles_of_windRate_readout
    (χ₃ : DirichletCharacter ℂ 3)
    (hread : Chi3WindingRateReadoutOnLogDerivPoles χ₃) :
    GeometricHelixUnitaryReadoutOnLogDerivPoles χ₃ := by
  intro ρ hρ
  rcases hread ρ hρ with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  rw [spectral_w_eq_windRate ρ (GRHSpectral.nontrivial_ne_zero hρ), ht]

/-- The explicit-formula winding readout gives unitary Möbius values on χ₃
    log-derivative poles. -/
theorem chi3_pole_modes_unitary_of_windRate_readout
    (χ₃ : DirichletCharacter ℂ 3)
    (hread : Chi3WindingRateReadoutOnLogDerivPoles χ₃)
    (ρ : ℂ)
    (hρ : ρ ∈ GRHSpectral.NontrivialZeros χ₃) :
    Complex.normSq (SpectralSide.w ρ) = 1 := by
  rcases hread ρ hρ with ⟨t, ht⟩
  have hhalf : ρ.re = 1 / 2 :=
    HelixEF.windRate_reads_unit_imp_half ρ
      (GRHSpectral.nontrivial_ne_zero hρ)
      (helixUnitary_norm t) ht
  exact (SpectralSide.w_unit_iff_half ρ
    (GRHSpectral.nontrivial_ne_zero hρ)).mpr hhalf

/-- If the explicit-formula winding readout is geometric-unitary on χ₃ poles,
    then the entire χ₃ winding-loss spectrum is unitary. -/
theorem chi3_windingLossSpectrum_unitary_of_windRate_readout
    (χ₃ : DirichletCharacter ℂ 3)
    (hread : Chi3WindingRateReadoutOnLogDerivPoles χ₃) :
    ∀ z ∈ WindingLossSpectrum χ₃, Complex.normSq (SpectralSide.w z) = 1 := by
  intro z hz
  rw [chi3_windingLossSpectrum_eq_nontrivialZeros χ₃] at hz
  exact chi3_pole_modes_unitary_of_windRate_readout χ₃ hread z hz

/-- χ₃ GRH from the geometric-unitary wind-rate readout on the captured
    winding-loss spectrum. -/
theorem GRH_chi3_of_windRate_readout_on_windingLossSpectrum
    (χ₃ : DirichletCharacter ℂ 3)
    (hread : Chi3WindingRateReadoutOnLogDerivPoles χ₃) :
    GRHSpectral.GRH χ₃ :=
  GRH_chi3_of_windingLossSpectrum_unitary χ₃
    (chi3_windingLossSpectrum_unitary_of_windRate_readout χ₃ hread)

/-- Completed pole-spectrum operator with the geometric unitary readout included
    in the operator data. -/
structure GeometricCompletedHelixOperatorOnPoleSpectrum
    (χ : DirichletCharacter ℂ N)
    extends CompletedHelixOperatorOnPoleSpectrum χ where
  geometric_readout : GeometricHelixUnitaryReadoutOnLogDerivPoles χ

/-- The geometric helix-unitary readout gives unitary Möbius values on all
    completed log-derivative poles. -/
theorem geometric_helix_unitary_on_logderiv_poles
    (χ : DirichletCharacter ℂ N)
    (hgeom : GeometricHelixUnitaryReadoutOnLogDerivPoles χ) :
    ∀ ρ : ℂ, CompletedLogDerivPole χ ρ →
      Complex.normSq (SpectralSide.w ρ) = 1 := by
  intro ρ hρ
  rcases hgeom ρ hρ with ⟨t, ht⟩
  rw [ht]
  exact Circle.normSq_coe (helixUnitary t)

/-- χ₃ form of the geometric bridge from poles to unitary Möbius values. -/
theorem geometric_chi3_helix_unitary_on_logderiv_poles
    (χ₃ : DirichletCharacter ℂ 3)
    (hgeom : GeometricHelixUnitaryReadoutOnLogDerivPoles χ₃) :
    ∀ ρ : ℂ, CompletedLogDerivPole χ₃ ρ →
      Complex.normSq (SpectralSide.w ρ) = 1 :=
  geometric_helix_unitary_on_logderiv_poles χ₃ hgeom

/-- Per-pole helix isometry data gives unitary Möbius values on the completed
    log-derivative pole spectrum. -/
theorem unitary_on_logderiv_poles_of_pole_helix_isometry
    (χ : DirichletCharacter ℂ N)
    (D : PoleHelixIsometryData χ) :
    ∀ ρ : ℂ, CompletedLogDerivPole χ ρ →
      Complex.normSq (SpectralSide.w ρ) = 1 := by
  intro ρ hρ
  exact (completed_helix_operator_unitary_iff_zero_drift_on_pole_spectrum χ).mpr
    (fun ρ hρ x => zero_drift_on_logderiv_poles_of_pole_helix_isometry χ D ρ hρ x)
    ρ hρ

/-- Per-pole helix isometry data gives the geometric helix-unitary readout without
    passing through a pre-existing completed operator. -/
theorem geometric_readout_on_logderiv_poles_of_pole_helix_isometry
    (χ : DirichletCharacter ℂ N)
    (D : PoleHelixIsometryData χ) :
    GeometricHelixUnitaryReadoutOnLogDerivPoles χ := by
  intro ρ hρ
  have hunit : Complex.normSq (SpectralSide.w ρ) = 1 :=
    unitary_on_logderiv_poles_of_pole_helix_isometry χ D ρ hρ
  let z : Circle := ⟨SpectralSide.w ρ, by
    change SpectralSide.w ρ ∈ Metric.sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm]
    rw [Complex.normSq_eq_norm_sq] at hunit
    nlinarith [norm_nonneg (SpectralSide.w ρ)]
  ⟩
  rcases helixUnitary_surjective z with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  rw [ht]

/-- The no-drift source chain gives unitary Möbius values on the completed
    log-derivative pole spectrum. -/
theorem unitary_on_logderiv_poles_of_no_radial_drift_chain
    (χ : DirichletCharacter ℂ N)
    (D : PoleHelixNoRadialDriftChain χ) :
    ∀ ρ : ℂ, CompletedLogDerivPole χ ρ →
      Complex.normSq (SpectralSide.w ρ) = 1 := by
  intro ρ hρ
  exact (completed_helix_operator_unitary_iff_zero_drift_on_pole_spectrum χ).mpr
    (fun ρ hρ x => zero_drift_on_logderiv_poles_of_no_radial_drift_chain χ D ρ hρ x)
    ρ hρ

/-- The no-drift source chain gives the geometric helix-unitary readout. -/
theorem geometric_readout_on_logderiv_poles_of_no_radial_drift_chain
    (χ : DirichletCharacter ℂ N)
    (D : PoleHelixNoRadialDriftChain χ) :
    GeometricHelixUnitaryReadoutOnLogDerivPoles χ := by
  intro ρ hρ
  have hunit : Complex.normSq (SpectralSide.w ρ) = 1 :=
    unitary_on_logderiv_poles_of_no_radial_drift_chain χ D ρ hρ
  let z : Circle := ⟨SpectralSide.w ρ, by
    change SpectralSide.w ρ ∈ Metric.sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm]
    rw [Complex.normSq_eq_norm_sq] at hunit
    nlinarith [norm_nonneg (SpectralSide.w ρ)]
  ⟩
  rcases helixUnitary_surjective z with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  rw [ht]

/-- Upgrade the isometry-built completed operator with its derived geometric
    helix-unitary readout. -/
def geometricCompletedHelixOperatorOnPoleSpectrumOfIsometryData
    (χ : DirichletCharacter ℂ N)
    (D : PoleHelixIsometryData χ) :
    GeometricCompletedHelixOperatorOnPoleSpectrum χ where
  toCompletedHelixOperatorOnPoleSpectrum :=
    completedHelixOperatorOnPoleSpectrumOfIsometryData χ D
  geometric_readout := geometric_readout_on_logderiv_poles_of_pole_helix_isometry χ D

/-- Upgrade the no-drift-chain-built completed operator with its derived geometric
    helix-unitary readout. -/
def geometricCompletedHelixOperatorOnPoleSpectrumOfNoRadialDriftChain
    (χ : DirichletCharacter ℂ N)
    (D : PoleHelixNoRadialDriftChain χ) :
    GeometricCompletedHelixOperatorOnPoleSpectrum χ where
  toCompletedHelixOperatorOnPoleSpectrum :=
    completedHelixOperatorOnPoleSpectrumOfNoRadialDriftChain χ D
  geometric_readout := geometric_readout_on_logderiv_poles_of_no_radial_drift_chain χ D

/-- Construct the completed pole-spectrum operator from the geometric helix-unitary readout. -/
def completedHelixOperatorOnPoleSpectrumOfGeometricReadout
    (χ : DirichletCharacter ℂ N)
    (hgeom : GeometricHelixUnitaryReadoutOnLogDerivPoles χ) :
    CompletedHelixOperatorOnPoleSpectrum χ :=
  completedHelixOperatorOnPoleSpectrumOfUnitary χ
    (geometric_helix_unitary_on_logderiv_poles χ hgeom)

/-- χ₃ completed pole-spectrum operator constructed from the geometric readout bridge. -/
def chi3CompletedHelixOperatorOnPoleSpectrumOfGeometricReadout
    (χ₃ : DirichletCharacter ℂ 3)
    (hgeom : GeometricHelixUnitaryReadoutOnLogDerivPoles χ₃) :
    CompletedHelixOperatorOnPoleSpectrum χ₃ :=
  completedHelixOperatorOnPoleSpectrumOfGeometricReadout χ₃ hgeom

/-- A geometric completed pole operator is unitary on every log-derivative pole. -/
theorem geometric_completed_helix_operator_is_unitary_on_logderiv_poles
    (χ : DirichletCharacter ℂ N)
    (T : GeometricCompletedHelixOperatorOnPoleSpectrum χ) :
    ∀ ρ : ℂ, CompletedLogDerivPole χ ρ →
      Complex.normSq (SpectralSide.w ρ) = 1 :=
  geometric_helix_unitary_on_logderiv_poles χ T.geometric_readout

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

/-- χ₃ GRH from the geometric helix-unitary bridge, with `T` constructed internally. -/
theorem GRH_chi3_of_geometric_helix_unitary_on_logderiv_poles
    (χ₃ : DirichletCharacter ℂ 3)
    (hgeom : GeometricHelixUnitaryReadoutOnLogDerivPoles χ₃) :
    GRHSpectral.GRH χ₃ :=
  GRH_chi3_of_unitary_on_logderiv_poles χ₃
    (geometric_chi3_helix_unitary_on_logderiv_poles χ₃ hgeom)

/-- χ₃ GRH from the geometric completed helix operator. -/
theorem GRH_chi3_of_geometric_completed_helix_operator
    (χ₃ : DirichletCharacter ℂ 3)
    (T : GeometricCompletedHelixOperatorOnPoleSpectrum χ₃) :
    GRHSpectral.GRH χ₃ :=
  GRH_chi3_of_unitary_on_logderiv_poles χ₃
    (geometric_completed_helix_operator_is_unitary_on_logderiv_poles χ₃ T)

/-- χ₃ GRH from the per-pole helix isometry source data. -/
theorem GRH_chi3_of_pole_helix_isometry
    (χ₃ : DirichletCharacter ℂ 3)
    (D : PoleHelixIsometryData χ₃) :
    GRHSpectral.GRH χ₃ :=
  GRH_chi3_of_geometric_completed_helix_operator χ₃
    (geometricCompletedHelixOperatorOnPoleSpectrumOfIsometryData χ₃ D)

/-- χ₃ GRH from the concrete no-drift helix source chain. -/
theorem GRH_chi3_of_no_radial_drift_chain
    (χ₃ : DirichletCharacter ℂ 3)
    (D : PoleHelixNoRadialDriftChain χ₃) :
    GRHSpectral.GRH χ₃ :=
  GRH_chi3_of_geometric_completed_helix_operator χ₃
    (geometricCompletedHelixOperatorOnPoleSpectrumOfNoRadialDriftChain χ₃ D)

/-- Pythagorean preservation by `G₁` builds the source no-drift chain used by the
    completed pole-spectrum construction. -/
def poleHelixNoRadialDriftChainOfG1EnergyPreserved
    (χ : DirichletCharacter ℂ N)
    (henergy : ∀ ρ : ℂ, CompletedLogDerivPole χ ρ → ∀ x : ℝ,
      helixEnergy (apply_G1 (zero_embed ρ.re ρ.im x)) =
        helixEnergy (zero_embed ρ.re ρ.im x)) :
    PoleHelixNoRadialDriftChain χ where
  source_no_drift := by
    intro ρ hρ x
    exact (G1_energy_preserved_iff_radial_zero (zero_embed ρ.re ρ.im x)).mp
      (henergy ρ hρ x)

/-- Construction-data endpoint on the captured winding-loss spectrum:
    the raw Möbius readout is a value of the helix unitary. -/
theorem windingLossSpectrum_raw_w_helixUnitary_of_no_radial_drift_chain
    (χ : DirichletCharacter ℂ N)
    (D : PoleHelixNoRadialDriftChain χ) :
    ∀ z : ℂ, z ∈ WindingLossSpectrum χ →
      ∃ t : ℝ, SpectralSide.w z = (helixUnitary t : ℂ) := by
  intro z hz
  have hpole : CompletedLogDerivPole χ z := by
    rwa [windingLossSpectrum_eq_nontrivialZeros χ] at hz
  exact geometric_readout_on_logderiv_poles_of_no_radial_drift_chain χ D z hpole

/-- χ₃ construction-data endpoint on the captured winding-loss spectrum. -/
theorem chi3_windingLossSpectrum_raw_w_helixUnitary_of_no_radial_drift_chain
    (χ₃ : DirichletCharacter ℂ 3)
    (D : PoleHelixNoRadialDriftChain χ₃) :
    ∀ z : ℂ, z ∈ WindingLossSpectrum χ₃ →
      ∃ t : ℝ, SpectralSide.w z = (helixUnitary t : ℂ) :=
  windingLossSpectrum_raw_w_helixUnitary_of_no_radial_drift_chain χ₃ D

/-- Pythagorean endpoint on the captured winding-loss spectrum:
    `G₁` energy preservation gives the raw Möbius readout as a helix-unitary value. -/
theorem windingLossSpectrum_raw_w_helixUnitary_of_G1_energy_preserved
    (χ : DirichletCharacter ℂ N)
    (henergy : ∀ ρ : ℂ, CompletedLogDerivPole χ ρ → ∀ x : ℝ,
      helixEnergy (apply_G1 (zero_embed ρ.re ρ.im x)) =
        helixEnergy (zero_embed ρ.re ρ.im x)) :
    ∀ z : ℂ, z ∈ WindingLossSpectrum χ →
      ∃ t : ℝ, SpectralSide.w z = (helixUnitary t : ℂ) :=
  windingLossSpectrum_raw_w_helixUnitary_of_no_radial_drift_chain χ
    (poleHelixNoRadialDriftChainOfG1EnergyPreserved χ henergy)

/-- χ₃ Pythagorean endpoint on the captured winding-loss spectrum. -/
theorem chi3_windingLossSpectrum_raw_w_helixUnitary_of_G1_energy_preserved
    (χ₃ : DirichletCharacter ℂ 3)
    (henergy : ∀ ρ : ℂ, CompletedLogDerivPole χ₃ ρ → ∀ x : ℝ,
      helixEnergy (apply_G1 (zero_embed ρ.re ρ.im x)) =
        helixEnergy (zero_embed ρ.re ρ.im x)) :
    ∀ z : ℂ, z ∈ WindingLossSpectrum χ₃ →
      ∃ t : ℝ, SpectralSide.w z = (helixUnitary t : ℂ) :=
  windingLossSpectrum_raw_w_helixUnitary_of_G1_energy_preserved χ₃ henergy

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
#print axioms HelixReadsGRH.sourceRadialPitchWinding_eq_mul
#print axioms HelixReadsGRH.sourceRadialPitchWinding_coe_eq_mul
#print axioms HelixReadsGRH.sourceRadialPitchWinding_norm
#print axioms HelixReadsGRH.sourceRadialPitchWinding_pow_norm
#print axioms HelixReadsGRH.sourceWindingLossReadout_pow_norm
#print axioms HelixReadsGRH.windingLossSpectrum_source_energy_conserved
#print axioms HelixReadsGRH.chi3_windingLossSpectrum_source_energy_conserved
#print axioms HelixReadsGRH.radialPitchWinding_re_im
#print axioms HelixReadsGRH.windingLossReadout_eq_zero
#print axioms HelixReadsGRH.fullLoopWindingLoss_eq_one_iff_half
#print axioms HelixReadsGRH.fullLoopWindingLoss_eq_one_iff_raw_unitary
#print axioms HelixReadsGRH.G1_energy_preserved_zero_embed_iff_fullLoopWindingLoss_eq_one
#print axioms HelixReadsGRH.G1_energy_defect_zero_embed
#print axioms HelixReadsGRH.fullLoopWindingLoss_FE_reciprocal
#print axioms HelixReadsGRH.fullLoopWindingLoss_FE_pair_eq_iff_half
#print axioms HelixReadsGRH.radialPitchWinding_mem_nontrivialZeros
#print axioms HelixReadsGRH.windingLossReadout_mem_nontrivialZeros
#print axioms HelixReadsGRH.windingLossSpectrum_eq_nontrivialZeros
#print axioms HelixReadsGRH.nontrivialZeros_eq_windingLossSpectrum
#print axioms HelixReadsGRH.eulerProductHelixSourceReadoutOfSourceReadout
#print axioms HelixReadsGRH.eulerProductHelixSourceReadout_w_power_norm_eq_one
#print axioms HelixReadsGRH.sourceWindingLossReadout_helixUnitary
#print axioms HelixReadsGRH.windingLossSpectrum_source_helixUnitary_by_construction
#print axioms HelixReadsGRH.chi3_windingLossSpectrum_source_helixUnitary_by_construction
#print axioms HelixReadsGRH.windingLossSpectrum_raw_w_helixUnitary_of_source_identification
#print axioms HelixReadsGRH.chi3_windingLossSpectrum_raw_w_helixUnitary_of_source_identification
#print axioms HelixReadsGRH.raw_w_helixUnitary_readout_iff_unitary
#print axioms HelixReadsGRH.windingLossSpectrum_raw_w_helixUnitary_iff_unitary
#print axioms HelixReadsGRH.chi3_windingLossSpectrum_raw_w_helixUnitary_iff_unitary
#print axioms HelixReadsGRH.eulerProductHelixSourceReadoutOfWindingLossSpectrumUnitary
#print axioms HelixReadsGRH.chi3PoleMode_windingLossReadout_mem_nontrivialZeros
#print axioms HelixReadsGRH.chi3_windingLossSpectrum_eq_nontrivialZeros
#print axioms HelixReadsGRH.chi3_nontrivialZeros_eq_windingLossSpectrum
#print axioms HelixReadsGRH.chi3PoleMode_radialPitchWinding_eq
#print axioms HelixReadsGRH.chi3PoleMode_radialPitchWinding_mem_nontrivialZeros
#print axioms HelixReadsGRH.chi3PoleMode_completedSpectralMode_unitary
#print axioms HelixReadsGRH.chi3PoleMode_completedStep_unitary
#print axioms HelixReadsGRH.chi3PoleMode_completed_eq_raw_iff_raw_norm_eq_one
#print axioms HelixReadsGRH.completed_logDeriv_pole_loss_radial_defect
#print axioms HelixReadsGRH.chi3_raw_spectral_unitary_of_saved_radial_loss_zero
#print axioms HelixReadsGRH.chi3_raw_spectral_unitary_of_source_radial_zero
#print axioms HelixReadsGRH.GRH_chi3_of_saved_radial_loss_zero
#print axioms HelixReadsGRH.GRH_chi3_of_source_radial_zero
#print axioms HelixReadsGRH.chi3_saved_radial_loss_zero_of_G1_energy_preserved
#print axioms HelixReadsGRH.GRH_chi3_of_G1_energy_preserved
#print axioms HelixReadsGRH.GRH_of_windingLossSpectrum_unitary
#print axioms HelixReadsGRH.GRH_chi3_of_windingLossSpectrum_unitary
#print axioms HelixReadsGRH.windingLossSpectrum_unitary_of_w_power_norm_eq_one
#print axioms HelixReadsGRH.GRH_of_windingLossSpectrum_w_power_norm_eq_one
#print axioms HelixReadsGRH.GRH_chi3_of_windingLossSpectrum_w_power_norm_eq_one
#print axioms HelixReadsGRH.GRH_of_eulerProductHelixSourceReadout
#print axioms HelixReadsGRH.GRH_chi3_of_eulerProductHelixSourceReadout
#print axioms HelixReadsGRH.GRH_of_windingLossSpectrum_raw_w_helixUnitary
#print axioms HelixReadsGRH.GRH_chi3_of_windingLossSpectrum_raw_w_helixUnitary
#print axioms HelixReadsGRH.windingLossSpectrum_fullLoop_invariant_iff_unitary
#print axioms HelixReadsGRH.windingLossSpectrum_G1_energy_preserved_iff_unitary
#print axioms HelixReadsGRH.GRH_of_fullLoopWindingLoss_invariant
#print axioms HelixReadsGRH.GRH_chi3_of_fullLoopWindingLoss_invariant
#print axioms HelixReadsGRH.GRH_of_G1_energy_preserved_on_windingLossSpectrum
#print axioms HelixReadsGRH.GRH_chi3_of_G1_energy_preserved_on_windingLossSpectrum
#print axioms HelixReadsGRH.completed_helix_operator_zero_drift
#print axioms HelixReadsGRH.GRH_of_completed_helix_operator_unitary_on_pole_spectrum
#print axioms HelixReadsGRH.GRH_of_completed_helix_operator_zero_drift_on_pole_spectrum
#print axioms HelixReadsGRH.GRH_of_completed_helix_operator_on_pole_spectrum
#print axioms HelixReadsGRH.completed_helix_operator_unitary_iff_zero_drift_on_pole_spectrum
#print axioms HelixReadsGRH.zero_drift_on_logderiv_poles_of_pole_helix_isometry
#print axioms HelixReadsGRH.pole_helix_chain_no_radial_drift_audit
#print axioms HelixReadsGRH.retained_pole_helix_chain_no_radial_drift_by_construction
#print axioms HelixReadsGRH.zero_drift_on_logderiv_poles_of_no_radial_drift_chain
#print axioms HelixReadsGRH.completedHelixOperatorOnPoleSpectrumOfUnitary
#print axioms HelixReadsGRH.chi3CompletedHelixOperatorOnPoleSpectrumOfUnitary
#print axioms HelixReadsGRH.completedHelixOperatorOnPoleSpectrumOfIsometryData
#print axioms HelixReadsGRH.chi3CompletedHelixOperatorOnPoleSpectrumOfIsometryData
#print axioms HelixReadsGRH.completedHelixOperatorOnPoleSpectrumOfNoRadialDriftChain
#print axioms HelixReadsGRH.chi3CompletedHelixOperatorOnPoleSpectrumOfNoRadialDriftChain
#print axioms HelixReadsGRH.geometric_helix_unitary_on_logderiv_poles
#print axioms HelixReadsGRH.geometric_chi3_helix_unitary_on_logderiv_poles
#print axioms HelixReadsGRH.spectral_w_eq_windRate
#print axioms HelixReadsGRH.geometric_readout_on_logderiv_poles_of_windRate_readout
#print axioms HelixReadsGRH.chi3_pole_modes_unitary_of_windRate_readout
#print axioms HelixReadsGRH.chi3_windingLossSpectrum_unitary_of_windRate_readout
#print axioms HelixReadsGRH.GRH_chi3_of_windRate_readout_on_windingLossSpectrum
#print axioms HelixReadsGRH.unitary_on_logderiv_poles_of_pole_helix_isometry
#print axioms HelixReadsGRH.geometric_readout_on_logderiv_poles_of_pole_helix_isometry
#print axioms HelixReadsGRH.unitary_on_logderiv_poles_of_no_radial_drift_chain
#print axioms HelixReadsGRH.geometric_readout_on_logderiv_poles_of_no_radial_drift_chain
#print axioms HelixReadsGRH.geometricCompletedHelixOperatorOnPoleSpectrumOfIsometryData
#print axioms HelixReadsGRH.geometricCompletedHelixOperatorOnPoleSpectrumOfNoRadialDriftChain
#print axioms HelixReadsGRH.completedHelixOperatorOnPoleSpectrumOfGeometricReadout
#print axioms HelixReadsGRH.chi3CompletedHelixOperatorOnPoleSpectrumOfGeometricReadout
#print axioms HelixReadsGRH.geometric_completed_helix_operator_is_unitary_on_logderiv_poles
#print axioms HelixReadsGRH.completed_helix_operator_is_unitary_on_logderiv_poles
#print axioms HelixReadsGRH.completed_chi3_helix_is_unitary_on_logderiv_poles
#print axioms HelixReadsGRH.GRH_chi3_of_completed_helix_operator
#print axioms HelixReadsGRH.GRH_chi3_of_unitary_on_logderiv_poles
#print axioms HelixReadsGRH.GRH_chi3_of_geometric_helix_unitary_on_logderiv_poles
#print axioms HelixReadsGRH.GRH_chi3_of_geometric_completed_helix_operator
#print axioms HelixReadsGRH.GRH_chi3_of_pole_helix_isometry
#print axioms HelixReadsGRH.GRH_chi3_of_no_radial_drift_chain
#print axioms HelixReadsGRH.poleHelixNoRadialDriftChainOfG1EnergyPreserved
#print axioms HelixReadsGRH.windingLossSpectrum_raw_w_helixUnitary_of_no_radial_drift_chain
#print axioms HelixReadsGRH.chi3_windingLossSpectrum_raw_w_helixUnitary_of_no_radial_drift_chain
#print axioms HelixReadsGRH.windingLossSpectrum_raw_w_helixUnitary_of_G1_energy_preserved
#print axioms HelixReadsGRH.chi3_windingLossSpectrum_raw_w_helixUnitary_of_G1_energy_preserved
#print axioms HelixReadsGRH.GRH_trivial_character_of_completed_helix_operator
#print axioms HelixReadsGRH.GRH_trivial_mod3_of_completed_helix_operator
