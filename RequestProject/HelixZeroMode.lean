import Mathlib
import RequestProject.Chi3CompletedLogDeriv

/-!
# Helix zero-mode normalization

The `codex6` extraction scripts normalize both the principal `ζ` channel and
the nonprincipal `χ₃` channel by `sqrt x`, with `x = exp u`. This file records
the kernel proof of the invariant behind that normalization:

* a zero-mode has helix form `exp(ρ u)`;
* dividing by `sqrt(exp u) = exp(u/2)` leaves envelope
  `exp((Re ρ - 1/2)u)`;
* unit envelope at every helix scale is equivalent to `Re ρ = 1/2`.

The statement is channel-independent. The ζ and χ₃ channels differ in their
prime weights and frequencies; the half-unit normalization is the same helix
geometry in both.
-/

noncomputable section

open Complex ArithmeticFunction
open scoped BigOperators

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-- Principal von Mangoldt weight for the ζ channel. -/
def zetaHelixWeight (n : ℕ) : ℂ := (vonMangoldt n : ℂ)

/-- Twisted von Mangoldt weight for the `χ₃` channel. -/
def chi3HelixWeight (n : ℕ) : ℂ := (vonMangoldt n : ℂ) * chi3 n

/-- A helix zero-mode in logarithmic scale `u = log x`. -/
def helixZeroMode (ρ : ℂ) (u : ℝ) : ℂ :=
  Complex.exp (ρ * (u : ℂ))

/-- The common `sqrt x` scale, written in logarithmic coordinate `u = log x`. -/
def sqrtScale (u : ℝ) : ℂ :=
  (Real.exp (u / 2) : ℂ)

/-- The zero-mode after the empirical `sqrt x` normalization. -/
def sqrtNormalizedZeroMode (ρ : ℂ) (u : ℝ) : ℂ :=
  helixZeroMode ρ u / sqrtScale u

/-- The normalized envelope is exactly `exp((Re ρ - 1/2)u)`. -/
theorem sqrtNormalizedZeroMode_norm (ρ : ℂ) (u : ℝ) :
    ‖sqrtNormalizedZeroMode ρ u‖ = Real.exp ((ρ.re - 1 / 2) * u) := by
  unfold sqrtNormalizedZeroMode helixZeroMode sqrtScale
  rw [norm_div, Complex.norm_exp]
  have hden : ‖(Real.exp (u / 2) : ℂ)‖ = Real.exp (u / 2) := by
    exact Complex.norm_of_nonneg (Real.exp_pos _).le
  rw [hden, div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_add]
  congr 1
  simp [Complex.mul_re]
  ring

/-- The `sqrt x` normalization has unit envelope at every helix scale exactly
    at the half-unit. -/
theorem sqrtNormalizedZeroMode_unit_all_scales_iff (ρ : ℂ) :
    (∀ u : ℝ, ‖sqrtNormalizedZeroMode ρ u‖ = 1) ↔ ρ.re = 1 / 2 := by
  constructor
  · intro h
    have h1 := h 1
    rw [sqrtNormalizedZeroMode_norm] at h1
    have hzero : (ρ.re - 1 / 2) * 1 = 0 := by
      have h0 : Real.exp ((ρ.re - 1 / 2) * 1) = Real.exp 0 := by
        simpa using h1
      exact Real.exp_injective h0
    linarith
  · intro h u
    rw [sqrtNormalizedZeroMode_norm, h]
    norm_num

/-- The principal ζ channel uses the same half-unit envelope. -/
theorem zeta_zero_mode_unit_all_scales_iff (ρ : ℂ) :
    (∀ u : ℝ, ‖sqrtNormalizedZeroMode ρ u‖ = 1) ↔ ρ.re = 1 / 2 :=
  sqrtNormalizedZeroMode_unit_all_scales_iff ρ

/-- The `χ₃` channel uses the same half-unit envelope. -/
theorem chi3_zero_mode_unit_all_scales_iff (ρ : ℂ) :
    (∀ u : ℝ, ‖sqrtNormalizedZeroMode ρ u‖ = 1) ↔ ρ.re = 1 / 2 :=
  sqrtNormalizedZeroMode_unit_all_scales_iff ρ

/-- Multiplying a zero-mode by a nonzero channel coefficient does not change
    the fitted radial rate; it only multiplies the envelope by a constant. -/
theorem weighted_sqrtNormalizedZeroMode_norm
    (a ρ : ℂ) (ha : a ≠ 0) (u : ℝ) :
    ‖a * sqrtNormalizedZeroMode ρ u‖ / ‖a‖ =
      Real.exp ((ρ.re - 1 / 2) * u) := by
  rw [norm_mul, sqrtNormalizedZeroMode_norm]
  exact mul_div_cancel_left₀ _ (norm_ne_zero_iff.mpr ha)

/-- The ζ prime weight does not change the normalized radial rate. -/
theorem zeta_weighted_sqrtNormalizedZeroMode_norm
    (n : ℕ) (ρ : ℂ) (hn : zetaHelixWeight n ≠ 0) (u : ℝ) :
    ‖zetaHelixWeight n * sqrtNormalizedZeroMode ρ u‖ / ‖zetaHelixWeight n‖ =
      Real.exp ((ρ.re - 1 / 2) * u) :=
  weighted_sqrtNormalizedZeroMode_norm (zetaHelixWeight n) ρ hn u

/-- The `χ₃` prime weight does not change the normalized radial rate. -/
theorem chi3_weighted_sqrtNormalizedZeroMode_norm
    (n : ℕ) (ρ : ℂ) (hn : chi3HelixWeight n ≠ 0) (u : ℝ) :
    ‖chi3HelixWeight n * sqrtNormalizedZeroMode ρ u‖ / ‖chi3HelixWeight n‖ =
      Real.exp ((ρ.re - 1 / 2) * u) :=
  weighted_sqrtNormalizedZeroMode_norm (chi3HelixWeight n) ρ hn u

/-- The `χ₃` completed-log-derivative grammar is the helix-weight Dirichlet
    series plus its archimedean correction. -/
theorem chi3_completed_logderiv_grammar_weighted (s : ℂ) (hs : 1 < s.re) :
    negCompletedLogDerivChi3 s =
      (∑' n : ℕ, chi3HelixWeight n * (n : ℂ) ^ (-s))
        - (1 / 2) * Complex.log (3 / Real.pi)
        - (1 / 2) * digamma ((s + 1) / 2) := by
  have h := chi3_completed_logderiv_grammar_Re_gt_one s hs
  simpa [chi3HelixWeight] using h

/-- A single helix mode with nonzero channel coefficient. The two intrinsic
    mode coordinates are radial rate `ρ.re` and angular frequency `ρ.im`. -/
structure HelixMode where
  coeff : ℂ
  rho : ℂ
  coeff_ne_zero : coeff ≠ 0

/-- The radial rate fitted from the helix mode. -/
def HelixMode.radialRate (m : HelixMode) : ℝ := m.rho.re

/-- The angular frequency fitted from the helix mode. -/
def HelixMode.frequency (m : HelixMode) : ℝ := m.rho.im

/-- Unit normalized envelope for a fitted mode. -/
def HelixMode.UnitEnvelope (m : HelixMode) : Prop :=
  ∀ u : ℝ, ‖m.coeff * sqrtNormalizedZeroMode m.rho u‖ / ‖m.coeff‖ = 1

/-- The empirical fitted radial rate is definitionally `Re ρ`. -/
theorem HelixMode.radialRate_eq_re (m : HelixMode) :
    m.radialRate = m.rho.re :=
  rfl

/-- The empirical fitted frequency is definitionally `Im ρ`. -/
theorem HelixMode.frequency_eq_im (m : HelixMode) :
    m.frequency = m.rho.im :=
  rfl

/-- A fitted mode has unit normalized envelope at all helix scales exactly
    when its radial rate is the half-unit. -/
theorem HelixMode.unitEnvelope_iff_radialRate_half (m : HelixMode) :
    m.UnitEnvelope ↔ m.radialRate = 1 / 2 := by
  constructor
  · intro h
    have h1 := h 1
    have hnorm := weighted_sqrtNormalizedZeroMode_norm m.coeff m.rho m.coeff_ne_zero 1
    rw [hnorm] at h1
    have hzero : (m.rho.re - 1 / 2) * 1 = 0 := by
      have h0 : Real.exp ((m.rho.re - 1 / 2) * 1) = Real.exp 0 := by
        simpa using h1
      exact Real.exp_injective h0
    unfold HelixMode.radialRate
    linarith
  · intro h u
    have hnorm := weighted_sqrtNormalizedZeroMode_norm m.coeff m.rho m.coeff_ne_zero u
    rw [hnorm]
    unfold HelixMode.radialRate at h
    rw [h]
    norm_num

/-- A fitted ζ-channel mode with unit normalized envelope has radial rate `1/2`. -/
theorem zeta_mode_unitEnvelope_forces_half (m : HelixMode) (hm : m.UnitEnvelope) :
    m.radialRate = 1 / 2 :=
  (m.unitEnvelope_iff_radialRate_half).mp hm

/-- A fitted `χ₃`-channel mode with unit normalized envelope has radial rate `1/2`. -/
theorem chi3_mode_unitEnvelope_forces_half (m : HelixMode) (hm : m.UnitEnvelope) :
    m.radialRate = 1 / 2 :=
  (m.unitEnvelope_iff_radialRate_half).mp hm

/-- A `χ₃` grammar mode with unit normalized envelope has the helix half-unit
    radial rate. -/
theorem chi3_grammar_modes_have_half_unit
    (m : HelixMode) (hm : m.UnitEnvelope) :
    m.radialRate = 1 / 2 :=
  chi3_mode_unitEnvelope_forces_half m hm

end
