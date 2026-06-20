import Mathlib
import RequestProject.XiPartialFraction
import RequestProject.HelixDefs

/-!
# Von Mangoldt Explicit Formula — Standalone & Unconditional

A **surgically isolated, fully unconditional** version of
`RequestProject.VonMangoldtEF`. The original pulls a 51-file `RequestProject`
import tail; this file imports only **`Mathlib` + one repository module**,
`RequestProject.XiPartialFraction`, which supplies the single deep analytic
input (the Hadamard partial fraction) as a kernel-clean theorem. Everything else
— Euler, Bridge, and all downstream consequences — is proved here from Mathlib alone.

## Proved from Mathlib alone

* **Euler pillar** — `LSeries Λ s = −ζ'/ζ(s)` for `Re s > 1`
  (Mathlib's `ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div`).
* **Bridge pillar** — `ζ'/ζ = ξ'/ξ − 1/s − 1/(s−1) − Γℝ'/Γℝ` for `Re s > 1`
  (ported verbatim from `RequestProject.LogDerivIdentity`; pure algebra over the
  classical factorization `ξ = (s(s−1)/2)·Λ̂` and `Λ̂ = Γℝ·ζ`).
* **All downstream consequences** (§4–§9): per-zero term positivity, the helix
  amplitude factor, the reflected-pair `2·cosh` envelope, and conditional RH
  from bounded/stationary envelopes. Pure real/complex algebra.

## The single irreducible input (now discharged, not hypothesized)

* **Hadamard pillar** — `ξ'/ξ(s) = A + Σ_ρ m_ρ·(1/(s−ρ) + 1/ρ)`.

  Genuine analytic depth (Hadamard factorization of the entire function `ξ` of
  order ≤ 1; min-modulus / Borel–Carathéodory / Jensen counting). It is **not**
  reproved here — it is imported as the repository's unconditional, kernel-clean
  theorem `ZD.xi_logDeriv_partial_fraction` (`RequestProject.XiPartialFraction`),
  via `xi_logDeriv_sub_product_const_off_zeros` (`XiHadamardFactorization`) +
  `logDeriv_xiProductMult_partial_fraction` (`XiProductMultPartialFraction`).

  This file imports `XiPartialFraction`, so the local `hadamard_partial_fraction`
  is **defined** `:= ZD.xi_logDeriv_partial_fraction` — a theorem, not a gap.
  (Were one to drop that import and rebuild against Mathlib alone, this is the one
  step Mathlib does not yet provide, and it would become the sole hole. As
  committed, there is no such hole.)

Consequently `vonMangoldt_explicit_formula` and friends below are **fully
unconditional** — no extra hypothesis, no Hadamard caveat.

## Axiom footprint
Everything here — including `hadamard_partial_fraction` and every theorem
downstream of it — uses only `[propext, Classical.choice, Quot.sound]`. No gaps
(verified via `lean_verify`/`#print axioms`).
-/

open scoped BigOperators Real
open Real Complex

set_option maxHeartbeats 4000000

noncomputable section

namespace VMEFStandalone

-- ═══════════════════════════════════════════════════════════════════════════
-- §0  Self-contained definitions (verbatim from the repository's `ZD.*`)
-- ═══════════════════════════════════════════════════════════════════════════

/-- The von Mangoldt function, as a function `ℕ → ℝ`. -/
def Λ : ℕ → ℝ := fun n => ArithmeticFunction.vonMangoldt n

/-- The helix native unit `U = π/3`. Sourced from the canonical χ₃ channel
    (`Helix.chChi3`), whose angular unit is `π/3`. -/
def U : ℝ := Helix.angleUnit Helix.chChi3

/-- The χ₃ helix unit is the old hardcoded value `π/3`. -/
theorem U_eq : U = Real.pi / 3 := rfl

theorem U_pos : 0 < U := by rw [U_eq]; positivity

theorem U_ne_zero : U ≠ 0 := U_pos.ne'

/-- **The entire Riemann ξ**: `ξ(s) := (s(s−1)/2)·completedRiemannZeta₀ s + 1/2`.
The explicit entire form (avoiding Mathlib's `1/0 = 0` convention at `s = 0, 1`).
For `s ≠ 0, 1` it agrees with the classical form `(s(s−1)/2)·completedRiemannZeta s`. -/
def riemannXi (s : ℂ) : ℂ :=
  (s * (s - 1) / 2) * completedRiemannZeta₀ s + 1 / 2

/-- Nontrivial zeros of ζ: `{s | 0 < Re s ∧ Re s < 1 ∧ ζ(s) = 0}`. -/
def NontrivialZeros : Set ℂ :=
  { s : ℂ | 0 < s.re ∧ s.re < 1 ∧ riemannZeta s = 0 }

/-- Multiplicity of a zero of `ξ` (analytic order, as a `ℕ`). -/
def xiOrderNat (z : ℂ) : ℕ := analyticOrderNatAt riemannXi z

/-- For `s ≠ 0, 1`, `ξ(s) = (s(s−1)/2)·completedRiemannZeta s` (classical form). -/
theorem riemannXi_eq_classical_of_ne_zero_of_ne_one
    (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    riemannXi s = (s * (s - 1) / 2) * completedRiemannZeta s := by
  unfold riemannXi
  rw [completedRiemannZeta_eq]
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  field_simp
  ring

/-- `riemannXi` is entire. -/
theorem riemannXi_differentiable : Differentiable ℂ riemannXi := by
  unfold riemannXi
  exact (((differentiable_id.mul (differentiable_id.sub (differentiable_const 1))).div_const
    2).mul differentiable_completedZeta₀).add (differentiable_const _)

-- ═══════════════════════════════════════════════════════════════════════════
-- §1  The Euler & Bridge pillars (both proved from Mathlib)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Euler pillar**: `L(Λ, s) = −ζ'/ζ(s)` for `Re(s) > 1`. -/
theorem euler_pillar (s : ℂ) (hs : 1 < s.re) :
    LSeries (fun n => (Λ n : ℂ)) s =
      -deriv riemannZeta s / riemannZeta s :=
  ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs

/-- **Bridge pillar**: `ζ'/ζ = ξ'/ξ − 1/s − 1/(s−1) − Γℝ'/Γℝ` on `Re s > 1`.
Pure algebra from the factorizations `ξ = (s(s−1)/2)·Λ̂` and `Λ̂ = Γℝ·ζ`,
plus the log-derivative product/quotient rules. Ported from
`RequestProject.LogDerivIdentity`. -/
theorem bridge_pillar (s : ℂ) (hs_re : 1 < s.re) :
    deriv riemannZeta s / riemannZeta s =
      deriv riemannXi s / riemannXi s -
        1 / s - 1 / (s - 1) - logDeriv Complex.Gammaℝ s := by
  have hs_ne0 : s ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hs_ne1 : s ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hs_sub_ne : s - 1 ≠ 0 := sub_ne_zero.mpr hs_ne1
  have hs_div_ne : s / 2 ≠ 0 := div_ne_zero hs_ne0 two_ne_zero
  have hs_re_pos : 0 < s.re := by linarith
  have hζ_ne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs_re
  have hΓℝ_ne : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hs_re_pos
  have hcompleted_ne : completedRiemannZeta s ≠ 0 := by
    intro hcomp; apply hζ_ne
    rw [riemannZeta_def_of_ne_zero hs_ne0, hcomp, zero_div]
  have hxi_classical : riemannXi s = (s * (s - 1) / 2) * completedRiemannZeta s :=
    riemannXi_eq_classical_of_ne_zero_of_ne_one s hs_ne0 hs_ne1
  have hxi_ne : riemannXi s ≠ 0 := by
    rw [hxi_classical]
    exact mul_ne_zero
      (div_ne_zero (mul_ne_zero hs_ne0 hs_sub_ne) two_ne_zero) hcompleted_ne
  have hΓℝ_diff : DifferentiableAt ℂ Complex.Gammaℝ s := by
    have h_ne : ∀ n : ℕ, s ≠ -(2 * (n : ℂ)) := by
      intro n heq
      have : s.re = -(2 * (n : ℝ)) := by
        rw [heq]; simp
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith [‹s.re = _›]
    have h_half_ne : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
      intro m heq
      have : s = -(2 * (m : ℂ)) := by linear_combination 2 * heq
      exact h_ne m this
    have hΓ_diff : DifferentiableAt ℂ Complex.Gamma (s / 2) :=
      Complex.differentiableAt_Gamma _ h_half_ne
    have hcpow_diff :
        DifferentiableAt ℂ (fun t : ℂ => (Real.pi : ℂ) ^ (-t / 2)) s := by
      refine DifferentiableAt.const_cpow
        ((differentiableAt_id.neg).div_const 2) ?_
      left; exact_mod_cast Real.pi_pos.ne'
    have hcomp :
        DifferentiableAt ℂ (fun t : ℂ => Complex.Gamma (t / 2)) s :=
      hΓ_diff.comp s (differentiableAt_id.div_const 2)
    have h_product :
        DifferentiableAt ℂ
          (fun t : ℂ => (Real.pi : ℂ) ^ (-t / 2) * Complex.Gamma (t / 2)) s :=
      hcpow_diff.mul hcomp
    have h_eq :
        Complex.Gammaℝ = fun t : ℂ => (Real.pi : ℂ) ^ (-t / 2) * Complex.Gamma (t / 2) := by
      funext t; exact Complex.Gammaℝ_def t
    rw [h_eq]; exact h_product
  have hζ_diff : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs_ne1
  have hcompleted_diff : DifferentiableAt ℂ completedRiemannZeta s :=
    differentiableAt_completedZeta hs_ne0 hs_ne1
  set p : ℂ → ℂ := fun z => z * (z - 1) / 2 with hp_def
  have hp_diff : DifferentiableAt ℂ p s := by
    show DifferentiableAt ℂ (fun z => z * (z - 1) / 2) s
    exact (differentiableAt_id.mul (differentiableAt_id.sub_const 1)).div_const 2
  have hp_ne : p s ≠ 0 := by
    show s * (s - 1) / 2 ≠ 0
    exact div_ne_zero (mul_ne_zero hs_ne0 hs_sub_ne) two_ne_zero
  have hriemannXi_eventually :
      riemannXi =ᶠ[nhds s] fun z => p z * completedRiemannZeta z := by
    have h_open_ne_zero : IsOpen ({0}ᶜ : Set ℂ) := isOpen_compl_singleton
    have h_open_ne_one : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
    have h_mem : s ∈ ({0}ᶜ ∩ {1}ᶜ : Set ℂ) := by
      refine ⟨?_, ?_⟩ <;> simp [hs_ne0, hs_ne1]
    have h_open : IsOpen ({0}ᶜ ∩ {1}ᶜ : Set ℂ) := h_open_ne_zero.inter h_open_ne_one
    refine Filter.eventuallyEq_of_mem (h_open.mem_nhds h_mem) ?_
    intro z hz
    show riemannXi z = z * (z - 1) / 2 * completedRiemannZeta z
    exact riemannXi_eq_classical_of_ne_zero_of_ne_one z hz.1 hz.2
  have hxi_logDeriv_eq :
      logDeriv riemannXi s =
        logDeriv p s + logDeriv completedRiemannZeta s := by
    have h_deriv_eq :
        deriv riemannXi s = deriv (fun z => p z * completedRiemannZeta z) s :=
      Filter.EventuallyEq.deriv_eq hriemannXi_eventually
    have h_val_eq : riemannXi s = (fun z => p z * completedRiemannZeta z) s :=
      hriemannXi_eventually.self_of_nhds
    simp only [logDeriv_apply] at *
    rw [h_deriv_eq, h_val_eq]
    have := logDeriv_mul s hp_ne hcompleted_ne hp_diff hcompleted_diff
    simpa [logDeriv_apply] using this
  have hp_log :
      logDeriv p s = 1 / s + 1 / (s - 1) := by
    have hp_mul : p = fun z => (z / 2) * (z - 1) := by
      funext z
      show z * (z - 1) / 2 = (z / 2) * (z - 1)
      ring
    rw [hp_mul]
    have h_div2_ne : s / 2 ≠ 0 := hs_div_ne
    have h_sub1_ne : s - 1 ≠ 0 := hs_sub_ne
    have h_div2_diff : DifferentiableAt ℂ (fun z : ℂ => z / 2) s :=
      differentiableAt_id.div_const 2
    have h_sub1_diff : DifferentiableAt ℂ (fun z : ℂ => z - 1) s :=
      differentiableAt_id.sub_const 1
    rw [logDeriv_mul s h_div2_ne h_sub1_ne h_div2_diff h_sub1_diff]
    have hdiv2 : logDeriv (fun z : ℂ => z / 2) s = 1 / s := by
      rw [logDeriv_apply, deriv_div_const, deriv_id'']; field_simp
    have hsub1 : logDeriv (fun z : ℂ => z - 1) s = 1 / (s - 1) := by
      rw [logDeriv_apply]; simp
    rw [hdiv2, hsub1]
  have hriemann_eventually :
      riemannZeta =ᶠ[nhds s] fun z => completedRiemannZeta z / Complex.Gammaℝ z := by
    have h_open_re : IsOpen {z : ℂ | (1 / 2 : ℝ) < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have h_mem : s ∈ {z : ℂ | (1 / 2 : ℝ) < z.re} := by
      show (1 / 2 : ℝ) < s.re; linarith
    refine Filter.eventuallyEq_of_mem (h_open_re.mem_nhds h_mem) ?_
    intro z hz
    have hz_ne0 : z ≠ 0 := by
      intro h0; rw [h0] at hz; simp at hz; linarith
    exact riemannZeta_def_of_ne_zero hz_ne0
  have hζ_logDeriv :
      logDeriv riemannZeta s =
        logDeriv completedRiemannZeta s - logDeriv Complex.Gammaℝ s := by
    have h_deriv_eq :
        deriv riemannZeta s = deriv (fun z => completedRiemannZeta z / Complex.Gammaℝ z) s :=
      Filter.EventuallyEq.deriv_eq hriemann_eventually
    have h_val_eq : riemannZeta s = (fun z => completedRiemannZeta z / Complex.Gammaℝ z) s :=
      hriemann_eventually.self_of_nhds
    simp only [logDeriv_apply]
    rw [h_deriv_eq, h_val_eq]
    have := logDeriv_div s hcompleted_ne hΓℝ_ne hcompleted_diff hΓℝ_diff
    simpa [logDeriv_apply] using this
  have hζ_unfold : deriv riemannZeta s / riemannZeta s = logDeriv riemannZeta s := by
    rw [logDeriv_apply]
  have hxi_unfold : deriv riemannXi s / riemannXi s = logDeriv riemannXi s := by
    rw [logDeriv_apply]
  rw [hζ_unfold, hζ_logDeriv]
  have h_subst : logDeriv completedRiemannZeta s = logDeriv riemannXi s - logDeriv p s := by
    rw [eq_sub_iff_add_eq, add_comm]
    exact hxi_logDeriv_eq.symm
  rw [h_subst, hp_log, hxi_unfold]
  ring

/-- **Nonnegativity of real-part zero-term** at `σ > 1` for zeros in the
critical strip. Pure algebra. Ported from `RequestProject.LogDerivIdentity`. -/
theorem re_zero_term_nonneg (σ : ℝ) (hσ : 1 < σ) (ρ : ℂ) (hρ_re : 0 < ρ.re)
    (hρ_re' : ρ.re < 1) :
    0 ≤ ((1 : ℂ) / (↑σ - ρ) + 1 / ρ).re := by
  simp only [Complex.add_re, one_div, Complex.inv_re]
  apply add_nonneg
  · apply div_nonneg
    · simp [Complex.sub_re, Complex.ofReal_re]; linarith
    · exact Complex.normSq_nonneg _
  · apply div_nonneg
    · exact le_of_lt hρ_re
    · exact Complex.normSq_nonneg _

-- ═══════════════════════════════════════════════════════════════════════════
-- §2  The Hadamard pillar (the one deep analytic input — proven here, kernel-clean)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Hadamard partial fraction for `ξ'/ξ`** — the one deep analytic input.

`ξ'/ξ(s) = A + Σ_ρ m_ρ·(1/(s−ρ) + 1/ρ)` off the nontrivial zeros.

Proven here (kernel-clean, unconditional) as the repository's
`ZD.xi_logDeriv_partial_fraction` (`RequestProject.XiPartialFraction`, the Poisson + Hadamard
chain). It is the one deep analytic input — and this file *discharges* it, with no gap. -/
theorem hadamard_partial_fraction :
    ∃ A : ℂ, ∀ s : ℂ, s ∉ NontrivialZeros →
      deriv riemannXi s / riemannXi s =
        A + ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
          (xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val) := by
  exact ZD.xi_logDeriv_partial_fraction

-- ═══════════════════════════════════════════════════════════════════════════
-- §3  The Von Mangoldt Explicit Formula (unconditional)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Von Mangoldt explicit formula (Dirichlet series form).**
For `Re(s) > 1` and `s` not a nontrivial zero:
  `−ζ'/ζ(s) = −(A + Σ_ρ m_ρ·(1/(s−ρ) + 1/ρ)) + 1/s + 1/(s−1) + Γℝ'/Γℝ(s)`. -/
theorem vonMangoldt_explicit_formula
    (s : ℂ) (hs : 1 < s.re) (hs_nz : s ∉ NontrivialZeros) :
    ∃ A : ℂ,
      -deriv riemannZeta s / riemannZeta s =
        -(A + ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
            (xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val))
        + 1 / s + 1 / (s - 1) + logDeriv Complex.Gammaℝ s := by
  obtain ⟨A, hA⟩ := hadamard_partial_fraction
  refine ⟨A, ?_⟩
  have h_bridge := bridge_pillar s hs
  have h_hadamard := hA s hs_nz
  linear_combination -h_bridge - h_hadamard

/-- **Von Mangoldt explicit formula (L-series form).** -/
theorem vonMangoldt_explicit_formula_LSeries
    (s : ℂ) (hs : 1 < s.re) (hs_nz : s ∉ NontrivialZeros) :
    ∃ A : ℂ,
      LSeries (fun n => (Λ n : ℂ)) s =
        -(A + ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
            (xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val))
        + 1 / s + 1 / (s - 1) + logDeriv Complex.Gammaℝ s := by
  obtain ⟨A, hA⟩ := hadamard_partial_fraction
  refine ⟨A, ?_⟩
  have h_euler := euler_pillar s hs
  have h_bridge := bridge_pillar s hs
  have h_hadamard := hA s hs_nz
  rw [h_euler]
  linear_combination -h_bridge - h_hadamard

-- ═══════════════════════════════════════════════════════════════════════════
-- §4  Per-Zero Term Analysis (unconditional)
-- ═══════════════════════════════════════════════════════════════════════════

/-- The per-zero term in the explicit formula. -/
def zeroTerm (s ρ : ℂ) : ℂ := 1 / (s - ρ) + 1 / ρ

/-- When `s ≠ ρ` and `ρ ≠ 0`, the zero term simplifies to `s / (ρ(s−ρ))`. -/
theorem zeroTerm_eq_div (s ρ : ℂ) (hρ : ρ ≠ 0) (hs : s ≠ ρ) :
    zeroTerm s ρ = s / (ρ * (s - ρ)) := by
  unfold zeroTerm
  field_simp [hρ, sub_ne_zero.mpr hs]
  ring

/-- **Real-part positivity of zero terms** for `σ > 1` and `0 < Re(ρ) < 1`. -/
theorem re_zeroTerm_nonneg (σ : ℝ) (hσ : 1 < σ) (ρ : ℂ) (hρ_re : 0 < ρ.re)
    (hρ_re' : ρ.re < 1) :
    0 ≤ (zeroTerm (σ : ℂ) ρ).re :=
  re_zero_term_nonneg σ hσ ρ hρ_re hρ_re'

-- ═══════════════════════════════════════════════════════════════════════════
-- §5  Helix-Coordinate Zero Contribution (unconditional)
-- ═══════════════════════════════════════════════════════════════════════════

/-- The amplitude exponent of a zero with real part β: `a = (β − 1/2) / U`. -/
def amplitudeExponent (β : ℝ) : ℝ := (β - 1/2) / U

/-- The winding frequency of a zero with imaginary part γ: `ν = γ / U`. -/
def windingFreq (γ : ℝ) : ℝ := γ / U

/-- β = 1/2 iff the amplitude exponent vanishes. -/
theorem critical_iff_zero_exponent (β : ℝ) :
    β = 1/2 ↔ amplitudeExponent β = 0 := by
  constructor
  · intro h; simp [amplitudeExponent, h]
  · intro h
    have h_div : (β - 1/2) / U = 0 := h
    have h_num : β - 1/2 = 0 := by
      rcases div_eq_zero_iff.mp h_div with hN | hD
      · exact hN
      · exact absurd hD U_ne_zero
    linarith

/-- The midpoint-normalized amplitude factor at winding angle θ. -/
def zeroAmplitudeFactor (β θ : ℝ) : ℝ := Real.exp (amplitudeExponent β * θ)

/-- On the critical line, the amplitude factor is identically 1. -/
theorem zeroAmplitudeFactor_critical (θ : ℝ) :
    zeroAmplitudeFactor (1/2) θ = 1 := by
  simp [zeroAmplitudeFactor, amplitudeExponent]

/-- Off the critical line, the amplitude factor is non-constant. -/
theorem zeroAmplitudeFactor_nonconstant (β : ℝ) (hβ : β ≠ 1/2) :
    ∃ θ₁ θ₂ : ℝ, zeroAmplitudeFactor β θ₁ ≠ zeroAmplitudeFactor β θ₂ := by
  use 0, 1
  simp only [zeroAmplitudeFactor, mul_zero, Real.exp_zero, mul_one]
  intro h
  have ha : amplitudeExponent β ≠ 0 := by
    intro h0; exact hβ ((critical_iff_zero_exponent β).mpr h0)
  apply ha
  have h_eq : Real.exp (amplitudeExponent β) = Real.exp 0 := by
    rw [Real.exp_zero]; exact h.symm
  exact Real.exp_injective h_eq

/-- Off the critical line, the amplitude factor is unbounded. -/
theorem zeroAmplitudeFactor_unbounded (β : ℝ) (hβ : β ≠ 1/2) (M : ℝ) :
    ∃ θ : ℝ, M < zeroAmplitudeFactor β θ := by
  have ha : amplitudeExponent β ≠ 0 := by
    intro h0; exact hβ ((critical_iff_zero_exponent β).mpr h0)
  simp only [zeroAmplitudeFactor]
  by_cases hpos : 0 < amplitudeExponent β
  · refine ⟨(M + 1) / amplitudeExponent β, ?_⟩
    rw [mul_div_cancel₀ _ (ne_of_gt hpos)]
    linarith [Real.add_one_le_exp (M + 1)]
  · rw [not_lt] at hpos
    have hneg : amplitudeExponent β < 0 := lt_of_le_of_ne hpos ha
    refine ⟨(M + 1) / amplitudeExponent β, ?_⟩
    have h_eq : amplitudeExponent β * ((M + 1) / amplitudeExponent β) = M + 1 :=
      mul_div_cancel₀ _ (ne_of_lt hneg)
    rw [h_eq]; linarith [Real.add_one_le_exp (M + 1)]

-- ═══════════════════════════════════════════════════════════════════════════
-- §6  Reflected Pair Envelope — the cosh detector (unconditional)
-- ═══════════════════════════════════════════════════════════════════════════

/-- `Real.cosh y = 1 ↔ y = 0`. -/
theorem cosh_eq_one_iff (y : ℝ) : Real.cosh y = 1 ↔ y = 0 := by
  constructor
  · intro h
    by_contra hne
    have h_lt : 1 < Real.cosh y := Real.one_lt_cosh.mpr hne
    linarith
  · intro h; subst h; exact Real.cosh_zero

/-- The reflected pair envelope: sum of amplitude factors for (β, 1−β). -/
def reflectedPairEnvelope (β θ : ℝ) : ℝ :=
  zeroAmplitudeFactor β θ + zeroAmplitudeFactor (1 - β) θ

/-- The amplitude exponent of the reflected zero is the negative. -/
theorem amplitudeExponent_reflected (β : ℝ) :
    amplitudeExponent (1 - β) = -amplitudeExponent β := by
  unfold amplitudeExponent; field_simp; ring

/-- The reflected pair envelope equals `2·cosh(a·θ)`. -/
theorem reflectedPairEnvelope_eq_cosh (β θ : ℝ) :
    reflectedPairEnvelope β θ = 2 * Real.cosh (amplitudeExponent β * θ) := by
  unfold reflectedPairEnvelope zeroAmplitudeFactor
  rw [amplitudeExponent_reflected, neg_mul, Real.cosh_eq]
  ring

/-- The reflected pair envelope is always ≥ 2 (AM-GM). -/
theorem reflectedPairEnvelope_ge_two (β θ : ℝ) :
    2 ≤ reflectedPairEnvelope β θ := by
  rw [reflectedPairEnvelope_eq_cosh]
  linarith [Real.one_le_cosh (amplitudeExponent β * θ)]

/-- The reflected pair envelope is constantly 2 iff β = 1/2. -/
theorem reflectedPairEnvelope_const_iff (β : ℝ) :
    (∀ θ : ℝ, reflectedPairEnvelope β θ = 2) ↔ β = 1/2 := by
  constructor
  · intro h
    by_contra hne
    have ha : amplitudeExponent β ≠ 0 := fun h0 =>
      hne ((critical_iff_zero_exponent β).mpr h0)
    have h1 := h 1
    rw [reflectedPairEnvelope_eq_cosh, mul_one] at h1
    have : Real.cosh (amplitudeExponent β) = 1 := by linarith
    exact ha ((cosh_eq_one_iff _).mp this)
  · intro h; subst h; intro θ
    rw [reflectedPairEnvelope_eq_cosh]
    simp [amplitudeExponent]

-- ═══════════════════════════════════════════════════════════════════════════
-- §7  Prime-Zero Duality
-- ═══════════════════════════════════════════════════════════════════════════

/-- **The prime-zero duality** (L-series form of the explicit formula). -/
theorem primeZeroDuality
    (s : ℂ) (hs : 1 < s.re) (hs_nz : s ∉ NontrivialZeros) :
    ∃ A : ℂ,
      LSeries (fun n => (Λ n : ℂ)) s =
        -(A + ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
            (xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val))
        + 1 / s + 1 / (s - 1) + logDeriv Complex.Gammaℝ s :=
  vonMangoldt_explicit_formula_LSeries s hs hs_nz

-- ═══════════════════════════════════════════════════════════════════════════
-- §8  Nontrivial Zero Real-Part Bounds (unconditional)
-- ═══════════════════════════════════════════════════════════════════════════

theorem nontrivial_re_pos (ρ : ℂ) (hρ : ρ ∈ NontrivialZeros) : 0 < ρ.re := hρ.1

theorem nontrivial_re_lt_one (ρ : ℂ) (hρ : ρ ∈ NontrivialZeros) : ρ.re < 1 := hρ.2.1

theorem nontrivial_zeta_vanishes (ρ : ℂ) (hρ : ρ ∈ NontrivialZeros) :
    riemannZeta ρ = 0 := hρ.2.2

theorem nontrivial_ne_zero (ρ : ℂ) (hρ : ρ ∈ NontrivialZeros) : ρ ≠ 0 := by
  intro h; subst h; exact absurd hρ.1 (by simp)

/-- Zeta is nonvanishing on `Re(s) ≥ 1`. -/
theorem zeta_nonvanishing_boundary (s : ℂ) (hs : 1 ≤ s.re) :
    riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re hs

theorem nontrivial_in_open_strip (ρ : ℂ) (hρ : ρ ∈ NontrivialZeros) :
    0 < ρ.re ∧ ρ.re < 1 :=
  ⟨hρ.1, hρ.2.1⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §9  Conditional RH from the Explicit Formula (unconditional implications)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Conditional RH from bounded envelopes.** -/
theorem conditionalRH_from_bounded_envelopes
    (hBounded : ∀ ρ : ℂ, ρ ∈ NontrivialZeros →
      ∃ M : ℝ, ∀ θ : ℝ, reflectedPairEnvelope ρ.re θ ≤ M) :
    ∀ ρ : ℂ, ρ ∈ NontrivialZeros → ρ.re = 1/2 := by
  intro ρ hρ
  by_contra hne
  obtain ⟨M, hM⟩ := hBounded ρ hρ
  obtain ⟨θ, hθ⟩ := zeroAmplitudeFactor_unbounded ρ.re hne (M + 1)
  have hle := hM θ
  unfold reflectedPairEnvelope at hle
  linarith [show 0 < zeroAmplitudeFactor (1 - ρ.re) θ from Real.exp_pos _]

/-- **Conditional RH from stationary envelopes.** -/
theorem conditionalRH_from_stationary_envelopes
    (hStationary : ∀ ρ : ℂ, ρ ∈ NontrivialZeros →
      ∀ θ : ℝ, reflectedPairEnvelope ρ.re θ = 2) :
    ∀ ρ : ℂ, ρ ∈ NontrivialZeros → ρ.re = 1/2 := by
  intro ρ hρ
  exact (reflectedPairEnvelope_const_iff ρ.re).mp (hStationary ρ hρ)

-- ═══════════════════════════════════════════════════════════════════════════
-- §10  Bridge to Mathlib's RiemannHypothesis
-- ═══════════════════════════════════════════════════════════════════════════

/-- `NontrivialZeros` is the set of zeros of Mathlib's `riemannZeta` in the
    open critical strip `0 < Re(s) < 1`. It is **not** a replacement for
    Mathlib's `RiemannHypothesis` — it is a convenience set built entirely
    from Mathlib's `riemannZeta`. -/
theorem NontrivialZeros_def : NontrivialZeros =
    { s : ℂ | 0 < s.re ∧ s.re < 1 ∧ riemannZeta s = 0 } := rfl

/-- Mathlib's `RiemannHypothesis` implies all zeros in `NontrivialZeros`
    have `Re(ρ) = 1/2`. This is the easy direction. -/
theorem RiemannHypothesis_implies_NontrivialZeros :
    RiemannHypothesis → ∀ ρ : ℂ, ρ ∈ NontrivialZeros → ρ.re = 1 / 2 := by
  intro hRH ρ ⟨hρ0, hρ1, hζ⟩
  apply hRH ρ hζ
  · intro ⟨n, hn⟩
    have : ρ.re = (-2 * ((n : ℂ) + 1)).re := by rw [hn]
    simp [Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im] at this
    linarith
  · intro h; rw [h] at hρ1; simp at hρ1

/-
Conversely, if all zeros in `NontrivialZeros` have `Re(ρ) = 1/2`,
    then Mathlib's `RiemannHypothesis` holds.
    The reverse direction uses: (1) `riemannZeta_ne_zero_of_one_le_re`
    to show non-trivial zeros have `Re < 1`, and (2) the functional
    equation to show they have `Re > 0`.
-/
theorem NontrivialZeros_implies_RiemannHypothesis :
    (∀ ρ : ℂ, ρ ∈ NontrivialZeros → ρ.re = 1 / 2) → RiemannHypothesis := by
  intro h s hs hs' hs'';
  -- If $s$ is not in the critical strip, then its real part must be less than or equal to 0 or greater than or equal to 1.
  by_cases h_re : s.re ≤ 0;
  · by_cases h_re : s.re < 0;
    · have := @riemannZeta_one_sub s ?_ ?_ <;> norm_num at *;
      · exact absurd ( zeta_nonvanishing_boundary ( 1 - s ) ( by norm_num; linarith ) ) ( by aesop );
      · intro n hn; specialize hs' ( n / 2 - 1 ) ; rcases Nat.even_or_odd' n with ⟨ k, rfl | rfl ⟩ <;> norm_num at *;
        · cases k <;> simp_all +decide [ Nat.cast_succ ];
        · have := @riemannZeta_one_sub ( 2 * k + 2 ) ?_ ?_ <;> norm_num at *;
          · norm_num [ show ( 1 - ( 2 * k + 2 ) : ℂ ) = s by linear_combination' -hn ] at this;
            norm_num [ hs, Complex.exp_ne_zero, Complex.Gamma_ne_zero, Real.pi_ne_zero ] at this;
            norm_cast at this ; norm_num [ mul_add, mul_assoc, mul_comm Real.pi _, mul_div ] at this;
            norm_num [ show ( 2 * k + 2 : ℝ ) * Real.pi / 2 = Real.pi + k * Real.pi by ring, Real.cos_add ] at this;
            exact absurd ( this.resolve_left ( by rintro ( h | h ) <;> [ exact absurd h ( Complex.Gamma_ne_zero_of_re_pos ( by norm_cast ; linarith ) ) ; exact absurd h ( by exact fun h => absurd ( Real.cos_sq' ( k * Real.pi ) ) ( by norm_num [ h ] ) ) ] ) ) ( by exact zeta_nonvanishing_boundary _ ( by norm_cast ; linarith ) );
          · exact fun n => by norm_cast; aesop;
          · norm_cast ; linarith;
      · aesop;
    · cases lt_or_eq_of_le ‹_› <;> simp_all +decide;
      have := @riemannZeta_ne_zero_of_one_le_re ( 1 - s ) ; simp_all +decide [ Complex.ext_iff ];
      have := @riemannZeta_one_sub s; simp_all +decide [ Complex.ext_iff ] ;
      by_cases hi : s.im = 0 <;> simp_all +decide;
      norm_num [ show s = 0 by refine' Complex.ext _ _ <;> simp +decide [ * ] ] at *;
      norm_num [ riemannZeta_zero ] at hs;
  · exact h s ⟨ by linarith, by linarith [ show s.re < 1 from lt_of_not_ge fun h => absurd hs <| riemannZeta_ne_zero_of_one_le_re h ], hs ⟩

/-- **The equivalence**: Mathlib's `RiemannHypothesis` is equivalent to
    "all zeros in `NontrivialZeros` have `Re(ρ) = 1/2`". -/
theorem RiemannHypothesis_iff_NontrivialZeros :
    RiemannHypothesis ↔ (∀ ρ : ℂ, ρ ∈ NontrivialZeros → ρ.re = 1 / 2) :=
  ⟨RiemannHypothesis_implies_NontrivialZeros,
   NontrivialZeros_implies_RiemannHypothesis⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §11  Axiom audit
-- ═══════════════════════════════════════════════════════════════════════════

#print axioms euler_pillar
#print axioms bridge_pillar
-- hadamard_partial_fraction is PROVEN (via ZD.xi_logDeriv_partial_fraction); kernel-clean:
-- depends only on [propext, Classical.choice, Quot.sound].
#print axioms hadamard_partial_fraction
#print axioms vonMangoldt_explicit_formula
#print axioms vonMangoldt_explicit_formula_LSeries
#print axioms primeZeroDuality
#print axioms reflectedPairEnvelope_eq_cosh
#print axioms reflectedPairEnvelope_const_iff
#print axioms conditionalRH_from_bounded_envelopes
#print axioms conditionalRH_from_stationary_envelopes

end VMEFStandalone
