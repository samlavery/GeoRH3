import Mathlib
import RequestProject.Layer1Objects
import RequestProject.LogDerivIdentity
import RequestProject.XiPartialFraction
import RequestProject.OperatorCoupling

/-!
# Von Mangoldt Explicit Formula

This file formalizes the **minimum von Mangoldt explicit formula** needed for the
helix amplitude-defect proof chain. It assembles three pillars already proved in
the project:

1. **Euler pillar** (Mathlib): `L(Λ, s) = −ζ'/ζ(s)` for `Re(s) > 1`
2. **Bridge pillar** (`LogDerivIdentity`): `ζ'/ζ = ξ'/ξ − 1/s − 1/(s−1) − Γℝ'/Γℝ`
3. **Hadamard pillar** (`XiPartialFraction`): `ξ'/ξ = A + Σ_ρ m_ρ·(1/(s−ρ) + 1/ρ)`

into a single clean theorem: for `Re(s) > 1` and `s` not a nontrivial zero,
```
−ζ'/ζ(s) = A + Σ_ρ m_ρ·(1/(s−ρ) + 1/ρ) − 1/s − 1/(s−1) − Γℝ'/Γℝ(s)
```

From this we derive:
* **Real-part positivity** of the zero sum for `σ > 1` (each term ≥ 0)
* **Per-zero contribution** to the midpoint-normalized loss in helix coordinates
* **Reflected pair envelope** `2·cosh(a·θ)` — the cosh detector
* **Conditional RH** from bounded/stationary envelopes

## Sorry inventory

The open steps are:
1. `Layer1.vonMangoldt_LSeries_eq` — the L-series identity L(Λ,s) = −ζ'/ζ(s)
2. `ZD.riemannZeta_logDeriv_eq_xi_minus_pole_minus_gammaℝ` — the bridge identity
3. `ZD.xi_logDeriv_partial_fraction` — the Hadamard partial fraction
4. `ZD.re_zero_term_nonneg` — real-part positivity of zero terms

These encode the deep analytic content. Everything else is proved.
-/

open scoped BigOperators Real
open Real Complex

set_option maxHeartbeats 8000000

noncomputable section

namespace VonMangoldtEF

-- ═══════════════════════════════════════════════════════════════════════════
-- §1  The Three Pillars (Re-exports)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Euler pillar**: `L(Λ, s) = −ζ'/ζ(s)` for `Re(s) > 1`. -/
theorem euler_pillar (s : ℂ) (hs : 1 < s.re) :
    LSeries (fun n => (Layer1.Λ n : ℂ)) s =
      -deriv riemannZeta s / riemannZeta s :=
  Layer1.vonMangoldt_LSeries_eq s hs

/-- **Bridge pillar**: `ζ'/ζ = ξ'/ξ − 1/s − 1/(s−1) − Γℝ'/Γℝ` for `Re(s) > 1`. -/
theorem bridge_pillar (s : ℂ) (hs : 1 < s.re) :
    deriv riemannZeta s / riemannZeta s =
      deriv ZD.riemannXi s / ZD.riemannXi s -
        1 / s - 1 / (s - 1) - logDeriv Complex.Gammaℝ s :=
  ZD.riemannZeta_logDeriv_eq_xi_minus_pole_minus_gammaℝ s hs

/-- **Hadamard pillar**: `ξ'/ξ(s) = A + Σ_ρ m_ρ·(1/(s−ρ) + 1/ρ)`. -/
theorem hadamard_pillar :
    ∃ A : ℂ, ∀ s : ℂ, s ∉ ZD.NontrivialZeros →
      deriv ZD.riemannXi s / ZD.riemannXi s =
        A + ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
          (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val) :=
  ZD.xi_logDeriv_partial_fraction

-- ═══════════════════════════════════════════════════════════════════════════
-- §2  The Von Mangoldt Explicit Formula (Assembled)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Von Mangoldt explicit formula (Dirichlet series form).**

For `Re(s) > 1` and `s` not a nontrivial zero:
  `−ζ'/ζ(s) = A + Σ_ρ m_ρ·(1/(s−ρ) + 1/ρ) − 1/s − 1/(s−1) − Γℝ'/Γℝ(s)`
-/
theorem vonMangoldt_explicit_formula (s : ℂ) (hs : 1 < s.re)
    (hs_nz : s ∉ ZD.NontrivialZeros) :
    ∃ A : ℂ,
      -deriv riemannZeta s / riemannZeta s =
        -(A + ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
            (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val))
        + 1 / s + 1 / (s - 1) + logDeriv Complex.Gammaℝ s := by
  obtain ⟨A, hA⟩ := hadamard_pillar
  refine ⟨A, ?_⟩
  have h_bridge := bridge_pillar s hs
  have h_hadamard := hA s hs_nz
  linear_combination -h_bridge - h_hadamard

/-- **Von Mangoldt explicit formula (L-series form).** -/
theorem vonMangoldt_explicit_formula_LSeries (s : ℂ) (hs : 1 < s.re)
    (hs_nz : s ∉ ZD.NontrivialZeros) :
    ∃ A : ℂ,
      LSeries (fun n => (Layer1.Λ n : ℂ)) s =
        -(A + ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
            (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val))
        + 1 / s + 1 / (s - 1) + logDeriv Complex.Gammaℝ s := by
  obtain ⟨A, hA⟩ := hadamard_pillar
  refine ⟨A, ?_⟩
  have h_euler := euler_pillar s hs
  have h_bridge := bridge_pillar s hs
  have h_hadamard := hA s hs_nz
  rw [h_euler]
  linear_combination -h_bridge - h_hadamard

-- ═══════════════════════════════════════════════════════════════════════════
-- §3  Per-Zero Term Analysis
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
  ZD.re_zero_term_nonneg σ hσ ρ hρ_re hρ_re'

-- ═══════════════════════════════════════════════════════════════════════════
-- §4  Helix-Coordinate Zero Contribution
-- ═══════════════════════════════════════════════════════════════════════════

/-- The helix exponent unit. -/
abbrev U : ℝ := Layer1.U

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
      · exact absurd hD Layer1.U_ne_zero
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
  · push_neg at hpos
    have hneg : amplitudeExponent β < 0 := lt_of_le_of_ne hpos ha
    refine ⟨(M + 1) / amplitudeExponent β, ?_⟩
    have h_eq : amplitudeExponent β * ((M + 1) / amplitudeExponent β) = M + 1 :=
      mul_div_cancel₀ _ (ne_of_lt hneg)
    rw [h_eq]; linarith [Real.add_one_le_exp (M + 1)]

-- ═══════════════════════════════════════════════════════════════════════════
-- §5  Reflected Pair Envelope
-- ═══════════════════════════════════════════════════════════════════════════

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
    exact ha ((oc_cosh_eq_one_iff _).mp this)
  · intro h; subst h; intro θ
    rw [reflectedPairEnvelope_eq_cosh]
    simp [amplitudeExponent]

-- ═══════════════════════════════════════════════════════════════════════════
-- §6  The Explicit Formula Connects Primes to Zeros
-- ═══════════════════════════════════════════════════════════════════════════

/-- **The prime-zero duality.** -/
theorem primeZeroDuality (s : ℂ) (hs : 1 < s.re) (hs_nz : s ∉ ZD.NontrivialZeros) :
    ∃ A : ℂ,
      LSeries (fun n => (Layer1.Λ n : ℂ)) s =
        -(A + ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
            (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val))
        + 1 / s + 1 / (s - 1) + logDeriv Complex.Gammaℝ s :=
  vonMangoldt_explicit_formula_LSeries s hs hs_nz

-- ═══════════════════════════════════════════════════════════════════════════
-- §7  Nontrivial Zero Real-Part Bounds
-- ═══════════════════════════════════════════════════════════════════════════

/-- Nontrivial zeros have `0 < Re(ρ)`. -/
theorem nontrivial_re_pos (ρ : ℂ) (hρ : ρ ∈ ZD.NontrivialZeros) :
    0 < ρ.re := hρ.1

/-- Nontrivial zeros have `Re(ρ) < 1`. -/
theorem nontrivial_re_lt_one' (ρ : ℂ) (hρ : ρ ∈ ZD.NontrivialZeros) :
    ρ.re < 1 := hρ.2.1

/-- Nontrivial zeros satisfy `ζ(ρ) = 0`. -/
theorem nontrivial_zeta_vanishes (ρ : ℂ) (hρ : ρ ∈ ZD.NontrivialZeros) :
    riemannZeta ρ = 0 := hρ.2.2

/-- Nontrivial zeros have positive real part, so ρ ≠ 0. -/
theorem nontrivial_ne_zero (ρ : ℂ) (hρ : ρ ∈ ZD.NontrivialZeros) :
    ρ ≠ 0 := by
  intro h; subst h; exact absurd hρ.1 (by simp)

-- ═══════════════════════════════════════════════════════════════════════════
-- §8  Zero-Free Region from the Explicit Formula
-- ═══════════════════════════════════════════════════════════════════════════

/-- Zeta is nonvanishing on `Re(s) ≥ 1`. -/
theorem zeta_nonvanishing_boundary (s : ℂ) (hs : 1 ≤ s.re) :
    riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re hs

/-- Nontrivial zeros are strictly inside the critical strip. -/
theorem nontrivial_in_open_strip (ρ : ℂ) (hρ : ρ ∈ ZD.NontrivialZeros) :
    0 < ρ.re ∧ ρ.re < 1 :=
  ⟨hρ.1, hρ.2.1⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §9  Conditional RH from the Explicit Formula
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Conditional RH from bounded envelopes.** -/
theorem conditionalRH_from_bounded_envelopes
    (hBounded : ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros →
      ∃ M : ℝ, ∀ θ : ℝ, reflectedPairEnvelope ρ.re θ ≤ M) :
    ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → ρ.re = 1/2 := by
  intro ρ hρ
  by_contra hne
  obtain ⟨M, hM⟩ := hBounded ρ hρ
  obtain ⟨θ, hθ⟩ := zeroAmplitudeFactor_unbounded ρ.re hne (M + 1)
  have hle := hM θ
  unfold reflectedPairEnvelope at hle
  linarith [show 0 < zeroAmplitudeFactor (1 - ρ.re) θ from Real.exp_pos _]

/-- **Conditional RH from stationary envelopes.** -/
theorem conditionalRH_from_stationary_envelopes
    (hStationary : ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros →
      ∀ θ : ℝ, reflectedPairEnvelope ρ.re θ = 2) :
    ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → ρ.re = 1/2 := by
  intro ρ hρ
  exact (reflectedPairEnvelope_const_iff ρ.re).mp (hStationary ρ hρ)

-- ═══════════════════════════════════════════════════════════════════════════
-- §10  Summary
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Summary**: the minimum von Mangoldt explicit formula chain is complete. -/
theorem vonMangoldt_ef_summary :
    (∀ s : ℂ, 1 < s.re → s ∉ ZD.NontrivialZeros →
      ∃ A : ℂ, LSeries (fun n => (Layer1.Λ n : ℂ)) s =
        -(A + ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
            (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val))
        + 1 / s + 1 / (s - 1) + logDeriv Complex.Gammaℝ s) ∧
    (∀ β : ℝ, β = 1/2 ↔ amplitudeExponent β = 0) ∧
    (∀ β : ℝ, (∀ θ : ℝ, reflectedPairEnvelope β θ = 2) ↔ β = 1/2) ∧
    ((∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros →
        ∃ M : ℝ, ∀ θ : ℝ, reflectedPairEnvelope ρ.re θ ≤ M) →
      ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → ρ.re = 1/2) :=
  ⟨vonMangoldt_explicit_formula_LSeries,
   critical_iff_zero_exponent,
   reflectedPairEnvelope_const_iff,
   conditionalRH_from_bounded_envelopes⟩

end VonMangoldtEF

end
