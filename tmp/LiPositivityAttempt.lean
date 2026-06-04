import Mathlib
import RequestProject.HelixExplicitFormula

/-!
# Li Positivity from Unique Factorization — Attempt & Gap Analysis

## The Question

Can we prove `λ_n ≥ 0` (Li positivity, equivalent to RH) from unique
factorization on the helix?

## The Chain

1. **Unique factorization** in ℤ (or ℤ[ω] for mod-6 helix)
   → Euler product `ζ(s) = ∏_p (1 − p⁻ˢ)⁻¹`
   → von Mangoldt `Λ(n) ≥ 0`

2. **Λ ≥ 0** → Weil diagonal form `W(f) = Σ f(n)² Λ(n) ≥ 0`

3. **Explicit formula** (Hadamard + Bridge):
   `−ζ'/ζ(s) = Σ_ρ (1/(s−ρ) + 1/ρ) − 1/s − 1/(s−1) − Γℝ'/Γℝ(s)`

4. **Li coefficients**: `λ_n = Σ_ρ Re[1 − (1−1/ρ)^n]`

5. **Per-zero**: `Re[1−w^n] ≥ 0` when `‖w‖ = 1` (i.e. β = 1/2)

## The Gap

Steps 1–2 are proved. Step 3 needs Hadamard (sorry'd). Step 5 is proved.

The **irreducible gap** is between steps 2 and 4: showing that
`Λ(n) ≥ 0` implies `λ_n ≥ 0`. This is NOT a consequence of the
diagonal Weil form alone. The diagonal form gives:

  `Σ f(n)² Λ(n) ≥ 0`  (trivially, since each term ≥ 0)

But `λ_n` involves the FULL explicit formula, which has:
- A sum over zeros (not over primes)
- Contributions from the pole at s=1
- Contributions from the Gamma factor

The standard Weil criterion for RH requires showing that a certain
**distributional** positivity holds — not just pointwise Λ ≥ 0 but
positivity of the Weil quadratic form for ALL Schwartz test functions.
This is strictly stronger than Λ ≥ 0 and is in fact equivalent to RH.

## What We Can Prove

We formalize the chain as far as it goes, and identify the precise
lemma whose proof would constitute a proof of RH.

## Axiom footprint
`[propext, Classical.choice, Quot.sound]` (plus sorry where noted).
-/

open scoped BigOperators Real
open Real Complex VMEFStandalone HelixExplicitFormula

noncomputable section

namespace LiPositivityAttempt

-- ═══════════════════════════════════════════════════════════════════════════
-- §1  Step 1: Unique Factorization → Λ ≥ 0
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Unique factorization gives the Euler product, which gives Λ ≥ 0.**
This is the foundation: `Λ(n) ≥ 0` for all `n`, with equality iff `n`
is not a prime power. -/
theorem step1_vonMangoldt_nonneg : ∀ n : ℕ, (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt n :=
  fun n => ArithmeticFunction.vonMangoldt_nonneg

/-- Prime powers carry positive weight. -/
theorem step1_vonMangoldt_pos_of_prime (p : ℕ) (hp : p.Prime) :
    0 < ArithmeticFunction.vonMangoldt p := by
  rw [ArithmeticFunction.vonMangoldt_apply_prime hp]
  exact Real.log_pos (by exact_mod_cast hp.one_lt)

-- ═══════════════════════════════════════════════════════════════════════════
-- §2  Step 2: Λ ≥ 0 → Weil Diagonal Form ≥ 0
-- ═══════════════════════════════════════════════════════════════════════════

/-- **The Weil diagonal form is nonneg from Λ ≥ 0.** -/
theorem step2_weil_diagonal_nonneg (f : ℕ → ℝ) (S : Finset ℕ) :
    0 ≤ ∑ n ∈ S, f n ^ 2 * ArithmeticFunction.vonMangoldt n :=
  Finset.sum_nonneg fun n _ => mul_nonneg (sq_nonneg _) ArithmeticFunction.vonMangoldt_nonneg

-- ═══════════════════════════════════════════════════════════════════════════
-- §3  Step 3: The Explicit Formula (connects primes to zeros)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **The explicit formula** connects the prime side (Λ) to the zero side (ρ).
    Re-exported from `HelixExplicitFormula`. -/
theorem step3_explicit_formula
    (s : ℂ) (hs : 1 < s.re) (hs_nz : s ∉ VMEFStandalone.NontrivialZeros) :
    ∃ A : ℂ,
      LSeries (fun n => (VMEFStandalone.Λ n : ℂ)) s =
        -(A + ∑' ρ : {ρ : ℂ // ρ ∈ VMEFStandalone.NontrivialZeros},
            helixZeroContribution ρ.val (VMEFStandalone.xiOrderNat ρ.val) s)
        + 1 / s + 1 / (s - 1) + logDeriv Complex.Gammaℝ s :=
  helix_explicit_formula s hs hs_nz

-- ═══════════════════════════════════════════════════════════════════════════
-- §4  Step 4: Per-Zero Li Nonnegativity (on the critical line)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **On the critical line, each Li coefficient is nonneg.** -/
theorem step4_per_zero_li_nonneg (ρ : ℂ) (hρ : ρ.re = 1/2) (n : ℕ) :
    0 ≤ helixLiCoeff ρ n :=
  helixLiCoeff_nonneg_on_line ρ hρ n

-- ═══════════════════════════════════════════════════════════════════════════
-- §5  The Gap: What Would Prove Li Positivity
-- ═══════════════════════════════════════════════════════════════════════════

/-- **THE GAP LEMMA** — This is the statement whose proof would give RH.

Given:
- The explicit formula (zero-sum representation of −ζ'/ζ)
- Λ(n) ≥ 0 for all n
- The Jensen zero-density bound N(T) = O(T log T)

Show: λ_n ≥ 0 for all n.

The difficulty: the Li coefficient `λ_n = Σ_ρ Re[1 − (1−1/ρ)^n]` is a
sum over ALL nontrivial zeros. Even though `Λ ≥ 0` gives positivity on
the prime side, converting this to positivity of the zero-side sum
requires controlling the infinite sum — specifically, showing that the
Weil explicit formula, when evaluated at the Li test function, produces
a nonneg answer.

This is NOT a consequence of the diagonal Weil form alone, because the
Li test function is not supported on a finite set of primes. The full
Weil criterion requires positivity for distributional test functions,
which is strictly stronger than pointwise Λ ≥ 0.

**Status: This is equivalent to RH.** -/
theorem gap_lemma_li_positivity
    (hΛ : ∀ n : ℕ, (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt n)
    (hEF : ∀ s : ℂ, 1 < s.re → s ∉ VMEFStandalone.NontrivialZeros →
      ∃ A : ℂ, LSeries (fun n => (VMEFStandalone.Λ n : ℂ)) s =
        -(A + ∑' ρ : {ρ : ℂ // ρ ∈ VMEFStandalone.NontrivialZeros},
            helixZeroContribution ρ.val (VMEFStandalone.xiOrderNat ρ.val) s)
        + 1 / s + 1 / (s - 1) + logDeriv Complex.Gammaℝ s) :
    -- Conclusion: all zeros on the critical line
    ∀ ρ : ℂ, ρ ∈ VMEFStandalone.NontrivialZeros → ρ.re = 1/2 := by
  sorry

-- ═══════════════════════════════════════════════════════════════════════════
-- §6  What the Helix Framework DOES Prove
-- ═══════════════════════════════════════════════════════════════════════════

/-- **The helix proves: RH ⟺ bounded paired Li ⟺ unitary Möbius ⟺ zero amplitude.**
This is a complete PER-ZERO characterization. The five-way equivalence
does not assume RH — it characterizes each zero independently. -/
theorem helix_proves_per_zero_equivalence (ρ : ℂ)
    (hρ : ρ ∈ VMEFStandalone.NontrivialZeros)
    (hρ_im : ρ.im ≠ 0) :
    (ρ.re = 1/2 ↔ helixAmplitude ρ = 0) ∧
    (ρ.re = 1/2 ↔ ‖helixMoebius ρ‖ = 1) ∧
    (ρ.re = 1/2 ↔ ∃ M : ℝ, ∀ n : ℕ, M ≤ pairedLiCoeff ρ n) ∧
    (ρ.re = 1/2 ↔ ∀ θ : ℝ, VMEFStandalone.reflectedPairEnvelope ρ.re θ = 2) :=
  helix_five_way_equivalence ρ hρ hρ_im

/-- **The helix proves: the CONDITIONAL chain from Λ ≥ 0.**

If we additionally know that every zero satisfies one of the five
equivalent conditions, then RH holds. The chain is:

  Λ ≥ 0  (unique factorization, proved)
  → Weil diagonal ≥ 0  (proved)
  → ???  (the gap — need Weil distributional positivity)
  → each paired Li bounded below  (proved equivalent to RH)
  → each β = 1/2  (proved)
  → RH  (by definition)

The helix DOES close the loop: it shows that bounded paired Li ⟹ RH
and RH ⟹ bounded paired Li, making the characterization complete.
What remains is filling the ??? step. -/
theorem helix_conditional_chain :
    -- If all zeros have bounded paired Li, then all zeros are on the line
    (∀ ρ : ℂ, ρ ∈ VMEFStandalone.NontrivialZeros → ρ.im ≠ 0 →
      (∃ M : ℝ, ∀ n : ℕ,
        M ≤ (li_helix_term ρ.re ρ.im n).re +
            (li_helix_term (1 - ρ.re) (-ρ.im) n).re) →
      ρ.re = 1/2) ∧
    -- Conversely, on the line, paired Li is bounded below by 0
    (∀ ρ : ℂ, ρ.re = 1/2 →
      ∀ n : ℕ,
        0 ≤ (li_helix_term ρ.re ρ.im n).re +
            (li_helix_term (1 - ρ.re) (-ρ.im) n).re) := by
  constructor
  · intro ρ hρ hρ_im hbdd
    have := forced_half_from_bounded_li ρ.re ρ.im hρ_im hbdd
    linarith
  · intro ρ hρ n
    rw [hρ]
    have h1 := li_helix_nonneg_on_line ρ.im n
    have h2 := li_helix_nonneg_on_line (-ρ.im) n
    convert add_nonneg h1 h2 using 2
    norm_num

-- ═══════════════════════════════════════════════════════════════════════════
-- §7  Why Unique Factorization Alone Is Insufficient
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Diagnostic: the Davenport-Heilbronn counterexample principle.**

The Davenport-Heilbronn function has a Dirichlet series with
coefficients that are NOT all nonneg, and it has zeros off the
critical line. This shows that the sign of the coefficients matters.

Unique factorization gives Λ ≥ 0 (nonneg coefficients), but
L-functions with signed coefficients can have off-line zeros.
So Λ ≥ 0 is NECESSARY for RH but the question is whether it's
SUFFICIENT.

The helix framework shows: Λ ≥ 0 gives the Weil diagonal positivity,
but the full Weil criterion needs distributional positivity, which is
strictly stronger.

**The irreducible content of RH** is the step from:
  "Λ ≥ 0 pointwise" → "Weil form ≥ 0 for ALL test functions"

This step uses the ANALYTIC structure of ζ (meromorphic continuation,
functional equation, Hadamard factorization) in addition to the
ARITHMETIC structure (Euler product, Λ ≥ 0). Neither alone suffices. -/
theorem coefficient_sign_matters :
    -- Λ ≥ 0 is a fact (from unique factorization / Euler product)
    (∀ n : ℕ, (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt n) ∧
    -- Each prime contributes positively
    (∀ p : ℕ, p.Prime → 0 < ArithmeticFunction.vonMangoldt p) := by
  exact ⟨fun n => ArithmeticFunction.vonMangoldt_nonneg,
         fun p hp => by
           rw [ArithmeticFunction.vonMangoldt_apply_prime hp]
           exact Real.log_pos (by exact_mod_cast hp.one_lt)⟩

end LiPositivityAttempt
