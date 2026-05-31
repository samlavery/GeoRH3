import Mathlib

/-!
# Layer 1 Objects: Core Definitions for the Helix Framework

This file provides the foundational objects used throughout the
von Mangoldt explicit formula chain:
- `Layer1.Λ`: the von Mangoldt function (wrapper around Mathlib's)
- `Layer1.U`: the helix exponent unit (= 1, the width of the critical strip)
- `Layer1.vonMangoldt_LSeries_eq`: L(Λ, s) = −ζ'/ζ(s) for Re(s) > 1
-/

noncomputable section

open scoped BigOperators Real
open Real Complex

namespace Layer1

/-- The von Mangoldt function Λ : ℕ → ℝ. -/
def Λ (n : ℕ) : ℝ := ArithmeticFunction.vonMangoldt n

/-- Λ is nonneg. -/
theorem Λ_nonneg (n : ℕ) : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg

/-- Λ is positive on primes. -/
theorem Λ_prime_pos (p : ℕ) (hp : p.Prime) : 0 < Λ p :=
  ArithmeticFunction.vonMangoldt_pos_iff.mpr hp.isPrimePow

/-- The helix exponent unit U = 1 (width of the critical strip). -/
def U : ℝ := 1

/-- U is positive. -/
theorem U_pos : (0 : ℝ) < U := by norm_num [U]

/-- U is nonzero. -/
theorem U_ne_zero : U ≠ 0 := ne_of_gt U_pos

/-
**The von Mangoldt L-series identity** (sorry'd).

    For Re(s) > 1:
      L(Λ, s) = Σ_n Λ(n) · n^{-s} = −ζ'/ζ(s)

    This is a fundamental identity connecting the arithmetic function Λ
    to the logarithmic derivative of ζ. It follows from the Euler product
    and term-by-term differentiation.
-/
theorem vonMangoldt_LSeries_eq (s : ℂ) (hs : 1 < s.re) :
    LSeries (fun n => (Λ n : ℂ)) s =
      -deriv riemannZeta s / riemannZeta s := by
  have h_vonMangoldt : LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ)) s = -deriv riemannZeta s / riemannZeta s := by
    grind +suggestions;
  convert h_vonMangoldt using 1

end Layer1

end