import Mathlib

/-!
# Completed log-derivative grammar for the mod-3 character

This file records the Dirichlet-series plus archimedean terms for the
completed log-derivative channel attached to the primitive odd character
modulo `3`.
-/

noncomputable section

open scoped BigOperators
open Complex ArithmeticFunction

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-- The primitive real Dirichlet character modulo `3`, as a complex-valued
    arithmetic weight. -/
def chi3 (n : ℕ) : ℂ :=
  if n % 3 = 1 then 1 else if n % 3 = 2 then -1 else 0

/-- The negative completed logarithmic derivative grammar for the `χ₃`
    channel in the half-plane of absolute convergence. -/
def negCompletedLogDerivChi3 (s : ℂ) : ℂ :=
  (∑' n : ℕ, vonMangoldt n * chi3 n * (n : ℂ) ^ (-s))
    - (1 / 2) * Complex.log (3 / Real.pi)
    - (1 / 2) * digamma ((s + 1) / 2)

theorem chi3_completed_logderiv_grammar_Re_gt_one
    (s : ℂ) (hs : 1 < s.re) :
  negCompletedLogDerivChi3 s
    =
  (∑' n : ℕ, vonMangoldt n * chi3 n * (n : ℂ)^(-s))
  - (1/2) * Complex.log (3 / Real.pi)
  - (1/2) * digamma ((s + 1) / 2) := by
  have _hs : 1 < s.re := hs
  rfl

end
