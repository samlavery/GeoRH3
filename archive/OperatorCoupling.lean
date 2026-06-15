import Mathlib

/-!
# Operator Coupling Identities

Auxiliary identities used in the helix amplitude-defect chain.
-/

noncomputable section

open Real

/-- `cosh(x) = 1` iff `x = 0`. -/
theorem oc_cosh_eq_one_iff (x : ℝ) : Real.cosh x = 1 ↔ x = 0 := by
  constructor
  · intro h
    rw [Real.cosh_eq] at h
    have hinv : Real.exp x * Real.exp (-x) = 1 := by
      rw [← Real.exp_add]; simp
    have hsum : Real.exp x + Real.exp (-x) = 2 := by linarith
    have : Real.exp x = 1 := by nlinarith [Real.exp_pos x, Real.exp_pos (-x)]
    exact (Real.exp_eq_one_iff x).mp this
  · intro h; subst h; simp [Real.cosh_zero]

end
