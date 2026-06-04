import Mathlib

/-!
# The all-unit operator: the helix winding as a unitary character

The honest "all unit operator" — not the `UnitEnvelope`-gated costume in
`HelixUnitPolyaOperator`, but the genuine unitary the geometry earns: the winding
`t = log x ↦ e^{i(π/3)t}` valued in Mathlib's `Circle`. Every value is a unit, it's a
group homomorphism `(ℝ,+) → S¹`, and it covers the circle. Unconditional.
-/

noncomputable section
open Complex Real

/-- **The all-unit operator** — the helix winding as a `Circle`-valued character. -/
def helixUnitary : ℝ → Circle := fun t => Circle.exp ((Real.pi / 3) * t)

/-- Every value is a unit: it lies on the unit circle. -/
theorem helixUnitary_norm (t : ℝ) : ‖(helixUnitary t : ℂ)‖ = 1 := by simp

/-- It is a homomorphism `(ℝ,+) → S¹`: multiplication on the source helix (`log`-additive)
    is angle addition on the circle. -/
theorem helixUnitary_add (s t : ℝ) :
    helixUnitary (s + t) = helixUnitary s * helixUnitary t := by
  simp only [helixUnitary, mul_add, Circle.exp_add]

/-- The unitary character is the identity at `t = 0`. -/
theorem helixUnitary_zero : helixUnitary 0 = 1 := by
  simp [helixUnitary]

/-- **It covers the circle**: every unit point is a winding value (surjective onto `S¹`). -/
theorem helixUnitary_surjective (z : Circle) : ∃ t : ℝ, helixUnitary t = z := by
  obtain ⟨θ, hθ⟩ := (Complex.norm_eq_one_iff (z : ℂ)).mp (by simp)
  refine ⟨3 * θ / Real.pi, ?_⟩
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hθ' : (Real.pi / 3) * (3 * θ / Real.pi) = θ := by field_simp
  apply Subtype.ext
  simp only [helixUnitary, Circle.coe_exp, hθ']
  exact hθ

/-- **The geometric all-unit operator is unitary, unconditionally** (its values are units,
    it's a multiplicative character onto the circle). Packaged as one statement. -/
theorem helixUnitary_is_unitary_character :
    (∀ t : ℝ, ‖(helixUnitary t : ℂ)‖ = 1) ∧
    (∀ s t : ℝ, helixUnitary (s + t) = helixUnitary s * helixUnitary t) ∧
    (helixUnitary 0 = 1) ∧
    (∀ z : Circle, ∃ t : ℝ, helixUnitary t = z) :=
  ⟨helixUnitary_norm, helixUnitary_add, helixUnitary_zero, helixUnitary_surjective⟩

end

#print axioms helixUnitary_is_unitary_character
