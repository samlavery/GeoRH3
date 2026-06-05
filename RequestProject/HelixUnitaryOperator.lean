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

/-- Every finite winding power of the source helix character is still unitary. -/
theorem helixUnitary_pow_norm (t : ℝ) (M : ℕ) :
    ‖((helixUnitary t : ℂ) ^ M)‖ = 1 := by
  rw [norm_pow, helixUnitary_norm, one_pow]

/-- `normSq` form of finite-winding source unitarity. -/
theorem helixUnitary_pow_normSq (t : ℝ) (M : ℕ) :
    Complex.normSq ((helixUnitary t : ℂ) ^ M) = 1 := by
  rw [Complex.normSq_eq_norm_sq, helixUnitary_pow_norm]
  norm_num

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

/-- A completed χ₃ mode is a complex spectral mode already completed onto the
    unit spectral circle. -/
structure Chi3CompletedMode where
  val : ℂ
  unit_normSq : Complex.normSq val = 1

instance : Coe Chi3CompletedMode ℂ where
  coe v := v.val

instance : Norm Chi3CompletedMode where
  norm v := ‖v.val‖

/-- Complete any complex spectral value onto the unit spectral circle. -/
def completedSpectralMode (z : ℂ) : Chi3CompletedMode :=
  if hz : z = 0 then
    ⟨1, by simp⟩
  else
    ⟨z / (‖z‖ : ℂ), by
      have hnorm_ne : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
      have hnorm : ‖z / (‖z‖ : ℂ)‖ = 1 := by
        rw [norm_div, norm_real, Real.norm_eq_abs,
          abs_of_nonneg (norm_nonneg z)]
        exact div_self hnorm_ne
      rw [Complex.normSq_eq_norm_sq, hnorm]
      norm_num⟩

/-- The completed spectral mode is unitary by construction. -/
theorem completedSpectralMode_unitary (z : ℂ) :
    Complex.normSq (completedSpectralMode z : ℂ) = 1 :=
  (completedSpectralMode z).unit_normSq

/-- Completion agrees with the raw spectral value exactly when the raw value was
    already unit norm. This is the guardrail: completion cannot prove raw
    unitarity; it preserves the raw value only after raw unitarity is known. -/
theorem completedSpectralMode_eq_raw_iff_norm_eq_one (z : ℂ) :
    (completedSpectralMode z : ℂ) = z ↔ ‖z‖ = 1 := by
  by_cases hz : z = 0
  · subst z
    simp [completedSpectralMode]
  · constructor
    · intro hraw
      have hnorm_left : ‖z / (‖z‖ : ℂ)‖ = 1 := by
        rw [norm_div, norm_real, Real.norm_eq_abs,
          abs_of_nonneg (norm_nonneg z)]
        exact div_self (norm_ne_zero_iff.mpr hz)
      have hnorm_eq : ‖z / (‖z‖ : ℂ)‖ = ‖z‖ := by
        simpa [completedSpectralMode, hz] using congrArg norm hraw
      exact hnorm_eq ▸ hnorm_left
    · intro hunit
      simp [completedSpectralMode, hz, hunit]

/-- One completed χ₃ helix step stays inside the completed unit mode space. -/
def completedStep (v : Chi3CompletedMode) : Chi3CompletedMode := v

/-- The completed χ₃ helix step is unitary. -/
theorem chi3_completed_helix_step_unitary
    (v : Chi3CompletedMode) :
    ‖completedStep v‖ = ‖v‖ := rfl

end

#print axioms helixUnitary_is_unitary_character
#print axioms helixUnitary_pow_norm
#print axioms helixUnitary_pow_normSq
#print axioms completedSpectralMode_unitary
#print axioms completedSpectralMode_eq_raw_iff_norm_eq_one
#print axioms chi3_completed_helix_step_unitary
