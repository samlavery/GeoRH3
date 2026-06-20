import RequestProject.DirichletLStripBound
import RequestProject.DirichletLLeftBound
import RequestProject.DirichletLCompletedGrowth

/-!
# Unconditional order-1 growth of `completedLFunction χ`

The capstone of the growth port: feed the three half-plane sub-bounds (`hStrip`, `hRight`, `hLeft`)
into the assembly `completedL_order_one_log_bound_of_subbounds`, yielding the **unconditional**
order-1 log bound

  `∃ C R₀ > 0, ∀ R ≥ R₀, ∀ s, ‖s‖ ≤ R → log(‖Λ(s,χ)‖ + 1) ≤ C·R·log R`

for primitive non-principal `χ`. No gaps, no GRH — pure classical analysis (Stirling + Abel + FE).
This is the gate the summability `Σ ord(ρ)/‖ρ‖² < ∞` (→ product → Hadamard factorization) descends from.
-/

namespace DirichletLHadamard

variable {N : ℕ} [NeZero N]

/-- **Unconditional order-1 growth of the completed Dirichlet `L`** (primitive `χ ≠ 1`). -/
theorem completedL_order_one_log_bound {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hχp : χ.IsPrimitive) :
    ∃ C > (0 : ℝ), ∃ R₀ > (0 : ℝ), ∀ R, R₀ ≤ R → ∀ s : ℂ, ‖s‖ ≤ R →
      Real.log (‖DirichletCharacter.completedLFunction χ s‖ + 1) ≤ C * R * Real.log R := by
  refine completedL_order_one_log_bound_of_subbounds hχ (completedL_bound_strip hχ hχp) ?_
    (completedL_bound_left hχ hχp)
  obtain ⟨C, hC, R₀, hR₀, h⟩ := completedL_bound_right hχ
  exact ⟨C, hC, R₀, hR₀, fun s hsR hsre => h s hsR (le_of_lt hsre)⟩

end DirichletLHadamard

#print axioms DirichletLHadamard.completedL_order_one_log_bound
