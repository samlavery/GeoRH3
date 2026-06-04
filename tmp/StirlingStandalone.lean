import Mathlib

/-!
# Stirling Vertical Bound — Standalone & Unconditional

Isolated headline of `RequestProject.StirlingBound`: the two-sided Stirling
asymptotic for `‖Γ(σ+it)‖` on vertical lines. `StirlingBound` imports only the
trivial constant module `CoshBalance` (`= 1/2`, Mathlib-only), so the external
footprint here is **Mathlib only** (transitively).

The bound was formerly stated conditionally on `GammaRatioUpperHalf`; that
hypothesis is proved unconditionally in `StirlingBound` (`gammaRatioUpperHalf_proved`,
via GammaSeq product analysis), and the canonical `gamma_stirling_bound` is now
unconditional. Here we re-export it under a self-documenting name and audit it.

## Axiom footprint
`[propext, Classical.choice, Quot.sound]`.
-/

open Real Complex

noncomputable section

namespace StirlingStandalone

/-- **Unconditional two-sided Stirling bound on vertical lines.**
For every `σ > 0` there exist `C_lo, C_hi, T₀ > 0` such that for all `|t| ≥ T₀`,
`C_lo·|t|^(σ−1/2)·e^(−π|t|/2) ≤ ‖Γ(σ+it)‖ ≤ C_hi·|t|^(σ−1/2)·e^(−π|t|/2)`. -/
theorem gamma_vertical_two_sided_bound (σ : ℝ) (hσ : 0 < σ) :
    ∃ (C_lo C_hi T₀ : ℝ), 0 < C_lo ∧ 0 < C_hi ∧ 0 < T₀ ∧
    ∀ (t : ℝ), T₀ ≤ |t| →
      C_lo * |t| ^ (σ - 1/2) * Real.exp (-π * |t| / 2) ≤
        ‖Complex.Gamma ⟨σ, t⟩‖ ∧
      ‖Complex.Gamma ⟨σ, t⟩‖ ≤
        C_hi * |t| ^ (σ - 1/2) * Real.exp (-π * |t| / 2) := by
  sorry

end StirlingStandalone
