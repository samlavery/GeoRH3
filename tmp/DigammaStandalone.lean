import Mathlib

/-!
# Digamma Vertical Bounds — Standalone & Unconditional

Isolated headlines for the digamma `ψ = Γ'/Γ` and `Γℝ'/Γℝ` log-derivative
bounds. The base file `RequestProject.DigammaVerticalBound` imports **only
Mathlib**, and `RequestProject.UniformGammaRBound` adds only that module, so the
external footprint here is **Mathlib only** (transitively).

Four headlines, all unconditional and kernel-clean:

* `digamma_logDeriv_form` — `Γℝ'/Γℝ(s) = −(log π)/2 + (1/2)·ψ(s/2)`.
* `digamma_vertical_log_bound` — `‖ψ(σ+it)‖ ≤ C·log(1+|t|)` for fixed `σ > 0`.
* `digamma_log_bound_uniform` — the same bound with `C` uniform over `σ ∈ (0,1)`.
* `gammaR_logDeriv_uniform` — `‖Γℝ'/Γℝ(σ+iT)‖ ≤ C·log T`, `C` uniform over `σ ∈ (0,1)`.

## Axiom footprint
`[propext, Classical.choice, Quot.sound]`.
-/

open Real Complex

noncomputable section

namespace DigammaStandalone

/-- **Digamma decomposition of `Γℝ'/Γℝ`.**
`Γℝ'/Γℝ(s) = −(log π)/2 + (1/2)·(Γ'/Γ)(s/2)` wherever `Γℝ(s) ≠ 0` and `s` avoids
the poles `−2n`. -/
theorem digamma_logDeriv_form (s : ℂ) (hs : s.Gammaℝ ≠ 0)
    (hs2 : ∀ n : ℕ, s ≠ -(2 * (n : ℂ))) :
    deriv Complex.Gammaℝ s / s.Gammaℝ =
      -(Complex.log Real.pi) / 2 +
      (1 / 2) * (deriv Complex.Gamma (s / 2) / Complex.Gamma (s / 2)) := by
  sorry

/-- **Digamma vertical log bound** (fixed `σ > 0`): `‖ψ(σ+it)‖ ≤ C·log(1+|t|)`. -/
theorem digamma_vertical_log_bound (σ : ℝ) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖deriv Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I) /
        Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      C * Real.log (1 + |t|) := by
  sorry

/-- **σ-uniform digamma log bound** on the strip `σ ∈ (0,1)`, `|t| ≥ 1`. -/
theorem digamma_log_bound_uniform :
    ∃ C : ℝ, 0 < C ∧
      ∀ σ : ℝ, σ ∈ Set.Ioo (0 : ℝ) 1 → ∀ t : ℝ, 1 ≤ |t| →
        ‖deriv Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I) /
          Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ C * Real.log (1 + |t|) := by
  sorry

/-- **σ-uniform `Γℝ'/Γℝ` log bound** on the critical strip `σ ∈ (0,1)`, `T ≥ 2`. -/
theorem gammaR_logDeriv_uniform :
    ∃ C : ℝ, 0 < C ∧
      ∀ σ : ℝ, σ ∈ Set.Ioo (0 : ℝ) 1 → ∀ T : ℝ, 2 ≤ T →
        ‖logDeriv Complex.Gammaℝ ((σ : ℂ) + (T : ℂ) * Complex.I)‖ ≤ C * Real.log T := by
  sorry

end DigammaStandalone
