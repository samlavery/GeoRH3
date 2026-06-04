import Mathlib

/-!
# `1/2` is derived from the helix scaling alone — not assumed, not tautological

`GapAnalysis.lean` warns that "`radial = 0 ⟺ σ = 1/2`" is a *tautology* when the
embedding defines `radial := σ − 1/2` (and `silly_embed` shows you can rig it to
`σ = 7`). So a real derivation of `1/2` must contain **no `1/2` in its setup** and
force it from a genuine symmetry.

The helix's defining symmetry is multiplicative scaling (multiplication-is-addition,
the log-spiral). The dilation `U_λ f(x) = λ^c · f(λ x)` acts on `L²(ℝ₊, dx)`. Its
energy scales by `λ^{2c-1}` (a pure change of variables), so it is an **isometry at
every scale iff `c = 1/2`**. Here `c` is a *free parameter*; the half-unit is forced
by the isometry, and it emerges from the change-of-variables Jacobian
(`λ^{2c-1} = 1 ⟺ c = 1/2`) — there is no `1/2` baked in anywhere.

All three results are axiom-clean (`[propext, Classical.choice, Quot.sound]`).
This is the `½` = critical line as the self-adjointness/isometry constant of the
helix scaling operator, made rigorous and free of any tautology.
-/

open MeasureTheory Set Real

noncomputable section

namespace HelixHalfUnit

/-- §1  The dilation `U_λ f(x) = λ^c · f(λ x)` scales the `L²(ℝ₊, dx)` energy by
    `λ^{2c-1}` (pure change of variables — the helix scaling acting on energy). -/
theorem helix_dilation_energy (c lam : ℝ) (hlam : 0 < lam) (f : ℝ → ℝ) :
    (∫ x in Ioi (0:ℝ), (lam ^ c * f (lam * x)) ^ 2)
      = lam ^ (2 * c - 1) * ∫ x in Ioi (0:ℝ), (f x) ^ 2 := by
  have hpow : ∀ x, (lam ^ c * f (lam * x)) ^ 2
      = lam ^ (2*c) * ((fun y => (f y)^2) (lam * x)) := by
    intro x; simp only
    rw [mul_pow]; congr 1
    rw [pow_two, ← Real.rpow_add hlam, ← two_mul]
  simp_rw [hpow]
  rw [integral_const_mul,
      integral_comp_mul_left_Ioi (fun y => (f y)^2) 0 hlam,
      mul_zero, smul_eq_mul, ← mul_assoc]
  congr 1
  rw [← Real.rpow_neg_one lam, ← Real.rpow_add hlam]
  congr 1

/-- §2  The energy factor is `1` at *every* scale `λ > 0`  ⟺  `c = 1/2`. -/
theorem helix_isometry_forces_half (c : ℝ) :
    (∀ lam : ℝ, 0 < lam → lam ^ (2 * c - 1) = 1) ↔ c = 1 / 2 := by
  refine ⟨fun h => ?_, fun h lam hlam => by rw [h]; norm_num⟩
  have hlog : (2 * c - 1) * Real.log 2 = 0 := by
    have := congrArg Real.log (h 2 (by norm_num))
    rwa [Real.log_rpow (by norm_num), Real.log_one] at this
  rcases mul_eq_zero.mp hlog with h' | h'
  · linarith
  · exact absurd h' (Real.log_pos (by norm_num)).ne'

/-- **`1/2` derived from the helix scaling alone** (no functional equation, no ζ,
    no zeros). For any signal of nonzero energy, the multiplicative dilation
    `U_λ f = λ^c · f(λ·)` preserves the `L²(ℝ₊, dx)` energy at *every* scale `λ`
    **iff** `c = 1/2`. The half-unit is the unique isometry exponent of the
    helix's defining (multiplication-is-addition) symmetry. -/
theorem helix_forces_half (c : ℝ) (f : ℝ → ℝ)
    (hE : 0 < ∫ x in Ioi (0:ℝ), (f x) ^ 2) :
    (∀ lam : ℝ, 0 < lam →
        (∫ x in Ioi (0:ℝ), (lam ^ c * f (lam * x)) ^ 2)
          = ∫ x in Ioi (0:ℝ), (f x) ^ 2)
      ↔ c = 1 / 2 := by
  refine ⟨fun h => (helix_isometry_forces_half c).mp (fun lam hlam => ?_),
          fun h lam hlam => by rw [helix_dilation_energy c lam hlam f, h]; norm_num⟩
  have he := h lam hlam
  rw [helix_dilation_energy c lam hlam f] at he
  exact mul_right_cancel₀ (ne_of_gt hE) (by rw [one_mul]; exact he)

end HelixHalfUnit

#print axioms HelixHalfUnit.helix_dilation_energy
#print axioms HelixHalfUnit.helix_isometry_forces_half
#print axioms HelixHalfUnit.helix_forces_half
