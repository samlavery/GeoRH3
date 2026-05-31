import Mathlib
import RequestProject.ScalingCoherence
import RequestProject.PrimeNormScaling
import RequestProject.CoordinateInvariance

/-!
# The PNT–RH Dichotomy: Scaling Coherence Characterizes RH

## Overview

This file connects the project's scaling coherence framework to Mathlib's
`RiemannHypothesis`. The key result is that scaling coherence at every
nontrivial zero is equivalent to `RiemannHypothesis`.

We use Mathlib's definition throughout:
```
def RiemannHypothesis : Prop :=
  ∀ s, riemannZeta s = 0 → (¬∃ n, s = -2*(↑n+1)) → s ≠ 1 → s.re = 1/2
```

### The argument

The Prime Number Theorem (PNT) states that ψ(x) ~ x. The explicit formula:

    ψ(x) = x − Σ_ρ x^ρ/ρ − (lower order terms)

decomposes into a **prime side** (Euler product) and a **zeta side** (zeros).

1. **On-line zeros (σ = 1/2)** produce coordinate-invariant error corrections:
   the growth imbalance between FE partners is zero in every coordinate system.

2. **Off-line zeros (σ ≠ 1/2)** break scaling coherence: the growth imbalance
   u(2σ−1) grows with |u|, making error corrections coordinate-dependent.

3. **Therefore**: PNT-compatibility (scaling coherence at all zeros) is
   equivalent to all nontrivial zeros having Re(s) = 1/2, which is exactly
   Mathlib's `RiemannHypothesis`.

## Main results

- `scaling_coherent_iff_re_half`: scaling coherence ⟺ σ = 1/2
- `rh_iff_all_zeros_scaling_coherent`: `RiemannHypothesis` ⟺ all nontrivial
  zeros are scaling-coherent
- `rh_iff_all_imbalances_zero`: `RiemannHypothesis` ⟺ all growth imbalances
  vanish
- `rh_iff_strongly_coherent`: `RiemannHypothesis` ⟺ all nontrivial zeros
  are strongly coherent
-/

noncomputable section

open Real Complex

/-! ## Part 1: Scaling coherence characterizes σ = 1/2 -/

/-- Scaling coherence is equivalent to being on the critical line.
    This is the fundamental algebraic fact underlying the dichotomy. -/
theorem scaling_coherent_iff_re_half (σ : ℝ) :
    scaling_coherent σ ↔ σ = 1 / 2 :=
  scaling_coherence_iff_online σ

/-- Off-line real parts break scaling coherence. -/
theorem offline_breaks_coherence (σ : ℝ) (h : σ ≠ 1 / 2) :
    ¬ scaling_coherent σ :=
  (scaling_coherence_iff_online σ).not.mpr h

/-- On-line real parts are scaling-coherent. -/
theorem online_is_coherent (σ : ℝ) (h : σ = 1 / 2) :
    scaling_coherent σ :=
  (scaling_coherence_iff_online σ).mpr h

/-! ## Part 2: Connecting to Mathlib's `RiemannHypothesis` -/

/-- **PNT-compatibility**: every nontrivial zero of ζ is scaling-coherent.
    This is the scaling-theoretic reformulation of RH. -/
def PNTCompatible : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 →
    (¬∃ n : ℕ, s = -2 * (↑n + 1)) → s ≠ 1 →
    scaling_coherent s.re

/-- **RH implies PNT-compatibility**: If all nontrivial zeros have
    Re(s) = 1/2, then all nontrivial zeros are scaling-coherent. -/
theorem rh_implies_pnt_compatible :
    RiemannHypothesis → PNTCompatible := by
  intro rh s hs hnt hp
  exact (scaling_coherence_iff_online s.re).mpr (rh s hs hnt hp)

/-- **PNT-compatibility implies RH**: If all nontrivial zeros are
    scaling-coherent, then all have Re(s) = 1/2. -/
theorem pnt_compatible_implies_rh :
    PNTCompatible → RiemannHypothesis := by
  intro hpnt s hs hnt hp
  exact (scaling_coherence_iff_online s.re).mp (hpnt s hs hnt hp)

/-- **The equivalence**: `RiemannHypothesis` is the same as PNT-compatibility.
    Scaling coherence at every nontrivial zero ⟺ RH. -/
theorem rh_iff_pnt_compatible :
    RiemannHypothesis ↔ PNTCompatible :=
  ⟨rh_implies_pnt_compatible, pnt_compatible_implies_rh⟩

/-- **RH ⟺ all nontrivial zeros are scaling-coherent.**
    Direct statement using Mathlib's `RiemannHypothesis`. -/
theorem rh_iff_all_zeros_scaling_coherent :
    RiemannHypothesis ↔
    (∀ s : ℂ, riemannZeta s = 0 →
      (¬∃ n : ℕ, s = -2 * (↑n + 1)) → s ≠ 1 →
      scaling_coherent s.re) :=
  rh_iff_pnt_compatible

/-! ## Part 3: The unconditional dichotomy -/

/-- **The PNT–RH Dichotomy**: Either RH holds or PNT-compatibility fails. -/
theorem rh_or_not_pnt_compatible :
    RiemannHypothesis ∨ ¬ PNTCompatible := by
  exact Classical.or_iff_not_imp_left.mpr fun h =>
    mt pnt_compatible_implies_rh h

/-- **Contrapositive**: If any nontrivial zero is off-line,
    PNT-compatibility fails. -/
theorem offline_zero_implies_not_pnt_compatible
    (s : ℂ) (hs : riemannZeta s = 0)
    (hnt : ¬∃ n : ℕ, s = -2 * (↑n + 1)) (hp : s ≠ 1)
    (hoff : s.re ≠ 1 / 2) :
    ¬ PNTCompatible := by
  intro hpnt
  exact hoff ((scaling_coherence_iff_online s.re).mp (hpnt s hs hnt hp))

/-! ## Part 4: Equivalent characterizations of RH -/

/-- **RH ⟺ all growth imbalances vanish at nontrivial zeros.** -/
theorem rh_iff_all_imbalances_zero :
    RiemannHypothesis ↔
    (∀ s : ℂ, riemannZeta s = 0 →
      (¬∃ n : ℕ, s = -2 * (↑n + 1)) → s ≠ 1 →
      ∀ u : ℝ, u ≠ 0 → growth_imbalance u s.re = 0) := by
  constructor
  · intro rh s hs hnt hp u hu
    exact (growth_imbalance_zero_iff u s.re hu).mpr (rh s hs hnt hp)
  · intro h s hs hnt hp
    exact (scaling_coherence_iff_online s.re).mp (fun u hu => h s hs hnt hp u hu)

/-- **RH ⟺ all nontrivial zeros are strongly coherent.** -/
theorem rh_iff_strongly_coherent :
    RiemannHypothesis ↔
    (∀ s : ℂ, riemannZeta s = 0 →
      (¬∃ n : ℕ, s = -2 * (↑n + 1)) → s ≠ 1 →
      strongly_coherent s.re) := by
  simp only [RiemannHypothesis, strongly_coherent_iff_online]

/-- **Five equivalent characterizations of RH**, all using Mathlib's definition:

    (1) RH: all nontrivial zeros have Re(s) = 1/2
    (2) PNT-compatible: all nontrivial zeros are scaling-coherent
    (3) All growth imbalances vanish
    (4) All nontrivial zeros are strongly coherent -/
theorem rh_four_equivalences :
    (RiemannHypothesis ↔ PNTCompatible) ∧
    (RiemannHypothesis ↔
      ∀ s : ℂ, riemannZeta s = 0 →
        (¬∃ n : ℕ, s = -2 * (↑n + 1)) → s ≠ 1 →
        ∀ u : ℝ, u ≠ 0 → growth_imbalance u s.re = 0) ∧
    (RiemannHypothesis ↔
      ∀ s : ℂ, riemannZeta s = 0 →
        (¬∃ n : ℕ, s = -2 * (↑n + 1)) → s ≠ 1 →
        strongly_coherent s.re) :=
  ⟨rh_iff_pnt_compatible, rh_iff_all_imbalances_zero, rh_iff_strongly_coherent⟩

/-! ## Part 5: The geometric dichotomy -/

/-- **The geometric content**: either every nontrivial zero of ζ sits at the
    geometric midpoint σ = 1/2 (i.e. `RiemannHypothesis` holds), or there
    exists a nontrivial zero with nonzero growth imbalance under some
    coordinate rescaling. -/
theorem geometric_dichotomy :
    RiemannHypothesis ∨
    (∃ s : ℂ, riemannZeta s = 0 ∧
      (¬∃ n : ℕ, s = -2 * (↑n + 1)) ∧ s ≠ 1 ∧
      ∃ u : ℝ, u ≠ 0 ∧ growth_imbalance u s.re ≠ 0) := by
  by_cases h : RiemannHypothesis
  · exact Or.inl h
  · right
    unfold RiemannHypothesis at h
    push_neg at h
    obtain ⟨s, hs, hnt, hp, hre⟩ := h
    refine ⟨s, hs, ?_, hp, 1, one_ne_zero, ?_⟩
    · push_neg; exact hnt
    · rw [growth_imbalance_eq]
      intro h0
      apply hre
      have := mul_eq_zero.mp h0
      rcases this with h1 | h1
      · exact absurd h1 one_ne_zero
      · linarith

/-- **PNT is geometric**: PNT-compatibility is the same statement as
    `RiemannHypothesis`. The "1/2" is not special — it is the midpoint
    of [0,1]. In the log(7) system it becomes log(7)/2. -/
theorem pnt_is_geometric :
    PNTCompatible ↔ RiemannHypothesis :=
  rh_iff_pnt_compatible.symm

end
