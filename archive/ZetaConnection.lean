import Mathlib
import RequestProject.HelixRoundTrip
import RequestProject.ForcedAlignment
import RequestProject.BridgeToZeroFree

/-!
# Connection to Mathlib's Riemann Zeta Function

## Gap being closed

The project's theorems are about abstract operators and individual complex
numbers. This file connects them to Mathlib's actual `riemannZeta`, including:

1. **Mathlib's RH definition** — `RiemannHypothesis` is already in Mathlib!
2. **The functional equation** — `completedRiemannZeta_one_sub`
3. **The zero-free region** — `riemannZeta_ne_zero_of_one_le_re`
4. **Bridge theorems** connecting our Möbius characterization to actual zeros
5. **Formal gap statement** — what exactly needs to be proved

## What Mathlib defines

```
def RiemannHypothesis : Prop :=
  ∀ s, riemannZeta s = 0 → (¬∃ n, s = -2*(↑n+1)) → s ≠ 1 → s.re = 1/2
```

This says: every zero of ζ that is not trivial (not at -2, -4, -6, ...)
and not the pole at s = 1, has Re(s) = 1/2.
-/

noncomputable section

open Complex Real

/-! ## Part 1: Mathlib's RH and what it already proves -/

/-- Mathlib's RH definition is ready to use. -/
example : RiemannHypothesis =
    (∀ s : ℂ, riemannZeta s = 0 →
      (¬∃ n : ℕ, s = -2 * (↑n + 1)) → s ≠ 1 → s.re = 1/2) := rfl

/-- **Mathlib proves**: ζ(s) ≠ 0 for Re(s) ≥ 1. -/
theorem zeta_nonvanishing_right (s : ℂ) (hs : 1 ≤ s.re) :
    riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re hs

/-- **Mathlib proves**: ξ(1-s) = ξ(s). -/
theorem zeta_functional_equation (s : ℂ) :
    completedRiemannZeta (1 - s) = completedRiemannZeta s :=
  completedRiemannZeta_one_sub s

/-- **Mathlib proves**: ζ is holomorphic away from s = 1. -/
theorem zeta_holomorphic (s : ℂ) (hs : s ≠ 1) :
    DifferentiableAt ℂ riemannZeta s :=
  differentiableAt_riemannZeta hs

/-- **Mathlib proves**: Λ(n) ≥ 0. -/
theorem vonmangoldt_nonneg' (n : ℕ) :
    (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt n :=
  ArithmeticFunction.vonMangoldt_nonneg

/-! ## Part 2: The Möbius characterization applies to actual ζ zeros -/

/-- **Bridge**: For any nontrivial zero ρ of ζ with Im(ρ) ≠ 0,
    the Möbius image w(ρ) = 1 - 1/ρ has |w(ρ)| = 1 ⟺ Re(ρ) = 1/2.

    This connects our algebraic characterization to the actual zeros. -/
theorem moebius_characterization_at_zero (s : ℂ)
    (_h_zero : riemannZeta s = 0)
    (_h_not_trivial : ¬∃ n : ℕ, s = -2 * (↑n + 1))
    (_h_not_pole : s ≠ 1)
    (h_im : s.im ≠ 0) :
    ‖moebius_helix s.re s.im‖ = 1 ↔ s.re = 1/2 :=
  moebius_unit_iff s.re s.im h_im

/-- **Bridge**: The functional equation pairs zeros via the Möbius reciprocal. -/
theorem moebius_reciprocal_at_zeros (σ γ : ℝ) (hγ : γ ≠ 0) :
    moebius_helix σ γ * moebius_helix (1 - σ) (-γ) = 1 :=
  moebius_product_one σ γ hγ

/-- **Bridge**: If ρ is a zero with |w(ρ)| ≠ 1 (off-line), then
    the paired Li terms for ρ and 1-ρ̄ are unbounded below. -/
theorem li_divergence_for_offline_zero (σ γ : ℝ)
    (hσ : σ ≠ 1/2) (hγ : γ ≠ 0) :
    ∀ M : ℝ, ∃ n : ℕ,
      (li_helix_term σ γ n).re +
      (li_helix_term (1 - σ) (-γ) n).re < M :=
  paired_li_unbounded_off_line σ γ hσ hγ

/-! ## Part 3: RH in the Möbius language -/

/-- **RH ⟹ all Möbius values on the unit circle** (for zeros with Im ≠ 0). -/
theorem rh_implies_moebius_unitary :
    RiemannHypothesis →
    (∀ s : ℂ, riemannZeta s = 0 →
      (¬∃ n : ℕ, s = -2 * (↑n + 1)) → s ≠ 1 →
      s.im ≠ 0 → ‖moebius_helix s.re s.im‖ = 1) := by
  intro rh s hs hnt hp him
  exact (moebius_unit_iff s.re s.im him).mpr (rh s hs hnt hp)

/-- **Möbius unitary ⟹ RH for zeros with Im ≠ 0.**
    The reverse direction: if all Möbius values at zeros with Im ≠ 0 are
    on the unit circle, then those zeros have Re = 1/2.

    For the FULL reverse (including real zeros in (0,1)), one additionally
    needs the classical fact that ζ has no real zeros in (0,1) — this
    follows from ζ(s) < 0 for real s ∈ (0,1), which is not yet in Mathlib. -/
theorem moebius_unitary_implies_rh_nonreal
    (h : ∀ s : ℂ, riemannZeta s = 0 →
      (¬∃ n : ℕ, s = -2 * (↑n + 1)) → s ≠ 1 →
      s.im ≠ 0 → ‖moebius_helix s.re s.im‖ = 1)
    (s : ℂ) (hs : riemannZeta s = 0)
    (hnt : ¬∃ n : ℕ, s = -2 * (↑n + 1)) (hp : s ≠ 1)
    (him : s.im ≠ 0) : s.re = 1/2 :=
  (moebius_unit_iff s.re s.im him).mp (h s hs hnt hp him)

/-! ## Part 4: The Mertens trick feeds the zero-free region -/

/-- **The Mertens positivity from this project + Λ ≥ 0 from Mathlib
    together give the zero-free region Re(s) ≥ 1.**

    The project provides: 3 + 4cos θ + cos 2θ ≥ 0 (`mertens_nonneg`).
    Mathlib provides: Λ(n) ≥ 0 and ζ(s) ≠ 0 for Re(s) ≥ 1.

    These are the same mathematical content: the Mertens inequality
    is the key input to the de la Vallée Poussin proof of the zero-free
    region, which Mathlib formalizes via L-function nonvanishing. -/
theorem mertens_feeds_zero_free :
    -- Our contribution: the Mertens inequality
    (∀ θ : ℝ, 0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ)) ∧
    -- Mathlib's conclusion: zero-free on Re(s) ≥ 1
    (∀ (s₀ : ℂ), 1 ≤ s₀.re → riemannZeta s₀ ≠ 0) :=
  ⟨mertens_nonneg, fun _s hs => riemannZeta_ne_zero_of_one_le_re hs⟩

/-! ## Part 5: The precise remaining gap -/

/-- **Gap statement**: What is proved unconditionally and what remains.

    ✅ PROVED (unconditionally):
    - ζ(s) ≠ 0 for Re(s) ≥ 1 (Mathlib)
    - |1-1/ρ| = 1 ⟺ Re(ρ) = 1/2 (this project)
    - Single-pair Li divergence for |w| > 1 (this project)
    - Mertens positivity 3+4cosθ+cos2θ ≥ 0 (this project)
    - Self-adjoint projections have spectrum ⊂ {0,1} (this project)
    - Functional equation ξ(1-s) = ξ(s) (Mathlib)

    ❌ REMAINING:
    - The global Li criterion: Σ_ρ Re[1-(1-1/ρ)^n] ≥ 0 for all n
    - Constructing a Hilbert-Pólya operator for ζ
    - Full Weil positivity for all test functions
    - Nyman-Beurling approximation property -/
theorem precise_gap_statement :
    -- Unconditional results:
    (∀ s₀ : ℂ, 1 ≤ s₀.re → riemannZeta s₀ ≠ 0) ∧
    (∀ σ γ : ℝ, γ ≠ 0 → (‖moebius_helix σ γ‖ = 1 ↔ σ = 1/2)) ∧
    (∀ σ γ : ℝ, σ ≠ 1/2 → γ ≠ 0 → ∀ M : ℝ, ∃ n : ℕ,
      (li_helix_term σ γ n).re + (li_helix_term (1-σ) (-γ) n).re < M) ∧
    (∀ θ : ℝ, 0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ)) ∧
    (∀ (s' : ℂ), completedRiemannZeta (1-s') = completedRiemannZeta s') :=
  ⟨fun _s hs => riemannZeta_ne_zero_of_one_le_re hs,
   fun σ γ hγ => moebius_unit_iff σ γ hγ,
   fun σ γ hσ hγ => paired_li_unbounded_off_line σ γ hσ hγ,
   mertens_nonneg,
   completedRiemannZeta_one_sub⟩

/-! ## Part 6: Euler product connection -/

/-- The Euler product for ζ exists (from Mathlib). -/
theorem euler_product_for_zeta (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => (1 - (p : ℂ) ^ (-s))⁻¹) (riemannZeta s) :=
  riemannZeta_eulerProduct_hasProd hs

end
