import Mathlib

/-!
# Bridge from Λ ≥ 0 to Zero-Free Regions

This file attempts to close the gap identified in `GapAudit.lean`.

## The gap (restated)

We proved: IF P is an orthogonal projection, THEN ⟪Pv, (I-P)v⟫ = 0.
We need:  The spectral projection onto ζ zeros IS an orthogonal projection.

This is equivalent to: the full Weil quadratic form W(g*g̃) ≥ 0 for all g.

## Strategy

The **unconditional** bridge from Λ ≥ 0 to zero-free regions uses the
de la Vallée Poussin / Mertens trigonometric trick:

  `3 + 4 cos θ + cos 2θ = 2(1 + cos θ)² ≥ 0`

This inequality, combined with Λ(n) ≥ 0, gives:
  `3 log ζ(σ) + 4 Re log ζ(σ+it) + Re log ζ(σ+2it) ≥ 0`  for σ > 1

which implies `|ζ(σ+it)|` can't vanish too fast as σ → 1⁺, giving:
  - ζ(1+it) ≠ 0 for all t ≠ 0 (no zeros on Re(s) = 1)
  - Classical zero-free region: no zeros with Re(s) > 1 - c/log|t|

This is the **strongest unconditional result** that follows from Λ ≥ 0 alone.
It's not RH (which would need Re(s) ≥ 1/2), but it demonstrates that the
positivity of Λ genuinely constrains the zeros.

## What we prove here

1. The trigonometric inequality `3 + 4cos θ + cos 2θ ≥ 0` (unconditional)
2. The stronger form `2(1 + cos θ)² = 3 + 4cos θ + cos 2θ` (identity)
3. The "Weil test": for any weights `a₀, a₁, a₂ ≥ 0` and frequencies,
   the positivity of `Σ aₖ cos(kθ)` constrains what can vanish
4. The unconditional positivity of the Mertens-type sum
5. The precise statement of what remains to close the gap

## Honest status (updated)

The trigonometric trick gives Re(s) > 1 - c/log|t| (proved in ANT textbooks).
RH needs Re(s) ≥ 1/2. The improvement from 1-c/log|t| to 1/2 is the open core.
No amount of abstract projection theory closes it — you need a quantitative
bound on the Weil form, not just its sign.

NOTE (state of the art in Mathlib + this repo): the ANALYTIC 3-4-1 weld is DONE in Mathlib —
`DirichletCharacter.norm_LFunction_product_ge_one` (the dlVP product `‖L(χ⁰)³L(χ)⁴L(χ²)‖ ≥ 1`),
the pole bound `LFunctionTrivChar_isBigO_near_one_horizontal`, and the edge consequence
`LFunction_ne_zero_of_one_le_re` (no zeros on Re = 1). This file's Parts 1–3 are the elementary
real-variable shadow of those. The repo's quantitative composite lives in
`HelixZeroFreeStep.zero_repulsion_near_one`; the interior REGION (1 − β ≥ c/log) is still not
formalized anywhere — its missing ingredients are the edge growth bound and the mean-value step
(see `HelixZeroFreeStep`).
-/

noncomputable section

open Real

/-! ## Part 1: The de la Vallée Poussin trigonometric inequality -/

/-
The Mertens/de la Vallée Poussin identity:
    `3 + 4 cos θ + cos(2θ) = 2(1 + cos θ)²`.
    This is the algebraic identity, not an inequality.
-/
theorem mertens_identity (theta : ℝ) :
    3 + 4 * Real.cos theta + Real.cos (2 * theta) =
    2 * (1 + Real.cos theta) ^ 2 := by
  rw [ Real.cos_two_mul ] ; ring;

/-
The Mertens/de la Vallée Poussin positivity:
    `3 + 4 cos θ + cos(2θ) ≥ 0`.
    This is the key inequality that bridges Λ ≥ 0 to zero-free regions.
    It follows from the identity since `2(1 + cos θ)² ≥ 0`.
-/
theorem mertens_nonneg (theta : ℝ) :
    0 ≤ 3 + 4 * Real.cos theta + Real.cos (2 * theta) := by
  rw [ Real.cos_two_mul ] ; nlinarith [ Real.cos_sq' theta ]

/-
The Mertens inequality is tight: equality iff `cos θ = -1`, i.e., `θ = π mod 2π`.
-/
theorem mertens_eq_zero_iff (theta : ℝ) :
    3 + 4 * Real.cos theta + Real.cos (2 * theta) = 0 ↔
    Real.cos theta = -1 := by
  constructor <;> intro h <;> rw [ Real.cos_two_mul ] at * <;> nlinarith

/-! ## Part 2: The weighted positivity for Dirichlet series -/

/-
For any function `a : ℕ → ℝ` with `a(n) ≥ 0` for all n, and any `θ : ℝ`,
    the weighted sum `3 Σ a(n) + 4 Σ a(n)cos(nθ) + Σ a(n)cos(2nθ) ≥ 0`.

    This follows from `(3 + 4cos(nθ) + cos(2nθ)) · a(n) ≥ 0` for each n,
    since each factor is nonneg (Mertens) and a(n) ≥ 0.

    When `a(n) = Λ(n)/n^σ`, this gives the classical bound on ζ.
-/
theorem weighted_mertens_nonneg (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (theta : ℝ) (S : Finset ℕ) :
    0 ≤ ∑ n ∈ S, a n * (3 + 4 * Real.cos (n * theta) +
      Real.cos (2 * n * theta)) := by
  exact Finset.sum_nonneg fun n _ => mul_nonneg ( ha n ) ( by simpa only [ mul_assoc ] using mertens_nonneg ( n * theta ) )

/-
Each term in the weighted sum is nonneg.
-/
theorem weighted_mertens_term_nonneg (a_val : ℝ) (ha : 0 ≤ a_val) (theta : ℝ) (n : ℕ) :
    0 ≤ a_val * (3 + 4 * Real.cos (↑n * theta) + Real.cos (2 * ↑n * theta)) := by
  exact mul_nonneg ha ( by rw [ mul_assoc ] ; exact mertens_nonneg _ )

/-! ## Part 3: The Von Mangoldt specialization -/

/-
Specializing to `a(n) = Λ(n)`: the Mertens sum with von Mangoldt weights
    is nonneg. This is the prime-side input to the classical zero-free region.

    `Σ_{n ∈ S} Λ(n) · (3 + 4cos(n·t) + cos(2n·t)) ≥ 0`
-/
theorem vonmangoldt_mertens_nonneg (t : ℝ) (S : Finset ℕ) :
    0 ≤ ∑ n ∈ S, ArithmeticFunction.vonMangoldt n *
      (3 + 4 * Real.cos (↑n * t) + Real.cos (2 * ↑n * t)) := by
  exact weighted_mertens_nonneg _ ( fun n => by exact ( ArithmeticFunction.vonMangoldt_nonneg ) ) t S

/-
Expanding the Mertens sum into three Dirichlet-type sums:
    `3 · Σ Λ(n) + 4 · Σ Λ(n)cos(nt) + Σ Λ(n)cos(2nt) ≥ 0`

    In the language of ζ: this becomes
    `3 · (-Re ζ'/ζ(σ)) + 4 · (-Re ζ'/ζ(σ+it)) + (-Re ζ'/ζ(σ+2it)) ≥ 0`
    which gives the classical bound `ζ(σ)^3 |ζ(σ+it)|^4 |ζ(σ+2it)| ≥ 1`.
-/
theorem mertens_three_sums (t : ℝ) (S : Finset ℕ) :
    ∑ n ∈ S, ArithmeticFunction.vonMangoldt n *
      (3 + 4 * Real.cos (↑n * t) + Real.cos (2 * ↑n * t)) =
    3 * ∑ n ∈ S, ArithmeticFunction.vonMangoldt n +
    4 * ∑ n ∈ S, ArithmeticFunction.vonMangoldt n * Real.cos (↑n * t) +
    ∑ n ∈ S, ArithmeticFunction.vonMangoldt n * Real.cos (2 * ↑n * t) := by
  simp +decide only [mul_add, mul_left_comm, Finset.sum_add_distrib, Finset.mul_sum _ _ _];
  grind +locals

/-! ## Part 4: The precise gap statement -/

/-- **The gap, stated precisely.**

    What we have (unconditionally):
    - Λ(n) ≥ 0
    - The Mertens inequality 3 + 4cos θ + cos 2θ ≥ 0
    - These together give: no zeros of ζ on Re(s) = 1

    What we need for RH:
    - The full Weil positivity: for ALL test functions h ≥ 0 (positive definite),
      the explicit formula sum Σ_ρ h(ρ) ≥ (explicit terms involving Λ and arch)

    The Mertens trick is a SPECIFIC choice of test function:
      h(s) = 3 + 4·x^{it·Im(s)} + x^{2it·Im(s)}
    which only tests a 3-dimensional subspace of test functions.

    RH requires positivity for ALL test functions — an infinite-dimensional
    condition. The Mertens trick gives the BEST result from a finite-dimensional
    test, but finite-dimensional tests can only reach Re(s) > 1 - c/log|t|,
    never Re(s) ≥ 1/2.

    This is the fundamental reason the gap persists: we're testing with
    too few functions. The full Weil positivity requires testing with all
    of L², not just trigonometric polynomials.

    Stated formally as a placeholder definition: -/
def weil_positivity_full : Prop :=
  ∀ (h : ℝ → ℝ),
    (∀ x, 0 ≤ h x) →  -- h is nonneg
    (∀ x, h x = h (-x)) →  -- h is even
    -- Then the Weil sum is nonneg:
    -- (This is a placeholder — the actual Weil formula involves ζ zeros,
    --  Γ factors, and the Mellin transform of h, which requires the
    --  analytic theory of ζ that Mathlib doesn't have.)
    True  -- placeholder for the actual inequality

/-- What the Mertens trick proves: a specific 3-term test gives nonneg.
    This is a theorem, not a conjecture. -/
theorem mertens_specific_test (theta : ℝ) :
    0 ≤ 3 + 4 * Real.cos theta + Real.cos (2 * theta) :=
  mertens_nonneg theta

/-- The honest conclusion: the Mertens trick + Λ ≥ 0 gives a zero-free
    region strictly larger than Re(s) > 1, but strictly smaller than
    Re(s) ≥ 1/2.

    In our projection language: the Mertens trick proves that the projection
    loss is positive for a FINITE-DIMENSIONAL subspace of test signals.
    RH would require positivity for the FULL function space.

    The projection framework correctly identifies the structure
    (self-adjoint + idempotent ⟹ orthogonal decomposition), but the
    gap between "positive on finitely many tests" and "positive on all tests"
    is the irreducible hard core of RH. -/
theorem zero_free_from_mertens :
    -- The Mertens trick gives: for all θ,
    (∀ theta : ℝ, 0 ≤ 3 + 4 * Real.cos theta + Real.cos (2 * theta)) ∧
    -- Combined with Λ ≥ 0:
    (∀ n : ℕ, (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt n) ∧
    -- Together these are the inputs to the classical zero-free region proof.
    -- The analytic weld of these inputs IS in Mathlib now
    -- (`DirichletCharacter.norm_LFunction_product_ge_one`, `LFunction_ne_zero_of_one_le_re`);
    -- the interior region (Re(s) > 1 - c/log|t|) remains unformalized — see
    -- `HelixZeroFreeStep.zero_repulsion_near_one` for the quantitative composite.
    True := by
  exact ⟨mertens_nonneg, fun n => ArithmeticFunction.vonMangoldt_nonneg, trivial⟩

end