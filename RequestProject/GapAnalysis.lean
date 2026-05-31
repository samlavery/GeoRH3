import Mathlib
import RequestProject.HelixRoundTrip
import RequestProject.ForcedAlignment
import RequestProject.ConcreteOperators
import RequestProject.BridgeToZeroFree

/-!
# Gap Analysis: Geometric 1/2 vs RH 1/2, and Paths Forward

## Executive summary

This file performs a rigorous audit of every appearance of `1/2` in the project,
classifies each as "geometric" (unconditional) or "RH-dependent" (would need
proving), identifies the precise logical gaps, and explores paths to close them.

## Classification of all 1/2 instances

### ✅ Geometric 1/2 (unconditionally proved, no RH needed)

These are consequences of the algebraic fact that 1/2 is the fixed point
of the involution σ ↦ 1−σ:

1. `moebius_unit_iff`: |1−1/ρ| = 1 ↔ Re(ρ) = 1/2
   **Source**: Pure algebra. The circle |1−1/z| = 1 in ℂ is exactly
   the vertical line Re(z) = 1/2 (excluding z=0). No number theory.

2. `radial_loss_zero_iff`: (σ − 1/2) = 0 ↔ σ = 1/2
   **Source**: Tautology. The "radial loss" is DEFINED as σ − 1/2.

3. `amgm_reciprocal` / `mirror_pair_defect`: r + 1/r ≥ 2, equality iff r = 1
   **Source**: Pure AM-GM inequality. Applied to r = ‖w(ρ)‖, this says
   the defect vanishes iff ‖w‖ = 1, which by (1) is iff σ = 1/2.

4. `moebius_product_one`: w(ρ)·w(1−ρ) = 1
   **Source**: Direct algebraic computation. The functional equation's
   involution ρ ↦ 1−ρ maps w = 1−1/ρ to 1/w.

5. `critical_line_iff_bounded_li`: For a SINGLE pair (σ,γ) and (1−σ,−γ),
   σ = 1/2 ↔ Re[1−w^n] + Re[1−w̄^n] is bounded below.
   **Source**: Cofinal recurrence on the unit circle + AM-GM.

### ⚠️  RH-Dependent 1/2 (NOT proved, would require RH or equivalent)

These are claims that would need the actual zeta zeros to satisfy σ = 1/2:

A. "The combined loss IS the explicit formula": (I−G₂∘G₁)x = Σ_ρ x^ρ/ρ.
   **Status**: Stated in comments only, never formalized. This would require
   defining G₁, G₂ as actual operators on a function space containing
   the prime counting function, and proving the identification.

B. "The self-adjoint projection structure forces all spectral content to
   satisfy σ = 1/2."
   **Status**: The abstract theorem is proved (self-adjoint projections
   have spectrum ⊂ {0,1}), but the identification of zeta zeros as
   eigenvalues of such a projection is not established.

C. "The Li coefficients of ζ are bounded below."
   **Status**: This IS the Riemann Hypothesis (Li's criterion, 1997).
   The project proves it for a single pair; RH requires it for the
   sum over ALL pairs simultaneously.

## The precise logical gap

The project proves two types of theorems:

**Type 1 (Abstract)**: "If P is a self-adjoint projection, then ⟪Px, (I−P)x⟫ = 0."
  → TRUE, fully proved, no gap.

**Type 2 (Concrete)**: "For a complex number w = 1−1/ρ, |w| = 1 iff σ = 1/2."
  → TRUE, fully proved, no gap.

**The gap**: There is no theorem connecting Type 1 to Type 2 via the actual
Riemann zeta function. The project never defines ζ(s), never constructs
the explicit formula, and never identifies any specific operator whose
eigenvalues are the zeta zeros.

The comments bridge this gap informally ("the loss IS the explicit formula"),
but this bridge is never formalized. This informal bridge is doing 100% of
the work of the Riemann Hypothesis.

## Counter-argument: why can't we just prove "no offline zeros"?

The abstract machinery CANNOT rule out offline zeros because:

1. **The operators G₁, G₂ are not connected to ζ.** The `apply_G1`, `apply_G2`
   in ConcreteOperators.lean are coordinate projections on a 3-tuple.
   This 3-tuple is defined by the user — it has `radial := σ − 1/2` BY
   CONSTRUCTION. So `radial_loss = 0 ↔ σ = 1/2` is a tautology.

2. **The Li boundedness is per-pair, not global.** The theorem
   `critical_line_iff_bounded_li` shows that for a SINGLE pair {ρ, 1−ρ},
   the paired Li terms are bounded iff σ = 1/2. But Li's criterion for RH
   requires λ_n = Σ_{ALL ρ} [1 − (1−1/ρ)^n] ≥ 0, which involves an
   infinite sum over all zeros. Individual pair boundedness doesn't imply
   sum boundedness (the sum could diverge even if each pair is bounded).

3. **No Hilbert-Pólya operator is constructed.** The self-adjoint projection
   theorems are about abstract operators satisfying given axioms. No specific
   operator on a specific Hilbert space is constructed whose spectrum is
   {γ : ζ(1/2 + iγ) = 0}. Constructing such an operator is the
   Hilbert-Pólya conjecture, which is open.

## Paths that could close the gap

We formalize the precise mathematical statements that would need to
be proved to close the gap, organized by approach.
-/

noncomputable section

open Complex Real

/-! ## Part 1: Audit — demonstrating that geometric 1/2 is unconditional -/

/-- The geometric 1/2: fixed point of the involution σ ↦ 1−σ.
    This is pure algebra, no number theory. -/
theorem geometric_half_is_fixed_point : (1 : ℝ) - (1/2 : ℝ) = 1/2 := by norm_num

/-- The Möbius characterization uses ONLY the involution, not RH.
    We can verify this by noting it holds for ANY complex number,
    not just zeta zeros. -/
theorem moebius_works_for_any_point (σ γ : ℝ) (hγ : γ ≠ 0) :
    (‖moebius_helix σ γ‖ = 1 ↔ σ = 1/2) :=
  moebius_unit_iff σ γ hγ

/-- Example: σ = 0.3 is off-line, and the Möbius value confirms it. -/
theorem example_off_line :
    (0.3 : ℝ) ≠ 1/2 := by norm_num

/-- The Li criterion for a single pair is NOT the same as Li's criterion for ζ.
    Li's actual criterion: RH ↔ λ_n ≥ 0 for all n, where
    λ_n = Σ_{ALL nontrivial zeros ρ} [1 − (1−1/ρ)^n].

    Our `critical_line_iff_bounded_li` only addresses a SINGLE pair.
    The distinction is crucial. -/

-- A single pair's Li terms being bounded does NOT imply the full sum is bounded.
-- Here's a concrete illustration: individual bounded sequences can sum to
-- an unbounded sequence.
theorem individual_bounded_sum_unbounded :
    -- Each term is bounded
    (∀ _k : ℕ, ∀ _n : ℕ, |((1 : ℝ))| ≤ 1) ∧
    -- But their sum over k from 0 to N grows without bound
    (∀ M : ℝ, ∃ N : ℕ, M < (N : ℝ)) := by
  refine ⟨fun _ _ => by norm_num, fun M => ⟨⌈M⌉₊ + 1, ?_⟩⟩
  push_cast
  linarith [Nat.le_ceil M]

/-! ## Part 2: The gap — what would need to be true -/

/-- **Gap Statement 1**: The "operator identification" gap.
    To close the gap, one would need to construct a specific Hilbert space
    and a specific self-adjoint operator T on it such that:
    - T has discrete spectrum {γ_n} where ζ(1/2 + iγ_n) = 0
    - T is bounded below (or: I−T is a projection)

    This is the Hilbert-Pólya conjecture. We state it as a Prop. -/
def HilbertPolyaOperatorExists : Prop :=
  ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H)
    (T : H →ₗ[ℝ] H),
    -- T is self-adjoint
    (∀ x y : H, @inner ℝ H _ (T x) y = @inner ℝ H _ x (T y)) ∧
    -- T's spectrum encodes the zeta zeros
    -- (placeholder: we can't state this without defining ζ in Lean)
    True

/-- **Gap Statement 2**: The "explicit formula as operator loss" gap.
    The claim: the deviation ψ(x) − x = −Σ_ρ x^ρ/ρ − log(2π) − (1/2)log(1−x^{−2})
    equals the loss of a self-adjoint projection.

    This requires:
    (a) Defining ψ(x) = Σ_{n≤x} Λ(n) (the Chebyshev function)
    (b) The explicit formula (analytic number theory, not in Mathlib)
    (c) Identifying the RHS as (I−P)f for some projection P and signal f

    We can state what this would look like abstractly: -/
def ExplicitFormulaIsProjectionLoss : Prop :=
  ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H)
    (P : H →ₗ[ℝ] H) (_ψ_signal : H),
    -- P is a self-adjoint projection
    (∀ x y : H, @inner ℝ H _ (P x) y = @inner ℝ H _ x (P y)) ∧
    (∀ x : H, P (P x) = P x) ∧
    -- The loss of ψ equals the explicit formula sum
    -- (placeholder: actual ζ zeros not definable in current Mathlib)
    True

/-- **Gap Statement 3**: Li's criterion (the real one).
    RH is equivalent to: for all n ≥ 1,
    λ_n = Σ_ρ [1 − (1−1/ρ)^n] ≥ 0
    where the sum is over ALL nontrivial zeros of ζ.

    Our project proves the single-pair version. The full version requires
    the sum over infinitely many zeros to converge and be nonneg. -/
def LiCriterionFull : Prop :=
  -- Placeholder: requires defining ζ and its zeros
  -- The actual statement: ∀ n ≥ 1, Σ_ρ Re[1 − (1−1/ρ)^n] ≥ 0
  True  -- can't state without ζ in Lean

/-! ## Part 3: Why the abstract framework can't close the gap alone -/

/-- **The tautology trap**: The HelixVector construction defines
    `radial := σ − 1/2`, so `radial = 0 ↔ σ = 1/2` is definitional.

    This does NOT constrain what σ actually is for zeta zeros.
    It's like defining `cold := temperature − 0` and concluding
    "cold = 0 iff temperature = 0" — true but vacuous.

    We can demonstrate this by showing the same framework
    "proves" σ = 7 for a different embedding: -/
def silly_embed (σ γ x : ℝ) : HelixVector where
  proj := x ^ σ * Real.cos (γ * Real.log x)
  angular := x ^ σ * Real.sin (γ * Real.log x)
  radial := σ - 7  -- different "target"

theorem silly_radial_zero_iff (σ γ x : ℝ) :
    (silly_embed σ γ x).radial = 0 ↔ σ = 7 := by
  simp [silly_embed]; constructor <;> intro h <;> linarith

/-- The choice of `radial := σ − 1/2` encodes the ANSWER, not derives it.
    Changing the target to any value c gives `radial = 0 ↔ σ = c`. -/
def parametric_embed (c σ γ x : ℝ) : HelixVector where
  proj := x ^ σ * Real.cos (γ * Real.log x)
  angular := x ^ σ * Real.sin (γ * Real.log x)
  radial := σ - c

theorem parametric_radial_zero_iff (c σ γ x : ℝ) :
    (parametric_embed c σ γ x).radial = 0 ↔ σ = c := by
  simp [parametric_embed]; constructor <;> intro h <;> linarith

/-! ## Part 4: What IS genuinely proved (the non-trivial content) -/

/-- The genuinely nontrivial content of the project, stated precisely:

    **Theorem (Cofinal Li divergence for single pairs)**:
    For ANY complex number w with |w| > 1, the sequence Re(w^n) is
    unbounded above. Therefore Re(1 − w^n) is unbounded below.

    Combined with the Möbius reciprocal property w·w̄ = 1:
    if σ ≠ 1/2, then one of {w(ρ), w(1−ρ)} has |w| > 1,
    so the paired Li terms diverge to −∞.

    This is a genuine theorem about single pairs of complex numbers.
    It does NOT, by itself, say anything about the Riemann zeta function.

    To connect to ζ, one would need to show that the INFINITE SUM
    Σ_ρ Re[1 − w(ρ)^n] over all zeros ρ is bounded below. This
    requires controlling the cancellation between infinitely many
    divergent (off-line) and convergent (on-line) terms — which is
    exactly the content of RH. -/
theorem genuine_content_summary :
    -- (1) Cofinal recurrence: |w| > 1 ⟹ Re(w^n) unbounded above
    (∀ w : ℂ, 1 < ‖w‖ → ∀ C : ℝ, ∃ n : ℕ, C < (w ^ n).re) ∧
    -- (2) Möbius reciprocal: norms are reciprocal
    (∀ σ γ : ℝ, γ ≠ 0 →
      ‖moebius_helix σ γ‖ * ‖moebius_helix (1-σ) (-γ)‖ = 1) ∧
    -- (3) Single-pair characterization: σ = 1/2 iff paired Li bounded
    (∀ σ γ : ℝ, γ ≠ 0 →
      (σ = 1/2 ↔ ∃ M : ℝ, ∀ n : ℕ,
        M ≤ (li_helix_term σ γ n).re +
            (li_helix_term (1-σ) (-γ) n).re)) ∧
    -- (4) Mertens positivity: 3 + 4cosθ + cos2θ ≥ 0
    (∀ θ : ℝ, 0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ)) :=
  ⟨re_pow_unbounded_above,
   moebius_norm_product_one,
   critical_line_iff_bounded_li,
   mertens_nonneg⟩

/-! ## Part 5: The three paths forward and what each requires -/

/-- **Path 1: Full Weil Explicit Formula Positivity**

    The Weil explicit formula says: for suitable test functions h,
    Σ_ρ h̃(ρ) = h(0) + h(1) − Σ_p Σ_k (log p)/p^{k/2} · h̃(k·log p) + (arch terms)

    RH is equivalent to: for all h with h̃ ≥ 0 (positive definite),
    the LHS is ≥ 0.

    The Mertens trick tests with h̃(t) = 3 + 4cos(αt) + cos(2αt),
    which is ≥ 0 by AM-GM. This gives the zero-free region near σ = 1.

    For RH, one needs positivity for ALL positive definite h, which
    is an infinite-dimensional condition. The Mertens trick is a
    3-dimensional test — finite-dimensional tests can only reach
    σ > 1 − c/log|t|, never σ ≥ 1/2.

    **Requirements**:
    - Analytic continuation of ζ (not in Mathlib)
    - Functional equation (not in Mathlib)
    - Explicit formula (not in Mathlib)
    - Positivity of Weil form for all test functions (this IS RH) -/
def path1_weil_positivity : Prop :=
  -- For all positive-definite test functions h:
  -- Σ_ρ h̃(ρ) ≥ 0
  -- This is equivalent to RH (by Weil, 1952)
  True  -- placeholder

/-- **Path 2: Hilbert-Pólya Operator Construction**

    Construct a self-adjoint operator T on L²(0,∞) (or similar) such that
    the eigenvalues of T are {γ : ζ(1/2 + iγ) = 0}.

    The self-adjointness of T immediately gives γ ∈ ℝ, hence all zeros
    on the critical line.

    This is the Hilbert-Pólya conjecture (1914/1950s). Notable approaches:
    - Berry-Keating (1999): T = xp + px where p = −i(d/dx)
    - Connes (1999): via noncommutative geometry and adeles
    - Bender-Brody-Müller (2017): via PT-symmetric quantum mechanics

    **Requirements**:
    - Construct the specific operator T
    - Prove T is self-adjoint (or essentially self-adjoint)
    - Prove the spectral identification (eigenvalues = zeros)
    - Each of these is a major open problem -/
def path2_hilbert_polya : Prop :=
  HilbertPolyaOperatorExists

/-- **Path 3: Nyman-Beurling-Báez-Duarte Approach**

    RH is equivalent to: the constant function 1 is in the closure
    (in the L²(0,∞) norm weighted by x^{−2}) of the subspace spanned by
    {ρ_α(x) = {α/x} − α{1/x} : 0 < α ≤ 1}
    where {·} denotes fractional part.

    **Requirements**:
    - Define the weighted L² space
    - Define the ρ_α functions
    - Show the approximation property (this IS RH)

    This approach is attractive because it's purely real-analytic
    (no complex analysis needed) and connects to the "projection"
    framework: RH says the projection of 1 onto the span of the ρ_α
    has zero loss. -/
def path3_nyman_beurling : Prop :=
  -- 1 ∈ closure(span{ρ_α : 0 < α ≤ 1}) in L²((0,∞), x^{−2} dx)
  True  -- placeholder

/-! ## Part 6: Concrete demonstration that individual pair arguments fail -/

/-- **Why individual pair boundedness doesn't give global boundedness.**

    Consider N pairs, each with σ = 1/2 (on-line). Each pair's Li term
    is in [0, 2] (by `li_re_nonneg` and `li_re_le_two`).

    The sum over N pairs is in [0, 2N], so it IS bounded below by 0.
    But for INFINITELY MANY pairs, we need the sum to converge — which
    requires the individual terms to decay. On the line, the terms
    Re[1 − e^{iγ_n·log(k)}] don't decay, so convergence of the
    Li coefficients is a nontrivial analytic fact.

    Key point: even for on-line zeros, the convergence of
    λ_n = Σ_ρ Re[1 − w(ρ)^n]
    requires specific information about the DISTRIBUTION of the γ_n
    (essentially the density of zeros), not just the individual pair
    property. -/
theorem on_line_pairs_bounded (γ : ℝ) (n : ℕ) :
    0 ≤ (li_helix_term (1/2) γ n).re :=
  li_helix_nonneg_on_line γ n

/-- Each on-line pair contributes at most 2 to the Li sum. -/
theorem on_line_pairs_le_two (γ : ℝ) (n : ℕ) :
    (li_helix_term (1/2) γ n).re ≤ 2 := by
  unfold li_helix_term
  apply li_re_le_two
  by_cases hγ : γ = 0
  · subst hγ; simp [moebius_helix]; norm_num [Complex.norm_def, Complex.normSq]
  · exact le_of_eq ((moebius_unit_iff (1/2) γ hγ).mpr rfl)

/-- **Sum over N on-line pairs grows like N** (at worst).
    This shows why infinitely many pairs require care. -/
theorem li_sum_grows_linearly (zeros : Finset (ℝ × ℝ))
    (h_online : ∀ z ∈ zeros, z.1 = 1/2) (n : ℕ) :
    (li_trace zeros n).re ≤ 2 * zeros.card := by
  simp only [li_trace, spectral_value]
  rw [Complex.re_sum]
  calc ∑ z ∈ zeros, (1 - moebius_helix z.1 z.2 ^ n).re
      ≤ ∑ z ∈ zeros, (2 : ℝ) := by
        apply Finset.sum_le_sum
        intro z hz
        rw [h_online z hz]
        exact on_line_pairs_le_two z.2 n
    _ = 2 * zeros.card := by simp [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-! ## Part 7: Summary of findings -/

/-- **Final summary of the gap analysis.**

    ✅ CLEAN (geometric 1/2, no contamination):
    - moebius_unit_iff: |1−1/ρ| = 1 ↔ σ = 1/2 (algebra of the involution)
    - moebius_product_one: w(ρ)·w(1−ρ) = 1 (FE as reciprocal)
    - mirror_pair_defect: (1−r)+(1−1/r) = −(r−1)²/r (AM-GM)
    - li_helix_nonneg_on_line: Re[1−w^n] ≥ 0 when |w|=1 (triangle inequality)
    - re_pow_unbounded_above: Re(w^n) unbounded for |w|>1 (cofinal recurrence)
    - critical_line_iff_bounded_li: single-pair characterization

    ✅ CLEAN (abstract Hilbert space, no number theory):
    - All theorems in CombinedLoss.lean, GreenHelmholtz.lean,
      ProjectionSelfAdjoint.lean, HelixSelfDual.lean
    - These are about abstract operators satisfying axioms

    ⚠️  TAUTOLOGICAL (encodes σ=1/2, doesn't derive it):
    - radial_loss_zero_iff: defined radial := σ−1/2, so trivially = 0 ↔ σ=1/2
    - spectral_geometric_match: chains tautology to moebius_unit_iff
    - The HelixVector embedding chooses the target value 1/2

    ❌ UNPROVED GAP (would require RH or equivalent):
    - No connection between abstract operators and ζ(s)
    - No construction of a Hilbert-Pólya operator
    - No proof that the infinite Li sum is bounded below
    - The explicit formula is never formalized
    - "The loss IS the explicit formula" is commentary, not a theorem

    The project's abstract theorems are correct and genuinely nontrivial.
    The cofinal recurrence argument (`re_pow_unbounded_above`) is elegant.
    But the bridge from "single-pair Li characterization" to "all zeros
    on the line" requires the full analytic theory of ζ, which is not
    present. This bridge IS the Riemann Hypothesis. -/
theorem gap_analysis_clean : True := trivial

end
