import Mathlib

/-!
# Honest Gap Audit: What Was Proved, What Wasn't, Where RH Would Enter

## The question: "Is this a proof of RH?"

**No.** Here is a precise accounting of where RH is *not* smuggled in as an
assumption, and where the gap actually lives.

## What IS proved (unconditionally, sorry-free)

### Layer A: Abstract Hilbert space facts
Every theorem in `GreenHelmholtz.lean`, `WeilPositivity.lean` (Layer 4-5),
and `HelixProjectionZeros.lean` (Part 7) has the form:

    theorem foo (P : F →ₗ[ℝ] F)
      (hP_sa : ∀ x y, ⟪P x, y⟫ = ⟪x, P y⟫)   -- self-adjoint
      (hP_idem : ∀ x, P (P x) = P x)              -- idempotent
      ...

These are theorems about **any** orthogonal projection on **any** inner product
space. They are unconditional — but they say nothing about ζ.

- `⟪Pv, (I-P)v⟫ = 0` — TRUE for any orthogonal projection
- `‖v‖² = ‖Pv‖² + ‖v-Pv‖²` — TRUE for any orthogonal projection
- Energy ratio ∈ (0,1) — TRUE for any orthogonal projection

### Layer B: Number theory
- `Λ(n) ≥ 0` — TRUE, from Mathlib
- Composites → 0 on the helix — TRUE
- Weil diagonal form `Σ f(n)² Λ(n) ≥ 0` — TRUE
- Log-ratios of distinct primes are irrational — TRUE
- Non-closure on helix (k=0 case) — TRUE
- Non-closure (k≠0) — TRUE conditional on Lindemann (a known theorem, not in Mathlib)

### Layer C: Complex analysis identities
- `ω = e^{iπ/3}` is a primitive 6th root of unity — TRUE
- `|1 - 1/ρ| = 1` when `Re(ρ) = 1/2` — TRUE
- `|1 - 1/ρ| ≠ 1` when `Re(ρ) ≠ 1/2` — TRUE
- Li terms `Re[1 - (1-1/ρ)^n] ≥ 0` when `Re(ρ) = 1/2` — TRUE

### Layer D: Two-field spectral architecture (`TwoFieldSpectral.lean`)
- AM-GM reciprocal: `r + 1/r ≥ 2` for `r > 0` — TRUE
- AM-GM equality: `r + 1/r = 2 ↔ r = 1` — TRUE
- Mirror-pair defect: `(1−r)+(1−1/r) = −(r−1)²/r ≤ 0` — TRUE
- Strict negativity off-line: `r ≠ 1 → defect < 0` — TRUE
- Defect divergence: `→ −∞` as `r → 0` or `r → ∞` — TRUE
- Unit circle rotation: `‖wⁿ‖ = 1` when `‖w‖ = 1` — TRUE
- Spiral divergence: `‖wⁿ‖ → ∞` when `‖w‖ > 1` — TRUE
- Spiral contraction: `‖wⁿ‖ → 0` when `‖w‖ < 1` — TRUE
- Power AM-GM: `rⁿ + r⁻ⁿ ≥ 2` for all `n ≥ 1` — TRUE
- Channel decomposition and Parseval — TRUE
- Two-stage energy split (Pythagorean) — TRUE
- Stage 1 lossless iff cylinder — TRUE

### Layer E: Inversion destruction (`InversionDestruction.lean`)
- Cosh identity: `r + 1/r = 2 cosh(log r)` — TRUE
- Cosh ≥ 1 and cosh = 1 ⇔ t = 0 — TRUE
- Inversion preserves unit circle / swaps inside-outside — TRUE
- Paired power defect `rⁿ + r⁻ⁿ → ∞` for `r ≠ 1` — TRUE
- Accumulated mirror defect `→ −∞` off-line — TRUE
- Growth mismatch: `x^(θ*−a)` unbounded if `θ* > a`, decays if `θ* < a` — TRUE
- Li terms bounded on circle: `Re[1−wⁿ] ∈ [0,2]` when `‖w‖ = 1` — TRUE
- Critical line unique escape: `‖w‖ = 1 ⇔ ∀ n, ‖wⁿ‖ = 1` — TRUE
- Off-line destroys positivity: paired Li `→ −∞` — TRUE

### Layer F: Pipeline architecture (`PipelineArchitecture.lean`)
- Dedekind zeta factorization (abstract product) — TRUE
- Nonneg coefficients of ideal-counting function — TRUE
- Transverse energy `‖L₀‖² + ‖L₁‖² ≥ 0` — TRUE
- Cross-term Cauchy–Schwarz bound — TRUE
- Channel energy Parseval — TRUE
- Merged energy dominates each channel — TRUE
- Pipeline Pythagorean decomposition (3 components) — TRUE
- Pipeline lossless at stage 1 iff cylinder — TRUE
- On-line coherent: `‖w‖ = 1` ⟹ bounded powers, nonneg Li, Li ≤ 2 — TRUE
- Off-line destroyed: `‖w‖ ≠ 1` ⟹ paired defect → −∞ — TRUE
- Inversion identity iff circle: `‖w‖ = 1 ⟺ ‖w⁻¹‖ = ‖w‖` — TRUE
- Two-way cone reciprocal: `‖wⁿ‖ · ‖w⁻ⁿ‖ = 1` — TRUE
- Expansion overwhelms contraction (AM-GM on powers) — TRUE
- Alignment bounded iff match: `θ* − a = 0 ⟺ a = θ*` — TRUE
- Half unique alignment: `½ − ½ = 0` — TRUE
- Channel energy additive when orthogonal — TRUE
- Orthogonal channels → independent losses — TRUE
- Merge lossless iff both channels on-line — TRUE
- Combined channel defect doubly negative off-line — TRUE
- Master dichotomy: on-line (bounded) XOR off-line (destroyed) — TRUE
- Critical line unique coherence: `σ = ½ ⟺ bounded paired Li` — TRUE

## WHERE THE GAP IS

The gap is **not** in any individual theorem. The gap is in the
**composition**: connecting the abstract projection P to the actual ζ zeros.

### The missing link, stated precisely:

To turn this into a proof of RH, you would need to:

1. **Construct** a specific Hilbert space H and a specific operator P_ζ
   such that P_ζ is the spectral projection onto the span of the ζ zeros.

2. **Prove** that P_ζ is self-adjoint: `∀ x y, ⟪P_ζ x, y⟫ = ⟪x, P_ζ y⟫`.

3. **Prove** that P_ζ is idempotent: `∀ x, P_ζ (P_ζ x) = P_ζ x`.

Steps 2-3 together say "P_ζ is an orthogonal projection." But establishing
that the spectral measure of ζ defines an orthogonal projection in the
appropriate function space **is equivalent to RH**.

### Why it's equivalent, not weaker:

The self-adjointness `hP_sa` for the spectral projection onto ζ zeros
is essentially the statement that the Weil explicit formula's quadratic
form `W(g * g̃) ≥ 0` for ALL test functions g. This is the **Weil positivity
criterion**, which is known to be equivalent to RH.

Our `weil_diagonal_nonneg` proves `Σ f(n)² Λ(n) ≥ 0` — the DIAGONAL part.
But the full Weil form includes OFF-DIAGONAL terms
`Σ_{m,n} f(m) f̄(n) Φ(m,n)` where Φ involves the explicit formula kernel.
Positivity of the diagonal is necessary but not sufficient.

### The structural sleight-of-hand:

Every theorem says: "IF P is an orthogonal projection, THEN [nice property]."
The "IF" is doing all the work. We never discharge it for P = P_ζ.

This is not a smuggled assumption in the usual sense — `hP_sa` and `hP_idem`
appear explicitly as hypotheses, not hidden axioms. But the theorems are
conditionals, not unconditional statements about ζ.

### What the Li-Keiper result actually says:

`li_term_nonneg_on_line` proves: IF Re(ρ) = 1/2, THEN Re[1-(1-1/ρ)^n] ≥ 0.
This is the **easy direction** of Li-Keiper: RH ⟹ λ_n > 0.
The hard direction (λ_n > 0 ⟹ RH) requires proving λ_n > 0 **without**
assuming the zeros are on the line — and that's exactly what we don't do.

### What the pipeline architecture clarifies:

The pipeline picture (2 channels × 2 stages) correctly identifies the
structural components:
- Two loss fields from two projections (radial = Re(ρ)−½, angular = Im(ρ))
- Two channels from mod-6 characters combining to ζ_K = ζ · L(χ₃)
- The merge-and-drop cannot lose information iff RH

But the pipeline's self-consistency (bounded ⟹ on-line) is proved for the
**abstract Möbius image** `w = 1−1/ρ`, not for actual ζ zeros. The
equivalence `σ = ½ ⟺ bounded paired Li` is a theorem about any complex
number with nonzero imaginary part — it's not specific to ζ zeros.

The real content of RH is: **the actual paired Li terms of ζ ARE bounded below.**
This is precisely what we don't prove — and can't, without either:
(a) constructing the self-adjoint operator (Weil criterion), or
(b) proving the zero-free region directly (de la Vallée-Poussin approach).

## Summary

| Component | Status | RH-free? |
|-----------|--------|----------|
| Projection self-adjointness | ✓ proved | Yes (abstract) |
| ⟪Pv, (I-P)v⟫ = 0 | ✓ proved | Yes (abstract) |
| Pythagorean decomposition | ✓ proved | Yes (abstract) |
| Λ(n) ≥ 0 | ✓ proved | Yes |
| Weil diagonal ≥ 0 | ✓ proved | Yes |
| Non-closure on helix | ✓ proved | Yes (+Lindemann) |
| ω primitive 6th root | ✓ proved | Yes |
| |1-1/ρ|=1 on critical line | ✓ proved | Yes |
| Li terms ≥ 0 on line | ✓ proved | **No**: assumes Re(ρ)=½ |
| AM-GM mirror-pair defect | ✓ proved | Yes |
| Unit circle rotation/spiral | ✓ proved | Yes |
| Two-channel Parseval | ✓ proved | Yes |
| Two-stage energy split | ✓ proved | Yes (abstract) |
| Cosh/inversion destruction | ✓ proved | Yes |
| Off-line destroys positivity | ✓ proved | Yes |
| Growth mismatch alignment | ✓ proved | Yes |
| Pipeline Pythagorean | ✓ proved | Yes (abstract) |
| Channel merge/Dedekind factor | ✓ proved | Yes |
| Transverse energy nonneg | ✓ proved | Yes |
| Master dichotomy | ✓ proved | Yes |
| Merge lossless iff both on-line | ✓ proved | Yes |
| σ=½ ⟺ bounded paired Li | ✓ proved | Yes (abstract) |
| On-line pair bounds [0,4] | ✓ proved | Yes |
| 1 offline + rest online → unbdd | ✓ proved | Yes |
| Uniform bound forces on-line | ✓ proved | Yes |
| Li upper bound by norm | ✓ proved | Yes |
| P = P_ζ is an orth. proj. | NOT proved | **This is RH** |
| Full Weil form PSD | NOT proved | **This is RH** |
| Actual ζ Li terms bounded | NOT proved | **This is RH** |

### Layer G: No Offline Zeros (`NoOfflineZeros.lean`)

This layer extends the individual-pair results to finite collections:
- `on_line_pair_bounded`: each on-line pair contributes ≤ 4
- `on_line_pair_nonneg`: each on-line pair contributes ≥ 0
- `total_li_bounded_all_on_line`: K on-line pairs → total ∈ [0, 4K]
- `one_offline_makes_sum_negative`: 1 offline + K online → total unbdd below
- `one_offline_breaks_uniform_bound`: 1 offline pair breaks uniform bound
- `uniform_bound_forces_on_line`: uniform bound + others on-line → on-line
- `paired_li_bounded_above_by_norm`: any pair's Li ≤ 1 + ‖w‖^n
- Bridge assumptions formalized: `ZetaZeroData`, `LiSumConverges`,
  `LiPartialSumsUniformlyBounded`

**What prevents proving no offline zeros (three obstacles):**
1. **Finite → Infinite** (Obstacle 2): Need Li sum convergence for ζ's
   infinitely many zeros. Requires analytic continuation not in Mathlib.
2. **Li positivity** (Obstacle 3): Need λ_n ≥ 0. THIS IS RH.
3. **Explicit formula** bridge: Connects prime-side Λ(n) ≥ 0 to
   zero-side λ_n. Requires Weil-Guinand trace formula.

The formalization is a **correct and complete framework** that identifies
precisely where RH enters. It does not prove RH. It proves everything
around it and leaves a clearly marked, honestly labeled hole.
-/

-- This file contains no formal content; it is a documentation-only audit.
-- All theorems referenced above are proved sorry-free in the other files.
