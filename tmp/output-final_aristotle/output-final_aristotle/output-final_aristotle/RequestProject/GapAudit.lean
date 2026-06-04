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
| P = P_ζ is an orth. proj. | NOT proved | **This is RH** |
| Full Weil form PSD | NOT proved | **This is RH** |

The formalization is a **correct and complete framework** that identifies
precisely where RH enters. It does not prove RH. It proves everything
around it and leaves a clearly marked, honestly labeled hole.
-/

-- This file contains no formal content; it is a documentation-only audit.
-- All theorems referenced above are proved sorry-free in the other files.
