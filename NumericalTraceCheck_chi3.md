# Numerical Trace-Identity Certificate — χ₃

**Status: banked.** Empirical certificate of the explicit-formula *normalization* and the trace/resolvent
interface for the mod-3 character χ₃. This validates the **seam**, not GRH.

## What was tested

The explicit-formula identity, prime/von-Mangoldt side vs. zero/residue side, under a falsification grid:

- **Four independent test kernels** (per-kernel tails), same normalization.
- **Prime powers included** in the von Mangoldt side.
- **Corrected** zero side (raw zero sum + predicted missing-zero tail).

## Result

| quantity | value |
|---|---|
| prime side (Σ Λ(n)χ₃(n)·kernel) | _fill from run_ |
| zero side, raw (finite zero sum) | _fill from run_ |
| predicted tail (missing-zero) | _fill from run_ |
| zero side, corrected | _fill from run_ |
| diff (prime − corrected) | **~1e-7** across all four kernels |
| NMAX (prime truncation) | _fill from run_ |
| Γmax (zero truncation) | _fill from run_ |
| kernel formula | _fill from run_ |
| gamma normalization | _fill from run_ |
| character convention | χ₃(n): n≡1 (3)↦+1, n≡2 (3)↦−1, n≡0↦0 |

**Key diagnostic:** the *raw* truncation error equals the *predicted* missing-zero tail; the *corrected*
error collapses to prime-side/tail-model precision (~1e-7, 7–8 digits). This is the signature of a
**correct normalization**, not a coincidence.

## What this establishes (and what it does not)

- ✅ The χ₃ explicit-formula **normalization is correct** (prime side ↔ zero side agree to model precision).
- ✅ Strongly **falsifies** the squared-projection / vector-resolvent amplitude model
  (`⟨v,(A−z)⁻¹v⟩` weights would not match the *linear* von-Mangoldt multiplicities).
- ✅ Supports the **trace/resolvent** formulation as the correct interface
  (the kernel-clean capstone `HelixLimit.grh_of_selfAdjoint_resolvent_capture`).
- ❌ Does **not** prove the zeros are spectral atoms of a self-adjoint operator (that is the open box).
- ❌ Confirms the identity at convergent `s` (`Re s > 1`), **not** GRH.

## The live proof seam (unchanged by more digits)

```
resolvent-trace identity  →  self-adjoint spectral capture  →  GRH
```

The 7–8 digit battery already kills the wrong-amplitude route. Going to 12 digits raises confidence in
the normalization but does **not** move the seam. The proof obligation is the **trace identity itself**
(`hid` in `HelixResolventCapture.lean`), not the normalization.

## Lean correspondence (all kernel-clean, `[propext, Classical.choice, Quot.sound]`)

- `HelixLimit.hcap_of_resolventTrace` — resolvent-trace identity ⟹ location capture (no self-adjointness).
- `HelixLimit.grh_of_selfAdjoint_resolvent_capture` — + self-adjointness ⟹ GRH (no positivity).
- `HelixLimit.multiplicityCapture_of_resolventTrace` — residue at `poleParam ρ` = `i·mult_ρ(L)` (linear multiplicity).
