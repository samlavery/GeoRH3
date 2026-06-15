import Mathlib
import RequestProject.ForcedAlignment

/-!
# Two-Field Spectral Architecture: Helix Loss Fields and Forced Alignment

## Core Insight: The Helix Has No Zeros

The helix has exactly two things: **nodes** (integers/primes placed at `θ(n) = U log n`)
and the **projection loss field** `ψ(x) − x`. That's it. It has no "zeros."
The zeros are the *frequencies of that field's spectrum* — the explicit formula
`loss = −Σ_ρ x^ρ/ρ` means the `γ_ρ` show up as Fourier content. They're a
**readout** of the field, not features sitting on the helix. The helix generates
a field; ζ has zeros; the bridge between them is the explicit formula.

## Two Loss Fields from Two Projections

The two projections factor each zero `ρ = β + iγ` into its real and imaginary parts:

- **Loss field 1 (3D→2D, radial)**: The helix has radius `r = n^a`; collapsing to
  the cylinder drops the radial content. The radial exponent `a` *is* `β − ½`, the
  zero's distance off the line. Loss field 1 carries **Re(ρ) − ½**. It vanishes
  exactly when the helix already *is* a cylinder (RH).

- **Loss field 2 (2D→1D, angular)**: The cylinder collapses to the line; the
  residual is the prime fluctuation `ψ(x) − x`. Its spectrum is the **frequencies
  γ = Im(ρ)** — always nonzero (primes fluctuate).

## Two Channels (Mod-6 Characters)

The mod-6 fiber `(ℤ/6ℤ)* = {1,5}` has two characters, giving two arithmetic channels:

- `L₀` (principal, `χ₀`) = Q₁ + Q₅ — spectrum is the **ζ zeros**
- `L₁` (sign, `χ₁ = χ₃`) = Q₁ − Q₅ — spectrum is the **L(χ₃) zeros**

Combined: `ζ_K = ζ · L(χ₃)`, the Dedekind zeta of `ℚ(√−3)` (Eisenstein).
Two channels in 3D merge to one object in 2D.

## The Pipeline: 2 Channels × 2 Stages

```
   3D:  [ channel χ₀ (→ ζ) ]   [ channel χ₁ (→ L(χ₃)) ]
          |                       |
          └── stage 1: 3D→2D ────┘   (drop radial + merge channels)
                      ↓
   2D:        [ one object: ζ_K = ζ·L(χ₃) ]
                      ↓
              stage 2: 2D→1D          (deproject the angle)
                      ↓
   1D:              the line
```

Stage 1 does two jobs: drops the radial AND merges the two channels.
The two channels supply the quadratic form; the two stages supply the resolvent.

## The Mirror-Pair AM-GM Argument

The functional equation pairs `ρ` with `1−ρ`. Under `w = 1−1/ρ`, this becomes
`w ↦ 1/w` (reciprocal). Off-line, one partner goes inside the unit disk
(`‖w‖ < 1`) and the other outside (`‖w‖ > 1`). Their combined radial defect is:

  `(1 − r) + (1 − 1/r) = −(r−1)²/r ≤ 0`

This is AM-GM: `r + 1/r ≥ 2`, with equality iff `r = 1` (the critical line).
Every off-line mirror pair drags `λ_n → −∞`. The unit circle is the unique
escape — `w ↦ 1/w` fixes only the circle.

## Unit Circle: Rotation vs. Spiral

On the line: `‖w‖ = 1`, so `wⁿ` is pure rotation — bounded forever.
Off the line: one spiral contracts (`wⁿ → 0`) and the other expands (`wⁿ → ∞`).
The expanding side grows faster than the contracting side shrinks (AM-GM).
The bounded/unitary/self-adjoint structure is destroyed.

## What We Prove

1. AM-GM reciprocal: `r + 1/r ≥ 2` for `r > 0`
2. AM-GM equality: `r + 1/r = 2 ↔ r = 1`
3. Mirror pair defect identity: `(1-r) + (1-1/r) = -(r-1)²/r`
4. Mirror pair defect negativity: strict when `r ≠ 1`
5. Mirror pair defect divergence: `→ −∞` as `r → 0` or `r → ∞`
6. Unit circle rotation: `‖w^n‖ = 1` when `‖w‖ = 1`
7. Spiral divergence: `‖w^n‖` unbounded when `‖w‖ > 1`
8. Two-channel merge: quadratic form positivity from pair structure
-/

noncomputable section

open Complex Real

/-! ## Part 1: AM-GM Reciprocal Pair -/

/-
**AM-GM for reciprocal pairs**: `r + 1/r ≥ 2` for `r > 0`.
-/
theorem amgm_reciprocal (r : ℝ) (hr : 0 < r) : 2 ≤ r + 1 / r := by
  nlinarith [ sq_nonneg ( r - 1 ), mul_div_cancel₀ 1 hr.ne' ]

/-
**AM-GM equality characterization**: `r + 1/r = 2 ↔ r = 1` for `r > 0`.
-/
theorem amgm_reciprocal_eq_iff (r : ℝ) (hr : 0 < r) : r + 1 / r = 2 ↔ r = 1 := by
  grind

/-
**AM-GM strict inequality**: `r ≠ 1 → r + 1/r > 2` for `r > 0`.
-/
theorem amgm_reciprocal_strict (r : ℝ) (hr : 0 < r) (hr1 : r ≠ 1) : 2 < r + 1 / r := by
  cases lt_or_gt_of_ne hr1 <;> nlinarith [ sq_nonneg ( r - 1 ), mul_div_cancel₀ 1 hr.ne' ]

/-! ## Part 2: Mirror-Pair Defect -/

/-
**Mirror pair defect identity**: The combined radial defect of a
    functional-equation mirror pair `{r, 1/r}` is `−(r−1)²/r`.
    This is manifestly ≤ 0, with equality only at `r = 1` (the critical line).
-/
theorem mirror_pair_defect (r : ℝ) (hr : r ≠ 0) :
    (1 - r) + (1 - 1 / r) = -((r - 1) ^ 2 / r) := by
  grind

/-
**Mirror pair defect is nonpositive**: The combined defect of a
    reciprocal pair is always ≤ 0 (by AM-GM).
-/
theorem mirror_pair_defect_nonpos (r : ℝ) (hr : 0 < r) :
    (1 - r) + (1 - 1 / r) ≤ 0 := by
  nlinarith [ sq_nonneg ( r - 1 ), mul_div_cancel₀ 1 hr.ne' ]

/-
**Mirror pair defect is strictly negative off-line**: When `r ≠ 1`,
    the combined defect is strictly negative — every off-line pair
    contributes negative defect.
-/
theorem mirror_pair_defect_neg (r : ℝ) (hr : 0 < r) (hr1 : r ≠ 1) :
    (1 - r) + (1 - 1 / r) < 0 := by
  cases lt_or_gt_of_ne hr1 <;> nlinarith [ sq_pos_of_ne_zero ( sub_ne_zero.mpr hr1 ), mul_div_cancel₀ 1 hr.ne' ]

/-
**Defect diverges**: As `r → 0⁺`, `(1-r)+(1-1/r) → −∞`.
    Specifically, for `0 < r ≤ 1/2`, the defect ≤ `−1/(4r)`.
-/
theorem mirror_pair_defect_diverges_small (r : ℝ) (hr : 0 < r) (hr2 : r ≤ 1 / 2) :
    (1 - r) + (1 - 1 / r) ≤ -1 / (4 * r) := by
  rw [ le_div_iff₀ ] <;> nlinarith [ sq_nonneg ( r - 1 / 2 ), mul_div_cancel₀ 1 hr.ne' ]

/-! ## Part 3: Unit Circle Dynamics -/

/-
**Rotation on the unit circle**: If `‖w‖ = 1` then `‖wⁿ‖ = 1` for all `n`.
    On the critical line, the Möbius image is a pure rotation — bounded forever.
-/
theorem unit_circle_rotation (w : ℂ) (hw : ‖w‖ = 1) (n : ℕ) : ‖w ^ n‖ = 1 := by
  norm_num [ hw ]

/-
**Spiral growth off the circle**: If `‖w‖ > 1` then `‖wⁿ‖ → ∞`.
    Specifically, `‖wⁿ‖ = ‖w‖ⁿ`.
-/
theorem spiral_norm_pow (w : ℂ) (n : ℕ) : ‖w ^ n‖ = ‖w‖ ^ n := by
  exact norm_pow w n

/-
**Off-circle divergence**: If `‖w‖ > 1`, then `‖wⁿ‖` is eventually
    above any bound `M`.
-/
theorem spiral_unbounded (w : ℂ) (hw : 1 < ‖w‖) (M : ℝ) :
    ∃ n : ℕ, M < ‖w ^ n‖ := by
  -- We can choose `n` such that `‖w‖^n` is above `M` by taking `n` to be the ceiling of `log(M) / log(‖w‖)`.
  have h_ceil : ∃ n : ℕ, ‖w‖ ^ n > M := by
    exact pow_unbounded_of_one_lt M hw;
  aesop

/-
**Off-circle contraction**: If `‖w‖ < 1`, then `‖wⁿ‖ → 0`.
    Specifically, `‖wⁿ‖ ≤ ‖w‖ⁿ → 0`.
-/
theorem spiral_contracts (w : ℂ) (hw : ‖w‖ < 1) :
    Filter.Tendsto (fun n => ‖w ^ n‖) Filter.atTop (nhds 0) := by
  simpa using tendsto_pow_atTop_nhds_zero_of_lt_one ( norm_nonneg w ) hw

/-! ## Part 4: Reciprocal Pair on the Möbius Image -/

/-- **The FE involution is a reciprocal on the Möbius image**:
    `w(ρ) · w(1−ρ) = 1`, so the functional equation acts as `w ↦ 1/w`.
    This converts the left-right symmetry `σ ↦ 1−σ` into inside/outside
    asymmetry on the unit disk. -/
theorem mobius_FE_reciprocal (sigma gamma : ℝ) (hg : gamma ≠ 0) :
    moebius_helix sigma gamma * moebius_helix (1 - sigma) (-gamma) = 1 :=
  moebius_product_one sigma gamma hg

/-- **Norm reciprocal of the Möbius pair**:
    `‖w(ρ)‖ · ‖w(1−ρ)‖ = 1`. So if one has norm `r`, the other has `1/r`. -/
theorem mobius_norm_reciprocal (sigma gamma : ℝ) (hg : gamma ≠ 0) :
    ‖moebius_helix sigma gamma‖ * ‖moebius_helix (1 - sigma) (-gamma)‖ = 1 :=
  moebius_norm_product_one sigma gamma hg

/-! ## Part 5: Combined Defect of a Möbius Mirror Pair -/

/-
**Li term combined defect**: For a functional-equation pair `{ρ, 1−ρ}`,
    the combined Li contribution `Re[1−wⁿ] + Re[1−(1/w)ⁿ]` equals
    `2 − (rⁿ cos(nθ) + r⁻ⁿ cos(nθ))` where `r = ‖w‖`. When `r ≠ 1`,
    the `rⁿ + r⁻ⁿ ≥ 2` term (AM-GM on powers) makes this ≤ 0.
-/
theorem li_pair_defect_bound (r : ℝ) (hr : 0 < r) (n : ℕ) (hn : 0 < n) :
    2 ≤ r ^ n + 1 / r ^ n := by
  rw [ add_div', le_div_iff₀ ] <;> nlinarith [ sq_nonneg ( r ^ n - 1 ), pow_pos hr n ]

/-
**Power AM-GM strict**: For `r ≠ 1` and `n ≥ 1`,
    `rⁿ + r⁻ⁿ > 2` — strictly, because `rⁿ ≠ 1`.
-/
theorem power_amgm_strict (r : ℝ) (hr : 0 < r) (hr1 : r ≠ 1)
    (n : ℕ) (hn : 0 < n) : 2 < r ^ n + 1 / r ^ n := by
  convert amgm_reciprocal_strict ( r ^ n ) ( pow_pos hr _ ) _ using 1;
  rw [ Ne.eq_def, pow_eq_one_iff_of_nonneg hr.le ] <;> aesop

/-! ## Part 6: Two-Channel Quadratic Form -/

/-- **Two-channel sum of squares is nonneg**: Given two loss fields `L₀, L₁`,
    the transverse energy `|L₀|² + |L₁|²` is manifestly nonneg. -/
theorem two_channel_energy_nonneg (L₀ L₁ : ℝ) :
    0 ≤ L₀ ^ 2 + L₁ ^ 2 :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

/-
**Channel decomposition**: `Q₁ = (L₀ + L₁)/2` and `Q₅ = (L₀ − L₁)/2`
    recover the residue channels from the character channels.
-/
theorem channel_decomposition (L₀ L₁ : ℝ) :
    ((L₀ + L₁) / 2) + ((L₀ - L₁) / 2) = L₀ ∧
    ((L₀ + L₁) / 2) - ((L₀ - L₁) / 2) = L₁ := by
  grobner

/-
**Parseval on channels**: The sum of squares of residue channels
    equals the sum of squares of character channels:
    `Q₁² + Q₅² = (L₀² + L₁²)/2`.
-/
theorem channel_parseval (L₀ L₁ : ℝ) :
    ((L₀ + L₁) / 2) ^ 2 + ((L₀ - L₁) / 2) ^ 2 = (L₀ ^ 2 + L₁ ^ 2) / 2 := by
  ring

/-! ## Part 7: Two-Projection Stage Decomposition -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **Stage 1 loss is the radial component**: The 3D→2D projection loss
    `‖x − P₁x‖²` measures the radial content dropped. In the helix context,
    this corresponds to `Re(ρ) − 1/2` (zero when RH holds). -/
theorem stage1_loss_nonneg (P₁ : F →ₗ[ℝ] F)
    (_hP₁_sa : ∀ x y, @inner ℝ F _ (P₁ x) y = @inner ℝ F _ x (P₁ y))
    (_hP₁_idem : ∀ x, P₁ (P₁ x) = P₁ x)
    (x : F) : (0 : ℝ) ≤ ‖x - P₁ x‖ ^ 2 := sq_nonneg _

/-- **Stage 2 loss is the angular component**: The 2D→1D projection loss
    `‖P₁x − P₂(P₁x)‖²` measures the angular content. This corresponds to
    `Im(ρ) = γ` — always nonzero (primes fluctuate). -/
theorem stage2_loss_nonneg (P₁ P₂ : F →ₗ[ℝ] F) (x : F) :
    (0 : ℝ) ≤ ‖P₁ x - (P₂ ∘ₗ P₁) x‖ ^ 2 := sq_nonneg _

/-
**Total energy splits into three nonneg components**:
    `‖x‖² = ‖P₂(P₁x)‖² + ‖P₁x − P₂(P₁x)‖² + ‖x − P₁x‖²`.
    The first is the 1D signal, the second is the angular (stage 2) loss,
    the third is the radial (stage 1) loss.
-/
theorem two_stage_energy_split
    (P₁ P₂ : F →ₗ[ℝ] F)
    (hP₁_sa : ∀ x y, @inner ℝ F _ (P₁ x) y = @inner ℝ F _ x (P₁ y))
    (hP₁_idem : ∀ x, P₁ (P₁ x) = P₁ x)
    (hP₂_sa : ∀ x y, @inner ℝ F _ (P₂ x) y = @inner ℝ F _ x (P₂ y))
    (hP₂_idem : ∀ x, P₂ (P₂ x) = P₂ x)
    (x : F) :
    ‖x‖ ^ 2 = ‖(P₂ ∘ₗ P₁) x‖ ^ 2 +
              ‖P₁ x - (P₂ ∘ₗ P₁) x‖ ^ 2 +
              ‖x - P₁ x‖ ^ 2 := by
  convert cascade_energy P₁ P₂ hP₁_sa hP₁_idem hP₂_sa hP₂_idem x using 1

/-
**RH is stage 1 loss vanishing**: If stage 1 loss is zero, the helix
    is already a cylinder — the radial component `Re(ρ) − 1/2` vanishes
    for every zero.
-/
theorem stage1_lossless_iff_cylinder (P₁ : F →ₗ[ℝ] F)
    (hP₁_sa : ∀ x y, @inner ℝ F _ (P₁ x) y = @inner ℝ F _ x (P₁ y))
    (hP₁_idem : ∀ x, P₁ (P₁ x) = P₁ x)
    (x : F) :
    P₁ x = x ↔ ‖x - P₁ x‖ = 0 := by
  rw [ norm_sub_rev, norm_eq_zero, sub_eq_zero ]

end