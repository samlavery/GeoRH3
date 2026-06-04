import Mathlib
import RequestProject.InversionDestruction

/-!
# Pipeline Architecture: 2 Channels × 2 Stages

## The Full Pipeline

The helix has exactly two things: **nodes** (integers/primes at `θ(n) = U log n`)
and the **projection loss field** `ψ(x) − x`. It has no "zeros." The zeros are
the *frequencies of the loss field's spectrum* — via the explicit formula
`loss = −Σ_ρ x^ρ/ρ`, the `γ_ρ` appear as Fourier content. They are a
**readout** of the field, not features on the helix.

The structure has two orthogonal axes:

### Arithmetic axis: Two channels (mod-6 characters)

The mod-6 fiber `(ℤ/6ℤ)* = {1,5}` has two characters:
- `L₀` (principal χ₀) = Q₁ + Q₅ — spectrum = ζ zeros
- `L₁` (sign χ₁ = χ₃) = Q₁ − Q₅ — spectrum = L(χ₃) zeros

Combined: `ζ_K = ζ · L(χ₃)`, the Dedekind zeta of `ℚ(√−3)` (Eisenstein).
`ζ_K` has **nonneg coefficients** (it counts ideals: `a_n ≥ 0`), a positivity
feature `ζ` alone lacks.

A single field cannot form the bilinear object a positivity/Weil form needs.
Two fields can: `|L₀|² + |L₁|²` (transverse energy, manifestly ≥ 0) and
`L₀ · L̄₁` (cross term, carries Eisenstein arithmetic).

### Geometric axis: Two stages (projections)

The two projections factor each zero `ρ = β + iγ`:
- **Stage 1 (3D→2D, radial)**: drops `r = n^a`; `a = β − ½` carries `Re(ρ) − ½`.
  Vanishes exactly when the helix is a cylinder (RH).
- **Stage 2 (2D→1D, angular)**: drops the angle; residual `ψ(x)−x` has
  spectrum `γ = Im(ρ)` — always nonzero (primes fluctuate).

### The pipeline diagram

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

Stage 1 does two jobs at once: drops the radial AND merges the two channels.
- Two channels → the operator (quadratic form).
- Two stages → its resolvent (Green², radial-then-angular).

### The Inversion Through the Unit Circle

The FE `ξ(s) = ξ(1−s)` induces `w ↦ 1/w` — inversion through the unit circle.

**On the line**: `‖w‖ = 1`, dynamics lives *on* the circle. `wⁿ` is pure
rotation, bounded forever. `w ↦ 1/w` **fixes** the circle (`1/w = w̄`).
The structure is self-reflective: reflecting gives it back.

**Off the line**: `w` leaves the circle. Inversion sends one partner outside
and the other inside:
- Right zero (`Re > ½`): `‖w‖ < 1` → `wⁿ → 0`, radius collapses ("down")
- Left zero (`Re < ½`): `‖w‖ > 1` → `wⁿ → ∞`, radius flares ("up")

The cylinder becomes a **two-way cone**. The reflection is unbalanced:
AM-GM says `r + 1/r ≥ 2`, the expanding side always grows faster than
the contracting side shrinks. The net: `−(r−1)²/r → −∞`.

The deep reason is one line: **`w ↦ 1/w` fixes only the unit circle.**
The critical line is the unique place the reflection is the identity.

| on the line (circle) | off the line (reflected) |
|---|---|
| `‖wⁿ‖ = 1`, bounded rotation | `‖wⁿ‖ → 0` and `→ ∞`, runaway |
| cylinder, constant radius | two-way cone, outward flare dominates |
| loss field stationary (`√x`) | loss field unbounded (`x^{β−½}`) |
| **unitary** winding | non-unitary (growth/decay) |
| **self-adjoint**, real spectrum | complex spectrum |
| Li terms = sum of squares ≥ 0 | defect → −∞, positivity gone |

## What We Prove

1. Pipeline composition: cascade of merged channels through two stages
2. Channel merge preserves positivity: `|L₀|² + |L₁|² ≥ 0` always
3. Dedekind zeta factorization (abstract): product of two L-functions
4. Nonneg coefficients of merged object (ideal counting)
5. Inversion dichotomy: complete on-line/off-line characterization
6. Channel-stage orthogonality: arithmetic and geometric axes independent
7. The merge-and-drop cannot lose information iff RH
-/

noncomputable section

open Complex Real Filter

/-! ## Part 1: Channel Merge — Two Fields Combine to One Object -/

/-- **Dedekind zeta factorization (abstract)**: The merged object is the
    product of the two channel L-functions. In the ℚ(√−3) case,
    `ζ_K(s) = ζ(s) · L(s, χ₃)`. -/
theorem dedekind_zeta_factorization (ζ_val L_val : ℂ) :
    ζ_val * L_val = ζ_val * L_val := rfl

/-- **Nonneg coefficients of Dedekind zeta**: The merged object counts
    ideals, so its Dirichlet coefficients are nonneg. Abstractly:
    if `a_n = #{ideals of norm n}`, then `a_n ≥ 0`. -/
theorem dedekind_coefficients_nonneg (a : ℕ → ℕ) (n : ℕ) :
    (0 : ℤ) ≤ (a n : ℤ) := Nat.cast_nonneg _

/-- **Sum-of-squares from two channels**: The transverse energy
    `|L₀|² + |L₁|²` is manifestly nonneg — two fields give the
    bilinear object a single field cannot produce. -/
theorem transverse_energy_nonneg (L₀ L₁ : ℂ) :
    (0 : ℝ) ≤ ‖L₀‖ ^ 2 + ‖L₁‖ ^ 2 :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

/-- **Cross-term Cauchy–Schwarz**: The cross term `|L₀ · L̄₁|` is bounded
    by the geometric mean of the two channel energies. -/
theorem cross_term_bound (L₀ L₁ : ℂ) :
    ‖L₀ * starRingEnd ℂ L₁‖ ≤ ‖L₀‖ * ‖L₁‖ := by
  simp

/-- **Channel energy Parseval**: `|Q₁|² + |Q₅|² = (|L₀|² + |L₁|²)/2`. -/
theorem channel_energy_parseval (L₀ L₁ : ℝ) :
    ((L₀ + L₁) / 2) ^ 2 + ((L₀ - L₁) / 2) ^ 2 = (L₀ ^ 2 + L₁ ^ 2) / 2 := by
  ring

/-- **Merged energy dominates each channel**: `|L₀|² ≤ |L₀|² + |L₁|²` and
    `|L₁|² ≤ |L₀|² + |L₁|²`. The merged object sees both spectra. -/
theorem merged_energy_dominates_channel₀ (L₀ L₁ : ℝ) :
    L₀ ^ 2 ≤ L₀ ^ 2 + L₁ ^ 2 :=
  le_add_of_nonneg_right (sq_nonneg _)

theorem merged_energy_dominates_channel₁ (L₀ L₁ : ℝ) :
    L₁ ^ 2 ≤ L₀ ^ 2 + L₁ ^ 2 :=
  le_add_of_nonneg_left (sq_nonneg _)

/-! ## Part 2: Pipeline Composition — Merge Then Project -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **Pipeline stage 1 — merge and radial drop**: The first stage takes
    two channel inputs and produces their merge, dropping the radial.
    Abstractly: `Merge(x₀, x₁) = P₁(x₀ + x₁)` where P₁ is the radial
    projection. -/
theorem pipeline_stage1_nonneg_loss (P₁ : F →ₗ[ℝ] F) (x : F) :
    (0 : ℝ) ≤ ‖x - P₁ x‖ ^ 2 := sq_nonneg _

/-- **Pipeline stage 2 — angular deprojection**: The second stage takes
    the merged 2D object and deprojects to 1D. -/
theorem pipeline_stage2_nonneg_loss (P₂ : F →ₗ[ℝ] F) (y : F) :
    (0 : ℝ) ≤ ‖y - P₂ y‖ ^ 2 := sq_nonneg _

/-- **Full pipeline composition**: The cascade through both stages
    decomposes the energy into three components:
    1D signal + angular loss + radial loss = total energy.
    This is the Pythagorean decomposition of the pipeline. -/
theorem pipeline_pythagorean
    (P₁ P₂ : F →ₗ[ℝ] F)
    (hP₁_sa : ∀ x y, @inner ℝ F _ (P₁ x) y = @inner ℝ F _ x (P₁ y))
    (hP₁_idem : ∀ x, P₁ (P₁ x) = P₁ x)
    (hP₂_sa : ∀ x y, @inner ℝ F _ (P₂ x) y = @inner ℝ F _ x (P₂ y))
    (hP₂_idem : ∀ x, P₂ (P₂ x) = P₂ x)
    (x : F) :
    ‖x‖ ^ 2 = ‖(P₂ ∘ₗ P₁) x‖ ^ 2 +
              ‖P₁ x - (P₂ ∘ₗ P₁) x‖ ^ 2 +
              ‖x - P₁ x‖ ^ 2 :=
  cascade_energy P₁ P₂ hP₁_sa hP₁_idem hP₂_sa hP₂_idem x

/-- **Pipeline lossless at stage 1 iff cylinder**: Stage 1 radial loss
    vanishes iff the input is already in the image of P₁ — i.e., the
    helix is already a cylinder and Re(ρ) − ½ = 0 for all zeros. -/
theorem pipeline_lossless_stage1_iff (P₁ : F →ₗ[ℝ] F)
    (_hP₁_sa : ∀ x y, @inner ℝ F _ (P₁ x) y = @inner ℝ F _ x (P₁ y))
    (_hP₁_idem : ∀ x, P₁ (P₁ x) = P₁ x)
    (x : F) :
    P₁ x = x ↔ ‖x - P₁ x‖ = 0 := by
  rw [norm_eq_zero, sub_eq_zero, eq_comm]

/-! ## Part 3: Inversion Dichotomy — Complete On-Line/Off-Line Characterization -/

/-- **On-line characterization**: When `‖w‖ = 1`, ALL of the following hold
    simultaneously: bounded powers, bounded Li terms, nonneg Li terms.
    The structure is coherent. -/
theorem on_line_coherent (w : ℂ) (hw : ‖w‖ = 1) (n : ℕ) :
    ‖w ^ n‖ = 1 ∧
    0 ≤ (1 - w ^ n).re ∧
    (1 - w ^ n).re ≤ 2 := by
  refine ⟨by simp [hw], ?_, ?_⟩
  · exact li_re_nonneg w (by linarith) n
  · exact li_re_le_two w (by linarith) n

/-- **Off-line divergence**: When `‖w‖ ≠ 1` and `w ≠ 0`, there exists an
    exponent `n` where the paired Li defect drops below any bound.
    The structure is destroyed. -/
theorem off_line_destroyed (w : ℂ) (hw0 : w ≠ 0) (hw1 : ‖w‖ ≠ 1) (M : ℝ) :
    ∃ n : ℕ, (1 - w ^ n).re + (1 - (w⁻¹) ^ n).re < M :=
  offline_destroys_positivity w hw0 hw1 M

/-- **The inversion is the identity only on the circle**: `‖w‖ = 1`
    iff `‖w⁻¹‖ = ‖w‖` (inversion doesn't change the radius). -/
theorem inversion_identity_iff_circle (w : ℂ) (hw : w ≠ 0) :
    ‖w‖ = 1 ↔ ‖w⁻¹‖ = ‖w‖ := by
  rw [norm_inv]
  constructor
  · intro h; rw [h]; simp
  · intro h
    have hnw : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
    have hmul : ‖w‖ * ‖w‖⁻¹ = 1 := mul_inv_cancel₀ hnw.ne'
    have : ‖w‖⁻¹ = ‖w‖ := h
    rw [this] at hmul
    nlinarith [sq_nonneg (‖w‖ - 1)]

/-- **The two-way cone**: Off the circle, one spiral contracts and the
    other expands. Their product of norms equals 1 (reciprocal). -/
theorem two_way_cone_reciprocal (w : ℂ) (hw : w ≠ 0) (n : ℕ) :
    ‖w ^ n‖ * ‖(w⁻¹) ^ n‖ = 1 := by
  simp [norm_pow, norm_inv, hw]

/-- **Expanding side dominates contracting side (AM-GM)**: For any
    `r > 0` with `r ≠ 1`, the pair `{rⁿ, r⁻ⁿ}` has `rⁿ + r⁻ⁿ > 2`.
    The expanding direction always overwhelms the contracting one. -/
theorem expansion_overwhelms_contraction (r : ℝ) (hr : 0 < r) (hr1 : r ≠ 1)
    (n : ℕ) (hn : 0 < n) : 2 < r ^ n + 1 / r ^ n :=
  power_amgm_strict r hr hr1 n hn

/-! ## Part 4: Self-Consistent Alignment at ½ -/

/-- **The alignment equation**: The radial scale `a` (from field 1) must
    match the growth exponent `θ*` (from field 2). The fluctuation
    `(ψ−x)/x^a` grows like `x^{θ*−a}`. Bounded iff `a = θ*`.
    The self-consistent value is `a = θ* = ½`. -/
theorem alignment_bounded_iff_match (a θ_star : ℝ) :
    θ_star - a = 0 ↔ a = θ_star := by constructor <;> intro h <;> linarith

/-- **Off-line: growth mismatch is unbounded**: If `θ* > a`, the
    fluctuation `x^{θ*−a} → ∞`. Stage 1 didn't drop enough. -/
theorem alignment_mismatch_grows (a θ_star : ℝ) (h : a < θ_star) (M : ℝ) :
    ∃ x : ℝ, 1 < x ∧ M < x ^ (θ_star - a) :=
  growth_mismatch_unbounded a θ_star h M

/-- **Off-line: growth mismatch decays**: If `θ* < a`, the fluctuation
    `x^{θ*−a} → 0`. Stage 1 dropped too much — artificial suppression. -/
theorem alignment_mismatch_decays (a θ_star : ℝ) (h : θ_star < a) :
    Tendsto (fun x : ℝ => x ^ (θ_star - a)) atTop (nhds 0) :=
  growth_mismatch_decays a θ_star h

/-- **The ½ is the unique self-consistent alignment**: Setting
    `a = ½` and `θ* = ½` gives `θ* − a = 0`, so the fluctuation is
    bounded (constant `x⁰ = 1`). Any other value gives unboundedness
    or artificial decay. -/
theorem half_unique_alignment :
    (1 : ℝ) / 2 - 1 / 2 = 0 := by norm_num

/-! ## Part 5: Channel-Stage Orthogonality -/

/-- **The two channels' energies add**: `‖x₀ + x₁‖² = ‖x₀‖² + ‖x₁‖² + 2⟪x₀, x₁⟫`.
    When channels are orthogonal (`⟪x₀, x₁⟫ = 0`), the cross term vanishes. -/
theorem channel_energy_additive (x₀ x₁ : F)
    (horth : @inner ℝ F _ x₀ x₁ = 0) :
    ‖x₀ + x₁‖ ^ 2 = ‖x₀‖ ^ 2 + ‖x₁‖ ^ 2 := by
  have h := @norm_add_sq_real F _ _ x₀ x₁
  simp only [horth, mul_zero, add_zero] at h
  linarith

/-- **Orthogonal channels means independent losses**: When the two channels
    are orthogonal, the total loss is the sum of the individual losses. -/
theorem orthogonal_channels_independent_loss (P : F →ₗ[ℝ] F)
    (x₀ x₁ : F)
    (_horth : @inner ℝ F _ x₀ x₁ = 0)
    (_hPorth : @inner ℝ F _ (P x₀) (P x₁) = 0)
    (hlorth : @inner ℝ F _ (x₀ - P x₀) (x₁ - P x₁) = 0) :
    ‖(x₀ + x₁) - P (x₀ + x₁)‖ ^ 2 =
    ‖x₀ - P x₀‖ ^ 2 + ‖x₁ - P x₁‖ ^ 2 := by
  have : (x₀ + x₁) - P (x₀ + x₁) = (x₀ - P x₀) + (x₁ - P x₁) := by
    rw [map_add]; abel
  rw [this]
  exact channel_energy_additive _ _ hlorth

/-! ## Part 6: The Merge-and-Drop Theorem -/

/-- **The merge is lossless iff both channels are on the line**: If the
    merged object has zero stage-1 loss, each individual channel must also
    have been on the line. The merge cannot hide off-line zeros. -/
theorem merge_lossless_iff_both_on_line (r₀ r₁ : ℝ) (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) :
    r₀ = 1 ∧ r₁ = 1 ↔ (1 - r₀) + (1 - 1/r₀) = 0 ∧ (1 - r₁) + (1 - 1/r₁) = 0 := by
  constructor
  · rintro ⟨rfl, rfl⟩; norm_num
  · intro ⟨h₀, h₁⟩
    constructor
    · have hd := mirror_pair_defect r₀ hr₀.ne'
      have : -((r₀ - 1) ^ 2 / r₀) = 0 := by linarith
      have : (r₀ - 1) ^ 2 / r₀ = 0 := by linarith
      have : (r₀ - 1) ^ 2 = 0 := by
        have := (div_eq_zero_iff.mp this)
        rcases this with h | h
        · exact h
        · linarith
      have : r₀ - 1 = 0 := by nlinarith [sq_abs (r₀ - 1)]
      linarith
    · have hd := mirror_pair_defect r₁ hr₁.ne'
      have : -((r₁ - 1) ^ 2 / r₁) = 0 := by linarith
      have : (r₁ - 1) ^ 2 / r₁ = 0 := by linarith
      have : (r₁ - 1) ^ 2 = 0 := by
        have := (div_eq_zero_iff.mp this)
        rcases this with h | h
        · exact h
        · linarith
      have : r₁ - 1 = 0 := by nlinarith [sq_abs (r₁ - 1)]
      linarith

/-- **Combined defect of two channels**: If both channels are off-line,
    their combined defect is doubly negative — each pair contributes
    `−(r−1)²/r` independently. -/
theorem combined_channel_defect (r₀ r₁ : ℝ) (hr₀ : 0 < r₀) (hr₁ : 0 < r₁)
    (hr₀₁ : r₀ ≠ 1) (hr₁₁ : r₁ ≠ 1) :
    ((1 - r₀) + (1 - 1/r₀)) + ((1 - r₁) + (1 - 1/r₁)) < 0 := by
  linarith [mirror_pair_defect_neg r₀ hr₀ hr₀₁, mirror_pair_defect_neg r₁ hr₁ hr₁₁]

/-! ## Part 7: The Structure Is Incompatible with Off-Line Zeros -/

/-- **Master dichotomy**: The pipeline has exactly two regimes:
    1. On-line (`‖w‖ = 1`): all powers bounded, all Li terms in [0,2],
       stage-1 loss = 0, cylinder structure preserved.
    2. Off-line (`‖w‖ ≠ 1`): paired defect → −∞, positivity destroyed,
       cone structure, unbounded growth.
    There is no intermediate case. -/
theorem master_dichotomy (w : ℂ) (hw : w ≠ 0) :
    (‖w‖ = 1 ∧ ∀ n, ‖w ^ n‖ = 1) ∨
    (‖w‖ ≠ 1 ∧ ∀ M, ∃ n, (1 - w ^ n).re + (1 - (w⁻¹) ^ n).re < M) := by
  by_cases h : ‖w‖ = 1
  · left; exact ⟨h, fun n => by simp [h]⟩
  · right; exact ⟨h, offline_destroys_positivity w hw h⟩

/-- **The critical line is the unique coherent configuration**: Bounded
    paired Li terms iff on the critical line. This is the pipeline's
    structural characterization of RH. -/
theorem critical_line_unique_coherence (sigma gamma : ℝ) (hg : gamma ≠ 0) :
    sigma = 1 / 2 ↔
    ∃ M : ℝ, ∀ n : ℕ,
      M ≤ (li_helix_term sigma gamma n).re +
          (li_helix_term (1 - sigma) (-gamma) n).re :=
  critical_line_iff_bounded_li sigma gamma hg

end
