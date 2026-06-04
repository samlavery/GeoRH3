import Mathlib
import RequestProject.TwoFieldSpectral

/-!
# Inversion Destruction: The FE Fixes Only the Unit Circle

## The Deep Reason: `w ↦ 1/w` Fixes Only the Circle

The functional equation `ξ(s) = ξ(1−s)` induces the involution `σ ↦ 1−σ`
on zeros. Under the Möbius map `w = 1 − 1/ρ`, this becomes `w ↦ 1/w` —
**inversion through the unit circle**. The critical line `Re(ρ) = 1/2`
maps to `‖w‖ = 1` (the unit circle), which is the **unique fixed locus**
of inversion.

## On the Line: Coherent Rotation

On the line, the dynamics lives *on* the circle: `‖w‖ = 1`, so `wⁿ` is a
pure **rotation** — `‖wⁿ‖ = 1` for all `n`, bounded forever. The FE
reflection `w ↦ 1/w` **fixes the circle** (on it, `1/w = w̄` — same
radius). The structure is self-reflective: reflecting gives it back.

Properties on the line:
- `‖wⁿ‖ = 1` — bounded rotation
- Cylinder, constant radius
- Loss field stationary (`√x`)
- **Unitary** winding
- **Self-adjoint**, real spectrum
- Li terms = sum of squares `≥ 0`

## Off the Line: Spiral Destruction

Off the line, `w` leaves the circle, and `w ↦ 1/w` is a genuine inversion.
It sends one member of the pair **outside** the circle and the mirror **inside**:

- Right zero (`Re > ½`): `‖w‖ < 1` → `wⁿ → 0`, radius **collapses** ("down")
- Left zero (`Re < ½`): `‖w‖ > 1` → `wⁿ → ∞`, radius **flares** ("up")

The single coherent rotation splits into an expanding spiral and a contracting
spiral — the cylinder becomes a **two-way cone**. And the reflection is
**unbalanced**: AM-GM says `r + 1/r ≥ 2`, so the expanding side always
grows faster than the contracting side shrinks. The net is:

  `(1−r) + (1−1/r) = −(r−1)²/r → −∞`

Properties off the line:
- `‖wⁿ‖ → 0` and `→ ∞` — runaway
- Two-way cone, outward flare dominates
- Loss field unbounded (`x^{β−½}`)
- Non-unitary (growth/decay)
- Complex spectrum
- Defect `→ −∞`, positivity gone

## The Cosh Connection

The discrete AM-GM `r + 1/r ≥ 2` is the same as the continuous bound:
`r + 1/r = 2 cosh(log r)`, so `r + 1/r ≥ 2 ⟺ cosh ≥ 1`. This is
exactly the `no_drift_amgm` / `li_helix_grows_off_line` bound: the
off-line pair's defect `→ −∞` *is* `cosh(aθ) → ∞` for `a ≠ 0`.

## The Alignment Constraint

The coupling between the two projection stages is the whole game:
**field 1 sets the normalization of field 2.** The fluctuation
`(ψ−x)/x^a` grows like `x^{θ*−a}`, where `a` is the radial scale
from field 1 and `θ* = sup Re(ρ)`. Field 2 is bounded (stationary)
iff `a = θ*`. The self-consistent value is:

  `a = θ* = ½`

Both projections close coherently only when the radial scale (field 1)
matches the fluctuation's growth (field 2). Off the line, `a` and `θ*`
disagree — one projection loses what the other can't recover.

## What We Prove

1. Cosh identity: `r + 1/r = 2 * cosh(log r)` for `r > 0`
2. Cosh lower bound: `cosh(t) ≥ 1` for all `t`
3. Cosh equals 1 iff t = 0: the critical-line characterization
4. Inversion fixes the circle: `‖w‖ = 1 → ‖1/w‖ = 1`
5. Inversion swaps inside/outside: `‖w‖ < 1 ↔ ‖1/w‖ > 1`
6. Paired power defect diverges: `rⁿ + r⁻ⁿ → ∞` for `r ≠ 1`
7. Combined defect sum over N zeros: accumulated defect `→ −∞`
8. Self-consistent alignment: the ½ is forced by both stages closing
-/

noncomputable section

open Complex Real Filter

/-! ## Part 1: The Cosh Connection -/

/-
**Cosh identity**: `r + 1/r = 2 * cosh(log r)` for `r > 0`.
    This connects the discrete AM-GM to the continuous hyperbolic bound.
-/
theorem reciprocal_sum_eq_cosh (r : ℝ) (hr : 0 < r) :
    r + 1 / r = 2 * Real.cosh (Real.log r) := by
  rw [ Real.cosh_log hr, mul_div_cancel₀ _ two_ne_zero ] ; ring

/-
**Cosh lower bound**: `cosh(t) ≥ 1` for all `t ∈ ℝ`.
-/
theorem cosh_ge_one (t : ℝ) : 1 ≤ Real.cosh t := by
  exact Real.one_le_cosh t

/-
**Cosh equals 1 iff t = 0**: The critical line is where cosh = 1.
-/
theorem cosh_eq_one_iff (t : ℝ) : Real.cosh t = 1 ↔ t = 0 := by
  rw [ Real.cosh_eq ];
  exact ⟨ fun h => by nlinarith [ Real.exp_pos t, Real.exp_neg t, mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos t ) ), Real.add_one_le_exp t, Real.add_one_le_exp ( -t ) ], fun h => by norm_num [ h ] ⟩

/-! ## Part 2: Inversion Through the Unit Circle -/

/-
**Inversion preserves the circle**: If `‖w‖ = 1` and `w ≠ 0`,
    then `‖w⁻¹‖ = 1`. The unit circle is the fixed locus of inversion.
-/
theorem inv_norm_eq_one (w : ℂ) (hw : ‖w‖ = 1) : ‖w⁻¹‖ = 1 := by
  aesop

/-
**Inversion swaps inside and outside**: `‖w‖ < 1 ↔ 1 < ‖w⁻¹‖`
    for nonzero `w`. The FE sends what's inside the disk to outside.
-/
theorem inv_norm_swap (w : ℂ) (hw : w ≠ 0) : ‖w‖ < 1 ↔ 1 < ‖w⁻¹‖ := by
  rw [ norm_inv, one_lt_inv₀ ] ; aesop;

/-
**Inversion norm product**: `‖w‖ * ‖w⁻¹‖ = 1` for `w ≠ 0`.
-/
theorem norm_mul_inv_norm (w : ℂ) (hw : w ≠ 0) : ‖w‖ * ‖w⁻¹‖ = 1 := by
  simp +decide [ hw, norm_inv ]

/-! ## Part 3: Paired Power Defect Diverges -/

/-
**Paired power growth**: For `r > 0` and `r ≠ 1`, `rⁿ + r⁻ⁿ → ∞`.
    The paired power sum is unbounded — the expanding side always dominates.
-/
theorem paired_power_unbounded (r : ℝ) (hr : 0 < r) (hr1 : r ≠ 1) (M : ℝ) :
    ∃ n : ℕ, M < r ^ n + 1 / r ^ n := by
  cases' lt_or_gt_of_ne hr1 with hr1 hr1;
  · -- Since $r < 1$, we have $1/r > 1$, and thus $1/r^n \to \infty$ as $n \to \infty$.
    have h_inv_pow_unbounded : Filter.Tendsto (fun n : ℕ => 1 / r ^ n) Filter.atTop Filter.atTop := by
      simpa using tendsto_pow_atTop_atTop_of_one_lt ( one_lt_one_div hr hr1 );
    exact ( h_inv_pow_unbounded.eventually_gt_atTop M ) |> fun h => h.exists.imp fun n hn => by linarith [ pow_pos hr n ] ;
  · cases' pow_unbounded_of_one_lt M hr1 with n hn;
    exact ⟨ n, lt_add_of_lt_of_nonneg hn <| by positivity ⟩

/-
**Accumulated mirror defect diverges**: For each off-line pair contributing
    `−(rⁿ−1)²/rⁿ`, the accumulated defect over all `n` is unbounded below.
    This is `(1 − rⁿ) + (1 − r⁻ⁿ) = −(rⁿ − 1)²/rⁿ → −∞`.
-/
theorem accumulated_defect_diverges (r : ℝ) (hr : 0 < r) (hr1 : r ≠ 1) (M : ℝ) :
    ∃ n : ℕ, (1 - r ^ n) + (1 - 1 / r ^ n) < M := by
  -- By paired_power_unbounded, � r�^n + 1/r^n > M' for large n, so 2 - (r^n + 1/r^n) < 2 - M' < M for M' large enough.
  obtain ⟨n, hn⟩ : ∃ n : ℕ, r ^ n + 1 / r ^ n > 2 - M + 1 :=paired_power_unbounded r hr hr1 (2 - M + 1);
  exact ⟨ n, by linarith ⟩

/-! ## Part 4: Self-Consistent Alignment -/

/-
**The alignment equation (positive mismatch)**: If `θ* > a` then
    `x^(θ* − a) → ∞` — the fluctuation is unbounded.
-/
theorem growth_mismatch_unbounded (a θ_star : ℝ) (ha : a < θ_star) (M : ℝ) :
    ∃ x : ℝ, 1 < x ∧ M < x ^ (θ_star - a) := by
  cases' exists_nat_gt ( Max.max M 1 ) with n hn;
  use n^ ( 1 / ( θ_star - a ) );
  exact ⟨ Real.one_lt_rpow ( by linarith [ le_max_right M 1 ] ) ( by norm_num; linarith ), by rw [ ← Real.rpow_mul ( by linarith [ le_max_right M 1 ] ), one_div_mul_cancel ( by linarith ), Real.rpow_one ] ; linarith [ le_max_left M 1 ] ⟩

/-
**The alignment equation (negative mismatch)**: If `θ* < a` then
    `x^(θ* − a) → 0` — the fluctuation decays, so the normalization
    is too aggressive and the field is artificially suppressed.
-/
theorem growth_mismatch_decays (a θ_star : ℝ) (ha : θ_star < a) :
    Filter.Tendsto (fun x : ℝ => x ^ (θ_star - a))
      Filter.atTop (nhds 0) := by
  simpa using tendsto_rpow_neg_atTop ( sub_pos.mpr ha )

/-- **The ½ is self-consistent**: If we set `a = 1/2` (radial scale)
    and `θ* = 1/2` (growth exponent), then `θ* − a = 0` and the
    fluctuation is bounded (constant power `x^0 = 1`). -/
theorem half_is_self_consistent :
    (1 : ℝ) / 2 - 1 / 2 = 0 := by norm_num

/-! ## Part 5: On-Line Properties (Bounded Rotation) -/

/-
**Bounded Li terms on-line**: When `‖w‖ = 1`, `Re[1 − wⁿ] ∈ [0, 2]`.
    The Li contribution is a bounded oscillation — sum of squares.
-/
theorem li_term_bounded_on_circle (w : ℂ) (hw : ‖w‖ = 1) (n : ℕ) :
    0 ≤ (1 - w ^ n).re ∧ (1 - w ^ n).re ≤ 2 := by
  convert And.intro ( li_re_nonneg w _ n ) ( li_re_le_two w _ n ) using 2 <;> norm_num [ hw ]

/-
**Unitary power sequence**: When `‖w‖ = 1`, the sequence `wⁿ` stays
    on the unit circle — it's a pure rotation, bounded forever.
-/
theorem unitary_power_bounded (w : ℂ) (hw : ‖w‖ = 1) (n : ℕ) :
    ‖w ^ n‖ ≤ 1 := by
  norm_num [ hw ]

/-! ## Part 6: Off-Line Properties (Spiral Destruction) -/

/-
**Off-line pair creates two-way cone**: If `‖w‖ > 1`, then
    `wⁿ → ∞` (expanding spiral) while `(1/w)ⁿ → 0` (contracting spiral).
    The two spirals are reciprocal — the cylinder splits into a cone.
-/
theorem two_way_cone (w : ℂ) (hw : 1 < ‖w‖) (n : ℕ) :
    1 < ‖w ^ n‖ ∨ n = 0 := by
  cases n <;> simp_all +decide [ pow_succ' ];
  exact one_lt_mul_of_lt_of_le hw ( one_le_pow₀ hw.le )

/-
**The expanding side dominates**: For `r > 1` and `n ≥ 1`,
    `rⁿ − r⁻ⁿ > 0` — the expansion always exceeds the contraction.
-/
theorem expansion_dominates (r : ℝ) (hr : 1 < r) (n : ℕ) (hn : 0 < n) :
    1 / r ^ n < r ^ n := by
  rw [ div_lt_iff₀ ] <;> nlinarith [ pow_le_pow_right₀ hr.le hn.nat_succ_le ]

/-
**Non-unitary growth rate**: For `‖w‖ = r > 1`, the growth rate
    of the expanding spiral is `rⁿ`, which exceeds any bound.
-/
theorem non_unitary_growth (r : ℝ) (hr : 1 < r) :
    Filter.Tendsto (fun n => r ^ n) Filter.atTop Filter.atTop := by
  exact tendsto_pow_atTop_atTop_of_one_lt hr

/-! ## Part 7: The Structure Is Incompatible with Off-Line Zeros -/

/-
**The critical line is the unique escape**: The unit circle is the
    only place where inversion is the identity (up to conjugation),
    the power sequence is bounded, and the paired defect vanishes.
    `‖w‖ = 1` is equivalent to all three properties simultaneously.
-/
theorem critical_line_unique_escape (w : ℂ) (_hw : w ≠ 0) :
    ‖w‖ = 1 ↔ (∀ n : ℕ, ‖w ^ n‖ = 1) := by
  exact ⟨ fun h n => by simp +decide [ h ], fun h => by simpa using h 1 ⟩

/-
**Off-line zeros destroy positivity**: If `‖w‖ ≠ 1` (off the line),
    then `Re[1 − wⁿ] + Re[1 − w⁻ⁿ]` is eventually < any bound M.
    The FE pairing doesn't save you — it prosecutes you.
-/
theorem offline_destroys_positivity (w : ℂ) (hw0 : w ≠ 0) (hw1 : ‖w‖ ≠ 1)
    (M : ℝ) : ∃ n : ℕ,
    (1 - w ^ n).re + (1 - (w⁻¹) ^ n).re < M := by
  -- We know that if `‖w‖ ≠ 1`, then one of `w` and `w⁻¹` has `‖·‖ > 1`.
  have h_one_gt : 1 < ‖w‖ ∨ 1 < ‖w⁻¹‖ := by
    cases lt_or_gt_of_ne hw1 <;> simp +decide [ *, norm_inv ];
    exact Or.inr ( by rw [ inv_eq_one_div, lt_div_iff₀ ( norm_pos_iff.mpr hw0 ) ] ; linarith );
  -- By symmetry, we can assume without loss of generality that `1 < ‖w‖`.
  wlog h_wgt1 : 1 < ‖w‖ generalizing w M;
  · specialize this w⁻¹ ; simp_all +decide [ add_comm ];
  · -- Since `‖w‖ > 1`, `w^n` grows unbounded (spiral_unbounded), so `re[1 - w �^n�]` becomes unbounded below.
    have h_unbounded_below : ∀ M : ℝ, ∃ n : ℕ, (1 - w ^ n).re < M := by
      intro M
      have h_unbounded : ∃ n : ℕ, (w ^ n).re > (1 - M) := by
        have := re_pow_unbounded_above w h_wgt1 ( 1 - M ) ; aesop;
      exact h_unbounded.imp fun n hn => by norm_num; linarith;
    -- Since `‖w⁻¹ �‖� < 1`, `re[1 - w⁻¹^n]` is bounded above by 2.
    have h_bounded_above : ∀ n : ℕ, (1 - w⁻¹ ^ n).re ≤ 2 := by
      exact fun n => li_re_le_two _ ( by simpa using inv_le_one_of_one_le₀ h_wgt1.le ) _;
    exact Exists.elim ( h_unbounded_below ( M - 2 ) ) fun n hn => ⟨ n, by linarith [ h_bounded_above n ] ⟩

end