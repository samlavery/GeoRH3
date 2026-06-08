import Mathlib
import RequestProject.DirichletLHadamard

/-!
# Step 4 (the hard brick): growth of `L(χ,·)` toward the order-1 Hadamard product

The character `χ ≠ 1` is *more* tractable than ζ here: its partial sums over a full period cancel
(`∑_{a : ZMod N} χ a = 0`), so the partial-sum function is **bounded**, which (via Abel summation)
gives an entire continuation with a polynomial vertical-strip bound and **no pole** — avoiding ζ's
Euler–Maclaurin-with-pole.

DONE here (all axiom-clean): bounded partial sums (`chiPartialSum_bounded`); the Abel representation
`L(χ,s)=s·∫S(⌊t⌋)t^{-(s+1)}` (`LFunction_eq_abel_integral`, `Re>1`) and its integral estimate
(`abelIntegral_norm_le`, `Re>0`); the Mellin continuation across the critical strip
(`abelIntegral_eq_mellin`, `mellin_chiSumStep_differentiableAt`, `LFunction_eq_mellin`) giving the
**strip bound** `‖L(χ,s)‖ ≤ ‖s‖·B/σ` on all `Re>0` (`LFunction_norm_le_of_pos_re`).

STAGED next (see `DirichletLHadamard_PLAN.md`): the order-1 growth of `completedLFunction χ` — NOT via
Γ-Stirling (mathlib has no complex-Γ upper bound), but via the entire completed-Hurwitz `₀`-parts on
vertical strips + the functional equation, mirroring the repo's ζ route; then the χ-agnostic Jensen
scaffold ⇒ `∑ ord(ρ)/‖ρ‖² < ∞`.
-/

open Complex

namespace DirichletLHadamard

variable {N : ℕ} [NeZero N]

/-- Summing a function over `Finset.range N` via the `ℕ → ZMod N` cast is the full sum over
    `ZMod N` (the cast is a bijection on a complete residue block). -/
theorem sum_range_eq_sum_zmod (g : ZMod N → ℂ) :
    ∑ j ∈ Finset.range N, g (j : ZMod N) = ∑ a : ZMod N, g a := by
  refine Finset.sum_nbij' (fun j => (j : ZMod N)) (fun a => a.val) ?_ ?_ ?_ ?_ ?_
  · intro j _; exact Finset.mem_univ _
  · intro a _; exact Finset.mem_range.mpr a.val_lt
  · intro j hj; exact ZMod.val_natCast_of_lt (Finset.mem_range.mp hj)
  · intro a _; exact ZMod.natCast_rightInverse a
  · intro j _; rfl

/-- **A full block of `N` consecutive character values cancels** (for `χ ≠ 1`): the translation
    invariance of the complete-residue sum plus `∑_{a} χ a = 0`. -/
theorem chi_block_sum_zero {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (M : ℕ) :
    ∑ j ∈ Finset.range N, χ ((M + j : ℕ) : ZMod N) = 0 := by
  have e1 : ∑ j ∈ Finset.range N, χ ((M + j : ℕ) : ZMod N)
      = ∑ j ∈ Finset.range N, χ ((M : ZMod N) + (j : ZMod N)) :=
    Finset.sum_congr rfl (fun j _ => by congr 1; push_cast; ring)
  have e2 : ∑ j ∈ Finset.range N, χ ((M : ZMod N) + (j : ZMod N))
      = ∑ a : ZMod N, χ ((M : ZMod N) + a) :=
    sum_range_eq_sum_zmod (fun a => χ ((M : ZMod N) + a))
  have e3 : ∑ a : ZMod N, χ ((M : ZMod N) + a) = ∑ a : ZMod N, χ a :=
    Equiv.sum_comp (Equiv.addLeft (M : ZMod N)) χ
  rw [e1, e2, e3]
  exact MulChar.sum_eq_zero_of_ne_one hχ

/-- **The character partial-sum function is `N`-periodic** (each added block cancels). -/
theorem chiPartialSum_periodic {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (M : ℕ) :
    ∑ n ∈ Finset.range (M + N), χ (n : ZMod N) = ∑ n ∈ Finset.range M, χ (n : ZMod N) := by
  have hblock : ∑ n ∈ Finset.Ico M (M + N), χ (n : ZMod N) = 0 := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_left]
    exact chi_block_sum_zero hχ M
  have hsub := Finset.sum_Ico_eq_sub (fun n => χ ((n : ℕ) : ZMod N)) (Nat.le_add_right M N)
  rw [hblock] at hsub
  exact sub_eq_zero.mp hsub.symm

/-- **Bounded character partial sums** — the key fact making `L(χ,·)` (for `χ ≠ 1`) tractable: the
    partial sums of `χ` are bounded uniformly in `M`, by `∑_{j<N} ‖χ(j)‖ ≤ N`. (This is what drives
    the Abel-summation polynomial strip bound, with no pole — unlike ζ.) -/
theorem chiPartialSum_bounded {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    ∃ B : ℝ, ∀ M : ℕ, ‖∑ n ∈ Finset.range M, χ (n : ZMod N)‖ ≤ B := by
  refine ⟨∑ j ∈ Finset.range N, ‖χ (j : ZMod N)‖, fun M => ?_⟩
  have hkr : ∀ (k r : ℕ),
      ∑ n ∈ Finset.range (N * k + r), χ (n : ZMod N)
        = ∑ n ∈ Finset.range r, χ (n : ZMod N) := by
    intro k
    induction k with
    | zero => intro r; simp
    | succ k ih =>
        intro r
        have he : N * (k + 1) + r = (N * k + r) + N := by ring
        rw [he, chiPartialSum_periodic hχ, ih]
  have hM : ∑ n ∈ Finset.range M, χ (n : ZMod N)
      = ∑ n ∈ Finset.range (M % N), χ (n : ZMod N) := by
    have h := hkr (M / N) (M % N)
    rwa [Nat.div_add_mod] at h
  rw [hM]
  have hNpos : 0 < N := Nat.pos_of_ne_zero (‹NeZero N›.out)
  calc ‖∑ n ∈ Finset.range (M % N), χ (n : ZMod N)‖
      ≤ ∑ n ∈ Finset.range (M % N), ‖χ (n : ZMod N)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range N, ‖χ (j : ZMod N)‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun x hx => Finset.mem_range.mpr
            (lt_of_lt_of_le (Finset.mem_range.mp hx) (le_of_lt (Nat.mod_lt M hNpos))))
          (fun _ _ _ => norm_nonneg _)

/-- Bounded partial sums over `Icc 1 m` (the form appearing in the Abel integrand). -/
theorem chiPartialSum_Icc_bounded {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ m : ℕ, ‖∑ k ∈ Finset.Icc 1 m, χ (k : ZMod N)‖ ≤ B := by
  obtain ⟨B, hB⟩ := chiPartialSum_bounded hχ
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  refine ⟨B + ‖χ (0 : ZMod N)‖, add_nonneg hB0 (norm_nonneg _), fun m => ?_⟩
  have hset : Finset.range (m + 1) = insert 0 (Finset.Icc 1 m) := by
    ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  have hsplit : ∑ k ∈ Finset.Icc 1 m, χ (k : ZMod N)
      = (∑ k ∈ Finset.range (m + 1), χ (k : ZMod N)) - χ (0 : ZMod N) := by
    rw [hset, Finset.sum_insert (by simp)]; simp only [Nat.cast_zero]; ring
  rw [hsplit]
  calc ‖(∑ k ∈ Finset.range (m + 1), χ (k : ZMod N)) - χ (0 : ZMod N)‖
      ≤ ‖∑ k ∈ Finset.range (m + 1), χ (k : ZMod N)‖ + ‖χ (0 : ZMod N)‖ := norm_sub_le _ _
    _ ≤ B + ‖χ (0 : ZMod N)‖ := by gcongr; exact hB (m + 1)

open MeasureTheory in
/-- **Abel integral representation of `L(χ,·)`** for `Re s > 1`: from mathlib's
    `LSeries_eq_mul_integral'`, using only `‖χ(k)‖ ≤ 1` (so `∑‖χ(k)‖ = O(n)`). The integrand's
    partial sums are bounded (`chiPartialSum_bounded`), so the right-hand integral in fact converges
    for all `Re s > 0` — this representation is the analytic continuation that gives the strip bound. -/
theorem LFunction_eq_abel_integral {χ : DirichletCharacter ℂ N} {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.LFunction χ s
      = s * ∫ t in Set.Ioi (1 : ℝ),
          (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ (k : ZMod N)) * (t : ℂ) ^ (-(s + 1)) := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  refine LSeries_eq_mul_integral' (fun n => χ (n : ZMod N)) zero_le_one hs ?_
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, Filter.Eventually.of_forall (fun n => ?_)⟩
  have hnn : (0 : ℝ) ≤ ∑ k ∈ Finset.Icc 1 n, ‖χ (k : ZMod N)‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnn, Real.rpow_one]
  calc ∑ k ∈ Finset.Icc 1 n, ‖χ (k : ZMod N)‖
      ≤ ∑ _k ∈ Finset.Icc 1 n, (1 : ℝ) :=
        Finset.sum_le_sum (fun k _ => DirichletCharacter.norm_le_one χ _)
    _ = (n : ℝ) := by simp [Nat.card_Icc]
    _ = 1 * ‖(n : ℝ)‖ := by rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n), one_mul]

open MeasureTheory in
omit [NeZero N] in
/-- **The Abel integral estimate**: `‖∫ S(⌊t⌋)·t^{-(s+1)}‖ ≤ B/σ` for `Re s = σ > 0`, where `B`
    bounds the partial sums. This is the strip bound on the Abel representation — it holds for all
    `Re s > 0` (the integral converges there), which is the analytic-continuation route. -/
theorem abelIntegral_norm_le {χ : DirichletCharacter ℂ N} {s : ℂ} (hs : 0 < s.re)
    {B : ℝ}
    (hB : ∀ m : ℕ, ‖∑ k ∈ Finset.Icc 1 m, χ (k : ZMod N)‖ ≤ B) :
    ‖∫ t in Set.Ioi (1 : ℝ),
        (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ (k : ZMod N)) * (t : ℂ) ^ (-(s + 1))‖ ≤ B / s.re := by
  have ha : -(s.re + 1) < -1 := by linarith
  have hnorm : ∀ t ∈ Set.Ioi (1 : ℝ),
      ‖(∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ (k : ZMod N)) * (t : ℂ) ^ (-(s + 1))‖
        ≤ B * t ^ (-(s.re + 1)) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_trans one_pos ht
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have hre : (-(s + 1)).re = -(s.re + 1) := by simp [Complex.neg_re, Complex.add_re]
    rw [hre]
    exact mul_le_mul_of_nonneg_right (hB _) (Real.rpow_nonneg (le_of_lt ht0) _)
  have hg_int : IntegrableOn (fun t : ℝ => B * t ^ (-(s.re + 1))) (Set.Ioi (1 : ℝ)) volume :=
    (integrableOn_Ioi_rpow_of_lt ha (by norm_num : (0 : ℝ) < 1)).const_mul B
  have hae := ae_restrict_of_forall_mem (μ := volume) measurableSet_Ioi hnorm
  calc ‖∫ t in Set.Ioi (1 : ℝ),
          (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ (k : ZMod N)) * (t : ℂ) ^ (-(s + 1))‖
      ≤ ∫ t in Set.Ioi (1 : ℝ), B * t ^ (-(s.re + 1)) :=
        norm_integral_le_of_norm_le hg_int hae
    _ = B * ∫ t in Set.Ioi (1 : ℝ), t ^ (-(s.re + 1)) := by rw [integral_const_mul]
    _ = B / s.re := by
        rw [integral_Ioi_rpow_of_lt ha one_pos, Real.one_rpow,
          show -(s.re + 1) + 1 = -s.re from by ring, neg_div_neg_eq, mul_one_div]

/-- **`L(χ,·)` bound from the Abel chain** (`Re s > 1`): `‖L(χ,s)‖ ≤ ‖s‖·B/σ`, combining the Abel
    representation with the integral estimate. The same bound extends to the critical strip once the
    representation is continued to `Re s > 0` (the integral already converges there). -/
theorem LFunction_norm_le_of_one_lt_re {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {s : ℂ}
    (hs : 1 < s.re) :
    ∃ B : ℝ, 0 ≤ B ∧ ‖DirichletCharacter.LFunction χ s‖ ≤ ‖s‖ * B / s.re := by
  obtain ⟨B, hB0, hB⟩ := chiPartialSum_Icc_bounded hχ
  refine ⟨B, hB0, ?_⟩
  rw [LFunction_eq_abel_integral hs, norm_mul]
  calc ‖s‖ * ‖∫ t in Set.Ioi (1 : ℝ),
          (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ (k : ZMod N)) * (t : ℂ) ^ (-(s + 1))‖
      ≤ ‖s‖ * (B / s.re) :=
        mul_le_mul_of_nonneg_left (abelIntegral_norm_le (by linarith) hB) (norm_nonneg _)
    _ = ‖s‖ * B / s.re := by ring

/-! ## Continuation to the strip via the Mellin transform

The Abel integral is the Mellin transform of the partial-sum step function `S(⌊t⌋)` (which is `0`
on `(0,1)` and bounded after). mathlib's `mellin_differentiableAt_of_isBigO_rpow` then gives
holomorphy on `Re s > 0` (bounded ⇒ `O(x^0)` at `∞`; zero near `0` ⇒ any decay), and the identity
theorem extends the representation from `Re s > 1` to the strip — yielding the strip bound. -/

/-- The character partial-sum step function `t ↦ ∑_{k≤⌊t⌋} χ(k)` (the Abel/Mellin integrand). -/
noncomputable def chiSumStep (χ : DirichletCharacter ℂ N) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ (k : ZMod N)

omit [NeZero N] in
/-- The step function vanishes on `(−∞, 1)` (`⌊t⌋₊ = 0`, so `Icc 1 0 = ∅`). -/
theorem chiSumStep_eq_zero {χ : DirichletCharacter ℂ N} {t : ℝ} (ht : t < 1) :
    chiSumStep χ t = 0 := by
  rw [chiSumStep, Nat.floor_eq_zero.mpr ht]
  simp

omit [NeZero N] in
/-- The step function is bounded by the partial-sum bound `B`. -/
theorem chiSumStep_norm_le {χ : DirichletCharacter ℂ N} {B : ℝ}
    (hB : ∀ m : ℕ, ‖∑ k ∈ Finset.Icc 1 m, χ (k : ZMod N)‖ ≤ B) (t : ℝ) :
    ‖chiSumStep χ t‖ ≤ B :=
  hB ⌊t⌋₊

omit [NeZero N] in
/-- The step function is measurable (`(ℕ → ℂ) ∘ ⌊·⌋₊`). -/
theorem measurable_chiSumStep (χ : DirichletCharacter ℂ N) : Measurable (chiSumStep χ) :=
  (measurable_of_countable (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, χ (k : ZMod N))).comp
    Nat.measurable_floor

omit [NeZero N] in
/-- `O(x^0)` at `+∞` (the boundedness bound, `a = 0` for the Mellin lemma). -/
theorem chiSumStep_isBigO_atTop {χ : DirichletCharacter ℂ N} {B : ℝ}
    (hB : ∀ m : ℕ, ‖∑ k ∈ Finset.Icc 1 m, χ (k : ZMod N)‖ ≤ B) :
    chiSumStep χ =O[Filter.atTop] (fun x : ℝ => x ^ (-(0 : ℝ))) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨B, Filter.Eventually.of_forall (fun x => ?_)⟩
  rw [neg_zero, Real.rpow_zero, norm_one, mul_one]
  exact chiSumStep_norm_le hB x

omit [NeZero N] in
/-- `O(x^{-b})` near `0` for every `b` (the step function is `0` there). -/
theorem chiSumStep_isBigO_zero {χ : DirichletCharacter ℂ N} (b : ℝ) :
    chiSumStep χ =O[nhdsWithin 0 (Set.Ioi 0)] (fun x : ℝ => x ^ (-b)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, ?_⟩
  have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), chiSumStep χ t = 0 :=
    ((Filter.eventually_of_mem (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
      (fun t ht => ht)).filter_mono nhdsWithin_le_nhds).mono (fun t ht => chiSumStep_eq_zero ht)
  filter_upwards [hev] with t ht
  rw [ht, norm_zero]
  positivity

open MeasureTheory in
omit [NeZero N] in
/-- The step function is locally integrable on `Ioi 0` (bounded + measurable). -/
theorem chiSumStep_locallyIntegrableOn {χ : DirichletCharacter ℂ N} {B : ℝ}
    (hB : ∀ m : ℕ, ‖∑ k ∈ Finset.Icc 1 m, χ (k : ZMod N)‖ ≤ B) :
    LocallyIntegrableOn (chiSumStep χ) (Set.Ioi 0) := by
  intro x _
  refine ⟨Metric.ball x 1, mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x one_pos), ?_⟩
  exact Measure.integrableOn_of_bounded measure_ball_lt_top.ne
    (measurable_chiSumStep χ).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun t => chiSumStep_norm_le hB t))

open MeasureTheory in
omit [NeZero N] in
/-- **Holomorphy of the Abel/Mellin integral on `Re s > 0`**: `mellin (chiSumStep χ)` is
    differentiable at `-s` (so the integral `= mellin (chiSumStep χ) (-s)` is holomorphic on the
    strip). The key continuation step, from mathlib's `mellin_differentiableAt_of_isBigO_rpow`. -/
theorem mellin_chiSumStep_differentiableAt {χ : DirichletCharacter ℂ N} {B : ℝ}
    (hB : ∀ m : ℕ, ‖∑ k ∈ Finset.Icc 1 m, χ (k : ZMod N)‖ ≤ B) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (mellin (chiSumStep χ)) (-s) := by
  refine mellin_differentiableAt_of_isBigO_rpow (chiSumStep_locallyIntegrableOn hB)
    (chiSumStep_isBigO_atTop hB) ?_ (chiSumStep_isBigO_zero (-s.re - 1)) ?_
  · rw [Complex.neg_re]; linarith
  · rw [Complex.neg_re]; linarith

open MeasureTheory in
omit [NeZero N] in
theorem abelIntegral_eq_mellin {χ : DirichletCharacter ℂ N} {s : ℂ} :
    (∫ t in Set.Ioi (1 : ℝ), chiSumStep χ t * (t : ℂ) ^ (-(s + 1)))
      = mellin (chiSumStep χ) (-s) := by
  unfold mellin
  -- Match the integrands: smul = mul, commute, and (-s)-1 = -(s+1).
  have hint : ∀ t : ℝ, (t : ℂ) ^ ((-s) - 1) • chiSumStep χ t
      = chiSumStep χ t * (t : ℂ) ^ (-(s + 1)) := by
    intro t
    rw [smul_eq_mul, mul_comm, show ((-s) - 1) = -(s + 1) from by ring]
  simp_rw [hint]
  -- Restrict Ioi 0 → Ioi 1 since the integrand vanishes a.e. on (0,1].
  symm
  apply setIntegral_eq_of_subset_of_ae_diff_eq_zero measurableSet_Ioi.nullMeasurableSet
    (Set.Ioi_subset_Ioi zero_le_one)
  filter_upwards [Measure.ae_ne (volume : Measure ℝ) 1] with t htne ht
  -- t ∈ Ioi 0 \ Ioi 1 means 0 < t and ¬(1 < t), i.e. t ≤ 1; with t ≠ 1, t < 1.
  have ht1 : t < 1 := lt_of_le_of_ne (not_lt.mp ht.2) htne
  rw [chiSumStep_eq_zero ht1, zero_mul]

open MeasureTheory in
/-- **Identity-theorem continuation (3b)**: the Abel/Mellin representation of `L(χ,·)` (`χ ≠ 1`)
    holds on the whole open half-plane `Re s > 0`, not just `Re s > 1`. Both `L(χ,·)` (entire) and
    `s ↦ s · mellin (chiSumStep χ) (-s)` (holomorphic on `Re>0` via `mellin_chiSumStep_differentiableAt`)
    agree on the open set `Re > 1` (the Abel rep), so they agree on the connected `Re > 0`. -/
theorem LFunction_eq_mellin {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.LFunction χ s = s * mellin (chiSumStep χ) (-s) := by
  obtain ⟨B, _hB0, hB⟩ := chiPartialSum_Icc_bounded hχ
  set U : Set ℂ := {z : ℂ | 0 < z.re} with hU
  set g : ℂ → ℂ := fun z => z * mellin (chiSumStep χ) (-z) with hg
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUconn : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have hf_an : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) U :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn.analyticOnNhd hUopen
  have hg_an : AnalyticOnNhd ℂ g U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUopen
    have hz' : 0 < z.re := hz
    exact (DifferentiableAt.mul differentiableAt_id
      ((mellin_chiSumStep_differentiableAt hB hz').comp z
        (differentiable_neg z))).differentiableWithinAt
  have h2U : (2 : ℂ) ∈ U := by rw [hU]; simp [Set.mem_setOf_eq]
  have hVopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have h2V : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by simp [Set.mem_setOf_eq]
  have heqV : Set.EqOn (DirichletCharacter.LFunction χ) g {z : ℂ | 1 < z.re} := by
    intro z hz
    have hz1 : 1 < z.re := hz
    rw [LFunction_eq_abel_integral hz1]
    simp only [hg]
    congr 1
    exact abelIntegral_eq_mellin
  have heventually : (DirichletCharacter.LFunction χ) =ᶠ[nhds (2 : ℂ)] g :=
    Filter.eventuallyEq_of_mem (hVopen.mem_nhds h2V) heqV
  exact hf_an.eqOn_of_preconnected_of_eventuallyEq hg_an hUconn h2U heventually hs

/-- **The strip bound (3c)**: `‖L(χ,s)‖ ≤ ‖s‖·B/σ` on the whole half-plane `Re s = σ > 0`
    (`χ ≠ 1`) — the Abel bound, now valid across the critical strip via the continuation. -/
theorem LFunction_norm_le_of_pos_re {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {s : ℂ}
    (hs : 0 < s.re) :
    ∃ B : ℝ, 0 ≤ B ∧ ‖DirichletCharacter.LFunction χ s‖ ≤ ‖s‖ * B / s.re := by
  obtain ⟨B, hB0, hB⟩ := chiPartialSum_Icc_bounded hχ
  refine ⟨B, hB0, ?_⟩
  rw [LFunction_eq_mellin hχ hs, norm_mul, ← abelIntegral_eq_mellin]
  calc ‖s‖ * ‖∫ t in Set.Ioi (1 : ℝ), chiSumStep χ t * (t : ℂ) ^ (-(s + 1))‖
      ≤ ‖s‖ * (B / s.re) :=
        mul_le_mul_of_nonneg_left (abelIntegral_norm_le hs hB) (norm_nonneg _)
    _ = ‖s‖ * B / s.re := by ring

end DirichletLHadamard
