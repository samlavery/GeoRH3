import RequestProject.ClosedForm
/-!
# L-functions in phasor form: character buckets, log-`n` spin, and magnitude decay
This file makes precise, and proves, the informal statement
> *L-functions can be represented in phasor form: the fiber/conductor modulus is set by the
> Dirichlet character, which accumulates the phasors into negative / positive / neutral
> buckets; the phasors spin in `log n` and decay towards `0` in magnitude.*
The mathematically honest content is a **representation equality** for the Dirichlet `L`-series
```
L(χ, s) = ∑ₙ χ(n) · n^{-s},   s = σ + i y,
```
together with the geometric description of each term.  On the vertical line `s = σ + i y`
the `n`-th term of `L(χ, s)` is the *phasor*
```
phasorTerm χ σ y n  =  χ(n) · n^{-σ} · exp(-(y · log n)·i),
```
a complex number with
* **bucket / character factor** `χ(n)` — for a *real (quadratic)* character this is one of
  `+1` (positive bucket), `-1` (negative bucket) or `0` (neutral bucket)
  (`phasorTerm_bucket_trichotomy`);
* **conductor modulus** `q`: the bucket of `n` is determined purely by `n mod q`, i.e. by the
  modulus/conductor of the character (`bucket_eq_of_mod_eq`);
* **magnitude** `|χ(n)|·n^{-σ}` (`phasorTerm_norm`), which **decays towards `0`** as `n → ∞`
  whenever `σ > 0` (`phasorMagnitude_tendsto_zero`, `phasorTerm_norm_tendsto_zero`);
* **spin** the unit phasor `exp(-(y·log n)·i)` (`spin`), of modulus `1` (`spin_norm`), which
  **spins in `log n`**: the angle is additive in `log n`, so the spin is multiplicative in `n`
  (`spin_mul`).
The capstone `LSeries_phasor_representation` records the representation equality
`L(χ, s) = ∑ₙ phasorTerm χ σ y n`, and `lfunction_phasor_form` bundles the full geometric
picture for a quadratic character.  No `axiom`, no `sorry`.
-/
open Complex
open scoped BigOperators
namespace CriticalLinePhasor.LFunctionPhasor
open CriticalLinePhasor
/-- The **spin phasor** attached to `n` on the line `s = σ + i y`: the unit-modulus rotation
`exp(-(y · log n)·i)`.  Its angle `-(y · log n)` is what "spins in `log n`". -/
noncomputable def spin (y : ℝ) (n : ℕ) : ℂ := Complex.exp (-(y * Real.log n) * I)
/-- The **phasor term** of the Dirichlet series with weight `χ` on the line `s = σ + i y`:
`χ(n) · n^{-σ} · exp(-(y · log n)·i)` for `n ≥ 1`, and `0` at `n = 0` (matching `LSeries.term`).
Its magnitude is `|χ(n)|·n^{-σ}`, its bucket is `χ(n)` and its spin is `spin y n`. -/
noncomputable def phasorTerm (χ : ℕ → ℂ) (σ y : ℝ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else χ n * ((n : ℝ) ^ (-σ) : ℝ) * spin y n
/-! ## 1. The spin: unit modulus, and "spins in `log n`" -/
/-- The spin phasor has **unit modulus**: `‖exp(-(y · log n)·i)‖ = 1`. -/
theorem spin_norm (y : ℝ) (n : ℕ) : ‖spin y n‖ = 1 := by
  rw [show spin y n = Complex.exp (-(y * Real.log n) * I) from rfl, Complex.norm_exp]
  norm_num [Complex.log_im]
/-- **The spin spins in `log n`.**  Because `log` turns products into sums, the spin angle is
*additive in `log n`*, hence the spin phasor is **multiplicative in `n`**:
`spin y (m·n) = spin y m · spin y n` for positive `m, n`.  This is the precise sense in which
"the phasors spin in `log n`". -/
theorem spin_mul (y : ℝ) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    spin y (m * n) = spin y m * spin y n := by
  rw [spin, spin, spin, ← Complex.exp_add]
  push_cast [Real.log_mul (by positivity : (m : ℝ) ≠ 0) (by positivity : (n : ℝ) ≠ 0)]
  ring_nf
/-! ## 2. The representation equality `L(χ, s) = ∑ₙ phasorTerm` -/
/-- **Each `L`-series term is the phasor term.**  On the line `s = σ + i y`, the `n`-th term
`χ(n) / n^{s}` of the Dirichlet `L`-series equals the phasor
`χ(n) · n^{-σ} · exp(-(y · log n)·i)`. -/
theorem term_eq_phasorTerm (χ : ℕ → ℂ) (σ y : ℝ) (n : ℕ) :
    LSeries.term χ ((σ : ℂ) + (y : ℂ) * I) n = phasorTerm χ σ y n := by
  rcases eq_or_ne n 0 with hn | hn
  · simp [LSeries.term, phasorTerm, hn]
  · rw [LSeries.term_of_ne_zero hn, phasorTerm, if_neg hn, spin, div_eq_mul_inv,
      ← Complex.cpow_neg]
    have h := CriticalLinePhasor.cpow_vertical_line_phasor (n : ℝ) (by positivity) σ y
    push_cast at h ⊢
    rw [h, mul_assoc]
/-- **L-functions in phasor form (representation equality).**  For any Dirichlet weight `χ`,
on the vertical line `s = σ + i y`,
```
L(χ, s) = ∑ₙ χ(n) · n^{-σ} · exp(-(y · log n)·i).
```
Each summand is a phasor with magnitude `|χ(n)|·n^{-σ}` and spin `exp(-(y · log n)·i)`. -/
theorem LSeries_phasor_representation (χ : ℕ → ℂ) (σ y : ℝ) :
    LSeries χ ((σ : ℂ) + (y : ℂ) * I) = ∑' n, phasorTerm χ σ y n :=
  tsum_congr fun n => term_eq_phasorTerm χ σ y n
/-! ## 3. Magnitude: value `|χ(n)|·n^{-σ}` and decay towards `0` -/
/-- **Magnitude of the phasor term.**  For `n ≥ 1`, `‖phasorTerm χ σ y n‖ = ‖χ(n)‖·n^{-σ}`:
the character bucket sets the amplitude weight, the spin contributes modulus `1`. -/
theorem phasorTerm_norm (χ : ℕ → ℂ) (σ y : ℝ) (n : ℕ) (hn : 0 < n) :
    ‖phasorTerm χ σ y n‖ = ‖χ n‖ * (n : ℝ) ^ (-σ) := by
  unfold phasorTerm
  rw [if_neg hn.ne', norm_mul, norm_mul, spin_norm, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
/-- **Magnitude bound for a bounded (e.g. Dirichlet) character.**  If `‖χ(n)‖ ≤ 1`, the phasor
magnitude is at most `n^{-σ}`. -/
theorem phasorTerm_norm_le (χ : ℕ → ℂ) (σ y : ℝ) (n : ℕ) (hb : ‖χ n‖ ≤ 1) :
    ‖phasorTerm χ σ y n‖ ≤ (n : ℝ) ^ (-σ) := by
  by_cases hn : n = 0
  · simp [phasorTerm, hn]; positivity
  · rw [phasorTerm_norm χ σ y n (Nat.pos_of_ne_zero hn)]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg n) (-σ)) hb
/-- **The magnitude weight decays to `0`.**  For `σ > 0` the amplitude `n^{-σ} → 0` as
`n → ∞`: the phasors decay towards `0` in magnitude. -/
theorem phasorMagnitude_tendsto_zero (σ : ℝ) (hσ : 0 < σ) :
    Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (-σ)) Filter.atTop (nhds 0) :=
  (tendsto_rpow_neg_atTop hσ).comp tendsto_natCast_atTop_atTop
/-- **The phasor terms decay to `0` in magnitude.**  For a character with `‖χ(n)‖ ≤ 1` for all
`n` and `σ > 0`, the magnitudes `‖phasorTerm χ σ y n‖ → 0`. -/
theorem phasorTerm_norm_tendsto_zero (χ : ℕ → ℂ) (σ y : ℝ) (hσ : 0 < σ)
    (hb : ∀ n, ‖χ n‖ ≤ 1) :
    Filter.Tendsto (fun n : ℕ => ‖phasorTerm χ σ y n‖) Filter.atTop (nhds 0) :=
  squeeze_zero (fun _ => norm_nonneg _) (fun n => phasorTerm_norm_le χ σ y n (hb n))
    (phasorMagnitude_tendsto_zero σ hσ)
/-! ## 4. Conductor modulus and the neg / pos / neutral buckets -/
/-- **The bucket is set by the conductor modulus.**  For a Dirichlet character `χ` modulo `q`,
the bucket value `χ(n)` depends only on `n mod q`: if `m ≡ n (mod q)` then `χ(m) = χ(n)`.
This is the precise content of "the fiber/conductor modulus is set by the character". -/
theorem bucket_eq_of_mod_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (m n : ℕ)
    (h : (m : ZMod q) = (n : ZMod q)) : χ m = χ n :=
  congrArg (fun z : ZMod q => χ z) h
/-- **The neg / pos / neutral buckets.**  For a *real (quadratic)* Dirichlet character `χ`,
every value `χ(n)` is one of `+1` (positive bucket), `-1` (negative bucket) or `0` (neutral
bucket).  Thus the character accumulates the phasors into exactly three buckets. -/
theorem phasorTerm_bucket_trichotomy {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hq : χ.IsQuadratic) (n : ℕ) :
    χ n = 0 ∨ χ n = 1 ∨ χ n = -1 :=
  hq n
/-- **Bucketed phasor term for a quadratic character.**  For `n ≥ 1` the phasor term is the
common magnitude·spin `n^{-σ}·exp(-(y·log n)·i)` multiplied by the bucket sign `χ(n) ∈ {0,±1}`:
the positive bucket adds it, the negative bucket subtracts it, the neutral bucket drops it. -/
theorem phasorTerm_bucketed {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hq : χ.IsQuadratic) (σ y : ℝ) (n : ℕ) (hn : 0 < n) :
    (phasorTerm (fun k => χ k) σ y n
        = ((n : ℝ) ^ (-σ) : ℝ) * spin y n
      ∧ χ n = 1)
    ∨ (phasorTerm (fun k => χ k) σ y n
        = -(((n : ℝ) ^ (-σ) : ℝ) * spin y n)
      ∧ χ n = -1)
    ∨ (phasorTerm (fun k => χ k) σ y n = 0 ∧ χ n = 0) := by
  unfold phasorTerm
  rcases phasorTerm_bucket_trichotomy χ hq n with h | h | h <;> simp +decide [h, hn.ne']
/-! ## 5. Capstone: the full phasor-form picture for a quadratic L-function -/
/-- **L-function phasor form (full picture).**  For a real (quadratic) Dirichlet character `χ`
modulo `q`, on the vertical line `s = σ + i y` with `σ > 0`:
1. **representation equality** `L(χ, s) = ∑ₙ phasorTerm χ σ y n`;
2. each term factors as `χ(n) · n^{-σ} · spin y n` with **unit-modulus spin** `‖spin y n‖ = 1`;
3. the spin **spins in `log n`** — `spin y (m·n) = spin y m · spin y n`;
4. the **magnitudes decay to `0`** — `‖phasorTerm χ σ y n‖ → 0`;
5. the **conductor modulus `q` sets the bucket** — `m ≡ n (mod q) ⟹ χ(m) = χ(n)`;
6. the buckets are **neg / pos / neutral** — `χ(n) ∈ {-1, 0, +1}`. -/
theorem lfunction_phasor_form {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hq : χ.IsQuadratic) (σ y : ℝ) (hσ : 0 < σ) :
    LSeries (fun n => χ n) ((σ : ℂ) + (y : ℂ) * I) = ∑' n, phasorTerm (fun n => χ n) σ y n
      ∧ (∀ n : ℕ, 0 < n →
          phasorTerm (fun n => χ n) σ y n = χ n * ((n : ℝ) ^ (-σ) : ℝ) * spin y n)
      ∧ (∀ n : ℕ, ‖spin y n‖ = 1)
      ∧ (∀ m n : ℕ, 0 < m → 0 < n → spin y (m * n) = spin y m * spin y n)
      ∧ Filter.Tendsto (fun n : ℕ => ‖phasorTerm (fun n => χ n) σ y n‖) Filter.atTop (nhds 0)
      ∧ (∀ m n : ℕ, (m : ZMod q) = (n : ZMod q) → χ m = χ n)
      ∧ (∀ n : ℕ, χ n = 0 ∨ χ n = 1 ∨ χ n = -1) := by
  refine ⟨LSeries_phasor_representation (fun n => χ n) σ y, ?_, spin_norm y, spin_mul y, ?_,
    fun m n h => bucket_eq_of_mod_eq χ m n h, fun n => phasorTerm_bucket_trichotomy χ hq n⟩
  · intro n hn
    simp only [phasorTerm, if_neg hn.ne']
  · refine phasorTerm_norm_tendsto_zero (fun n => χ n) σ y hσ (fun n => ?_)
    rcases phasorTerm_bucket_trichotomy χ hq n with h | h | h <;> norm_num [h]
/-! ## 6. Bucket cancellation: bounded character partial sums (the strip-extension input)

For a *non-principal* character the pos/neg/neutral buckets cancel: every block of `q` consecutive
integers is a complete residue system on which `∑ χ = 0`. Hence the partial sums `∑_{n<N} χ(n)` are
bounded — the Dirichlet's-test / Abel-summation input that carries the phasor channel past the
`Re = 1` absolute-convergence wall into the strip `Re > 0`. -/

/-- **A block of `q` consecutive integers sums to `0`** for a non-principal Dirichlet character:
it is a complete residue system, and `∑_{a : ZMod q} χ a = 0` (`MulChar.sum_eq_zero_of_ne_one`). -/
theorem character_block_sum_eq_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (M : ℕ) : ∑ k ∈ Finset.range q, χ ((M + k : ℕ) : ZMod q) = 0 := by
  classical
  have e : ∑ k ∈ Finset.range q, χ ((M + k : ℕ) : ZMod q) = ∑ a : ZMod q, χ a := by
    refine Finset.sum_bij' (fun k _ => ((M + k : ℕ) : ZMod q))
      (fun a _ => ((a - (M : ZMod q)).val))
      (fun k _ => Finset.mem_univ _)
      (fun a _ => Finset.mem_range.mpr (ZMod.val_lt _))
      ?_ ?_ ?_
    · intro k hk
      have hkq : k < q := Finset.mem_range.mp hk
      rw [Nat.cast_add, add_sub_cancel_left, ZMod.val_natCast_of_lt hkq]
    · intro a _
      rw [Nat.cast_add, ZMod.natCast_val, ZMod.cast_id, add_sub_cancel]
    · intro k _
      rfl
  rw [e]
  exact MulChar.sum_eq_zero_of_ne_one hχ

/-- **Bounded character partial sums.** For a non-principal Dirichlet character mod `q`, the partial
sums `∑_{n<N} χ(n)` are bounded by `q`: complete periods vanish (`character_block_sum_eq_zero`),
leaving a final partial block of `< q` unit-bounded terms. This is the Dirichlet's-test / Abel
input that carries the phasor channel from `Re > 1` into the strip `Re > 0`. -/
theorem character_partialSum_norm_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (N : ℕ) : ‖∑ n ∈ Finset.range N, χ ((n : ZMod q))‖ ≤ q := by
  classical
  have hperiods : ∀ k : ℕ, ∑ n ∈ Finset.range (q * k), χ ((n : ZMod q)) = 0 := by
    intro k
    induction k with
    | zero => simp
    | succ m ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih, zero_add]
      exact character_block_sum_eq_zero χ hχ (q * m)
  have hsplit : ∑ n ∈ Finset.range N, χ ((n : ZMod q))
      = ∑ k ∈ Finset.range (N % q), χ ((q * (N / q) + k : ℕ) : ZMod q) := by
    conv_lhs => rw [← Nat.div_add_mod N q]
    rw [Finset.sum_range_add, hperiods, zero_add]
  rw [hsplit]
  have hmod : N % q < q := Nat.mod_lt _ (NeZero.pos q)
  calc ‖∑ k ∈ Finset.range (N % q), χ ((q * (N / q) + k : ℕ) : ZMod q)‖
      ≤ ∑ k ∈ Finset.range (N % q), ‖χ ((q * (N / q) + k : ℕ) : ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range (N % q), (1 : ℝ) :=
        Finset.sum_le_sum (fun k _ => χ.norm_le_one _)
    _ = (↑(N % q) : ℝ) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    _ ≤ (q : ℝ) := by exact_mod_cast hmod.le

/-! ## 7. Abel-summation estimates: the weight `n^{-s}` in the strip `Re s > 0` -/

open Filter Topology in
/-- **Boundary term `n^{-s} → 0`** for `Re s > 0` (the `A(N)·N^{-s}` term of Abel summation). -/
theorem cpow_neg_tendsto_zero {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto (fun n : ℕ => (n : ℂ) ^ (-s)) Filter.atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply Tendsto.congr' (f₁ := fun n : ℕ => (n : ℝ) ^ (-s.re))
  · filter_upwards [eventually_ge_atTop 1] with n hn
    rw [Complex.norm_natCast_cpow_of_pos (by omega), neg_re]
  · exact (tendsto_rpow_neg_atTop hs).comp tendsto_natCast_atTop_atTop

open Filter in
/-- **Bounded variation of `n^{-s}`** for `Re s > 0`: `∑ₙ ‖(n+1)^{-s} − n^{-s}‖ < ∞`. The
mean-value bound `‖(n+1)^{-s} − n^{-s}‖ ≤ ‖s‖·n^{-(Re s + 1)}` compares to the convergent
p-series (`Re s + 1 > 1`). This + `cpow_neg_tendsto_zero` are the two Abel-summation inputs. -/
theorem cpow_diff_summable {s : ℂ} (hs : 0 < s.re) :
    Summable (fun n : ℕ => ‖((n : ℂ) + 1) ^ (-s) - (n : ℂ) ^ (-s)‖) := by
  rw [← summable_nat_add_iff 1]
  set p : ℝ := -(s.re + 1) with hp
  have hplt : p < -1 := by
    rw [hp]; linarith
  have hbase : Summable (fun n : ℕ => (((n : ℝ) + 1)) ^ p) := by
    have h0 : Summable (fun n : ℕ => ((n : ℝ)) ^ p) := (Real.summable_nat_rpow).mpr hplt
    have := (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ)) ^ p) 1).mpr h0
    simpa using this
  have hgsum : Summable (fun n : ℕ => ‖s‖ * (((n : ℝ) + 1)) ^ p) :=
    hbase.mul_left ‖s‖
  have hderiv : ∀ (x : ℝ), 0 < x →
      HasDerivAt (fun t : ℝ => (↑t : ℂ) ^ (-s)) (-s * (↑x : ℂ) ^ (-s - 1)) x := by
    intro x hx
    have hmem : (↑x : ℂ) ∈ Complex.slitPlane := by
      rw [Complex.ofReal_mem_slitPlane]; exact hx
    have hc : HasDerivAt (fun w : ℂ => w ^ (-s)) (-s * (↑x : ℂ) ^ (-s - 1) * 1) (↑x) :=
      (hasDerivAt_id (↑x : ℂ)).cpow_const hmem
    have hc' : HasDerivAt (fun w : ℂ => w ^ (-s)) (-s * (↑x : ℂ) ^ (-s - 1)) (↑x) := by
      simpa using hc
    simpa using hc'.comp_ofReal
  have hnormderiv : ∀ (x : ℝ), 0 < x →
      ‖-s * (↑x : ℂ) ^ (-s - 1)‖ = ‖s‖ * x ^ p := by
    intro x hx
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hx]
    congr 1
    rw [hp]
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    congr 1
    ring
  have hpnonpos : p ≤ 0 := by linarith
  have key : ∀ m : ℕ, 0 < m →
      ‖((m : ℂ) + 1) ^ (-s) - (m : ℂ) ^ (-s)‖ ≤ ‖s‖ * (m : ℝ) ^ p := by
    intro m hm
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    set f : ℝ → ℂ := fun t => (↑t : ℂ) ^ (-s) with hf
    set f' : ℝ → ℂ := fun t => -s * (↑t : ℂ) ^ (-s - 1) with hf'
    set C : ℝ := ‖s‖ * (m : ℝ) ^ p with hC
    have hderivW : ∀ x ∈ Set.Icc (m : ℝ) ((m : ℝ) + 1),
        HasDerivWithinAt f (f' x) (Set.Icc (m : ℝ) ((m : ℝ) + 1)) x := by
      intro x hx
      have hxpos : 0 < x := lt_of_lt_of_le hm0 hx.1
      exact (hderiv x hxpos).hasDerivWithinAt
    have hbound : ∀ x ∈ Set.Ico (m : ℝ) ((m : ℝ) + 1), ‖f' x‖ ≤ C := by
      intro x hx
      have hxpos : 0 < x := lt_of_lt_of_le hm0 hx.1
      have hxm : (m : ℝ) ≤ x := hx.1
      rw [hf', hnormderiv x hxpos, hC]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg s)
      exact Real.rpow_le_rpow_of_nonpos hm0 hxm hpnonpos
    have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' hderivW hbound
        ((m : ℝ) + 1) (Set.right_mem_Icc.mpr (by linarith))
    rw [hf] at hmvt
    simp only at hmvt
    have hcast : (↑((m : ℝ) + 1) : ℂ) = (m : ℂ) + 1 := by push_cast; ring
    rw [hcast] at hmvt
    have hCmul : C * ((m : ℝ) + 1 - (m : ℝ)) = C := by ring
    rw [hCmul] at hmvt
    exact hmvt
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ hgsum
  intro n
  have hk := key (n + 1) (Nat.succ_pos n)
  have hcast2 : ((↑(n + 1) : ℝ)) ^ p = ((n : ℝ) + 1) ^ p := by push_cast; ring_nf
  calc ‖(↑(n + 1) + 1 : ℂ) ^ (-s) - (↑(n + 1) : ℂ) ^ (-s)‖
      ≤ ‖s‖ * ((↑(n + 1) : ℝ)) ^ p := hk
    _ = ‖s‖ * ((n : ℝ) + 1) ^ p := by rw [hcast2]

/-! ## 8. Strip convergence: the phasor channel reaches `Re s > 0` (Abel summation) -/

open Filter Topology in
/-- **Dirichlet partial sums converge for `Re s > 0`** (Dirichlet's test / Abel summation).
For a non-principal Dirichlet character `χ` mod `q`, the partial sums `∑_{n<N} χ(n)·n^{-s}`
converge whenever `Re s > 0` — the `L`-series phasor channel extends from `Re s > 1` into the
strip `Re s > 0`. The bounded character partial sums (`character_partialSum_norm_le`, the bucket
cancellation) are summed by parts against the bounded-variation weight `n^{-s}`
(`cpow_neg_tendsto_zero`, `cpow_diff_summable`). No absolute convergence; this is the
conditional/continuous accumulation that has "no strip boundary." -/
theorem dirichlet_partialSum_converges {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    ∃ L : ℂ, Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, (χ (n : ZMod q)) * (n : ℂ) ^ (-s))
      Filter.atTop (nhds L) := by
  classical
  set f : ℕ → ℂ := fun n => (n : ℂ) ^ (-s) with hf
  set g : ℕ → ℂ := fun n => χ (n : ZMod q) with hg
  set G : ℕ → ℂ := fun k => ∑ i ∈ Finset.range k, g i with hG
  have hsum_eq : ∀ N : ℕ, (∑ n ∈ Finset.range N, (χ (n : ZMod q)) * (n : ℂ) ^ (-s))
      = ∑ i ∈ Finset.range N, f i • g i := by
    intro N
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hf, hg, smul_eq_mul, mul_comm]
  have hGbound : ∀ N : ℕ, ‖G N‖ ≤ (q : ℝ) := by
    intro N
    rw [hG, hg]
    exact character_partialSum_norm_le χ hχ N
  have hpred : Tendsto (fun N : ℕ => N - 1) atTop atTop := by
    exact tendsto_atTop_atTop_of_monotone (fun a b h => Nat.sub_le_sub_right h 1)
      (fun b => ⟨b + 1, by omega⟩)
  have hf_pred : Tendsto (fun N : ℕ => f (N - 1)) atTop (nhds 0) := by
    rw [hf]
    exact (cpow_neg_tendsto_zero hs).comp hpred
  have hGbdd : IsBoundedUnder (· ≤ ·) atTop ((fun x => ‖x‖) ∘ G) :=
    ⟨(q : ℝ), Filter.eventually_map.2 (Filter.Eventually.of_forall hGbound)⟩
  have hboundary : Tendsto (fun N : ℕ => f (N - 1) • G N) atTop (nhds 0) := by
    simp only [smul_eq_mul]
    exact hf_pred.zero_mul_isBoundedUnder_le hGbdd
  have hdiff_eq : ∀ i : ℕ, ‖f (i + 1) - f i‖ = ‖((i : ℂ) + 1) ^ (-s) - (i : ℂ) ^ (-s)‖ := by
    intro i
    rw [hf]
    norm_num
  have hsummable_diff : Summable (fun i : ℕ => ‖f (i + 1) - f i‖) := by
    apply (cpow_diff_summable hs).congr
    intro i; rw [hdiff_eq i]
  have hsummable_bound : Summable (fun i : ℕ => ‖f (i + 1) - f i‖ * (q : ℝ)) :=
    hsummable_diff.mul_right (q : ℝ)
  have hsummand : Summable (fun i : ℕ => (f (i + 1) - f i) • G (i + 1)) := by
    apply Summable.of_norm_bounded hsummable_bound
    intro i
    rw [smul_eq_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hGbound (i + 1)) (norm_nonneg _)
  obtain ⟨T, hT⟩ := hsummand
  have hH : Tendsto (fun M : ℕ => ∑ i ∈ Finset.range M, (f (i + 1) - f i) • G (i + 1))
      atTop (nhds T) := hT.tendsto_sum_nat
  have hH_pred : Tendsto
      (fun N : ℕ => ∑ i ∈ Finset.range (N - 1), (f (i + 1) - f i) • G (i + 1))
      atTop (nhds T) := hH.comp hpred
  refine ⟨0 - T, ?_⟩
  have hpointwise : ∀ N : ℕ,
      (∑ n ∈ Finset.range N, (χ (n : ZMod q)) * (n : ℂ) ^ (-s))
        = (f (N - 1) • G N) - ∑ i ∈ Finset.range (N - 1), (f (i + 1) - f i) • G (i + 1) := by
    intro N
    rw [hsum_eq N, Finset.sum_range_by_parts f g N]
  refine Tendsto.congr (fun N => (hpointwise N).symm) ?_
  exact hboundary.sub hH_pred

/-! ## 9. Analytic-continuation finish: strip convergence reaches `LFunction χ`

The partial sums `∑_{n<N} χ(n)·n^{-s}` converge (Section 8) on `Re s > 0`. We now identify the
limit with `DirichletCharacter.LFunction χ` on the whole strip `Re s > 0`, by analytic
continuation: the limit is the analytic tail series `g`, it agrees with `LFunction χ` on
`Re s > 1` (where the Dirichlet series converges absolutely and equals the `L`-function), and both
are analytic on the connected open half-plane `Re s > 0`, so they agree there (identity theorem). -/

open Filter Topology in
/-- **`Re s > 1` agreement.** For `1 < Re s` the partial sums `∑_{n<N} χ(n)·n^{-s}` tend to
`LFunction χ s`: there the Dirichlet series is summable and `LFunction χ s = LSeries (χ·) s`. -/
theorem dirichlet_partialSum_tendsto_LFunction_of_one_lt {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, (χ (n : ZMod q)) * (n : ℂ) ^ (-s))
      Filter.atTop (nhds (DirichletCharacter.LFunction χ s)) := by
  have hsummable : LSeriesSummable (fun n => χ (n : ZMod q)) s :=
    ZMod.LSeriesSummable_of_one_lt_re _ hs
  have heq : DirichletCharacter.LFunction χ s = LSeries (fun n => χ (n : ZMod q)) s :=
    DirichletCharacter.LFunction_eq_LSeries χ hs
  rw [heq]
  have htend := hsummable.hasSum.tendsto_sum_nat
  refine Tendsto.congr (fun N => ?_) htend
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rcases eq_or_ne n 0 with hn | hn
  · have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs; linarith
    simp [LSeries.term, hn, hs0]
  · rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg]

open Filter Topology in
/-- **Explicit tail limit.** Abel summation (Section 8) lands the partial sums on the explicit tail
series `∑ᵢ -((i+1)^{-s} − i^{-s})·(∑_{j<i+1} χ j)`, the boundary term vanishing as `N → ∞`. -/
theorem dirichlet_partialSum_tendsto_tail {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, (χ (n : ZMod q)) * (n : ℂ) ^ (-s))
      Filter.atTop
      (nhds (∑' i : ℕ,
        (-(((i : ℂ) + 1) ^ (-s) - (i : ℂ) ^ (-s)) *
          ∑ j ∈ Finset.range (i + 1), χ (j : ZMod q)))) := by
  classical
  set f : ℕ → ℂ := fun n => (n : ℂ) ^ (-s) with hf
  set g : ℕ → ℂ := fun n => χ (n : ZMod q) with hg
  set G : ℕ → ℂ := fun k => ∑ i ∈ Finset.range k, g i with hG
  have hsum_eq : ∀ N : ℕ, (∑ n ∈ Finset.range N, (χ (n : ZMod q)) * (n : ℂ) ^ (-s))
      = ∑ i ∈ Finset.range N, f i • g i := by
    intro N
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hf, hg, smul_eq_mul, mul_comm]
  have hGbound : ∀ N : ℕ, ‖G N‖ ≤ (q : ℝ) := by
    intro N
    rw [hG, hg]
    exact character_partialSum_norm_le χ hχ N
  have hpred : Tendsto (fun N : ℕ => N - 1) atTop atTop := by
    exact tendsto_atTop_atTop_of_monotone (fun a b h => Nat.sub_le_sub_right h 1)
      (fun b => ⟨b + 1, by omega⟩)
  have hf_pred : Tendsto (fun N : ℕ => f (N - 1)) atTop (nhds 0) := by
    rw [hf]
    exact (cpow_neg_tendsto_zero hs).comp hpred
  have hGbdd : IsBoundedUnder (· ≤ ·) atTop ((fun x => ‖x‖) ∘ G) :=
    ⟨(q : ℝ), Filter.eventually_map.2 (Filter.Eventually.of_forall hGbound)⟩
  have hboundary : Tendsto (fun N : ℕ => f (N - 1) • G N) atTop (nhds 0) := by
    simp only [smul_eq_mul]
    exact hf_pred.zero_mul_isBoundedUnder_le hGbdd
  have hdiff_eq : ∀ i : ℕ, ‖f (i + 1) - f i‖ = ‖((i : ℂ) + 1) ^ (-s) - (i : ℂ) ^ (-s)‖ := by
    intro i
    rw [hf]
    norm_num
  have hsummable_diff : Summable (fun i : ℕ => ‖f (i + 1) - f i‖) := by
    apply (cpow_diff_summable hs).congr
    intro i; rw [hdiff_eq i]
  have hsummable_bound : Summable (fun i : ℕ => ‖f (i + 1) - f i‖ * (q : ℝ)) :=
    hsummable_diff.mul_right (q : ℝ)
  have hsummand : Summable (fun i : ℕ => (f (i + 1) - f i) • G (i + 1)) := by
    apply Summable.of_norm_bounded hsummable_bound
    intro i
    rw [smul_eq_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hGbound (i + 1)) (norm_nonneg _)
  obtain ⟨T, hT⟩ := hsummand
  have hH : Tendsto (fun M : ℕ => ∑ i ∈ Finset.range M, (f (i + 1) - f i) • G (i + 1))
      atTop (nhds T) := hT.tendsto_sum_nat
  have hH_pred : Tendsto
      (fun N : ℕ => ∑ i ∈ Finset.range (N - 1), (f (i + 1) - f i) • G (i + 1))
      atTop (nhds T) := hH.comp hpred
  have hTval : T = ∑' i : ℕ, (f (i + 1) - f i) • G (i + 1) := hT.tsum_eq.symm
  have hpointwise : ∀ N : ℕ,
      (∑ n ∈ Finset.range N, (χ (n : ZMod q)) * (n : ℂ) ^ (-s))
        = (f (N - 1) • G N) - ∑ i ∈ Finset.range (N - 1), (f (i + 1) - f i) • G (i + 1) := by
    intro N
    rw [hsum_eq N, Finset.sum_range_by_parts f g N]
  have hlim : Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, (χ (n : ZMod q)) * (n : ℂ) ^ (-s))
      atTop (nhds (0 - T)) := by
    refine Tendsto.congr (fun N => (hpointwise N).symm) ?_
    exact hboundary.sub hH_pred
  have hgoal : (0 : ℂ) - T = ∑' i : ℕ,
      (-(((i : ℂ) + 1) ^ (-s) - (i : ℂ) ^ (-s)) * ∑ j ∈ Finset.range (i + 1), χ (j : ZMod q)) := by
    rw [zero_sub, hTval, ← tsum_neg]
    refine tsum_congr (fun i => ?_)
    simp only [hf, hG, hg, smul_eq_mul]
    push_cast
    ring
  rw [hgoal] at hlim
  exact hlim

open Filter Topology in
/-- **Differentiability of `s ↦ (n:ℂ)^{-s}` on `Re s > 0`.** For `n ≥ 1` it is a `cpow` of a
nonzero constant; for `n = 0` it is eventually the constant `0` (since `0^{-s} = 0` for `s ≠ 0`). -/
theorem differentiableAt_natCpow_neg (n : ℕ) (r : ℂ) (hr : 0 < r.re) :
    DifferentiableAt ℂ (fun s => (n : ℂ) ^ (-s)) r := by
  rcases eq_or_ne n 0 with hn | hn
  · subst hn
    have hev : (fun s => ((0 : ℕ) : ℂ) ^ (-s)) =ᶠ[nhds r] (fun _ => (0 : ℂ)) := by
      have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
      filter_upwards [hopen.mem_nhds hr] with z hz
      have hz0 : z ≠ 0 := by
        intro h; rw [h] at hz; simp at hz
      simp only [Nat.cast_zero]
      rw [Complex.zero_cpow (neg_ne_zero.mpr hz0)]
    refine (differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq hev
  · have : NeZero (n : ℂ) := ⟨Nat.cast_ne_zero.mpr hn⟩
    have hcomp : DifferentiableAt ℂ (fun s => (n : ℂ) ^ s) (-r) :=
      differentiableAt_const_cpow_of_neZero (n : ℂ) (-r)
    exact hcomp.comp r (differentiableAt_id.neg)

/-- **Mean-value bound `‖(m+1)^{-s} − m^{-s}‖ ≤ ‖s‖·m^{−(Re s+1)}`** for `m ≥ 1`, `Re s > 0`
(the uniform input to the M-test below). -/
theorem term_mvt_bound (s : ℂ) (hs : 0 < s.re) (m : ℕ) (hm : 0 < m) :
    ‖((m : ℂ) + 1) ^ (-s) - (m : ℂ) ^ (-s)‖ ≤ ‖s‖ * (m : ℝ) ^ (-(s.re + 1)) := by
  set p : ℝ := -(s.re + 1) with hp
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hpnonpos : p ≤ 0 := by rw [hp]; linarith
  have hderiv : ∀ (x : ℝ), 0 < x →
      HasDerivAt (fun t : ℝ => (↑t : ℂ) ^ (-s)) (-s * (↑x : ℂ) ^ (-s - 1)) x := by
    intro x hx
    have hmem : (↑x : ℂ) ∈ Complex.slitPlane := by
      rw [Complex.ofReal_mem_slitPlane]; exact hx
    have hc : HasDerivAt (fun w : ℂ => w ^ (-s)) (-s * (↑x : ℂ) ^ (-s - 1) * 1) (↑x) :=
      (hasDerivAt_id (↑x : ℂ)).cpow_const hmem
    have hc' : HasDerivAt (fun w : ℂ => w ^ (-s)) (-s * (↑x : ℂ) ^ (-s - 1)) (↑x) := by
      simpa using hc
    simpa using hc'.comp_ofReal
  have hnormderiv : ∀ (x : ℝ), 0 < x →
      ‖-s * (↑x : ℂ) ^ (-s - 1)‖ = ‖s‖ * x ^ p := by
    intro x hx
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hx]
    congr 1
    rw [hp]
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    congr 1
    ring
  set f : ℝ → ℂ := fun t => (↑t : ℂ) ^ (-s) with hf
  set f' : ℝ → ℂ := fun t => -s * (↑t : ℂ) ^ (-s - 1) with hf'
  set C : ℝ := ‖s‖ * (m : ℝ) ^ p with hC
  have hderivW : ∀ x ∈ Set.Icc (m : ℝ) ((m : ℝ) + 1),
      HasDerivWithinAt f (f' x) (Set.Icc (m : ℝ) ((m : ℝ) + 1)) x := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hm0 hx.1
    exact (hderiv x hxpos).hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Ico (m : ℝ) ((m : ℝ) + 1), ‖f' x‖ ≤ C := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hm0 hx.1
    have hxm : (m : ℝ) ≤ x := hx.1
    rw [hf', hnormderiv x hxpos, hC]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg s)
    exact Real.rpow_le_rpow_of_nonpos hm0 hxm hpnonpos
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' hderivW hbound
      ((m : ℝ) + 1) (Set.right_mem_Icc.mpr (by linarith))
  rw [hf] at hmvt
  simp only at hmvt
  have hcast : (↑((m : ℝ) + 1) : ℂ) = (m : ℂ) + 1 := by push_cast; ring
  rw [hcast] at hmvt
  have hCmul : C * ((m : ℝ) + 1 - (m : ℝ)) = C := by ring
  rw [hCmul] at hmvt
  exact hmvt

/-- **Local-uniform summability of the tail series on `Re s > 0`.** On any compact `K ⊆ {Re > 0}`
the difference terms are dominated by `q·(sup_K‖·‖)·i^{−(σ₀+1)}` with `σ₀ = min_K Re > 0`, a
convergent `p`-series (`σ₀+1 > 1`); the M-test (`SummableLocallyUniformlyOn_of_locally_bounded`)
gives locally-uniform summability. This is the uniform upgrade of `cpow_diff_summable`. -/
theorem summableLocallyUniformlyOn_tail {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) :
    SummableLocallyUniformlyOn
      (fun (i : ℕ) (s : ℂ) =>
        -(((i : ℂ) + 1) ^ (-s) - (i : ℂ) ^ (-s)) * ∑ j ∈ Finset.range (i + 1), χ (j : ZMod q))
      {s : ℂ | 0 < s.re} := by
  have hopen : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  refine SummableLocallyUniformlyOn_of_locally_bounded hopen ?_
  intro K hKsub hKcompact
  rcases K.eq_empty_or_nonempty with hKempty | hKne
  · refine ⟨fun _ => 0, summable_zero, ?_⟩
    intro n k hk
    rw [hKempty] at hk
    exact absurd hk (by simp)
  · obtain ⟨z₀, hz₀K, hz₀min⟩ :=
      hKcompact.exists_isMinOn hKne (Complex.continuous_re.continuousOn)
    rw [isMinOn_iff] at hz₀min
    set σ₀ : ℝ := z₀.re with hσ₀
    have hσ₀pos : 0 < σ₀ := hKsub hz₀K
    have hσ₀le : ∀ s ∈ K, σ₀ ≤ s.re := fun s hs => hz₀min s hs
    obtain ⟨w₀, hw₀K, hw₀max⟩ :=
      hKcompact.exists_isMaxOn hKne (continuous_norm.continuousOn (s := K))
    rw [isMaxOn_iff] at hw₀max
    set C : ℝ := ‖w₀‖ with hCdef
    have hC : ∀ s ∈ K, ‖s‖ ≤ C := fun s hs => hw₀max s hs
    have hCnonneg : 0 ≤ C := norm_nonneg _
    refine ⟨fun i => (q : ℝ) * C * (i : ℝ) ^ (-(σ₀ + 1)) + (if i = 0 then (q : ℝ) else 0),
      ?_, ?_⟩
    · apply Summable.add
      · apply Summable.mul_left
        rw [Real.summable_nat_rpow]
        linarith
      · apply summable_of_hasFiniteSupport
        apply Set.Finite.subset (Set.finite_singleton 0)
        intro i hi
        simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at hi
        simp only [Set.mem_singleton_iff]
        exact hi.1
    · intro i s hsK
      have hsre : 0 < s.re := hKsub hsK
      have hsC : ‖s‖ ≤ C := hC s hsK
      have hsσ₀ : σ₀ ≤ s.re := hσ₀le s hsK
      rw [norm_mul, norm_neg]
      have hGle : ‖∑ j ∈ Finset.range (i + 1), χ (j : ZMod q)‖ ≤ (q : ℝ) :=
        character_partialSum_norm_le χ hχ (i + 1)
      simp only []
      rcases eq_or_ne i 0 with hi | hi
      · subst hi
        have hs0 : s ≠ 0 := by
          intro h; rw [h] at hsre; simp at hsre
        rw [if_pos rfl]
        simp only [Nat.cast_zero, zero_add, Complex.zero_cpow (neg_ne_zero.mpr hs0),
          sub_zero, Complex.one_cpow, norm_one, one_mul]
        have hb : ‖∑ j ∈ Finset.range 1, χ (j : ZMod q)‖ ≤ (q : ℝ) :=
          character_partialSum_norm_le χ hχ 1
        have hnn : 0 ≤ (q : ℝ) * C * (0 : ℝ) ^ (-(σ₀ + 1)) := by positivity
        linarith
      · have hipos : 0 < i := Nat.pos_of_ne_zero hi
        have hi0 : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hipos
        have hmvt := term_mvt_bound s hsre i hipos
        have hexp : (i : ℝ) ^ (-(s.re + 1)) ≤ (i : ℝ) ^ (-(σ₀ + 1)) := by
          apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hipos) (by linarith)
        have hstep1 : ‖((i : ℂ) + 1) ^ (-s) - (i : ℂ) ^ (-s)‖ ≤ ‖s‖ * (i : ℝ) ^ (-(σ₀ + 1)) :=
          le_trans hmvt (by
            apply mul_le_mul_of_nonneg_left hexp (norm_nonneg s))
        have hstep2 :
            ‖((i : ℂ) + 1) ^ (-s) - (i : ℂ) ^ (-s)‖ *
              ‖∑ j ∈ Finset.range (i + 1), χ (j : ZMod q)‖
            ≤ (‖s‖ * (i : ℝ) ^ (-(σ₀ + 1))) * (q : ℝ) := by
          apply mul_le_mul hstep1 hGle (norm_nonneg _)
          positivity
        rw [if_neg hi, add_zero]
        refine le_trans hstep2 ?_
        have hrpownn : 0 ≤ (i : ℝ) ^ (-(σ₀ + 1)) := Real.rpow_nonneg (by positivity) _
        have heq2 : ‖s‖ * (i : ℝ) ^ (-(σ₀ + 1)) * (q : ℝ)
            = (q : ℝ) * ‖s‖ * (i : ℝ) ^ (-(σ₀ + 1)) := by ring
        rw [heq2]
        apply mul_le_mul_of_nonneg_right _ hrpownn
        apply mul_le_mul_of_nonneg_left hsC (by positivity)

/-- **Each tail summand is differentiable on `Re s > 0`** (a difference of `cpow`'s times a
constant), the per-term input to `SummableLocallyUniformlyOn.differentiableOn`. -/
theorem differentiableAt_tailSummand {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (i : ℕ) (r : ℂ) (hr : 0 < r.re) :
    DifferentiableAt ℂ
      (fun s => -(((i : ℂ) + 1) ^ (-s) - (i : ℂ) ^ (-s)) *
        ∑ j ∈ Finset.range (i + 1), χ (j : ZMod q)) r := by
  have h1 : DifferentiableAt ℂ (fun s => ((i : ℂ) + 1) ^ (-s)) r := by
    have := differentiableAt_natCpow_neg (i + 1) r hr
    simpa only [Nat.cast_add, Nat.cast_one] using this
  have h2 : DifferentiableAt ℂ (fun s => (i : ℂ) ^ (-s)) r := differentiableAt_natCpow_neg i r hr
  exact (((h1.sub h2).neg).mul_const _)

open Filter Topology in
/-- **Strip convergence to `LFunction χ` (analytic-continuation finish).** For a non-principal
Dirichlet character `χ` mod `q` and `Re s > 0`, the partial sums `∑_{n<N} χ(n)·n^{-s}` converge to
`DirichletCharacter.LFunction χ s`. The Abel-summed limit (`dirichlet_partialSum_tendsto_tail`) is
the analytic tail series `g`; it agrees with `LFunction χ` on `Re s > 1`
(`dirichlet_partialSum_tendsto_LFunction_of_one_lt`), and both are analytic on the connected open
half-plane `Re s > 0`, so the identity theorem forces agreement on the whole strip. -/
theorem dirichlet_strip_tendsto_LFunction {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, (χ (n : ZMod q)) * (n : ℂ) ^ (-s))
      Filter.atTop (nhds (DirichletCharacter.LFunction χ s)) := by
  classical
  set U : Set ℂ := {z : ℂ | 0 < z.re} with hU
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  set g : ℂ → ℂ := fun z => ∑' i : ℕ,
      (-(((i : ℂ) + 1) ^ (-z) - (i : ℂ) ^ (-z)) * ∑ j ∈ Finset.range (i + 1), χ (j : ZMod q))
    with hg
  have hg_diff : DifferentiableOn ℂ g U := by
    refine SummableLocallyUniformlyOn.differentiableOn hUopen
      (summableLocallyUniformlyOn_tail χ hχ) ?_
    intro i r hr
    exact differentiableAt_tailSummand χ i r (by simpa [hU] using hr)
  have hL_diff : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) U :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn
  have hg_an : AnalyticOnNhd ℂ g U := hg_diff.analyticOnNhd hUopen
  have hL_an : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) U :=
    hL_diff.analyticOnNhd hUopen
  have hUconn : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have h2U : (2 : ℂ) ∈ U := by simp [hU]
  have hev : g =ᶠ[nhds (2 : ℂ)] DirichletCharacter.LFunction χ := by
    have hopen1 : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have h2mem : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by norm_num
    filter_upwards [hopen1.mem_nhds h2mem] with z hz
    have hzre : 1 < z.re := hz
    have hzre0 : 0 < z.re := by linarith
    have hlim1 := dirichlet_partialSum_tendsto_LFunction_of_one_lt χ hzre
    have hlim2 := dirichlet_partialSum_tendsto_tail χ hχ hzre0
    exact tendsto_nhds_unique hlim2 hlim1
  have heqOn : Set.EqOn g (DirichletCharacter.LFunction χ) U :=
    hg_an.eqOn_of_preconnected_of_eventuallyEq hL_an hUconn h2U hev
  have hsU : s ∈ U := by simpa [hU] using hs
  rw [← heqOn hsU]
  exact dirichlet_partialSum_tendsto_tail χ hχ hs

/-! ## 10. Eta-mechanism strip extension: the trivial / principal-character case

The Dirichlet-bucket cancellation of Sections 6–9 needs a *non-principal* character. For the
trivial / principal character there is no bucket cancellation, so the same strip-extension is run
with the **alternating** coefficient `g n = (-1)^{n+1}` — the Dirichlet eta series. Its partial
sums lie in `{0, -1}` (bounded by `1`), supplying exactly the Dirichlet's-test / Abel input that
carried the bucketed channel past `Re = 1`. The continued function is the Dirichlet eta
`η(s) = (1 − 2^{1−s})·ζ(s)`. -/

/-- The alternating partial sum is `-(if Even N then 0 else 1)`, hence in `{0, -1}`. -/
theorem eta_partialSum_eq (N : ℕ) :
    ∑ n ∈ Finset.range N, (-1 : ℂ) ^ (n + 1) = -(if Even N then 0 else 1) := by
  have : ∀ n, (-1 : ℂ) ^ (n + 1) = -(-1 : ℂ) ^ n := by intro n; rw [pow_succ]; ring
  simp_rw [this, Finset.sum_neg_distrib, neg_one_geom_sum]

/-- **Bounded alternating partial sums.** The partial sums `∑_{n<N} (-1)^{n+1}` lie in `{0, -1}`,
hence are bounded by `1` — the eta analogue of `character_partialSum_norm_le` (no `q`-periodicity
needed; the alternating sign cancels in pairs). This is the Abel-summation input that carries the
phasor channel from `Re > 1` into the strip `Re > 0` in the principal-character case. -/
theorem eta_partialSum_norm_le (N : ℕ) :
    ‖∑ n ∈ Finset.range N, (-1 : ℂ) ^ (n + 1)‖ ≤ 1 := by
  rw [eta_partialSum_eq]
  rcases Nat.even_or_odd N with h | h <;> simp [h, Nat.not_even_iff_odd.mpr]

open Filter Topology in
/-- **Alternating Dirichlet partial sums converge for `Re s > 0`** (Dirichlet's test / Abel
summation), the eta analogue of `dirichlet_partialSum_converges` with bound `1` in place of `q`. -/
theorem eta_partialSum_converges {s : ℂ} (hs : 0 < s.re) :
    ∃ L : ℂ, Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, (-1 : ℂ) ^ (n + 1) * (n : ℂ) ^ (-s))
      Filter.atTop (nhds L) := by
  classical
  set f : ℕ → ℂ := fun n => (n : ℂ) ^ (-s) with hf
  set g : ℕ → ℂ := fun n => (-1 : ℂ) ^ (n + 1) with hg
  set G : ℕ → ℂ := fun k => ∑ i ∈ Finset.range k, g i with hG
  have hsum_eq : ∀ N : ℕ, (∑ n ∈ Finset.range N, (-1 : ℂ) ^ (n + 1) * (n : ℂ) ^ (-s))
      = ∑ i ∈ Finset.range N, f i • g i := by
    intro N
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hf, hg, smul_eq_mul, mul_comm]
  have hGbound : ∀ N : ℕ, ‖G N‖ ≤ (1 : ℝ) := by
    intro N
    rw [hG, hg]
    exact eta_partialSum_norm_le N
  have hpred : Tendsto (fun N : ℕ => N - 1) atTop atTop := by
    exact tendsto_atTop_atTop_of_monotone (fun a b h => Nat.sub_le_sub_right h 1)
      (fun b => ⟨b + 1, by omega⟩)
  have hf_pred : Tendsto (fun N : ℕ => f (N - 1)) atTop (nhds 0) := by
    rw [hf]
    exact (cpow_neg_tendsto_zero hs).comp hpred
  have hGbdd : IsBoundedUnder (· ≤ ·) atTop ((fun x => ‖x‖) ∘ G) :=
    ⟨(1 : ℝ), Filter.eventually_map.2 (Filter.Eventually.of_forall hGbound)⟩
  have hboundary : Tendsto (fun N : ℕ => f (N - 1) • G N) atTop (nhds 0) := by
    simp only [smul_eq_mul]
    exact hf_pred.zero_mul_isBoundedUnder_le hGbdd
  have hdiff_eq : ∀ i : ℕ, ‖f (i + 1) - f i‖ = ‖((i : ℂ) + 1) ^ (-s) - (i : ℂ) ^ (-s)‖ := by
    intro i
    rw [hf]
    norm_num
  have hsummable_diff : Summable (fun i : ℕ => ‖f (i + 1) - f i‖) := by
    apply (cpow_diff_summable hs).congr
    intro i; rw [hdiff_eq i]
  have hsummable_bound : Summable (fun i : ℕ => ‖f (i + 1) - f i‖ * (1 : ℝ)) :=
    hsummable_diff.mul_right (1 : ℝ)
  have hsummand : Summable (fun i : ℕ => (f (i + 1) - f i) • G (i + 1)) := by
    apply Summable.of_norm_bounded hsummable_bound
    intro i
    rw [smul_eq_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hGbound (i + 1)) (norm_nonneg _)
  obtain ⟨T, hT⟩ := hsummand
  have hH : Tendsto (fun M : ℕ => ∑ i ∈ Finset.range M, (f (i + 1) - f i) • G (i + 1))
      atTop (nhds T) := hT.tendsto_sum_nat
  have hH_pred : Tendsto
      (fun N : ℕ => ∑ i ∈ Finset.range (N - 1), (f (i + 1) - f i) • G (i + 1))
      atTop (nhds T) := hH.comp hpred
  refine ⟨0 - T, ?_⟩
  have hpointwise : ∀ N : ℕ,
      (∑ n ∈ Finset.range N, (-1 : ℂ) ^ (n + 1) * (n : ℂ) ^ (-s))
        = (f (N - 1) • G N) - ∑ i ∈ Finset.range (N - 1), (f (i + 1) - f i) • G (i + 1) := by
    intro N
    rw [hsum_eq N, Finset.sum_range_by_parts f g N]
  refine Tendsto.congr (fun N => (hpointwise N).symm) ?_
  exact hboundary.sub hH_pred

/-- `(n:ℂ)^{-s}` is summable for `1 < Re s`. -/
theorem summable_natCpow_neg {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => (n : ℂ) ^ (-s)) := by
  have := Complex.summable_one_div_nat_cpow.mpr hs
  simp_rw [one_div, ← Complex.cpow_neg] at this
  exact this

/-- The even-index reindexing `(2k)^{-s} = 2^{-s}·k^{-s}`. -/
theorem even_natCpow_neg (s : ℂ) (k : ℕ) :
    ((2 * k : ℕ) : ℂ) ^ (-s) = (2 : ℂ) ^ (-s) * (k : ℂ) ^ (-s) := by
  rw [show ((2 * k : ℕ) : ℂ) = ((2 : ℝ) : ℂ) * ((k : ℝ) : ℂ) by push_cast; ring,
    Complex.mul_cpow_ofReal_nonneg (by norm_num) (by positivity)]
  push_cast; ring

/-- **`Re s > 1` agreement (eta).** For `1 < Re s` the alternating Dirichlet series sums to
`(1 − 2^{1−s})·ζ(s)` — the eta analogue of `dirichlet_partialSum_tendsto_LFunction_of_one_lt`.
Splitting even/odd, `∑ (-1)^{n+1} n^{-s} = ζ − 2·2^{-s}ζ = (1 − 2^{1−s})ζ`. -/
theorem eta_tsum_eq_of_one_lt {s : ℂ} (hs : 1 < s.re) :
    ∑' n : ℕ, (-1 : ℂ) ^ (n + 1) * (n : ℂ) ^ (-s)
      = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
  have hζ : riemannZeta s = ∑' n : ℕ, (n : ℂ) ^ (-s) := by
    rw [zeta_eq_tsum_one_div_nat_cpow hs]
    refine tsum_congr (fun n => ?_)
    rw [Complex.cpow_neg, one_div]
  have hsum_z : Summable (fun n : ℕ => (n : ℂ) ^ (-s)) := summable_natCpow_neg hs
  have hsum_even : Summable (fun k : ℕ => ((2 * k : ℕ) : ℂ) ^ (-s)) :=
    hsum_z.comp_injective (fun a b h => by simpa using h)
  have hsum_odd : Summable (fun k : ℕ => ((2 * k + 1 : ℕ) : ℂ) ^ (-s)) :=
    hsum_z.comp_injective (fun a b h => by simpa using h)
  have heven_val : ∑' k : ℕ, ((2 * k : ℕ) : ℂ) ^ (-s) = (2 : ℂ) ^ (-s) * riemannZeta s := by
    rw [hζ, ← tsum_mul_left]
    exact tsum_congr (fun k => even_natCpow_neg s k)
  have hzeta_split : (2 : ℂ) ^ (-s) * riemannZeta s
      + ∑' k : ℕ, ((2 * k + 1 : ℕ) : ℂ) ^ (-s) = riemannZeta s := by
    have := tsum_even_add_odd (f := fun n : ℕ => (n : ℂ) ^ (-s)) hsum_even hsum_odd
    rw [heven_val] at this
    rw [this, hζ]
  have heta_even : Summable (fun k : ℕ => (-1 : ℂ) ^ (2 * k + 1) * ((2 * k : ℕ) : ℂ) ^ (-s)) := by
    apply Summable.of_norm_bounded (g := fun k : ℕ => ‖((2 * k : ℕ) : ℂ) ^ (-s)‖) (hsum_even.norm)
    intro k
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have heta_odd : Summable
      (fun k : ℕ => (-1 : ℂ) ^ (2 * k + 1 + 1) * ((2 * k + 1 : ℕ) : ℂ) ^ (-s)) := by
    apply Summable.of_norm_bounded (g := fun k : ℕ => ‖((2 * k + 1 : ℕ) : ℂ) ^ (-s)‖)
      (hsum_odd.norm)
    intro k
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have heta_split := tsum_even_add_odd
    (f := fun n : ℕ => (-1 : ℂ) ^ (n + 1) * (n : ℂ) ^ (-s)) heta_even heta_odd
  have heven_eta_val : ∑' k : ℕ, (-1 : ℂ) ^ (2 * k + 1) * ((2 * k : ℕ) : ℂ) ^ (-s)
      = -((2 : ℂ) ^ (-s) * riemannZeta s) := by
    rw [← heven_val, ← tsum_neg]
    refine tsum_congr (fun k => ?_)
    rw [Odd.neg_one_pow ⟨k, by ring⟩, neg_one_mul]
  have hodd_eta_val : ∑' k : ℕ, (-1 : ℂ) ^ (2 * k + 1 + 1) * ((2 * k + 1 : ℕ) : ℂ) ^ (-s)
      = ∑' k : ℕ, ((2 * k + 1 : ℕ) : ℂ) ^ (-s) := by
    refine tsum_congr (fun k => ?_)
    rw [Even.neg_one_pow ⟨k + 1, by ring⟩, one_mul]
  rw [heven_eta_val, hodd_eta_val] at heta_split
  have hodd_val : ∑' k : ℕ, ((2 * k + 1 : ℕ) : ℂ) ^ (-s)
      = riemannZeta s - (2 : ℂ) ^ (-s) * riemannZeta s := by
    linear_combination hzeta_split
  rw [← heta_split, hodd_val]
  have h2 : (2 : ℂ) ^ (1 - s) = 2 * (2 : ℂ) ^ (-s) := by
    rw [show (1 : ℂ) - s = 1 + (-s) by ring, Complex.cpow_add _ _ (by norm_num),
      Complex.cpow_one]
  rw [h2]; ring

open Filter Topology in
/-- **`Re s > 1` partial-sum tendsto (eta).** The partial sums tend to `(1 − 2^{1−s})·ζ(s)` for
`1 < Re s`, where the alternating series is absolutely summable. -/
theorem eta_partialSum_tendsto_of_one_lt {s : ℂ} (hs : 1 < s.re) :
    Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, (-1 : ℂ) ^ (n + 1) * (n : ℂ) ^ (-s))
      Filter.atTop (nhds ((1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s)) := by
  have hsum_eta : Summable (fun n : ℕ => (-1 : ℂ) ^ (n + 1) * (n : ℂ) ^ (-s)) := by
    apply Summable.of_norm_bounded (g := fun n : ℕ => ‖(n : ℂ) ^ (-s)‖)
      ((summable_natCpow_neg hs).norm)
    intro n
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  rw [← eta_tsum_eq_of_one_lt hs]
  exact hsum_eta.hasSum.tendsto_sum_nat

open Filter Topology in
/-- **Explicit tail limit (eta).** Abel summation lands the alternating partial sums on the tail
series `∑ᵢ −((i+1)^{-s} − i^{-s})·(∑_{j<i+1} (-1)^{j+1})`, mirroring
`dirichlet_partialSum_tendsto_tail`. -/
theorem eta_partialSum_tendsto_tail {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, (-1 : ℂ) ^ (n + 1) * (n : ℂ) ^ (-s))
      Filter.atTop
      (nhds (∑' i : ℕ,
        (-(((i : ℂ) + 1) ^ (-s) - (i : ℂ) ^ (-s)) *
          ∑ j ∈ Finset.range (i + 1), (-1 : ℂ) ^ (j + 1)))) := by
  classical
  set f : ℕ → ℂ := fun n => (n : ℂ) ^ (-s) with hf
  set g : ℕ → ℂ := fun n => (-1 : ℂ) ^ (n + 1) with hg
  set G : ℕ → ℂ := fun k => ∑ i ∈ Finset.range k, g i with hG
  have hsum_eq : ∀ N : ℕ, (∑ n ∈ Finset.range N, (-1 : ℂ) ^ (n + 1) * (n : ℂ) ^ (-s))
      = ∑ i ∈ Finset.range N, f i • g i := by
    intro N
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hf, hg, smul_eq_mul, mul_comm]
  have hGbound : ∀ N : ℕ, ‖G N‖ ≤ (1 : ℝ) := by
    intro N
    rw [hG, hg]
    exact eta_partialSum_norm_le N
  have hpred : Tendsto (fun N : ℕ => N - 1) atTop atTop := by
    exact tendsto_atTop_atTop_of_monotone (fun a b h => Nat.sub_le_sub_right h 1)
      (fun b => ⟨b + 1, by omega⟩)
  have hf_pred : Tendsto (fun N : ℕ => f (N - 1)) atTop (nhds 0) := by
    rw [hf]
    exact (cpow_neg_tendsto_zero hs).comp hpred
  have hGbdd : IsBoundedUnder (· ≤ ·) atTop ((fun x => ‖x‖) ∘ G) :=
    ⟨(1 : ℝ), Filter.eventually_map.2 (Filter.Eventually.of_forall hGbound)⟩
  have hboundary : Tendsto (fun N : ℕ => f (N - 1) • G N) atTop (nhds 0) := by
    simp only [smul_eq_mul]
    exact hf_pred.zero_mul_isBoundedUnder_le hGbdd
  have hdiff_eq : ∀ i : ℕ, ‖f (i + 1) - f i‖ = ‖((i : ℂ) + 1) ^ (-s) - (i : ℂ) ^ (-s)‖ := by
    intro i
    rw [hf]
    norm_num
  have hsummable_diff : Summable (fun i : ℕ => ‖f (i + 1) - f i‖) := by
    apply (cpow_diff_summable hs).congr
    intro i; rw [hdiff_eq i]
  have hsummable_bound : Summable (fun i : ℕ => ‖f (i + 1) - f i‖ * (1 : ℝ)) :=
    hsummable_diff.mul_right (1 : ℝ)
  have hsummand : Summable (fun i : ℕ => (f (i + 1) - f i) • G (i + 1)) := by
    apply Summable.of_norm_bounded hsummable_bound
    intro i
    rw [smul_eq_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hGbound (i + 1)) (norm_nonneg _)
  obtain ⟨T, hT⟩ := hsummand
  have hH : Tendsto (fun M : ℕ => ∑ i ∈ Finset.range M, (f (i + 1) - f i) • G (i + 1))
      atTop (nhds T) := hT.tendsto_sum_nat
  have hH_pred : Tendsto
      (fun N : ℕ => ∑ i ∈ Finset.range (N - 1), (f (i + 1) - f i) • G (i + 1))
      atTop (nhds T) := hH.comp hpred
  have hTval : T = ∑' i : ℕ, (f (i + 1) - f i) • G (i + 1) := hT.tsum_eq.symm
  have hpointwise : ∀ N : ℕ,
      (∑ n ∈ Finset.range N, (-1 : ℂ) ^ (n + 1) * (n : ℂ) ^ (-s))
        = (f (N - 1) • G N) - ∑ i ∈ Finset.range (N - 1), (f (i + 1) - f i) • G (i + 1) := by
    intro N
    rw [hsum_eq N, Finset.sum_range_by_parts f g N]
  have hlim : Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, (-1 : ℂ) ^ (n + 1) * (n : ℂ) ^ (-s))
      atTop (nhds (0 - T)) := by
    refine Tendsto.congr (fun N => (hpointwise N).symm) ?_
    exact hboundary.sub hH_pred
  have hgoal : (0 : ℂ) - T = ∑' i : ℕ,
      (-(((i : ℂ) + 1) ^ (-s) - (i : ℂ) ^ (-s)) * ∑ j ∈ Finset.range (i + 1),
        (-1 : ℂ) ^ (j + 1)) := by
    rw [zero_sub, hTval, ← tsum_neg]
    refine tsum_congr (fun i => ?_)
    simp only [hf, hG, hg, smul_eq_mul]
    push_cast
    ring
  rw [hgoal] at hlim
  exact hlim

/-- **Local-uniform summability of the eta tail series on `Re s > 0`**, mirroring
`summableLocallyUniformlyOn_tail` with the alternating coefficient bound `1`. -/
theorem eta_summableLocallyUniformlyOn_tail :
    SummableLocallyUniformlyOn
      (fun (i : ℕ) (s : ℂ) =>
        -(((i : ℂ) + 1) ^ (-s) - (i : ℂ) ^ (-s)) * ∑ j ∈ Finset.range (i + 1),
          (-1 : ℂ) ^ (j + 1))
      {s : ℂ | 0 < s.re} := by
  have hopen : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  refine SummableLocallyUniformlyOn_of_locally_bounded hopen ?_
  intro K hKsub hKcompact
  rcases K.eq_empty_or_nonempty with hKempty | hKne
  · refine ⟨fun _ => 0, summable_zero, ?_⟩
    intro n k hk
    rw [hKempty] at hk
    exact absurd hk (by simp)
  · obtain ⟨z₀, hz₀K, hz₀min⟩ :=
      hKcompact.exists_isMinOn hKne (Complex.continuous_re.continuousOn)
    rw [isMinOn_iff] at hz₀min
    set σ₀ : ℝ := z₀.re with hσ₀
    have hσ₀pos : 0 < σ₀ := hKsub hz₀K
    have hσ₀le : ∀ s ∈ K, σ₀ ≤ s.re := fun s hs => hz₀min s hs
    obtain ⟨w₀, hw₀K, hw₀max⟩ :=
      hKcompact.exists_isMaxOn hKne (continuous_norm.continuousOn (s := K))
    rw [isMaxOn_iff] at hw₀max
    set C : ℝ := ‖w₀‖ with hCdef
    have hC : ∀ s ∈ K, ‖s‖ ≤ C := fun s hs => hw₀max s hs
    have hCnonneg : 0 ≤ C := norm_nonneg _
    refine ⟨fun i => (1 : ℝ) * C * (i : ℝ) ^ (-(σ₀ + 1)) + (if i = 0 then (1 : ℝ) else 0),
      ?_, ?_⟩
    · apply Summable.add
      · apply Summable.mul_left
        rw [Real.summable_nat_rpow]
        linarith
      · apply summable_of_hasFiniteSupport
        apply Set.Finite.subset (Set.finite_singleton 0)
        intro i hi
        simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at hi
        simp only [Set.mem_singleton_iff]
        exact hi.1
    · intro i s hsK
      have hsre : 0 < s.re := hKsub hsK
      have hsC : ‖s‖ ≤ C := hC s hsK
      have hsσ₀ : σ₀ ≤ s.re := hσ₀le s hsK
      rw [norm_mul, norm_neg]
      have hGle : ‖∑ j ∈ Finset.range (i + 1), (-1 : ℂ) ^ (j + 1)‖ ≤ (1 : ℝ) :=
        eta_partialSum_norm_le (i + 1)
      simp only []
      rcases eq_or_ne i 0 with hi | hi
      · subst hi
        have hs0 : s ≠ 0 := by
          intro h; rw [h] at hsre; simp at hsre
        rw [if_pos rfl]
        simp only [Nat.cast_zero, zero_add, Complex.zero_cpow (neg_ne_zero.mpr hs0),
          sub_zero, Complex.one_cpow, norm_one, one_mul]
        have hb : ‖∑ j ∈ Finset.range 1, (-1 : ℂ) ^ (j + 1)‖ ≤ (1 : ℝ) :=
          eta_partialSum_norm_le 1
        have hnn : 0 ≤ (1 : ℝ) * C * (0 : ℝ) ^ (-(σ₀ + 1)) := by positivity
        linarith
      · have hipos : 0 < i := Nat.pos_of_ne_zero hi
        have hi0 : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hipos
        have hmvt := term_mvt_bound s hsre i hipos
        have hexp : (i : ℝ) ^ (-(s.re + 1)) ≤ (i : ℝ) ^ (-(σ₀ + 1)) := by
          apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hipos) (by linarith)
        have hstep1 : ‖((i : ℂ) + 1) ^ (-s) - (i : ℂ) ^ (-s)‖ ≤ ‖s‖ * (i : ℝ) ^ (-(σ₀ + 1)) :=
          le_trans hmvt (by
            apply mul_le_mul_of_nonneg_left hexp (norm_nonneg s))
        have hstep2 :
            ‖((i : ℂ) + 1) ^ (-s) - (i : ℂ) ^ (-s)‖ *
              ‖∑ j ∈ Finset.range (i + 1), (-1 : ℂ) ^ (j + 1)‖
            ≤ (‖s‖ * (i : ℝ) ^ (-(σ₀ + 1))) * (1 : ℝ) := by
          apply mul_le_mul hstep1 hGle (norm_nonneg _)
          positivity
        rw [if_neg hi, add_zero]
        refine le_trans hstep2 ?_
        have hrpownn : 0 ≤ (i : ℝ) ^ (-(σ₀ + 1)) := Real.rpow_nonneg (by positivity) _
        have heq2 : ‖s‖ * (i : ℝ) ^ (-(σ₀ + 1)) * (1 : ℝ)
            = (1 : ℝ) * ‖s‖ * (i : ℝ) ^ (-(σ₀ + 1)) := by ring
        rw [heq2]
        apply mul_le_mul_of_nonneg_right _ hrpownn
        apply mul_le_mul_of_nonneg_left hsC (by positivity)

/-- **Each eta tail summand is differentiable on `Re s > 0`**, mirroring
`differentiableAt_tailSummand`. -/
theorem eta_differentiableAt_tailSummand (i : ℕ) (r : ℂ) (hr : 0 < r.re) :
    DifferentiableAt ℂ
      (fun s => -(((i : ℂ) + 1) ^ (-s) - (i : ℂ) ^ (-s)) *
        ∑ j ∈ Finset.range (i + 1), (-1 : ℂ) ^ (j + 1)) r := by
  have h1 : DifferentiableAt ℂ (fun s => ((i : ℂ) + 1) ^ (-s)) r := by
    have := differentiableAt_natCpow_neg (i + 1) r hr
    simpa only [Nat.cast_add, Nat.cast_one] using this
  have h2 : DifferentiableAt ℂ (fun s => (i : ℂ) ^ (-s)) r := differentiableAt_natCpow_neg i r hr
  exact (((h1.sub h2).neg).mul_const _)

/-- **The punctured strip `{Re > 0} \ {1}` is preconnected.** Covered by four open convex
half-regions (upper/lower half, slabs `0 < Re < 1` / `Re > 1`), each avoiding the real point `1`,
glued along nonempty overlaps. This is the connected domain on which the identity theorem
identifies the eta tail series with `(1 − 2^{1−s})·ζ(s)`, which is not analytic at the pole
`s = 1`. -/
theorem isPreconnected_strip_diff_one :
    IsPreconnected ({z : ℂ | 0 < z.re} \ {1}) := by
  set A : Set ℂ := {z : ℂ | 0 < z.re ∧ 0 < z.im} with hA
  set B : Set ℂ := {z : ℂ | 0 < z.re ∧ z.im < 0} with hB
  set D : Set ℂ := {z : ℂ | 0 < z.re ∧ z.re < 1} with hD
  set E : Set ℂ := {z : ℂ | 1 < z.re} with hE
  have hAc : Convex ℝ A := (convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_gt 0)
  have hBc : Convex ℝ B := (convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_lt 0)
  have hDc : Convex ℝ D := (convex_halfSpace_re_gt 0).inter (convex_halfSpace_re_lt 1)
  have hEc : Convex ℝ E := convex_halfSpace_re_gt 1
  have hm2I_A : ((2 : ℝ) + I) ∈ A := by
    simp only [hA, Set.mem_setOf_eq]; constructor <;> simp
  have hm2I_E : ((2 : ℝ) + I) ∈ E := by simp only [hE, Set.mem_setOf_eq]; simp
  have hm2nI_E : ((2 : ℝ) - I) ∈ E := by simp only [hE, Set.mem_setOf_eq]; simp
  have hm2nI_B : ((2 : ℝ) - I) ∈ B := by
    simp only [hB, Set.mem_setOf_eq]; constructor <;> simp
  have hmhI_A : (((1 : ℝ) / 2) + I) ∈ A := by
    simp only [hA, Set.mem_setOf_eq]; constructor <;> simp
  have hmhI_D : (((1 : ℝ) / 2) + I) ∈ D := by
    simp only [hD, Set.mem_setOf_eq]; refine ⟨by simp, ?_⟩; simp; norm_num
  have hAE : IsPreconnected (A ∪ E) :=
    IsPreconnected.union ((2 : ℝ) + I) hm2I_A hm2I_E hAc.isPreconnected hEc.isPreconnected
  have hAEB : IsPreconnected (A ∪ E ∪ B) :=
    IsPreconnected.union ((2 : ℝ) - I) (Or.inr hm2nI_E) hm2nI_B hAE hBc.isPreconnected
  have hAEBD : IsPreconnected (A ∪ E ∪ B ∪ D) :=
    IsPreconnected.union (((1 : ℝ) / 2) + I) (Or.inl (Or.inl hmhI_A)) hmhI_D
      hAEB hDc.isPreconnected
  have hset : A ∪ E ∪ B ∪ D = ({z : ℂ | 0 < z.re} \ {1}) := by
    ext z
    simp only [hA, hB, hD, hE, Set.mem_union, Set.mem_setOf_eq, Set.mem_sdiff,
      Set.mem_singleton_iff]
    have hne_of_im : z.im ≠ 0 → z ≠ 1 := fun h hz => h (by rw [hz]; simp)
    have hne_of_re_lt : z.re < 1 → z ≠ 1 := fun h hz => by rw [hz] at h; simp at h
    have hne_of_re_gt : 1 < z.re → z ≠ 1 := fun h hz => by rw [hz] at h; simp at h
    constructor
    · rintro (((⟨hr, hi⟩ | hr) | ⟨hr, hi⟩) | ⟨hr, hlt⟩)
      · exact ⟨hr, hne_of_im (by positivity)⟩
      · exact ⟨by linarith, hne_of_re_gt hr⟩
      · exact ⟨hr, hne_of_im (by intro h; rw [h] at hi; simp at hi)⟩
      · exact ⟨hr, hne_of_re_lt hlt⟩
    · rintro ⟨hr, hne⟩
      rcases lt_trichotomy z.im 0 with him | him | him
      · exact Or.inl (Or.inr ⟨hr, him⟩)
      · have hre1 : z.re ≠ 1 := by
          intro h
          exact hne (Complex.ext h (by rw [him]; rfl))
        rcases lt_or_gt_of_ne hre1 with h | h
        · exact Or.inr ⟨hr, h⟩
        · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inl (Or.inl (Or.inl ⟨hr, him⟩))
  rw [← hset]
  exact hAEBD

open Filter Topology in
/-- **Eta-mechanism strip extension (trivial / principal-character case).** For `0 < Re s` and
`s ≠ 1`, the alternating phasor partial sums `∑_{n<N} (-1)^{n+1}·n^{-s}` converge to the Dirichlet
eta value `(1 − 2^{1−s})·ζ(s)`.

This is the eta analogue of `dirichlet_strip_tendsto_LFunction`: with NO Dirichlet-bucket
cancellation (principal character), the alternating coefficient `(-1)^{n+1}` supplies the bounded
partial sums (`eta_partialSum_norm_le`) that carry the channel past `Re = 1` into the strip
`Re > 0` by Abel summation. The Abel-summed limit (`eta_partialSum_tendsto_tail`) is the analytic
tail series `g`; it agrees with `(1 − 2^{1−s})·ζ(s)` on `Re > 1`
(`eta_partialSum_tendsto_of_one_lt` via the absolutely-convergent identity `eta_tsum_eq_of_one_lt`),
and both are analytic on the preconnected punctured strip `{Re > 0} \ {1}`
(`isPreconnected_strip_diff_one`), so the identity theorem forces agreement there.

The hypothesis `s ≠ 1` is genuinely necessary, not a convenience: at `s = 1` the *raw product*
`(1 − 2^{1−s})·riemannZeta s` equals `0 · riemannZeta 1 = 0` (the factor `1 − 2^{1−1} = 0` kills the
junk value `riemannZeta 1 ≠ 0`), whereas the alternating harmonic partial sums converge to
`Real.log 2 ≠ 0`. The honest analytic continuation `η` agrees with the raw product only away from
the pole `s = 1`. -/
theorem eta_strip_tendsto {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, (-1 : ℂ) ^ (n + 1) * (n : ℂ) ^ (-s))
      Filter.atTop (nhds ((1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s)) := by
  classical
  set U : Set ℂ := {z : ℂ | 0 < z.re} \ {1} with hU
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton
  set g : ℂ → ℂ := fun z => ∑' i : ℕ,
      (-(((i : ℂ) + 1) ^ (-z) - (i : ℂ) ^ (-z)) * ∑ j ∈ Finset.range (i + 1),
        (-1 : ℂ) ^ (j + 1))
    with hg
  have hg_diff_strip : DifferentiableOn ℂ g {z : ℂ | 0 < z.re} := by
    have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    refine SummableLocallyUniformlyOn.differentiableOn hopen
      eta_summableLocallyUniformlyOn_tail ?_
    intro i r hr
    exact eta_differentiableAt_tailSummand i r hr
  have hg_diff : DifferentiableOn ℂ g U := hg_diff_strip.mono Set.sdiff_subset
  set T : ℂ → ℂ := fun z => (1 - (2 : ℂ) ^ (1 - z)) * riemannZeta z with hT
  have hT_diff : DifferentiableOn ℂ T U := by
    intro z hz
    have hz1 : z ≠ 1 := by intro h; rw [hU] at hz; exact hz.2 (by simp [h])
    refine DifferentiableAt.differentiableWithinAt ?_
    refine DifferentiableAt.mul ?_ (differentiableAt_riemannZeta hz1)
    refine DifferentiableAt.sub (differentiableAt_const _) ?_
    exact ((differentiable_const_cpow_of_neZero (2 : ℂ)).comp
      ((differentiable_const (1 : ℂ)).sub differentiable_id)).differentiableAt
  have hg_an : AnalyticOnNhd ℂ g U := hg_diff.analyticOnNhd hUopen
  have hT_an : AnalyticOnNhd ℂ T U := hT_diff.analyticOnNhd hUopen
  have hUconn : IsPreconnected U := isPreconnected_strip_diff_one
  have h2U : (2 : ℂ) ∈ U := by rw [hU]; exact ⟨by norm_num, by simp⟩
  have hev : g =ᶠ[nhds (2 : ℂ)] T := by
    have hopen1 : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have h2mem : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by norm_num
    filter_upwards [hopen1.mem_nhds h2mem] with z hz
    have hzre : 1 < z.re := hz
    exact tendsto_nhds_unique (eta_partialSum_tendsto_tail (by linarith))
      (eta_partialSum_tendsto_of_one_lt hzre)
  have heqOn : Set.EqOn g T U :=
    hg_an.eqOn_of_preconnected_of_eventuallyEq hT_an hUconn h2U hev
  have hsU : s ∈ U := ⟨hs, by simpa using hs1⟩
  have htarget : g s = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := heqOn hsU
  rw [← htarget]
  exact eta_partialSum_tendsto_tail hs

end CriticalLinePhasor.LFunctionPhasor
