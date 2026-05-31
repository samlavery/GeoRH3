import Mathlib
import RequestProject.ForcedAlignment
import RequestProject.ConcreteOperators
import RequestProject.SimulRecurrence

/-!
# Finite RH: Extension from Single Pairs to Finite Zero Sets

## The gap being closed

The theorem `critical_line_iff_bounded_li` proves for a SINGLE pair:
  σ = 1/2 ⟺ paired Li bounded below.

This file extends to FINITE SETS of FE-paired zeros.

## What is proved here

1. Forward direction: all on-line ⟹ paired Li sum ≥ 0 (easy, fully proved)
2. Special case: one off-line pair + all others on-line ⟹ sum unbounded below
3. General case: any off-line pair ⟹ sum unbounded below
   (uses multi-dimensional Dirichlet approximation from SimulRecurrence.lean)
4. Full biconditional: all on-line ⟺ Li bounded below
-/

noncomputable section

open Complex Real

/-- The paired Li sum over a finite set of FE pairs. -/
def paired_li_sum (pairs : Finset (ℝ × ℝ)) (n : ℕ) : ℝ :=
  ∑ z ∈ pairs, ((li_helix_term z.1 z.2 n).re +
                 (li_helix_term (1 - z.1) (-z.2) n).re)

/-! ## Forward direction: all on-line ⟹ bounded below -/

/-- On-line paired Li is nonneg for each pair. -/
theorem on_line_pair_nonneg (γ : ℝ) (n : ℕ) :
    0 ≤ (li_helix_term (1/2) γ n).re +
        (li_helix_term (1 - 1/2) (-γ) n).re := by
  have h1 := li_helix_nonneg_on_line γ n
  have h2 := li_helix_nonneg_on_line (-γ) n
  convert add_nonneg h1 h2 using 1; norm_num

/-- **Forward direction**: All pairs on-line ⟹ paired Li sum ≥ 0. -/
theorem all_on_line_implies_li_nonneg (pairs : Finset (ℝ × ℝ))
    (h_online : ∀ z ∈ pairs, z.1 = 1/2) (n : ℕ) :
    0 ≤ paired_li_sum pairs n := by
  unfold paired_li_sum
  apply Finset.sum_nonneg
  intro z hz; rw [h_online z hz]; exact on_line_pair_nonneg z.2 n

/-! ## Special case: one off-line + rest on-line -/

/-- When on-line, each Li term is bounded by 2. -/
private theorem li_on_line_le_two (γ : ℝ) (n : ℕ) :
    (li_helix_term (1/2) γ n).re ≤ 2 := by
  unfold li_helix_term; apply li_re_le_two
  by_cases hγ : γ = 0
  · subst hγ; simp [moebius_helix]; norm_num [Complex.norm_def, Complex.normSq]
  · exact le_of_eq ((moebius_unit_iff (1/2) γ hγ).mpr rfl)

/-- Each on-line pair contributes at most 4. -/
theorem on_line_pair_le_four (γ : ℝ) (n : ℕ) :
    (li_helix_term (1/2) γ n).re +
    (li_helix_term (1 - 1/2) (-γ) n).re ≤ 4 := by
  have h1 := li_on_line_le_two γ n
  have h2 : (li_helix_term (1 - 1/2) (-γ) n).re ≤ 2 := by
    convert li_on_line_le_two (-γ) n using 2; norm_num
  linarith

/-- **Proved**: One off-line pair with on-line rest breaks the Li sum. -/
theorem offline_with_online_rest (pairs : Finset (ℝ × ℝ))
    (h_nontrivial : ∀ z ∈ pairs, z.2 ≠ 0)
    (bad : ℝ × ℝ) (hbad_mem : bad ∈ pairs) (hbad_off : bad.1 ≠ 1/2)
    (h_rest_online : ∀ z ∈ pairs, z ≠ bad → z.1 = 1/2) :
    ∀ M : ℝ, ∃ n : ℕ, paired_li_sum pairs n < M := by
  intro M
  obtain ⟨n, hn⟩ := paired_li_unbounded_off_line bad.1 bad.2 hbad_off
    (h_nontrivial bad hbad_mem) (M - 4 * ↑pairs.card)
  use n
  rw [paired_li_sum, ← Finset.add_sum_erase _ _ hbad_mem]
  have hrest : ∑ z ∈ pairs.erase bad,
      ((li_helix_term z.1 z.2 n).re + (li_helix_term (1 - z.1) (-z.2) n).re) ≤
      4 * ↑pairs.card := by
    calc ∑ z ∈ pairs.erase bad, _ ≤ ∑ z ∈ pairs.erase bad, (4 : ℝ) := by
          apply Finset.sum_le_sum; intro z hz
          rw [h_rest_online z (Finset.mem_of_mem_erase hz) (Finset.ne_of_mem_erase hz)]
          exact on_line_pair_le_four z.2 n
      _ = 4 * (pairs.erase bad).card := by
          simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ 4 * pairs.card := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 4)
          exact_mod_cast Finset.card_erase_le
  linarith

/-! ## General case: any off-line pair breaks the sum

Uses `multi_recur_cofinal` from SimulRecurrence.lean for synchronization:
at cofinally many n, every pair's unit-circle part uⁿ ≈ 1, so each pair's
paired Li ≤ 2 − (1−δ)(r + 1/r). The bad pair's r + 1/r → ∞ while
everyone else's stays ≥ 2 (AM-GM), driving the total to −∞. -/

/-- moebius_helix is nonzero when γ ≠ 0. -/
lemma moebius_helix_ne_zero (σ γ : ℝ) (hγ : γ ≠ 0) : moebius_helix σ γ ≠ 0 := by
  unfold moebius_helix; norm_num [Complex.ext_iff, hγ]
  exact fun h => by nlinarith [mul_self_pos.2 hγ]

/-- Re(w^n) ≥ (1−δ)·‖w‖ⁿ when the unit part satisfies ‖u^n − 1‖ < δ < 1. -/
lemma re_pow_ge_of_synced (w : ℂ) (hw : w ≠ 0) {δ : ℝ} (hδ1 : δ < 1) (n : ℕ)
    (hsync : ‖(w / (↑‖w‖ : ℂ)) ^ n - 1‖ < δ) :
    (1 - δ) * ‖w‖ ^ n ≤ (w ^ n).re := by
  have h_div : ‖(w ^ n / ‖w‖ ^ n) - 1‖ < δ := by
    simpa only [div_pow] using hsync
  have h_re : Complex.re (w ^ n / ‖w‖ ^ n) > 1 - δ := by
    norm_num [Complex.normSq, Complex.norm_def] at *
    nlinarith [Real.sqrt_nonneg (((w ^ n / Real.sqrt (w.re * w.re + w.im * w.im) ^ n |> Complex.re) - 1) * ((w ^ n / Real.sqrt (w.re * w.re + w.im * w.im) ^ n |> Complex.re) - 1) + (w ^ n / Real.sqrt (w.re * w.re + w.im * w.im) ^ n |> Complex.im) * (w ^ n / Real.sqrt (w.re * w.re + w.im * w.im) ^ n |> Complex.im)), Real.mul_self_sqrt (add_nonneg (mul_self_nonneg ((w ^ n / Real.sqrt (w.re * w.re + w.im * w.im) ^ n |> Complex.re) - 1)) (mul_self_nonneg (w ^ n / Real.sqrt (w.re * w.re + w.im * w.im) ^ n |> Complex.im)))]
  have hnorm_pos : (0:ℝ) < ‖w‖ := norm_pos_iff.mpr hw
  have hnorm_pow_pos : (0:ℝ) < ‖w‖ ^ n := pow_pos hnorm_pos n
  have hnorm_pow_ne : (‖w‖ ^ n : ℝ) ≠ 0 := hnorm_pow_pos.ne'
  have h_re' : 1 - δ ≤ (w ^ n / ↑(‖w‖ ^ n)).re := by
    convert h_re.le using 2; push_cast; rfl
  calc (1 - δ) * ‖w‖ ^ n
      ≤ (w ^ n / ↑(‖w‖ ^ n)).re * ‖w‖ ^ n :=
        mul_le_mul_of_nonneg_right h_re' hnorm_pow_pos.le
    _ = (w ^ n).re := by
        rw [Complex.div_ofReal_re, div_mul_cancel₀ _ (mod_cast hnorm_pow_ne)]

/-
The FE partner's unit-circle part is the conjugate of the original's.
-/
lemma fe_unit_conj (σ γ : ℝ) (hγ : γ ≠ 0) :
    moebius_helix (1 - σ) (-γ) / (↑‖moebius_helix (1 - σ) (-γ)‖ : ℂ) =
    starRingEnd ℂ (moebius_helix σ γ / (↑‖moebius_helix σ γ‖ : ℂ)) := by
  unfold moebius_helix;
  norm_num [ Complex.ext_iff, Complex.normSq, Complex.norm_def ];
  field_simp;
  rw [ Real.sqrt_div ( by positivity ), Real.sqrt_div ( by positivity ), Real.sqrt_sq ( by positivity ), Real.sqrt_sq ( by positivity ) ] ; ring;
  grind

/-
Synchronization transfers from w to its FE partner via conjugation.
-/
lemma fe_sync_transfer (σ γ : ℝ) (hγ : γ ≠ 0) {δ : ℝ} (n : ℕ)
    (hsync : ‖(moebius_helix σ γ / (↑‖moebius_helix σ γ‖ : ℂ)) ^ n - 1‖ < δ) :
    ‖(moebius_helix (1 - σ) (-γ) / (↑‖moebius_helix (1 - σ) (-γ)‖ : ℂ)) ^ n - 1‖ < δ := by
  convert hsync using 1;
  convert Complex.norm_conj _ using 2 ; norm_num [ fe_unit_conj σ γ hγ ]

/-
Sharp per-pair bound at synchronized n:
    paired Li ≤ 2 − (1−δ)(‖w‖ⁿ + ‖w'‖ⁿ).
-/
lemma synced_combine_sharp (σ γ : ℝ) (hγ : γ ≠ 0) {δ : ℝ} (hδ1 : δ < 1) (n : ℕ)
    (hsync : ‖(moebius_helix σ γ / (↑‖moebius_helix σ γ‖ : ℂ)) ^ n - 1‖ < δ) :
    (li_helix_term σ γ n).re + (li_helix_term (1 - σ) (-γ) n).re ≤
    2 - (1 - δ) * (‖moebius_helix σ γ‖ ^ n + ‖moebius_helix (1 - σ) (-γ)‖ ^ n) := by
  have := re_pow_ge_of_synced ( moebius_helix σ γ ) ( moebius_helix_ne_zero σ γ hγ ) hδ1 n hsync;
  have := re_pow_ge_of_synced ( moebius_helix ( 1 - σ ) ( -γ ) ) ( moebius_helix_ne_zero ( 1 - σ ) ( -γ ) ( neg_ne_zero.mpr hγ ) ) hδ1 n ( fe_sync_transfer σ γ hγ n hsync ) ; ( norm_num [ li_helix_term ] at * ; linarith; )

/-
At synchronized n, each pair's paired Li contribution is < 2δ.
    Follows from synced_combine_sharp + AM-GM (r + 1/r ≥ 2).
-/
lemma synced_pair_le (σ γ : ℝ) (hγ : γ ≠ 0) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (n : ℕ)
    (hsync : ‖(moebius_helix σ γ / (↑‖moebius_helix σ γ‖ : ℂ)) ^ n - 1‖ < δ) :
    (li_helix_term σ γ n).re + (li_helix_term (1 - σ) (-γ) n).re < 2 * δ := by
  -- Let $r =moebius_helix σ γ‖$ and $r' =moebius_helix (1 - σ) (-γ)‖$.
  set r := ‖moebius_helix σ γ‖
  set r' := ‖moebius_helix (1 - σ) (-γ)‖
  have hr : r * r' = 1 := by
    convert moebius_norm_product_one σ γ using 1;
    grind +qlia;
  -- By AM-GM: $r^n + r'^n \geq 2$.
  have h_am_gm : r^n + r'^n ≥ 2 := by
    nlinarith [ sq_nonneg ( r ^ n - r' ^ n ), show 0 < r ^ n by exact pow_pos ( norm_pos_iff.mpr <| moebius_helix_ne_zero σ γ hγ ) _, show 0 < r' ^ n by exact pow_pos ( norm_pos_iff.mpr <| moebius_helix_ne_zero ( 1 - σ ) ( -γ ) <| neg_ne_zero.mpr hγ ) _, show r ^ n * r' ^ n = 1 by rw [ ← mul_pow, hr, one_pow ] ];
  -- By synced_combine_sharp with δ' = (δ + ‖u^n-1‖)/2:
  set δ' := (δ + ‖(moebius_helix σ γ / r) ^ n - 1‖) / 2
  have hδ'_lt_δ : δ' < δ := by
    exact div_lt_iff₀' ( by positivity ) |>.2 ( by linarith )
  have hδ'_lt_1 : δ' < 1 := by
    linarith
  have hsync' : ‖(moebius_helix σ γ / r) ^ n - 1‖ < δ' := by
    exact lt_div_iff₀' ( by positivity ) |>.2 ( by linarith )
  have h_sum_le' : (li_helix_term σ γ n).re + (li_helix_term (1 - σ) (-γ) n).re ≤ 2 - (1 - δ') * (r^n + r'^n) := by
    apply synced_combine_sharp σ γ hγ hδ'_lt_1 n hsync'
  have h_am_gm' : r^n + r'^n ≥ 2 := by
    exact h_am_gm
  have h_final : (li_helix_term σ γ n).re + (li_helix_term (1 - σ) (-γ) n).re < 2 * δ := by
    nlinarith [ show 0 ≤ ‖ ( moebius_helix σ γ / r ) ^ n - 1‖ by positivity ]
  exact h_final

/-
‖w‖ⁿ + ‖w‖⁻ⁿ → ∞ when ‖w‖ ≠ 1 (for divergence of the bad pair).
-/
lemma norm_pow_sum_unbounded (r : ℝ) (hr : 0 < r) (hr1 : r ≠ 1) :
    ∀ C : ℝ, ∃ n : ℕ, C < r ^ n + (1/r) ^ n := by
  have h_diverge : Filter.Tendsto (fun n : ℕ => r ^ n + (1 / r) ^ n) Filter.atTop Filter.atTop := by
    by_cases hr_gt_1 : r > 1;
    · exact Filter.tendsto_atTop_mono ( fun n => le_add_of_nonneg_right <| by positivity ) ( tendsto_pow_atTop_atTop_of_one_lt hr_gt_1 );
    · exact Filter.tendsto_atTop_mono ( fun n => le_add_of_nonneg_left <| by positivity ) ( tendsto_pow_atTop_atTop_of_one_lt <| one_lt_one_div hr <| lt_of_le_of_ne ( le_of_not_gt hr_gt_1 ) hr1 );
  exact fun C => by have := h_diverge.eventually_gt_atTop C; exact this.exists;

/-
**General reverse**: any off-line pair breaks the sum.
    Uses `multi_recur_cofinal` to synchronize all unit-circle parts.
-/
theorem any_offline_breaks_sum (pairs : Finset (ℝ × ℝ))
    (h_nontrivial : ∀ z ∈ pairs, z.2 ≠ 0)
    (bad : ℝ × ℝ) (hbad_mem : bad ∈ pairs) (hbad_off : bad.1 ≠ 1/2) :
    ∀ M : ℝ, ∃ n : ℕ, paired_li_sum pairs n < M := by
  intro M
  set δ := (1 : ℝ) / 2
  obtain ⟨r, hr⟩ : ∃ r > 1, r = ‖moebius_helix bad.1 bad.2‖ ∨ r = ‖moebius_helix (1 - bad.1) (-bad.2)‖ := by
    have := one_partner_gt_one bad.1 bad.2 hbad_off ( h_nontrivial bad hbad_mem ) ; aesop;
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, 2 * (pairs.card + 2 - M) + 1 < r ^ N₀ := by
    exact pow_unbounded_of_one_lt _ hr.1 |> fun ⟨ N₀, hN₀ ⟩ => ⟨ N₀, hN₀ ⟩
  obtain ⟨n, hn₁, hn₂⟩ : ∃ n ≥ N₀, ∀ z ∈ pairs, ‖(moebius_helix z.1 z.2 / (‖moebius_helix z.1 z.2‖ : ℂ)) ^ n - 1‖ < δ := by
    have := @multi_recur_cofinal ( pairs ) ?_ ( fun z => moebius_helix z.val.1 z.val.2 / ( ‖moebius_helix z.val.1 z.val.2‖ : ℂ ) ) ?_ ( 2⁻¹ ) ?_ N₀ <;> norm_num at *;
    · exact this;
    · infer_instance;
    · exact fun a b hab => moebius_helix_ne_zero a b ( h_nontrivial a b hab )
  use n
  have h_sum : paired_li_sum pairs n ≤ (pairs.card : ℝ) + 2 - r ^ n / 2 := by
    have h_sum : paired_li_sum pairs n ≤ (paired_li_sum (pairs.erase bad) n) + (2 - r ^ n / 2) := by
      have h_sum : (li_helix_term bad.1 bad.2 n).re + (li_helix_term (1 - bad.1) (-bad.2) n).re ≤ 2 - r ^ n / 2 := by
        have h_offline_bound : (li_helix_term bad.1 bad.2 n).re + (li_helix_term (1 - bad.1) (-bad.2) n).re ≤ 2 - (1 - δ) * (‖moebius_helix bad.1 bad.2‖ ^ n + ‖moebius_helix (1 - bad.1) (-bad.2)‖ ^ n) := by
          apply synced_combine_sharp bad.1 bad.2 (h_nontrivial bad hbad_mem) (by norm_num) n (hn₂ bad hbad_mem)
        generalize_proofs at *; (
        rcases hr.2 with ( rfl | rfl ) <;> norm_num at * <;> linarith [ pow_nonneg ( norm_nonneg ( moebius_helix bad.1 bad.2 ) ) n, pow_nonneg ( norm_nonneg ( moebius_helix ( 1 - bad.1 ) ( -bad.2 ) ) ) n ] ;);
      unfold paired_li_sum; rw [ ← Finset.sum_erase_add _ _ hbad_mem ] ; linarith;
    have h_sum_erase : paired_li_sum (pairs.erase bad) n ≤ (pairs.erase bad).card := by
      have h_sum_erase : ∀ z ∈ pairs.erase bad, (li_helix_term z.1 z.2 n).re + (li_helix_term (1 - z.1) (-z.2) n).re ≤ 1 := by
        intros z hz
        have h_sync : ‖(moebius_helix z.1 z.2 / (‖moebius_helix z.1 z.2‖ :)) ^ n - 1‖ < δ := by
          exact hn₂ z ( Finset.mem_of_mem_erase hz )
        generalize_proofs at *;
        have := synced_pair_le z.1 z.2 ( h_nontrivial z ( Finset.mem_of_mem_erase hz ) ) ( by norm_num ) ( by norm_num ) n h_sync; norm_num at * ; linarith;
      exact le_trans ( Finset.sum_le_sum h_sum_erase ) ( by norm_num )
    generalize_proofs at *; (
    linarith [ show ( pairs.erase bad |> Finset.card : ℝ ) ≤ pairs.card by exact_mod_cast Finset.card_le_card ( Finset.erase_subset _ _ ) ] ;)
  have h_final : pairs.card + 2 - r ^ n / 2 < M := by
    linarith [ pow_le_pow_right₀ hr.1.le hn₁ ]
  linarith [h_sum]

/-! ## The full biconditional -/

/-- **Finite RH Theorem**: all on-line ⟺ Li bounded below.
    Forward proved unconditionally; reverse uses `any_offline_breaks_sum`. -/
theorem finite_rh (pairs : Finset (ℝ × ℝ))
    (h_nontrivial : ∀ z ∈ pairs, z.2 ≠ 0) :
    (∀ z ∈ pairs, z.1 = 1/2) ↔
    ∃ M : ℝ, ∀ n : ℕ, M ≤ paired_li_sum pairs n := by
  constructor
  · intro h; exact ⟨0, fun n => all_on_line_implies_li_nonneg pairs h n⟩
  · intro ⟨M, hM⟩
    by_contra h
    push_neg at h
    obtain ⟨bad, hbad_mem, hbad_off⟩ := h
    exact absurd (hM _) (not_le.mpr
      (any_offline_breaks_sum pairs h_nontrivial bad hbad_mem hbad_off M).choose_spec)

/-- **Three-way spectral chain** for finite zero sets. -/
theorem finite_spectral_chain (pairs : Finset (ℝ × ℝ))
    (h_nontrivial : ∀ z ∈ pairs, z.2 ≠ 0) :
    (∀ z ∈ pairs, ‖spectral_value z.1 z.2‖ = 1) ↔
    ∃ M : ℝ, ∀ n : ℕ, M ≤ paired_li_sum pairs n := by
  rw [show (∀ z ∈ pairs, ‖spectral_value z.1 z.2‖ = 1) ↔
      (∀ z ∈ pairs, z.1 = 1/2) from
    ⟨fun h z hz => (spectral_on_circle_iff _ _ (h_nontrivial z hz)).mp (h z hz),
     fun h z hz => (spectral_on_circle_iff _ _ (h_nontrivial z hz)).mpr (h z hz)⟩]
  exact finite_rh pairs h_nontrivial

end