/-
  RequestProject.DirichletClosureLedger.lean — the Dirichlet L closure-ledger asymptotic
  =======================================================================================

  Character-agnostic, unconditional partial-sum asymptotic for Dirichlet L-functions —
  for EVERY non-principal character `χ ≠ 1`, of every modulus, with no side hypothesis to supply.

  The single condition is `χ ≠ 1` (non-principal). It is discharged to `∑ j : ZMod N, χ j = 0`
  automatically via `MulChar.sum_eq_zero_of_ne_one`; the principal character `χ = 1` is the genuine
  exception (`∑ = φ(N) ≠ 0`, its L has a pole at `s = 1`, `A(M)` grows — the bounded ledger fails
  there, the ζ-like degenerate case). For a non-principal `χ : DirichletCharacter ℂ N`, write
  the running character sum `A(M) = Σ_{n=1}^M χ(n)` and the partial L-sum
  `L_M(s) = Σ_{n=1}^M χ(n) n^{-s}`. We prove, for `Re s > 0`:

    L_M(s) − L(s) = A(M)·M^{-s} + R_M(s),     ‖R_M(s)‖ ≤ C_χ(s)·M^{-(Re s)},

  where `L = DirichletCharacter.LFunction χ`. The leading coefficient `A(M)` is FREE of the
  height `Im s`: the height lives only in the unit phase of `M^{-s}`.

  Strategy (mirrors `EulerMaclaurinDirichlet.lean`, the ζ analogue): Abel summation
  (`Mathlib.NumberTheory.AbelSummation`) gives a finite identity; the running sum `A` is
  BOUNDED (no `N^{1-s}/(1-s)` non-decaying term appears, because χ is mean-zero per period),
  so the continuation function `cChar χ s = s·∫_{Ioi 1} A(⌊t⌋)·t^{-s-1} dt` is analytic on
  `Re s > 0`, agrees with `LSeries = LFunction` for `Re s > 1`, hence (identity principle on
  the convex half-plane `Re s > 0`) equals `LFunction χ` there.

  STATUS — what is proved here, kernel-clean (axioms = [propext, Classical.choice, Quot.sound]):
  * `closure_ledger` / `closure_ledger_identity`: the `A(M)`-leading decomposition with
    `‖R_M‖ ≤ (‖s‖·N/σ)·M^{-σ}`; `rate_bound`: the self-dual `‖L_M(s) − L(s)‖ ≤ C·M^{-σ}`.
  * `cChar_eq_LFunction`: the analytic-continuation identity on `Re s > 0`.

  THE EXACT, HEIGHT-FREE LEDGER (the mean-zero refinement — piece 2/3, now DONE):
  * `norm_meanzero_sum_le` / `norm_Btail_le`: the mean-zero tail gains one power of `M`,
    `‖Btail χ s M‖ ≤ C·M^{-σ-1}` (summation by parts on the bounded, mean-zero step sequence
    `B(n) = Asum χ n − cmean`, with the per-step weight variation `‖Δω_n‖ ≤ ‖s+1‖·n^{-σ-2}`).
  * `cmean_eq_LFunction_zero`: the channel constant `cmean χ = LFunction χ 0` (taken `s ↓ 0` in
    `LFunction χ s = cmean + s·Btail χ s 1`, no Bernoulli/Hurwitz needed);
    `cmean_closed_form`: `= −(1/N)·Σ_a a.val·χ(a)` (generalized Bernoulli `−B_{1,χ}`).
  * `closure_ledger_exact_identity`: `L_M(s) − L(s) = (A(M) − L(0,χ))·M^{-s} − s·Btail`.
  * `closure_ledger_exact` (HEADLINE): at a zero, `‖L_M(s)·M^s − (A(M) − L(0,χ))‖ ≤ C·M^{-1}`,
    so the rescaled closure error CONVERGES to the height-free fibre imbalance `A(M) − L(0,χ)`.
  * `closure_ledger_onLine`: the on-line `√N` form (`σ = ½`, `‖M^s‖ = √M`).
  * χ₃ instance: `LFunction_chi3_zero` (`L(0,χ₃) = 1/3`), `Asum_chi3_quantized` (`A(M) ∈ {0,1}`),
    `closure_constant_chi3` (`A(M) − L(0,χ₃) ∈ {−1/3, 2/3}`) — the data-mined quantized constant.

  `closure_error_bounded_at_zero` is the weaker piece-1 corollary (rescaled error BOUNDED),
  kept for reference; it is superseded by `closure_ledger_exact`.
-/
import Mathlib
import RequestProject.Chi3FibreBalance

open Finset Complex MeasureTheory Set Filter Topology

namespace DirichletClosureLedger

variable {N : ℕ} [NeZero N]

/-! ## Section 1: The running character sum and its boundedness -/

/-- The running character sum `A(M) = Σ_{k=0}^{M} χ(k)` (the `k=0` term is `χ 0 = 0`, so
    this equals `Σ_{k=1}^{M} χ(k)`). Defined with `Finset.Icc 0 M` to match Mathlib's Abel
    summation API (`∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k`). -/
noncomputable def Asum (χ : DirichletCharacter ℂ N) (M : ℕ) : ℂ :=
  ∑ k ∈ Finset.Icc 0 M, χ k

/-- The partial L-sum `L_M(s) = Σ_{k=1}^{M} χ(k)·k^{-s}`. -/
noncomputable def LM (χ : DirichletCharacter ℂ N) (s : ℂ) (M : ℕ) : ℂ :=
  ∑ k ∈ Finset.Icc 0 M, χ k * (k : ℂ) ^ (-s)

/-- A window of `N` consecutive naturals `Ioc M (M+N)` is a complete residue system mod `N`:
    the sum of `χ` over it equals the sum of `χ` over all of `ZMod N`. -/
theorem sum_Ioc_period (χ : DirichletCharacter ℂ N) (M : ℕ) :
    ∑ k ∈ Finset.Ioc M (M + N), χ (k : ZMod N) = ∑ j : ZMod N, χ j := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  refine Finset.sum_nbij' (fun k => (k : ZMod N))
    (fun j => M + 1 + (j - ((M + 1 : ℕ) : ZMod N)).val) ?_ ?_ ?_ ?_ ?_
  · intro k hk; exact Finset.mem_univ _
  · intro j _
    simp only [Finset.mem_Ioc]
    refine ⟨by omega, ?_⟩
    have := ZMod.val_lt (j - ((M + 1 : ℕ) : ZMod N)); omega
  · intro k hk
    simp only [Finset.mem_Ioc] at hk
    show M + 1 + ((k : ZMod N) - ((M + 1 : ℕ) : ZMod N)).val = k
    have h1 : ((k : ZMod N) - ((M + 1 : ℕ) : ZMod N)) = ((k - (M + 1) : ℕ) : ZMod N) := by
      rw [Nat.cast_sub (by omega : M + 1 ≤ k)]
    rw [h1]
    have h2 : (k - (M + 1)) < N := by omega
    rw [ZMod.val_natCast_of_lt h2]
    omega
  · intro j _
    show ((M + 1 + (j - ((M + 1 : ℕ) : ZMod N)).val : ℕ) : ZMod N) = j
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id]
    ring
  · intro k hk; rfl

/-- The zero-period-sum hypothesis forces `N ≠ 1` (the modulus-1 character has period sum `χ 0 = 1`). -/
theorem modulus_ne_one (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) : N ≠ 1 := by
  rintro rfl
  exact hχ (Subsingleton.elim χ 1)

omit [NeZero N] in
/-- `Asum` written over `Ioc 0 M` (dropping the vanishing `k = 0` term, since `χ 0 = 0`). -/
theorem Asum_eq_sum_Ioc (χ : DirichletCharacter ℂ N) (hN : N ≠ 1) (M : ℕ) :
    Asum χ M = ∑ k ∈ Finset.Ioc 0 M, χ (k : ZMod N) := by
  unfold Asum
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le M), Finset.sum_cons]
  simp only [Nat.cast_zero, DirichletCharacter.map_zero' χ hN, zero_add]

/-- Under the zero-period-sum hypothesis, the running character sum is periodic with period `N`. -/
theorem Asum_add_period (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (M : ℕ) :
    Asum χ (M + N) = Asum χ M := by
  have hN : N ≠ 1 := modulus_ne_one χ hχ
  rw [Asum_eq_sum_Ioc χ hN (M + N), Asum_eq_sum_Ioc χ hN M,
      ← Finset.sum_Ioc_consecutive _ (Nat.zero_le M) (by omega : M ≤ M + N),
      sum_Ioc_period, MulChar.sum_eq_zero_of_ne_one hχ, add_zero]

/-- **Boundedness of the running character sum.** For a character whose values sum to zero
    over a full period (every non-principal character), `‖A(M)‖ ≤ N`. -/
theorem norm_Asum_le (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (M : ℕ) :
    ‖Asum χ M‖ ≤ N := by
  have hN : N ≠ 1 := modulus_ne_one χ hχ
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  -- Reduce M mod N: A(M) = A(M % N) by periodicity.
  have hred : Asum χ M = Asum χ (M % N) := by
    -- Induction on the quotient: A(M) = A(M - N) repeatedly
    conv_lhs => rw [← Nat.div_add_mod M N]
    induction M / N with
    | zero => simp
    | succ q ih =>
      rw [show N * (q + 1) + M % N = (N * q + M % N) + N from by ring,
          Asum_add_period χ hχ, ih]
  rw [hred, Asum_eq_sum_Ioc χ hN (M % N)]
  calc ‖∑ k ∈ Finset.Ioc 0 (M % N), χ (k : ZMod N)‖
      ≤ ∑ k ∈ Finset.Ioc 0 (M % N), ‖χ (k : ZMod N)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.Ioc 0 (M % N), (1 : ℝ) :=
        Finset.sum_le_sum (fun k _ => DirichletCharacter.norm_le_one χ _)
    _ = ((M % N : ℕ) : ℝ) := by
        rw [Finset.sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul, mul_one]
    _ ≤ N := by
        have h : M % N < N := Nat.mod_lt M hNpos
        exact_mod_cast h.le

/-! ## Section 2: The Abel summation identity for the character L-sum

  With `c k = χ k`, `f t = t^{-s}`, `deriv f t = -s·t^{-s-1}`, Mathlib's Abel summation gives
    L_M(s) = M^{-s}·A(M) + s·∫_{Ioc 1 M} A(⌊t⌋)·t^{-s-1} dt.
  The running floor sum `A(⌊t⌋)` is bounded (by `norm_Asum_le`), so the tail integral
  converges on `Re s > 0` with no `M^{1-s}` term. -/

/-- `A(⌊t⌋)` as a function of a real argument: the running character sum up to `⌊t⌋`. -/
noncomputable def Afloor (χ : DirichletCharacter ℂ N) (t : ℝ) : ℂ := Asum χ ⌊t⌋₊

omit [NeZero N] in
/-- `Afloor` is `Asum` at the floor — definitional, recorded for rewriting. -/
theorem Afloor_eq (χ : DirichletCharacter ℂ N) (t : ℝ) :
    Afloor χ t = ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, χ k := rfl

omit [NeZero N] in
/-- `Afloor χ` is measurable (a step function: `Asum ∘ ⌊·⌋₊`). -/
theorem measurable_Afloor (χ : DirichletCharacter ℂ N) : Measurable (Afloor χ) :=
  (measurable_from_nat.comp Nat.measurable_floor)

omit [NeZero N] in
/-- The derivative of `t ↦ (↑t)^{-s}` (as a real-to-complex map) is `-s·(↑t)^{-s-1}` for `t > 0`. -/
theorem hasDerivAt_cpow_neg (s : ℂ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s)) (-s * (t : ℂ) ^ (-s - 1)) t := by
  by_cases hs : s = 0
  · subst hs
    simp only [neg_zero, Complex.cpow_zero, zero_mul]
    exact hasDerivAt_const t (1 : ℂ)
  · exact hasDerivAt_ofReal_cpow_const (ne_of_gt ht) (neg_ne_zero.mpr hs)

omit [NeZero N] in
/-- `deriv (fun t => (↑t)^{-s}) t = -s·(↑t)^{-s-1}` for `t > 0`. -/
theorem deriv_cpow_neg (s : ℂ) {t : ℝ} (ht : 0 < t) :
    deriv (fun y : ℝ => (y : ℂ) ^ (-s)) t = -s * (t : ℂ) ^ (-s - 1) :=
  (hasDerivAt_cpow_neg s ht).deriv

omit [NeZero N] in
/-- The integrand `A(⌊t⌋)·t^{-s-1}` is `AEStronglyMeasurable` on any `Ioi a` with `a ≥ 0`. -/
theorem integrand_aesm (χ : DirichletCharacter ℂ N) (s : ℂ) {a : ℝ} (ha : 0 ≤ a) :
    AEStronglyMeasurable (fun t : ℝ => Afloor χ t * (t : ℂ) ^ (-s - 1))
      (volume.restrict (Ioi a)) := by
  have h_slit : ∀ t ∈ Ioi a, (↑t : ℂ) ∈ Complex.slitPlane :=
    fun t ht => Complex.ofReal_mem_slitPlane.mpr (lt_of_le_of_lt ha ht)
  refine AEStronglyMeasurable.mul ?_
    ((ContinuousOn.cpow continuous_ofReal.continuousOn continuousOn_const
      h_slit).aestronglyMeasurable measurableSet_Ioi)
  -- Afloor χ = (Asum χ) ∘ ⌊·⌋₊ ∘ id ; measurable as composition with the floor.
  refine (Measurable.aestronglyMeasurable ?_)
  exact (measurable_from_nat.comp Nat.measurable_floor)

/-- Pointwise norm bound on the integrand: `‖A(⌊t⌋)·t^{-s-1}‖ ≤ N·t^{-σ-1}` for `t > 0`,
    under the zero-period-sum hypothesis. -/
theorem norm_integrand_le (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (s : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖Afloor χ t * (t : ℂ) ^ (-s - 1)‖ ≤ (N : ℝ) * t ^ (-s.re - 1) := by
  rw [norm_mul]
  have hA : ‖Afloor χ t‖ ≤ N := norm_Asum_le χ hχ ⌊t⌋₊
  have hcpow : ‖(t : ℂ) ^ (-s - 1)‖ = t ^ (-s.re - 1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht]
    simp [Complex.sub_re, Complex.neg_re, Complex.one_re]
  rw [hcpow]
  exact mul_le_mul hA le_rfl (Real.rpow_nonneg ht.le _) (by positivity)

/-- The integrand is integrable on `Ioi a` for `a ≥ 1` and `Re s > 0` (dominated by `N·t^{-σ-1}`). -/
theorem integrableOn_integrand (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (s : ℂ) (hσ : 0 < s.re) {a : ℝ} (ha : 1 ≤ a) :
    IntegrableOn (fun t : ℝ => Afloor χ t * (t : ℂ) ^ (-s - 1)) (Ioi a) := by
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le one_pos ha
  have h_dom : IntegrableOn (fun t : ℝ => (N : ℝ) * t ^ (-s.re - 1)) (Ioi a) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -s.re - 1 < -1) ha0).const_mul _
  refine h_dom.integrable.mono (integrand_aesm χ s ha0.le) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Set.mem_Ioi] at ht
  have ht_pos : (0 : ℝ) < t := lt_trans ha0 ht
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ (N:ℝ) * t ^ (-s.re - 1))]
  exact norm_integrand_le χ hχ s ht_pos

/-- The tail integral `∫_{Ioi a} A(⌊t⌋)·t^{-s-1} dt`. -/
noncomputable def tail (χ : DirichletCharacter ℂ N) (s : ℂ) (a : ℝ) : ℂ :=
  ∫ t in Ioi a, Afloor χ t * (t : ℂ) ^ (-s - 1)

/-- Bound on the tail integral: `‖∫_{Ioi a} A(⌊t⌋)·t^{-s-1}‖ ≤ N·a^{-σ}/σ` for `a ≥ 1`, `Re s > 0`. -/
theorem norm_tail_le (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (s : ℂ) (hσ : 0 < s.re) {a : ℝ} (ha : 1 ≤ a) :
    ‖tail χ s a‖ ≤ (N : ℝ) * a ^ (-s.re) / s.re := by
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le one_pos ha
  unfold tail
  have h_integ : IntegrableOn (fun t : ℝ => (N : ℝ) * t ^ (-s.re - 1)) (Ioi a) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -s.re - 1 < -1) ha0).const_mul _
  have h_bound : ∀ᵐ t ∂(volume.restrict (Ioi a)),
      ‖Afloor χ t * (t : ℂ) ^ (-s - 1)‖ ≤ (N : ℝ) * t ^ (-s.re - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Set.mem_Ioi] at ht
    exact norm_integrand_le χ hχ s (lt_trans ha0 ht)
  calc ‖∫ t in Ioi a, Afloor χ t * (t : ℂ) ^ (-s - 1)‖
      ≤ ∫ t in Ioi a, (N : ℝ) * t ^ (-s.re - 1) :=
        norm_integral_le_of_norm_le h_integ h_bound
    _ = (N : ℝ) * ∫ t in Ioi a, t ^ (-s.re - 1) := by
        rw [integral_const_mul]
    _ = (N : ℝ) * (-(a ^ (-s.re - 1 + 1)) / (-s.re - 1 + 1)) := by
        rw [integral_Ioi_rpow_of_lt (by linarith : -s.re - 1 < -1) ha0]
    _ = (N : ℝ) * a ^ (-s.re) / s.re := by
        rw [show -s.re - 1 + 1 = -s.re from by ring]; ring

/-- The continuation function `cChar χ s = s·∫_{Ioi 1} A(⌊t⌋)·t^{-s-1} dt`.
    Convergent and analytic on `Re s > 0` (bounded `A`), and equal to `LFunction χ s` there. -/
noncomputable def cChar (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  s * tail χ s 1

/-- **The finite Abel summation identity for the character L-sum.**
    `L_M(s) = M^{-s}·A(M) + s·∫_{Ioc 1 M} A(⌊t⌋)·t^{-s-1} dt` for `Re s > 0`, `M ≥ 1`.
    (No `M^{1-s}/(1-s)` term — that is the character cancellation, vs. the ζ case.) -/
theorem abel_identity (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (s : ℂ) (M : ℕ) :
    LM χ s M = (M : ℂ) ^ (-s) * Asum χ M
      + s * ∫ t in Ioc (1 : ℝ) (M : ℝ), Afloor χ t * (t : ℂ) ^ (-s - 1) := by
  have hN : N ≠ 1 := modulus_ne_one χ hχ
  -- Apply Mathlib's Abel summation with c k = χ k, f t = t^{-s}.
  have hc0 : (fun k : ℕ => χ (k : ZMod N)) 0 = 0 := by
    simp only [Nat.cast_zero, DirichletCharacter.map_zero' χ hN]
  have hdiff : ∀ t ∈ Set.Icc (1 : ℝ) (M : ℝ),
      DifferentiableAt ℝ (fun y : ℝ => (y : ℂ) ^ (-s)) t :=
    fun t ht => (hasDerivAt_cpow_neg s (lt_of_lt_of_le one_pos ht.1)).differentiableAt
  have hint : IntegrableOn (deriv (fun y : ℝ => (y : ℂ) ^ (-s))) (Set.Icc (1 : ℝ) (M : ℝ)) := by
    -- deriv f t = -s·t^{-s-1}, continuous on Icc 1 M
    have hcong : Set.EqOn (deriv (fun y : ℝ => (y : ℂ) ^ (-s)))
        (fun t => -s * (t : ℂ) ^ (-s - 1)) (Set.Icc (1 : ℝ) (M : ℝ)) :=
      fun t ht => deriv_cpow_neg s (lt_of_lt_of_le one_pos ht.1)
    rw [integrableOn_congr_fun hcong measurableSet_Icc]
    have h_slit : ∀ t ∈ Set.Icc (1 : ℝ) (M : ℝ), (↑t : ℂ) ∈ Complex.slitPlane :=
      fun t ht => Complex.ofReal_mem_slitPlane.mpr (lt_of_lt_of_le one_pos ht.1)
    exact (continuousOn_const.mul
      (ContinuousOn.cpow continuous_ofReal.continuousOn continuousOn_const
        h_slit)).integrableOn_compact isCompact_Icc
  have key := sum_mul_eq_sub_integral_mul₀ (fun k : ℕ => χ (k : ZMod N)) hc0 (M : ℝ) hdiff hint
  -- ⌊(M:ℝ)⌋₊ = M
  rw [Nat.floor_natCast] at key
  -- Rewrite LHS to LM, the boundary term to M^{-s}·A(M), and the integral via deriv.
  rw [show LM χ s M = ∑ k ∈ Finset.Icc 0 M, (fun y : ℝ => (y : ℂ) ^ (-s)) (k : ℝ) * χ (k : ZMod N) from by
        unfold LM; refine Finset.sum_congr rfl (fun k _ => by push_cast; ring)]
  rw [key]
  -- Boundary term: f M · A(M) = M^{-s}·A(M).  Integral: rewrite deriv to -s·t^{-s-1}.
  have hbdry : (fun y : ℝ => (y : ℂ) ^ (-s)) (M : ℝ) * ∑ k ∈ Finset.Icc 0 M, χ (k : ZMod N)
      = (M : ℂ) ^ (-s) * Asum χ M := by
    unfold Asum; push_cast; ring
  rw [hbdry]
  -- Integral congruence: ∫ Ioc 1 M, deriv f t · A(⌊t⌋) = ∫ Ioc 1 M, (-s·t^{-s-1})·A(⌊t⌋)
  have hint_eq : ∫ t in Ioc (1 : ℝ) (M : ℝ), deriv (fun y : ℝ => (y : ℂ) ^ (-s)) t
        * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, χ (k : ZMod N)
      = ∫ t in Ioc (1 : ℝ) (M : ℝ), (-s) * (Afloor χ t * (t : ℂ) ^ (-s - 1)) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    simp only
    rw [Set.mem_Ioc] at ht
    rw [deriv_cpow_neg s (lt_of_lt_of_le one_pos ht.1.le)]
    unfold Afloor Asum; ring
  rw [hint_eq, integral_const_mul]
  ring

/-! ## Section 3: Identification of `cChar` with the L-function

  For `Re s > 1` the partial sums `LM` converge to `LFunction χ s` and the boundary term
  `M^{-s}·A(M) → 0`, giving `cChar χ s = LFunction χ s`. Both sides are analytic on the
  connected domain `Re s > 0`, so they agree there (identity principle). -/

omit [NeZero N] in
/-- `LM χ s M` is the `(M+1)`-th partial sum of the L-series of `χ` (needs `N ≠ 1` so `χ 0 = 0`). -/
theorem LM_eq_partial_sum (χ : DirichletCharacter ℂ N) (hN : N ≠ 1) (s : ℂ) (M : ℕ) :
    LM χ s M = ∑ k ∈ Finset.range (M + 1), LSeries.term (fun n => χ (n : ZMod N)) s k := by
  unfold LM
  -- Both are sums over `Icc 0 M = range (M+1)`; match term-by-term.
  rw [show Finset.range (M + 1) = Finset.Icc 0 M from by
        rw [Finset.range_eq_Ico, Nat.Ico_zero_eq_range, Nat.range_succ_eq_Icc_zero]]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp [LSeries.term, Nat.cast_zero, DirichletCharacter.map_zero' χ hN]
  · rw [LSeries.term_of_ne_zero (by omega) (fun n => χ (n : ZMod N)) s]
    rw [Complex.cpow_neg]; field_simp

/-- For `Re s > 1`: `LM χ s M → LFunction χ s` as `M → ∞`. -/
theorem LM_tendsto_LFunction (χ : DirichletCharacter ℂ N) (hN : N ≠ 1) (s : ℂ) (hs : 1 < s.re) :
    Tendsto (fun M : ℕ => LM χ s M) atTop (𝓝 (DirichletCharacter.LFunction χ s)) := by
  have hsumm : LSeriesSummable (fun n => χ (n : ZMod N)) s :=
    DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs
  have hhassum := hsumm.LSeriesHasSum
  -- LSeriesHasSum is HasSum (term ..) (LSeries ..); LFunction = LSeries for Re s > 1.
  have hLF : DirichletCharacter.LFunction χ s = LSeries (fun n => χ (n : ZMod N)) s :=
    DirichletCharacter.LFunction_eq_LSeries χ hs
  rw [hLF]
  rw [hhassum.LSeries_eq]
  -- tendsto of partial sums (range (M+1))
  have htend := (hhassum : HasSum (LSeries.term (fun n => χ (n : ZMod N)) s)
    (LSeries (fun n => χ (n : ZMod N)) s)).tendsto_sum_nat
  -- htend : Tendsto (fun M => ∑ k ∈ range M, term ..) atTop (𝓝 (LSeries ..))
  -- We want range (M+1); compose with succ.
  have htend' := htend.comp (tendsto_add_atTop_nat 1)
  refine htend'.congr (fun M => ?_)
  rw [Function.comp_apply, LM_eq_partial_sum χ hN]

/-- The boundary term `M^{-s}·A(M) → 0` for `Re s > 0` (bounded `A`, decaying power). -/
theorem boundary_tendsto_zero (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (s : ℂ) (hσ : 0 < s.re) :
    Tendsto (fun M : ℕ => (M : ℂ) ^ (-s) * Asum χ M) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h_bound : ∀ᶠ M : ℕ in atTop, ‖(M : ℂ) ^ (-s) * Asum χ M‖ ≤ (N : ℝ) * (M : ℝ) ^ (-s.re) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with M hM
    rw [norm_mul]
    have hcpow : ‖(M : ℂ) ^ (-s)‖ = (M : ℝ) ^ (-s.re) := by
      rw [Complex.norm_natCast_cpow_of_pos (by omega)]; simp
    rw [hcpow, mul_comm]
    exact mul_le_mul (norm_Asum_le χ hχ M) le_rfl (Real.rpow_nonneg (by positivity) _) (by positivity)
  have h_tend : Tendsto (fun M : ℕ => (N : ℝ) * (M : ℝ) ^ (-s.re)) atTop (𝓝 0) := by
    have : Tendsto (fun M : ℕ => (N : ℝ) * (M : ℝ) ^ (-s.re)) atTop (𝓝 ((N : ℝ) * 0)) :=
      Tendsto.const_mul _ ((tendsto_rpow_neg_atTop hσ).comp tendsto_natCast_atTop_atTop)
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_tend
    (Eventually.of_forall (fun M => norm_nonneg _)) h_bound

/-- The truncated tail integral `∫_{Ioc 1 M} → tail χ s 1` for `Re s > 0`. -/
theorem truncated_tail_tendsto (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (s : ℂ) (hσ : 0 < s.re) :
    Tendsto (fun M : ℕ => ∫ t in Ioc (1 : ℝ) (M : ℝ), Afloor χ t * (t : ℂ) ^ (-s - 1))
      atTop (𝓝 (tail χ s 1)) := by
  have hint : IntegrableOn (fun t : ℝ => Afloor χ t * (t : ℂ) ^ (-s - 1)) (Ioi (1 : ℝ)) :=
    integrableOn_integrand χ hχ s hσ le_rfl
  have htend := MeasureTheory.intervalIntegral_tendsto_integral_Ioi (1 : ℝ) hint
    tendsto_natCast_atTop_atTop
  -- ∫ in 1..(M:ℝ) = ∫ in Ioc 1 M for 1 ≤ M
  refine htend.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with M hM
  rw [intervalIntegral.integral_of_le (by exact_mod_cast hM : (1:ℝ) ≤ (M:ℝ))]

/-- **For `Re s > 1`: `cChar χ s = LFunction χ s`.** -/
theorem cChar_eq_LFunction_of_one_lt_re (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (s : ℂ) (hs : 1 < s.re) :
    cChar χ s = DirichletCharacter.LFunction χ s := by
  have hN : N ≠ 1 := modulus_ne_one χ hχ
  have hσ : 0 < s.re := by linarith
  -- LM = boundary + s·(truncated integral); take limits.
  have h_lim_LM := LM_tendsto_LFunction χ hN s hs
  have h_lim_rhs : Tendsto (fun M : ℕ => (M : ℂ) ^ (-s) * Asum χ M
      + s * ∫ t in Ioc (1 : ℝ) (M : ℝ), Afloor χ t * (t : ℂ) ^ (-s - 1))
      atTop (𝓝 (0 + s * tail χ s 1)) :=
    (boundary_tendsto_zero χ hχ s hσ).add
      ((truncated_tail_tendsto χ hχ s hσ).const_mul s)
  -- The two sequences are equal (abel_identity), so limits agree.
  have h_eq : (fun M : ℕ => LM χ s M) = (fun M : ℕ => (M : ℂ) ^ (-s) * Asum χ M
      + s * ∫ t in Ioc (1 : ℝ) (M : ℝ), Afloor χ t * (t : ℂ) ^ (-s - 1)) := by
    funext M; exact abel_identity χ hχ s M
  rw [h_eq] at h_lim_LM
  have := tendsto_nhds_unique h_lim_LM h_lim_rhs
  rw [cChar]; rw [this]; ring

/-! ## Section 4: Analyticity of `cChar` and the identity principle -/

/-- The tail integral `∫_{Ioi 1} A(⌊t⌋)·t^{-w-1} dt` is differentiable in `w` for `Re w > 0`.
    (Leibniz rule, with the step function `A(⌊t⌋)` bounded by `N`; same domination as the ζ
    fractional-part integral, scaled by `N`.) -/
theorem tail_differentiableAt (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (z : ℂ) (hσ : 0 < z.re) :
    DifferentiableAt ℂ (fun w => ∫ t in Ioi (1 : ℝ), Afloor χ t * (t : ℂ) ^ (-w - 1)) z := by
  set μ := (volume : Measure ℝ).restrict (Ioi (1 : ℝ))
  show DifferentiableAt ℂ (fun w => ∫ t, Afloor χ t * (t : ℂ) ^ (-w - 1) ∂μ) z
  set σ := z.re
  set ε := σ / 4
  have hε_pos : 0 < ε := by positivity
  set F'val := fun (w : ℂ) (t : ℝ) =>
    Afloor χ t * ((t : ℂ) ^ (-w - 1) * Complex.log (t : ℂ) * (-1))
  set F' := fun (w : ℂ) (t : ℝ) =>
    ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (F'val w t)
  set bound := fun (t : ℝ) => (N : ℝ) * (|Real.log t| * t ^ (-(σ / 2 + 1)))
  suffices h : HasFDerivAt (fun w => ∫ t, Afloor χ t * (t : ℂ) ^ (-w - 1) ∂μ)
      (∫ t, F' z t ∂μ) z from h.differentiableAt
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := Metric.ball z ε) (bound := bound)
  · exact Metric.ball_mem_nhds z hε_pos
  · -- AEStronglyMeasurable of the integrand
    have h_slit : ∀ t ∈ Ioi (1 : ℝ), (↑t : ℂ) ∈ Complex.slitPlane :=
      fun t ht => Complex.ofReal_mem_slitPlane.mpr (lt_trans one_pos ht)
    exact .of_forall fun _ =>
      (measurable_Afloor χ).aestronglyMeasurable.mul
        ((ContinuousOn.cpow continuous_ofReal.continuousOn continuousOn_const
          h_slit).aestronglyMeasurable measurableSet_Ioi)
  · -- Integrable at z: dominated by N·t^{-(σ+1)}
    have h_slit : ∀ t ∈ Ioi (1 : ℝ), (↑t : ℂ) ∈ Complex.slitPlane :=
      fun t ht => Complex.ofReal_mem_slitPlane.mpr (lt_trans one_pos ht)
    have h_dom : IntegrableOn (fun t : ℝ => (N : ℝ) * t ^ (-(σ + 1))) (Ioi (1 : ℝ)) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith : -(σ + 1) < -1) one_pos).const_mul _
    have h_aesm : AEStronglyMeasurable (fun t : ℝ => Afloor χ t * (t : ℂ) ^ (-z - 1)) μ :=
      (measurable_Afloor χ).aestronglyMeasurable.mul
        ((ContinuousOn.cpow continuous_ofReal.continuousOn continuousOn_const
          h_slit).aestronglyMeasurable measurableSet_Ioi)
    exact h_dom.integrable.mono h_aesm (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [Set.mem_Ioi] at ht
      have ht_pos : (0 : ℝ) < t := lt_trans one_pos ht
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ (N:ℝ) * t ^ (-(σ + 1)))]
      have := norm_integrand_le χ hχ z ht_pos
      calc ‖Afloor χ t * (t : ℂ) ^ (-z - 1)‖ ≤ (N : ℝ) * t ^ (-z.re - 1) := this
        _ = (N : ℝ) * t ^ (-(σ + 1)) := by rw [show -z.re - 1 = -(σ + 1) from by ring])
  · -- AEStronglyMeasurable of F'
    have h_slit : ∀ t ∈ Ioi (1 : ℝ), (↑t : ℂ) ∈ Complex.slitPlane :=
      fun t ht => Complex.ofReal_mem_slitPlane.mpr (lt_trans one_pos ht)
    have h1 : ContinuousOn (fun t : ℝ => (↑t : ℂ) ^ (-z - 1)) (Ioi 1) :=
      ContinuousOn.cpow continuous_ofReal.continuousOn continuousOn_const h_slit
    have h2 : ContinuousOn (fun t : ℝ => Complex.log (↑t : ℂ)) (Ioi 1) :=
      fun _ ht => (continuous_ofReal.continuousAt.clog
        (Complex.ofReal_mem_slitPlane.mpr (lt_trans one_pos ht))).continuousWithinAt
    have h3 : ContinuousOn (fun t : ℝ =>
        (↑t : ℂ) ^ (-z - 1) * Complex.log (↑t : ℂ) * (-1)) (Ioi 1) :=
      (h1.mul h2).mul continuousOn_const
    have h_F'val : AEStronglyMeasurable (F'val z) μ :=
      (measurable_Afloor χ).aestronglyMeasurable.mul (h3.aestronglyMeasurable measurableSet_Ioi)
    exact (ContinuousLinearMap.smulRightL ℂ ℂ ℂ
      (1 : ℂ →L[ℂ] ℂ)).continuous.comp_aestronglyMeasurable h_F'val
  · -- ‖F' w t‖ ≤ bound t for w in ball(z, σ/4)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro w hw
    rw [Set.mem_Ioi] at ht
    have ht_pos : (0 : ℝ) < t := lt_trans one_pos ht
    have h_norm_F' : ‖F' w t‖ = ‖F'val w t‖ := by
      simp only [F']; rw [ContinuousLinearMap.norm_smulRight_apply]; simp
    rw [h_norm_F']
    simp only [F'val, norm_mul, norm_neg, norm_one, mul_one]
    have hA : ‖Afloor χ t‖ ≤ (N : ℝ) := norm_Asum_le χ hχ ⌊t⌋₊
    have h_cpow_norm : ‖(↑t : ℂ) ^ (-w - 1)‖ = t ^ (-w.re - 1) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos ht_pos]
      simp [Complex.sub_re, Complex.neg_re, Complex.one_re]
    have h_log_norm : ‖Complex.log (↑t : ℂ)‖ = |Real.log t| := by
      rw [(Complex.ofReal_log ht_pos.le).symm, Complex.norm_real, Real.norm_eq_abs]
    have hw_re : σ / 2 < w.re := by
      have h1 : |w.re - z.re| < σ / 4 := by
        calc |w.re - z.re| = |(w - z).re| := by simp [Complex.sub_re]
          _ ≤ ‖w - z‖ := Complex.abs_re_le_norm _
          _ = dist w z := by rw [dist_eq_norm]
          _ < ε := hw
      rw [show z.re = σ from rfl] at h1
      rw [abs_lt] at h1; linarith [h1.1]
    have h_rpow_le : t ^ (-w.re - 1) ≤ t ^ (-(σ / 2 + 1)) :=
      Real.rpow_le_rpow_of_exponent_le ht.le (by linarith : -w.re - 1 ≤ -(σ / 2 + 1))
    calc ‖Afloor χ t‖ * (‖(↑t : ℂ) ^ (-w - 1)‖ * ‖Complex.log (↑t : ℂ)‖)
        ≤ (N : ℝ) * (t ^ (-(σ / 2 + 1)) * |Real.log t|) := by
          apply mul_le_mul hA _ (by positivity) (by positivity)
          rw [h_cpow_norm, h_log_norm]
          exact mul_le_mul_of_nonneg_right h_rpow_le (abs_nonneg _)
      _ = (N : ℝ) * (|Real.log t| * t ^ (-(σ / 2 + 1))) := by ring
  · -- Integrable bound: ∫_Ioi1 N·|log t|·t^{-(σ/2+1)} < ∞
    have hσ4 : (0 : ℝ) < σ / 4 := by positivity
    have h_dom : IntegrableOn (fun t : ℝ => (N : ℝ) * ((4 / σ) * t ^ (-(σ / 4 + 1)))) (Ioi (1 : ℝ)) :=
      ((integrableOn_Ioi_rpow_of_lt (by linarith : -(σ / 4 + 1) < -1) one_pos).const_mul _).const_mul _
    have h_bound_meas : AEStronglyMeasurable bound μ :=
      (continuousOn_const.mul (ContinuousOn.mul
        (continuous_abs.comp_continuousOn
          (Real.continuousOn_log.mono (fun _ ht => ne_of_gt (lt_trans one_pos ht))))
        (ContinuousOn.rpow_const continuousOn_id
          (fun _ ht => Or.inl (ne_of_gt (lt_trans one_pos ht)))))).aestronglyMeasurable
        measurableSet_Ioi
    exact h_dom.integrable.mono h_bound_meas (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [Set.mem_Ioi] at ht
      have ht_pos : (0 : ℝ) < t := lt_trans one_pos ht
      have h_nn₁ : 0 ≤ bound t := by
        simp only [bound]; positivity
      have h_nn₂ : 0 ≤ (N : ℝ) * ((4 / σ) * t ^ (-(σ / 4 + 1))) := by positivity
      rw [Real.norm_of_nonneg h_nn₁, Real.norm_of_nonneg h_nn₂]
      simp only [bound]
      rw [abs_of_nonneg (Real.log_nonneg ht.le)]
      have h_log_bound : Real.log t ≤ t ^ (σ / 4) / (σ / 4) :=
        Real.log_le_rpow_div ht_pos.le hσ4
      have hkey : Real.log t * t ^ (-(σ / 2 + 1)) ≤ (4 / σ) * t ^ (-(σ / 4 + 1)) := by
        calc Real.log t * t ^ (-(σ / 2 + 1))
            ≤ (t ^ (σ / 4) / (σ / 4)) * t ^ (-(σ / 2 + 1)) :=
              mul_le_mul_of_nonneg_right h_log_bound (Real.rpow_nonneg ht_pos.le _)
          _ = (4 / σ) * (t ^ (σ / 4) * t ^ (-(σ / 2 + 1))) := by ring
          _ = (4 / σ) * t ^ (σ / 4 + (-(σ / 2 + 1))) := by rw [Real.rpow_add ht_pos]
          _ = (4 / σ) * t ^ (-(σ / 4 + 1)) := by ring_nf
      calc (N : ℝ) * (Real.log t * t ^ (-(σ / 2 + 1)))
          ≤ (N : ℝ) * ((4 / σ) * t ^ (-(σ / 4 + 1))) :=
            mul_le_mul_of_nonneg_left hkey (by positivity))
  · -- HasFDerivAt for each t (the per-point derivative)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro w _
    rw [Set.mem_Ioi] at ht
    have ht_pos : (0 : ℝ) < t := lt_trans one_pos ht
    apply HasDerivAt.hasFDerivAt
    show HasDerivAt (fun w => Afloor χ t * (t : ℂ) ^ (-w - 1)) (F'val w t) w
    have ht_ne : ((t : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht_pos)
    have hf : HasDerivAt (fun w : ℂ => -w - 1) (-1 : ℂ) w := by
      simpa using ((hasDerivAt_id w).neg.sub_const (1 : ℂ))
    show HasDerivAt (fun w => Afloor χ t * (↑t : ℂ) ^ (-w - 1))
      (Afloor χ t * ((↑t : ℂ) ^ (-w - 1) * Complex.log (↑t : ℂ) * (-1))) w
    exact (hf.const_cpow (Or.inl ht_ne)).const_mul _

/-- **`cChar χ` is analytic on `Re s > 0`.** -/
theorem cChar_analyticAt (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (s : ℂ) (hσ : 0 < s.re) :
    AnalyticAt ℂ (cChar χ) s := by
  rw [analyticAt_iff_eventually_differentiableAt]
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hs_mem : s ∈ {z : ℂ | 0 < z.re} := hσ
  filter_upwards [hU.mem_nhds hs_mem] with z hz_re
  unfold cChar tail
  exact differentiableAt_id.mul (tail_differentiableAt χ hχ z hz_re)

/-- `LFunction χ` is differentiable everywhere under the zero-period-sum hypothesis. -/
theorem LFunction_differentiableAt (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (s : ℂ) :
    DifferentiableAt ℂ (DirichletCharacter.LFunction χ) s := by
  have : DirichletCharacter.LFunction χ = ZMod.LFunction (fun j => χ j) := rfl
  rw [this]
  exact ZMod.differentiableAt_LFunction (fun j => χ j) s (Or.inr (MulChar.sum_eq_zero_of_ne_one hχ))

/-- **For `Re s > 0`: `cChar χ s = LFunction χ s`** (identity principle on the convex
    half-plane `Re s > 0`, agreement on the open subset `Re s > 1`). -/
theorem cChar_eq_LFunction (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (s : ℂ) (hσ : 0 < s.re) :
    cChar χ s = DirichletCharacter.LFunction χ s := by
  set U := {s : ℂ | 0 < s.re}
  have hf : AnalyticOnNhd ℂ (cChar χ) U := fun z hz => cChar_analyticAt χ hχ z hz
  have hg : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) U := by
    have h_diff : Differentiable ℂ (DirichletCharacter.LFunction χ) :=
      fun z => LFunction_differentiableAt χ hχ z
    exact (h_diff.differentiableOn.analyticOnNhd isOpen_univ).mono (fun z _ => Set.mem_univ z)
  -- U is convex hence preconnected
  have hUconn : IsPreconnected U := (convex_halfSpace_gt Complex.reLm.isLinear 0).isPreconnected
  -- agreement near z₀ = 2 (on the open set Re s > 1)
  have h₀ : (2 : ℂ) ∈ U := by show (0:ℝ) < (2:ℂ).re; simp
  have hfg : cChar χ =ᶠ[𝓝 (2 : ℂ)] DirichletCharacter.LFunction χ := by
    filter_upwards [(continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds
      (show 1 < (2 : ℂ).re by simp)] with z hz
    exact cChar_eq_LFunction_of_one_lt_re χ hχ z hz
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hUconn h₀ hfg hσ

/-- **The uniform polynomial growth bound on the whole right half-plane**: for `χ ≠ 1`,
    `‖L(χ,s)‖ ≤ N·‖s‖/Re s` for every `s` with `Re s > 0`. Elementary and explicit — the bounded
    running character sum (`norm_Asum_le`) through the Abel-summation continuation; no functional
    equation, no Stirling. This is the `M(T) ≍ T` input the classical zero-free region consumes:
    on any edge disk `‖s − (1+iy)‖ ≤ r < 1` it gives `‖L‖ ≤ N(|y|+2)/(1−r)`. -/
theorem norm_LFunction_le_half_plane (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (s : ℂ) (hσ : 0 < s.re) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ (N : ℝ) * ‖s‖ / s.re := by
  rw [← cChar_eq_LFunction χ hχ s hσ, cChar, norm_mul]
  have htail := norm_tail_le χ hχ s hσ (le_refl (1 : ℝ))
  rw [Real.one_rpow] at htail
  calc ‖s‖ * ‖tail χ s 1‖ ≤ ‖s‖ * ((N : ℝ) * 1 / s.re) :=
        mul_le_mul_of_nonneg_left htail (norm_nonneg s)
    _ = (N : ℝ) * ‖s‖ / s.re := by ring

/-! ## Section 5: The closure ledger — exact leading term and the rate bound

  Combining `abel_identity` with `cChar = LFunction`, the partial-sum defect is the running
  character imbalance `A(M)` carried by the unit phase `M^{-s}`, plus a one-power-faster tail
  remainder.  The leading coefficient `A(M)` is FREE of the height `Im s`. -/

/-- The remainder `R_M(s) = −s·∫_{Ioi M} A(⌊t⌋)·t^{-s-1} dt = −s·tail χ s M`. -/
noncomputable def Rrem (χ : DirichletCharacter ℂ N) (s : ℂ) (M : ℕ) : ℂ :=
  -s * tail χ s (M : ℝ)

/-- Splitting the tail: `∫_{Ioi 1} = ∫_{Ioc 1 M} + ∫_{Ioi M}` for `M ≥ 1`, `Re s > 0`. -/
theorem tail_split (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (s : ℂ) (hσ : 0 < s.re) (M : ℕ) (hM : 1 ≤ M) :
    tail χ s 1 = (∫ t in Ioc (1 : ℝ) (M : ℝ), Afloor χ t * (t : ℂ) ^ (-s - 1)) + tail χ s (M : ℝ) := by
  have hle : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hIoi1 : IntegrableOn (fun t : ℝ => Afloor χ t * (t : ℂ) ^ (-s - 1)) (Ioi (1 : ℝ)) :=
    integrableOn_integrand χ hχ s hσ le_rfl
  have hIoiM : IntegrableOn (fun t : ℝ => Afloor χ t * (t : ℂ) ^ (-s - 1)) (Ioi (M : ℝ)) :=
    integrableOn_integrand χ hχ s hσ hle
  have hkey := intervalIntegral.integral_interval_add_Ioi (a := (1:ℝ)) (b := (M:ℝ))
    hIoi1 hIoiM
  rw [intervalIntegral.integral_of_le hle] at hkey
  rw [tail, ← hkey, tail]

/-- **The closure-ledger identity.** For `Re s > 0`, `M ≥ 1`:
    `L_M(s) − L(s) = A(M)·M^{-s} + R_M(s)`, where the leading coefficient `A(M)` is the running
    character imbalance — FREE of the height `Im s` — and `R_M(s) = −s·tail χ s M`. -/
theorem closure_ledger_identity (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (s : ℂ) (hσ : 0 < s.re) (M : ℕ) (hM : 1 ≤ M) :
    LM χ s M - DirichletCharacter.LFunction χ s = Asum χ M * (M : ℂ) ^ (-s) + Rrem χ s M := by
  rw [abel_identity χ hχ s M, ← cChar_eq_LFunction χ hχ s hσ, cChar,
      tail_split χ hχ s hσ M hM, Rrem]
  ring

/-- **Bound on the remainder.** `‖R_M(s)‖ ≤ (‖s‖·N/σ)·M^{-σ}` for `Re s > 0`, `M ≥ 1`. -/
theorem norm_Rrem_le (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (s : ℂ) (hσ : 0 < s.re) (M : ℕ) (hM : 1 ≤ M) :
    ‖Rrem χ s M‖ ≤ ‖s‖ * (N : ℝ) / s.re * (M : ℝ) ^ (-s.re) := by
  have hle : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  rw [Rrem, norm_mul, norm_neg]
  calc ‖s‖ * ‖tail χ s (M : ℝ)‖
      ≤ ‖s‖ * ((N : ℝ) * (M : ℝ) ^ (-s.re) / s.re) :=
        mul_le_mul_of_nonneg_left (norm_tail_le χ hχ s hσ hle) (norm_nonneg _)
    _ = ‖s‖ * (N : ℝ) / s.re * (M : ℝ) ^ (-s.re) := by ring

/-- **The Dirichlet L closure-ledger asymptotic (rate bound + exact leading term).**

    For a Dirichlet character whose values sum to zero over a full period (every non-principal
    character), and `Re s > 0`:
      `L_M(s) − L(s) = A(M)·M^{-s} + R_M(s)`,    `‖R_M(s)‖ ≤ C·M^{-(Re s)}`,
    with `C = ‖s‖·N/(Re s)` independent of `M`.  The leading coefficient `A(M) = Σ_{n≤M} χ(n)`
    is the running character imbalance — **free of the height `Im s`**; the height lives only in
    the unit phase of `M^{-s}`. -/
theorem closure_ledger (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (s : ℂ) (hσ : 0 < s.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 1 ≤ M →
      (LM χ s M - DirichletCharacter.LFunction χ s
          = Asum χ M * (M : ℂ) ^ (-s) + Rrem χ s M)
        ∧ ‖Rrem χ s M‖ ≤ C * (M : ℝ) ^ (-s.re) := by
  refine ⟨‖s‖ * (N : ℝ) / s.re + 1, by positivity, fun M hM => ⟨closure_ledger_identity χ hχ s hσ M hM, ?_⟩⟩
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hpow_nonneg : (0 : ℝ) ≤ (M : ℝ) ^ (-s.re) := Real.rpow_nonneg hMpos.le _
  calc ‖Rrem χ s M‖
      ≤ ‖s‖ * (N : ℝ) / s.re * (M : ℝ) ^ (-s.re) := norm_Rrem_le χ hχ s hσ M hM
    _ ≤ (‖s‖ * (N : ℝ) / s.re + 1) * (M : ℝ) ^ (-s.re) := by
        rw [add_mul, one_mul]; linarith [hpow_nonneg]

/-- **The self-dual rate bound (piece 1).** `‖L_M(s) − L(s)‖ ≤ C·M^{-(Re s)}` for `Re s > 0`. -/
theorem rate_bound (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (s : ℂ) (hσ : 0 < s.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 1 ≤ M →
      ‖LM χ s M - DirichletCharacter.LFunction χ s‖ ≤ C * (M : ℝ) ^ (-s.re) := by
  obtain ⟨C, hC, hbound⟩ := closure_ledger χ hχ s hσ
  -- ‖A(M)·M^{-s}‖ ≤ N·M^{-σ}, plus the remainder bound.
  refine ⟨(N : ℝ) + C, by positivity, fun M hM => ?_⟩
  obtain ⟨hid, hrem⟩ := hbound M hM
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hpow_nonneg : (0 : ℝ) ≤ (M : ℝ) ^ (-s.re) := Real.rpow_nonneg hMpos.le _
  rw [hid]
  have hlead : ‖Asum χ M * (M : ℂ) ^ (-s)‖ ≤ (N : ℝ) * (M : ℝ) ^ (-s.re) := by
    rw [norm_mul]
    have hcpow : ‖(M : ℂ) ^ (-s)‖ = (M : ℝ) ^ (-s.re) := by
      rw [Complex.norm_natCast_cpow_of_pos (by omega)]; simp
    rw [hcpow]
    exact mul_le_mul (norm_Asum_le χ hχ M) le_rfl hpow_nonneg (by positivity)
  calc ‖Asum χ M * (M : ℂ) ^ (-s) + Rrem χ s M‖
      ≤ ‖Asum χ M * (M : ℂ) ^ (-s)‖ + ‖Rrem χ s M‖ := norm_add_le _ _
    _ ≤ (N : ℝ) * (M : ℝ) ^ (-s.re) + C * (M : ℝ) ^ (-s.re) := add_le_add hlead hrem
    _ = ((N : ℝ) + C) * (M : ℝ) ^ (-s.re) := by ring

/-- **Headline at a zero (piece-1 level): the rescaled closure error is bounded by the
    fibre-imbalance scale.**  At a zero `L(s) = 0` with `Re s > 0`, the height-rescaled partial
    sum `L_M(s)·M^s` differs from the running character imbalance `A(M)` by a uniformly bounded
    amount: `‖L_M(s)·M^s − A(M)‖ ≤ C` for all `M ≥ 1`, with `C` independent of `M`.

    The leading object `A(M) = Σ_{n≤M} χ(n)` is **free of the height `Im s`** — the height enters
    only through the unit phase `M^{-s}` (here cancelled by `M^s`).  (Upgrading the `O(1)` to a
    genuine limit `→ ‖A(M) − L(0,χ)‖` needs the one-power-faster `O(M^{-σ-1})` remainder, i.e. the
    mean-zero integration-by-parts refinement — not proved here.) -/
theorem closure_error_bounded_at_zero (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (s : ℂ) (hσ : 0 < s.re)
    (hzero : DirichletCharacter.LFunction χ s = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 1 ≤ M →
      ‖LM χ s M * (M : ℂ) ^ s - Asum χ M‖ ≤ C := by
  -- From the ledger identity at a zero: L_M(s) = A(M)·M^{-s} + R_M, so
  -- L_M(s)·M^s − A(M) = R_M·M^s, and ‖R_M·M^s‖ ≤ (‖s‖N/σ)·M^{-σ}·M^σ = ‖s‖N/σ.
  refine ⟨‖s‖ * (N : ℝ) / s.re + 1, by positivity, fun M hM => ?_⟩
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hMne : (M : ℂ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have hid := closure_ledger_identity χ hχ s hσ M hM
  rw [hzero, sub_zero] at hid
  -- L_M(s)·M^s − A(M) = (A(M)·M^{-s} + R_M)·M^s − A(M) = R_M·M^s
  have hcancel : LM χ s M * (M : ℂ) ^ s - Asum χ M = Rrem χ s M * (M : ℂ) ^ s := by
    rw [hid, add_mul, mul_assoc, ← Complex.cpow_add _ _ hMne, neg_add_cancel,
        Complex.cpow_zero, mul_one]
    ring
  rw [hcancel, norm_mul]
  have hcpow : ‖(M : ℂ) ^ s‖ = (M : ℝ) ^ s.re := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega)]
  have hRb : ‖Rrem χ s M‖ ≤ ‖s‖ * (N : ℝ) / s.re * (M : ℝ) ^ (-s.re) :=
    norm_Rrem_le χ hχ s hσ M hM
  calc ‖Rrem χ s M‖ * ‖(M : ℂ) ^ s‖
      = ‖Rrem χ s M‖ * (M : ℝ) ^ s.re := by rw [hcpow]
    _ ≤ (‖s‖ * (N : ℝ) / s.re * (M : ℝ) ^ (-s.re)) * (M : ℝ) ^ s.re :=
        mul_le_mul_of_nonneg_right hRb (Real.rpow_nonneg hMpos.le _)
    _ = ‖s‖ * (N : ℝ) / s.re := by
        rw [mul_assoc, ← Real.rpow_add hMpos, neg_add_cancel, Real.rpow_zero, mul_one]
    _ ≤ ‖s‖ * (N : ℝ) / s.re + 1 := by linarith

/-! ## Section 6: The mean-zero refinement — the exact, height-free ledger

  The step values `Asum χ n` are periodic mod `N` (`Asum_add_period`).  Their period-mean
  `cmean := (1/N)·Σ_{n<N} Asum χ n` is the channel constant.  Subtracting it gives the
  mean-zero step `Bfloor χ t := Afloor χ t − cmean`, whose antiderivative
  `G(t) := ∫_M^t Bfloor` is UNIFORMLY BOUNDED (a bounded sawtooth).  Integration by parts on
  `Ioi M` then gains one power of `M` in the `B`-tail, upgrading the remainder to `O(M^{-σ-1})`
  and the leading constant to `A(M) − cmean = A(M) − L(0,χ)`. -/

/-- The channel constant: the period-mean of the running character sum. -/
noncomputable def cmean (χ : DirichletCharacter ℂ N) : ℂ :=
  (∑ n ∈ Finset.range N, Asum χ n) / N

/-- The mean-zero step function `Bfloor χ t = A(⌊t⌋) − cmean`. -/
noncomputable def Bfloor (χ : DirichletCharacter ℂ N) (t : ℝ) : ℂ :=
  Afloor χ t - cmean χ

/-- `Asum χ` (as `ℕ → ℂ`) is periodic with period `N`. -/
theorem Asum_periodic (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) : Function.Periodic (Asum χ) N :=
  fun M => Asum_add_period χ hχ M

/-- The sum of `Asum χ` over any window of `N` consecutive integers `Ico k (k+N)` is
    independent of `k` (periodicity), hence equals the `range N` sum `= N·cmean`. -/
theorem sum_Asum_Ico_period (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (k : ℕ) :
    ∑ n ∈ Finset.Ico k (k + N), Asum χ n = ∑ n ∈ Finset.range N, Asum χ n := by
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  induction k with
  | zero => simp
  | succ m ih =>
    -- Telescope: shifting the window from m to m+1 drops Asum χ m, adds Asum χ (m+N);
    -- these are equal by periodicity, so the window sum is unchanged.
    rw [← ih, show m + 1 + N = (m + N) + 1 from by ring]
    -- LHS = Σ_{Ico (m+1) (m+N+1)},  RHS = Σ_{Ico m (m+N)}
    -- Peel the bottom of RHS (n = m) and the top of LHS (n = m+N).
    have hL : ∑ n ∈ Finset.Ico (m + 1) (m + N + 1), Asum χ n
        = (∑ n ∈ Finset.Ico (m + 1) (m + N), Asum χ n) + Asum χ (m + N) := by
      rw [← Finset.sum_Ico_consecutive _ (by omega : m + 1 ≤ m + N) (by omega : m + N ≤ m + N + 1),
          Nat.Ico_succ_singleton, Finset.sum_singleton]
    have hR : ∑ n ∈ Finset.Ico m (m + N), Asum χ n
        = Asum χ m + ∑ n ∈ Finset.Ico (m + 1) (m + N), Asum χ n := by
      rw [← Finset.sum_Ico_consecutive _ (by omega : m ≤ m + 1) (by omega : m + 1 ≤ m + N),
          Nat.Ico_succ_singleton, Finset.sum_singleton]
    rw [hL, hR, Asum_add_period χ hχ m]
    ring

/-- The full-period sum of the mean-zero sequence `Asum χ n − cmean` vanishes:
    `Σ_{n∈Ico k (k+N)} (Asum χ n − cmean) = 0`. -/
theorem sum_B_period_zero (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (k : ℕ) :
    ∑ n ∈ Finset.Ico k (k + N), (Asum χ n - cmean χ) = 0 := by
  have hNne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [Finset.sum_sub_distrib, sum_Asum_Ico_period χ hχ k, Finset.sum_const,
      Nat.card_Ico, Nat.add_sub_cancel_left]
  rw [cmean, nsmul_eq_mul]
  field_simp
  ring

/-- **Bounded partial sums of the mean-zero sequence.** For any window `Ico M K`,
    `‖Σ_{n∈Ico M K} (Asum χ n − cmean)‖ ≤ N·(N + ‖cmean‖)` — uniform in `M, K`. -/
theorem norm_sum_B_le (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (M K : ℕ) :
    ‖∑ n ∈ Finset.Ico M K, (Asum χ n - cmean χ)‖ ≤ (N : ℝ) * ((N : ℝ) + ‖cmean χ‖) := by
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  rcases le_or_gt K M with hKM | hMK
  · -- empty window
    rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty, norm_zero]
    positivity
  · -- Reduce K mod period: write K = M + q·N + r, drop the q full periods (each sums to 0).
    -- The leftover is a sum over < N terms, each of norm ≤ N + ‖cmean‖.
    set d := K - M with hd
    have hKeq : K = M + d := by omega
    -- Peel q := d/N full periods from the bottom; base `M₀` general inside the induction.
    have key : ∀ q : ℕ, ∀ M₀ r : ℕ, r < N →
        ‖∑ n ∈ Finset.Ico M₀ (M₀ + (N * q + r)), (Asum χ n - cmean χ)‖
          ≤ (N : ℝ) * ((N : ℝ) + ‖cmean χ‖) := by
      intro q
      induction q with
      | zero =>
        intro M₀ r hr
        -- Σ over Ico M₀ (M₀+r), r < N: at most r terms each bounded by N + ‖cmean‖
        simp only [Nat.mul_zero, Nat.zero_add]
        calc ‖∑ n ∈ Finset.Ico M₀ (M₀ + r), (Asum χ n - cmean χ)‖
            ≤ ∑ n ∈ Finset.Ico M₀ (M₀ + r), ‖Asum χ n - cmean χ‖ := norm_sum_le _ _
          _ ≤ ∑ n ∈ Finset.Ico M₀ (M₀ + r), ((N : ℝ) + ‖cmean χ‖) := by
              apply Finset.sum_le_sum (fun n _ => ?_)
              exact le_trans (norm_sub_le _ _) (add_le_add (norm_Asum_le χ hχ n) le_rfl)
          _ = (r : ℝ) * ((N : ℝ) + ‖cmean χ‖) := by
              rw [Finset.sum_const, Nat.card_Ico, Nat.add_sub_cancel_left, nsmul_eq_mul]
          _ ≤ (N : ℝ) * ((N : ℝ) + ‖cmean χ‖) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              exact_mod_cast hr.le
      | succ p ih =>
        intro M₀ r hr
        -- Peel one period from the bottom; the first chunk sums to 0.
        have hsplit : ∑ n ∈ Finset.Ico M₀ (M₀ + (N * (p + 1) + r)), (Asum χ n - cmean χ)
            = (∑ n ∈ Finset.Ico M₀ (M₀ + N), (Asum χ n - cmean χ))
              + ∑ n ∈ Finset.Ico (M₀ + N) (M₀ + (N * (p + 1) + r)), (Asum χ n - cmean χ) := by
          rw [← Finset.sum_Ico_consecutive _ (by omega : M₀ ≤ M₀ + N)
                (by nlinarith [Nat.zero_le p, Nat.zero_le r] : M₀ + N ≤ M₀ + (N * (p + 1) + r))]
        rw [hsplit, sum_B_period_zero χ hχ M₀, zero_add]
        rw [show M₀ + (N * (p + 1) + r) = (M₀ + N) + (N * p + r) from by ring]
        exact ih (M₀ + N) r hr
    rw [hKeq]
    obtain ⟨q, r, hr, hdqr⟩ : ∃ q r, r < N ∧ d = N * q + r :=
      ⟨d / N, d % N, Nat.mod_lt d hNpos, by rw [Nat.div_add_mod]⟩
    rw [hdqr]
    exact key q M r hr

/-! ### The step-integral decomposition of the tail

  `Afloor` is constant `= Asum χ n` on `[n, n+1)`, so the truncated tail integral over `Ioc M K`
  decomposes as a finite sum `Σ_{n∈Ico M K} Asum χ n · ω n`, with the unit weight
  `ω n = ∫_{Ioc n (n+1)} t^{-s-1} dt = (n^{-s} − (n+1)^{-s})/s`. -/

/-- The unit weight `ω n = ∫_{n}^{n+1} t^{-s-1} dt`. -/
noncomputable def omegaW (s : ℂ) (n : ℕ) : ℂ :=
  ∫ t in Ioc (n : ℝ) ((n : ℝ) + 1), (t : ℂ) ^ (-s - 1)

omit [NeZero N] in
/-- On `Ioc n (n+1)`, the floor sum is the constant `Asum χ n`, so the integral of
    `Afloor·t^{-s-1}` over that unit cell is `Asum χ n · ω n`. -/
theorem integral_unit_cell (χ : DirichletCharacter ℂ N) (s : ℂ) (n : ℕ) :
    ∫ t in Ioc (n : ℝ) ((n : ℝ) + 1), Afloor χ t * (t : ℂ) ^ (-s - 1)
      = Asum χ n * omegaW s n := by
  rw [omegaW, ← integral_const_mul]
  -- Pass to Ioo (drops the null endpoint), where ⌊t⌋₊ = n holds pointwise.
  rw [MeasureTheory.integral_Ioc_eq_integral_Ioo,
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  rw [Set.mem_Ioo] at ht
  have ht0 : (0 : ℝ) ≤ t := le_trans (Nat.cast_nonneg n) ht.1.le
  have hfloor : ⌊t⌋₊ = n := by
    rw [Nat.floor_eq_iff ht0]
    exact ⟨by exact_mod_cast ht.1.le, by linarith [ht.2]⟩
  show Afloor χ t * (t : ℂ) ^ (-s - 1) = Asum χ n * (t : ℂ) ^ (-s - 1)
  rw [Afloor, hfloor]

/-- The integrand `Afloor·t^{-s-1}` is interval-integrable on each `[k, k+1]` (k ≥ 1). -/
theorem intervalIntegrable_cell (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (s : ℂ) (hσ : 0 < s.re) (k : ℕ) (hk : 1 ≤ k) :
    IntervalIntegrable (fun t : ℝ => Afloor χ t * (t : ℂ) ^ (-s - 1)) volume
      (k : ℝ) ((k : ℝ) + 1) := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
  have hk0 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  exact (integrableOn_integrand χ hχ s hσ hk0).mono_set (fun t ht => ht.1)

/-- **Truncated tail as a finite weighted sum.** For naturals `M ≤ K` with `M ≥ 1`:
    `∫_{Ioc M K} A(⌊t⌋)·t^{-s-1} dt = Σ_{n∈Ico M K} Asum χ n · ω n`. -/
theorem truncated_tail_eq_sum (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (s : ℂ) (hσ : 0 < s.re) (M K : ℕ) (hM : 1 ≤ M) (hMK : M ≤ K) :
    ∫ t in Ioc (M : ℝ) (K : ℝ), Afloor χ t * (t : ℂ) ^ (-s - 1)
      = ∑ n ∈ Finset.Ico M K, Asum χ n * omegaW s n := by
  -- Σ adjacent unit intervals = ∫ M..K, then convert each to set-integral over Ioc.
  have hadj : ∑ k ∈ Finset.Ico M K, ∫ t in (k : ℝ)..((k : ℝ) + 1),
        Afloor χ t * (t : ℂ) ^ (-s - 1)
      = ∫ t in (M : ℝ)..(K : ℝ), Afloor χ t * (t : ℂ) ^ (-s - 1) := by
    have hkey := intervalIntegral.sum_integral_adjacent_intervals_Ico
      (a := fun k : ℕ => (k : ℝ))
      (f := fun t : ℝ => Afloor χ t * (t : ℂ) ^ (-s - 1)) hMK
      (by intro k hk; rw [Set.mem_Ico] at hk
          rw [show ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 from by push_cast; ring]
          exact intervalIntegrable_cell χ hχ s hσ k (by omega))
    rw [← hkey]
    apply Finset.sum_congr rfl (fun k _ => ?_)
    congr 1
    push_cast; ring
  rw [intervalIntegral.integral_of_le (by exact_mod_cast hMK : (M : ℝ) ≤ (K : ℝ))] at hadj
  rw [← hadj]
  apply Finset.sum_congr rfl (fun k hk => ?_)
  rw [Finset.mem_Ico] at hk
  rw [intervalIntegral.integral_of_le (by linarith : (k : ℝ) ≤ (k : ℝ) + 1)]
  exact integral_unit_cell χ s k

/-! ### Weight estimates and the mean-zero Abel bound

  The unit weight `ω n` evaluates to `(n^{-s} − (n+1)^{-s})/s`; `|ω n| ≤ n^{-σ-1}` and the
  per-step variation `|ω n − ω (n+1)| ≤ |s+1|·n^{-σ-2}`.  With the bounded partial sums of `B`
  (`norm_sum_B_le`), summation by parts gives the mean-zero tail bound `O(M^{-σ-1})`,
  uniform in the truncation. -/

omit [NeZero N] in
/-- Norm bound on the unit weight: `‖ω n‖ ≤ n^{-σ-1}` for `n ≥ 1`, `Re s > 0`. -/
theorem norm_omegaW_le (s : ℂ) (hσ : 0 < s.re) {n : ℕ} (hn : 1 ≤ n) :
    ‖omegaW s n‖ ≤ (n : ℝ) ^ (-s.re - 1) := by
  have hn0 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [omegaW]
  have hbound : ∀ᵐ t : ℝ ∂(volume.restrict (Ioc (n : ℝ) ((n : ℝ) + 1))),
      ‖(t : ℂ) ^ (-s - 1)‖ ≤ (n : ℝ) ^ (-s.re - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Set.mem_Ioc] at ht
    have ht_pos : (0 : ℝ) < t := lt_trans (by linarith : (0:ℝ) < (n:ℝ)) ht.1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht_pos]
    have : ((-s - 1).re) = -s.re - 1 := by simp [Complex.sub_re, Complex.neg_re, Complex.one_re]
    rw [this]
    -- t ≥ n ≥ 1, exponent -σ-1 < 0, so t^{-σ-1} ≤ n^{-σ-1}
    rw [Real.rpow_le_rpow_iff_of_neg ht_pos (lt_of_lt_of_le one_pos hn0) (by linarith)]
    exact ht.1.le
  calc ‖∫ t in Ioc (n : ℝ) ((n : ℝ) + 1), (t : ℂ) ^ (-s - 1)‖
      ≤ ∫ t in Ioc (n : ℝ) ((n : ℝ) + 1), (n : ℝ) ^ (-s.re - 1) := by
        apply norm_integral_le_of_norm_le _ hbound
        exact continuousOn_const.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
    _ = (n : ℝ) ^ (-s.re - 1) := by
        rw [setIntegral_const, MeasureTheory.measureReal_def, Real.volume_Ioc,
            show (n : ℝ) + 1 - n = 1 from by ring]
        simp

omit [NeZero N] in
/-- `HasDerivAt (t ↦ t^r) (r·t^{r-1}) t` for `t > 0` (the real-to-complex power). -/
theorem hasDerivAt_cpow_exp (r : ℂ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ r) (r * (t : ℂ) ^ (r - 1)) t := by
  by_cases hr : r = 0
  · subst hr
    simp only [Complex.cpow_zero, zero_mul]
    exact hasDerivAt_const t (1 : ℂ)
  · exact hasDerivAt_ofReal_cpow_const (ne_of_gt ht) hr

omit [NeZero N] in
/-- Pointwise: `‖t^{-s-1} − (t+1)^{-s-1}‖ ≤ ‖s+1‖·t^{-σ-2}` for `t ≥ 1`. -/
theorem norm_g_diff_le (s : ℂ) (hσ : 0 < s.re) {t : ℝ} (ht : 1 ≤ t) :
    ‖(t : ℂ) ^ (-s - 1) - ((t : ℝ) + 1 : ℝ) ^ (-s - 1)‖ ≤ ‖s + 1‖ * t ^ (-s.re - 2) := by
  have ht0 : (0 : ℝ) < t := by linarith
  -- (t+1)^{-s-1} − t^{-s-1} = ∫_t^{t+1} g'(u) du, g'(u) = (-s-1)u^{-s-2}
  have hderiv : ∀ u ∈ Set.uIcc t (t + 1), HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s - 1))
      ((-s - 1) * (u : ℂ) ^ (-s - 1 - 1)) u := by
    intro u hu
    rw [Set.uIcc_of_le (by linarith)] at hu
    exact hasDerivAt_cpow_exp (-s - 1) (lt_of_lt_of_le ht0 hu.1)
  have hcont : IntervalIntegrable (fun u : ℝ => (-s - 1) * (u : ℂ) ^ (-s - 1 - 1))
      volume t (t + 1) := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.mul
    apply ContinuousOn.cpow continuous_ofReal.continuousOn continuousOn_const
    intro u hu
    rw [Set.uIcc_of_le (by linarith)] at hu
    exact Complex.ofReal_mem_slitPlane.mpr (lt_of_lt_of_le ht0 hu.1)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont
  -- hFTC : ∫_t^{t+1} g'(u) du = (t+1)^{-s-1} − t^{-s-1}
  rw [show (t : ℂ) ^ (-s - 1) - ((t : ℝ) + 1 : ℝ) ^ (-s - 1)
        = -(((↑(t + 1) : ℂ)) ^ (-s - 1) - (t : ℂ) ^ (-s - 1)) from by push_cast; ring,
      ← hFTC, norm_neg]
  -- Bound the integral by ‖s+1‖·∫_t^{t+1} u^{-σ-2} ≤ ‖s+1‖·t^{-σ-2}
  calc ‖∫ u in t..(t + 1), (-s - 1) * (u : ℂ) ^ (-s - 1 - 1)‖
      ≤ ‖s + 1‖ * t ^ (-s.re - 2) * |(t + 1) - t| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro u hu
        rw [Set.uIoc_of_le (by linarith)] at hu
        simp only [Set.mem_Ioc] at hu
        have hu0 : (0 : ℝ) < u := lt_of_lt_of_le ht0 hu.1.le
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0]
        rw [show ((-s - 1 - 1).re) = -s.re - 2 from by
              simp [Complex.sub_re, Complex.neg_re, Complex.one_re]; ring]
        rw [show -(s : ℂ) - 1 = -(s + 1) from by ring, norm_neg]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        rw [Real.rpow_le_rpow_iff_of_neg hu0 ht0 (by linarith)]
        exact hu.1.le
    _ = ‖s + 1‖ * t ^ (-s.re - 2) := by rw [show (t + 1) - t = 1 from by ring]; simp

omit [NeZero N] in
/-- Closed form of the unit weight: `ω n = (n^{-s} − (n+1)^{-s})/s` for `n ≥ 1`, `s ≠ 0`. -/
theorem omegaW_eq (s : ℂ) (hs : s ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    omegaW s n = ((n : ℂ) ^ (-s) - ((n : ℝ) + 1 : ℝ) ^ (-s)) / s := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [omegaW]
  -- ∫_n^{n+1} t^{-s-1} dt = [t^{-s}/(-s)]; use integral_cpow.
  rw [← intervalIntegral.integral_of_le (by linarith : (n : ℝ) ≤ (n : ℝ) + 1)]
  rw [show (fun t : ℝ => (t : ℂ) ^ (-s - 1)) = (fun t : ℝ => (t : ℂ) ^ (-s - 1)) from rfl]
  have hr : (-s - 1) ≠ -1 := by
    intro h; apply hs; have : -s - 1 + 1 = -1 + 1 := by rw [h]
    simpa using this
  have hnotmem : (0 : ℝ) ∉ Set.uIcc (n : ℝ) ((n : ℝ) + 1) := by
    rw [Set.uIcc_of_le (by linarith : (n : ℝ) ≤ (n : ℝ) + 1)]
    simp only [Set.mem_Icc, not_and_or, not_le]; left; exact hn0
  rw [integral_cpow (Or.inr ⟨hr, hnotmem⟩)]
  rw [show -s - 1 + 1 = -s from by ring]
  push_cast
  field_simp
  ring

omit [NeZero N] in
/-- **Per-step weight variation:** `‖ω(i+1) − ω i‖ ≤ ‖s+1‖·i^{-σ-2}` for `i ≥ 1`, `Re s > 0`.
    This is the cancellation that gives the extra power of `M` in the mean-zero tail. -/
theorem norm_omegaW_diff_le (s : ℂ) (hσ : 0 < s.re) {i : ℕ} (hi : 1 ≤ i) :
    ‖omegaW s (i + 1) - omegaW s i‖ ≤ ‖s + 1‖ * (i : ℝ) ^ (-s.re - 2) := by
  have hi0 : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  -- ω(i+1) = ∫_i^{i+1} g(x+1), ω i = ∫_i^{i+1} g(x); difference is ∫_i^{i+1}(g(x+1)-g(x)).
  have hω1 : omegaW s (i + 1)
      = ∫ x in (i : ℝ)..((i : ℝ) + 1), ((↑(x + 1) : ℂ)) ^ (-s - 1) := by
    rw [omegaW]
    rw [intervalIntegral.integral_comp_add_right (fun x : ℝ => (↑x : ℂ) ^ (-s - 1)) 1]
    rw [← intervalIntegral.integral_of_le (by push_cast; linarith :
          ((↑(i + 1) : ℝ)) ≤ ((↑(i + 1) : ℝ)) + 1)]
    rw [show (i : ℝ) + 1 = ((i + 1 : ℕ) : ℝ) from by push_cast; ring,
        show ((i + 1 : ℕ) : ℝ) + 1 = ((i + 1 : ℕ) : ℝ) + 1 from rfl]
  have hω0 : omegaW s i = ∫ x in (i : ℝ)..((i : ℝ) + 1), (↑x : ℂ) ^ (-s - 1) := by
    rw [omegaW, ← intervalIntegral.integral_of_le (by linarith : (i : ℝ) ≤ (i : ℝ) + 1)]
  rw [hω1, hω0, ← intervalIntegral.integral_sub]
  · calc ‖∫ x in (i : ℝ)..((i : ℝ) + 1),
          ((↑(x + 1) : ℂ) ^ (-s - 1) - (↑x : ℂ) ^ (-s - 1))‖
        ≤ ‖s + 1‖ * (i : ℝ) ^ (-s.re - 2) * |((i : ℝ) + 1) - (i : ℝ)| := by
          apply intervalIntegral.norm_integral_le_of_norm_le_const
          intro x hx
          rw [Set.uIoc_of_le (by linarith)] at hx
          simp only [Set.mem_Ioc] at hx
          have hx1 : (1 : ℝ) ≤ x := le_trans hi0 hx.1.le
          rw [norm_sub_rev]
          have hg := norm_g_diff_le s hσ hx1
          rw [show ((↑(x + 1) : ℂ)) = (((x : ℝ) + 1 : ℝ) : ℂ) from by norm_cast]
          refine le_trans hg ?_
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          rw [Real.rpow_le_rpow_iff_of_neg (by linarith) (by linarith) (by linarith)]
          exact hx.1.le
      _ = ‖s + 1‖ * (i : ℝ) ^ (-s.re - 2) := by rw [show ((i : ℝ) + 1) - (i : ℝ) = 1 from by ring]; simp
  · -- IntervalIntegrable of (x+1)^{-s-1}
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.cpow (by
      exact (continuous_ofReal.comp (continuous_id.add continuous_const)).continuousOn) continuousOn_const
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    exact Complex.ofReal_mem_slitPlane.mpr (by linarith [hx.1, hi0])
  · -- IntervalIntegrable of x^{-s-1}
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.cpow continuous_ofReal.continuousOn continuousOn_const
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    exact Complex.ofReal_mem_slitPlane.mpr (lt_of_lt_of_le (by linarith) hx.1)

omit [NeZero N] in
/-- Sum-of-powers tail bound: `Σ_{i∈Ico M K} i^{-σ-2} ≤ (1 + 1/(σ+1))·M^{-σ-1}` for `M ≥ 1`. -/
theorem sum_rpow_Ico_le (s : ℂ) (hσ : 0 < s.re) (M K : ℕ) (hM : 1 ≤ M) :
    ∑ i ∈ Finset.Ico M K, (i : ℝ) ^ (-s.re - 2)
      ≤ (1 + 1 / (s.re + 1)) * (M : ℝ) ^ (-s.re - 1) := by
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hMpos : (0 : ℝ) < (M : ℝ) := by linarith
  rcases le_or_gt K M with hKM | hMK
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
    positivity
  · -- Peel the first term f(M); bound the rest Σ_{Ico (M+1) K} f(i) ≤ ∫_M^K f.
    have hpeel : ∑ i ∈ Finset.Ico M K, (i : ℝ) ^ (-s.re - 2)
        = (M : ℝ) ^ (-s.re - 2) + ∑ i ∈ Finset.Ico (M + 1) K, (i : ℝ) ^ (-s.re - 2) := by
      rw [← Finset.sum_Ico_consecutive _ (by omega : M ≤ M + 1) (by omega : M + 1 ≤ K),
          Nat.Ico_succ_singleton, Finset.sum_singleton]
    -- AntitoneOn f on [M, K]; sum_le_integral_Ico gives Σ_{Ico M (K-1)} f(i+1) ≤ ∫.
    have hanti : AntitoneOn (fun x : ℝ => x ^ (-s.re - 2)) (Set.Icc (M : ℝ) (K : ℝ)) := by
      intro a ha b hb hab
      simp only
      have ha0 : (0 : ℝ) < a := lt_of_lt_of_le hMpos ha.1
      have hb0 : (0 : ℝ) < b := lt_of_lt_of_le ha0 hab
      rw [Real.rpow_le_rpow_iff_of_neg hb0 ha0 (by linarith)]
      exact hab
    have hMK' : M ≤ K := le_of_lt hMK
    have hsumint : ∑ i ∈ Finset.Ico M K, ((i : ℝ) + 1) ^ (-s.re - 2)
        ≤ ∫ x in (M : ℝ)..(K : ℝ), x ^ (-s.re - 2) := by
      have h := AntitoneOn.sum_le_integral_Ico hMK' hanti
      simp only [Nat.cast_add, Nat.cast_one] at h
      exact h
    -- hsumint : Σ_{i∈Ico M K} (↑(i+1))^p ≤ ∫_M^K x^p
    -- Reindex Σ_{Ico (M+1) K} i^p = Σ_{j∈Ico M (K-1)} (j+1)^p ≤ Σ_{j∈Ico M K} (j+1)^p.
    have hreindex : ∑ i ∈ Finset.Ico (M + 1) K, (i : ℝ) ^ (-s.re - 2)
        ≤ ∑ i ∈ Finset.Ico M K, ((i : ℝ) + 1) ^ (-s.re - 2) := by
      rw [show ∑ i ∈ Finset.Ico (M + 1) K, (i : ℝ) ^ (-s.re - 2)
            = ∑ j ∈ Finset.Ico M (K - 1), ((j : ℝ) + 1) ^ (-s.re - 2) from by
        rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
        apply Finset.sum_congr (by congr 1; omega) (fun j _ => by push_cast; ring_nf)]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj; rw [Finset.mem_Ico] at hj ⊢; omega
      · intro j _ _; positivity
    have hintbound : (∫ x in (M : ℝ)..(K : ℝ), x ^ (-s.re - 2))
        ≤ (M : ℝ) ^ (-s.re - 1) / (s.re + 1) := by
      rw [integral_rpow (Or.inr ⟨by linarith, by
        rw [Set.uIcc_of_le (by exact_mod_cast hMK')]
        simp only [Set.mem_Icc, not_and_or, not_le]; left; linarith⟩)]
      rw [show -s.re - 2 + 1 = -s.re - 1 from by ring]
      -- (K^{-σ-1} - M^{-σ-1})/(-σ-1) ≤ M^{-σ-1}/(σ+1)
      have hK0 : (0 : ℝ) ≤ (K : ℝ) ^ (-s.re - 1) := Real.rpow_nonneg (by positivity) _
      have hM0 : (0 : ℝ) ≤ (M : ℝ) ^ (-s.re - 1) := Real.rpow_nonneg hMpos.le _
      have hp : (-s.re - 1) < 0 := by linarith
      -- LHS = (K^p - M^p)/p = (M^p - K^p)/(σ+1) ≤ M^p/(σ+1)
      rw [show ((K : ℝ) ^ (-s.re - 1) - (M : ℝ) ^ (-s.re - 1)) / (-s.re - 1)
            = ((M : ℝ) ^ (-s.re - 1) - (K : ℝ) ^ (-s.re - 1)) / (s.re + 1) from by
        rw [div_eq_div_iff (by linarith) (by linarith)]; ring]
      rw [div_le_div_iff_of_pos_right (by linarith : (0:ℝ) < s.re + 1)]
      linarith
    -- Assemble
    rw [hpeel]
    have key : ∑ i ∈ Finset.Ico (M + 1) K, (i : ℝ) ^ (-s.re - 2)
        ≤ (M : ℝ) ^ (-s.re - 1) / (s.re + 1) :=
      le_trans hreindex (le_trans hsumint hintbound)
    have hMle : (M : ℝ) ^ (-s.re - 2) ≤ (M : ℝ) ^ (-s.re - 1) := by
      apply Real.rpow_le_rpow_of_exponent_le hMR (by linarith)
    calc (M : ℝ) ^ (-s.re - 2) + ∑ i ∈ Finset.Ico (M + 1) K, (i : ℝ) ^ (-s.re - 2)
        ≤ (M : ℝ) ^ (-s.re - 1) + (M : ℝ) ^ (-s.re - 1) / (s.re + 1) :=
          add_le_add hMle key
      _ = (1 + 1 / (s.re + 1)) * (M : ℝ) ^ (-s.re - 1) := by ring

/-- The mean-zero partial-sum bound constant `C' = N·(N + ‖cmean‖)`. -/
noncomputable def Cprime (χ : DirichletCharacter ℂ N) : ℝ := (N : ℝ) * ((N : ℝ) + ‖cmean χ‖)

/-- **The mean-zero Abel bound (the crux).** Summation by parts on the mean-zero sequence
    `B(n) = Asum χ n − cmean`, weighted by the unit weights `ω_n`, gives a bound that gains one
    power of `M` over the trivial estimate:
    `‖Σ_{n∈Ico M K} B(n)·ω_n‖ ≤ C'·(2 + ‖s+1‖·(1+1/(σ+1)))·M^{-σ-1}` for `M ≥ 1`. -/
theorem norm_meanzero_sum_le (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (s : ℂ) (hσ : 0 < s.re) (M K : ℕ) (hM : 1 ≤ M) :
    ‖∑ n ∈ Finset.Ico M K, (Asum χ n - cmean χ) * omegaW s n‖
      ≤ Cprime χ * (2 + ‖s + 1‖ * (1 + 1 / (s.re + 1))) * (M : ℝ) ^ (-s.re - 1) := by
  set Bseq : ℕ → ℂ := fun n => Asum χ n - cmean χ with hB
  set C' := Cprime χ with hC'
  have hC'0 : 0 ≤ C' := by rw [hC', Cprime]; positivity
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hMpos : (0 : ℝ) < (M : ℝ) := by linarith
  have hMpow : (0 : ℝ) ≤ (M : ℝ) ^ (-s.re - 1) := Real.rpow_nonneg hMpos.le _
  -- Partial sums of B from 0 are bounded by C'.
  have hpart : ∀ j : ℕ, ‖∑ i ∈ Finset.range j, Bseq i‖ ≤ C' := by
    intro j
    rw [hB, hC', Finset.range_eq_Ico]
    exact norm_sum_B_le χ hχ 0 j
  rcases le_or_gt K M with hKM | hMK
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty, norm_zero]
    have : 0 ≤ Cprime χ * (2 + ‖s + 1‖ * (1 + 1 / (s.re + 1))) := by
      rw [Cprime]; positivity
    positivity
  · -- Rewrite the summand as ω(i) • B(i) and apply Finset.sum_Ico_by_parts.
    have hrw : ∑ n ∈ Finset.Ico M K, (Asum χ n - cmean χ) * omegaW s n
        = ∑ n ∈ Finset.Ico M K, omegaW s n • Bseq n := by
      apply Finset.sum_congr rfl (fun n _ => ?_); rw [hB, smul_eq_mul]; ring
    rw [hrw, Finset.sum_Ico_by_parts (omegaW s) Bseq hMK]
    -- = ω(K-1)•S_K - ω(M)•S_M - Σ_{Ico M (K-1)} (ω(i+1)-ω(i))•S_{i+1}
    -- where S_j = Σ_{range j} Bseq.   Bound each piece.
    have hMK1 : M ≤ K - 1 := by omega
    have hK1 : 1 ≤ K - 1 := by omega
    have hpowle : ∀ j : ℕ, M ≤ j → (j : ℝ) ^ (-s.re - 1) ≤ (M : ℝ) ^ (-s.re - 1) := by
      intro j hj
      have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (by omega : 1 ≤ j)
      have hj0 : (0 : ℝ) < (j : ℝ) := by linarith
      rw [Real.rpow_le_rpow_iff_of_neg hj0 hMpos (by linarith)]
      exact_mod_cast hj
    -- Piece 1: ‖ω(K-1)•S_K‖ ≤ (K-1)^{-σ-1}·C' ≤ M^{-σ-1}·C'
    have hbound1 : ‖omegaW s (K - 1) • ∑ i ∈ Finset.range K, Bseq i‖
        ≤ (M : ℝ) ^ (-s.re - 1) * C' := by
      rw [norm_smul]
      refine mul_le_mul (le_trans (norm_omegaW_le s hσ hK1) (hpowle (K - 1) hMK1))
        (hpart K) (norm_nonneg _) hMpow
    -- Piece 2: ‖ω(M)•S_M‖ ≤ M^{-σ-1}·C'
    have hbound2 : ‖omegaW s M • ∑ i ∈ Finset.range M, Bseq i‖
        ≤ (M : ℝ) ^ (-s.re - 1) * C' := by
      rw [norm_smul]
      refine mul_le_mul (norm_omegaW_le s hσ hM) (hpart M) (norm_nonneg _) hMpow
    -- Piece 3: Σ ‖(ω(i+1)-ω(i))•S_{i+1}‖ ≤ C'·‖s+1‖·(1+1/(σ+1))·M^{-σ-1}
    have hbound3 : ‖∑ i ∈ Finset.Ico M (K - 1), (omegaW s (i + 1) - omegaW s i)
          • ∑ j ∈ Finset.range (i + 1), Bseq j‖
        ≤ C' * (‖s + 1‖ * (1 + 1 / (s.re + 1))) * (M : ℝ) ^ (-s.re - 1) := by
      calc ‖∑ i ∈ Finset.Ico M (K - 1), (omegaW s (i + 1) - omegaW s i)
              • ∑ j ∈ Finset.range (i + 1), Bseq j‖
          ≤ ∑ i ∈ Finset.Ico M (K - 1), ‖(omegaW s (i + 1) - omegaW s i)
              • ∑ j ∈ Finset.range (i + 1), Bseq j‖ := norm_sum_le _ _
        _ ≤ ∑ i ∈ Finset.Ico M (K - 1), (‖s + 1‖ * (i : ℝ) ^ (-s.re - 2) * C') := by
            apply Finset.sum_le_sum (fun i hi => ?_)
            rw [Finset.mem_Ico] at hi
            rw [norm_smul]
            refine mul_le_mul (norm_omegaW_diff_le s hσ (by omega)) (hpart (i + 1))
              (norm_nonneg _) (by positivity)
        _ = C' * ‖s + 1‖ * ∑ i ∈ Finset.Ico M (K - 1), (i : ℝ) ^ (-s.re - 2) := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl (fun i _ => by ring)
        _ ≤ C' * ‖s + 1‖ * ((1 + 1 / (s.re + 1)) * (M : ℝ) ^ (-s.re - 1)) := by
            apply mul_le_mul_of_nonneg_left (sum_rpow_Ico_le s hσ M (K - 1) hM)
            positivity
        _ = C' * (‖s + 1‖ * (1 + 1 / (s.re + 1))) * (M : ℝ) ^ (-s.re - 1) := by ring
    -- Assemble via triangle inequality
    calc ‖omegaW s (K - 1) • ∑ i ∈ Finset.range K, Bseq i
            - omegaW s M • ∑ i ∈ Finset.range M, Bseq i
            - ∑ i ∈ Finset.Ico M (K - 1), (omegaW s (i + 1) - omegaW s i)
                • ∑ j ∈ Finset.range (i + 1), Bseq j‖
        ≤ ‖omegaW s (K - 1) • ∑ i ∈ Finset.range K, Bseq i‖
          + ‖omegaW s M • ∑ i ∈ Finset.range M, Bseq i‖
          + ‖∑ i ∈ Finset.Ico M (K - 1), (omegaW s (i + 1) - omegaW s i)
                • ∑ j ∈ Finset.range (i + 1), Bseq j‖ := by
          refine le_trans (norm_sub_le _ _) ?_
          exact add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ (M : ℝ) ^ (-s.re - 1) * C' + (M : ℝ) ^ (-s.re - 1) * C'
          + C' * (‖s + 1‖ * (1 + 1 / (s.re + 1))) * (M : ℝ) ^ (-s.re - 1) :=
          add_le_add (add_le_add hbound1 hbound2) hbound3
      _ = C' * (2 + ‖s + 1‖ * (1 + 1 / (s.re + 1))) * (M : ℝ) ^ (-s.re - 1) := by ring

/-- Complex tail integral closed form: `∫_{Ioi M} t^{-s-1} dt = M^{-s}/s` for `Re s > 0`, `M ≥ 1`. -/
theorem integral_cpow_tail (s : ℂ) (hσ : 0 < s.re) (hs : s ≠ 0) {M : ℕ} (hM : 1 ≤ M) :
    ∫ t in Ioi (M : ℝ), (t : ℂ) ^ (-s - 1) = (M : ℂ) ^ (-s) / s := by
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hre : (-s - 1).re < -1 := by simp [Complex.sub_re, Complex.neg_re, Complex.one_re]; linarith
  rw [integral_Ioi_cpow_of_lt hre hMpos]
  rw [show -s - 1 + 1 = -s from by ring]
  rw [show (((M : ℝ) : ℂ)) = (M : ℂ) from by norm_cast]
  field_simp

/-- The mean-zero tail `Btail χ s M = tail χ s M − cmean·M^{-s}/s`, obtained by subtracting the
    constant-channel contribution from the full tail. -/
noncomputable def Btail (χ : DirichletCharacter ℂ N) (s : ℂ) (M : ℕ) : ℂ :=
  tail χ s M - cmean χ * ((M : ℂ) ^ (-s) / s)

/-- **Truncated mean-zero sums converge to `Btail`.** -/
theorem meanzero_sum_tendsto (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (s : ℂ) (hσ : 0 < s.re) (M : ℕ) (hM : 1 ≤ M) :
    Tendsto (fun K : ℕ => ∑ n ∈ Finset.Ico M K, (Asum χ n - cmean χ) * omegaW s n)
      atTop (𝓝 (Btail χ s M)) := by
  have hs : s ≠ 0 := by intro h; rw [h] at hσ; simp at hσ
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  -- Σ_{Ico M K}(A n − c)·ω n = (∫_{Ioc M K} Afloor·t^{-s-1}) − c·Σ_{Ico M K} ω n.
  -- ∫_{Ioc M K} → tail χ s M;  c·Σ ω n = c·(M^{-s} − K^{-s})/s → c·M^{-s}/s.
  have hsplit : ∀ K : ℕ, M ≤ K →
      ∑ n ∈ Finset.Ico M K, (Asum χ n - cmean χ) * omegaW s n
        = (∫ t in Ioc (M : ℝ) (K : ℝ), Afloor χ t * (t : ℂ) ^ (-s - 1))
          - cmean χ * ∑ n ∈ Finset.Ico M K, omegaW s n := by
    intro K hK
    rw [truncated_tail_eq_sum χ hχ s hσ M K hM hK, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl (fun n _ => by ring)
  -- Limit of the integral part: ∫_{Ioc M K} → tail χ s M.
  have hint_tend : Tendsto
      (fun K : ℕ => ∫ t in Ioc (M : ℝ) (K : ℝ), Afloor χ t * (t : ℂ) ^ (-s - 1))
      atTop (𝓝 (tail χ s M)) := by
    have hintM : IntegrableOn (fun t : ℝ => Afloor χ t * (t : ℂ) ^ (-s - 1)) (Ioi (M : ℝ)) :=
      integrableOn_integrand χ hχ s hσ hMR
    have htend := MeasureTheory.intervalIntegral_tendsto_integral_Ioi (M : ℝ) hintM
      tendsto_natCast_atTop_atTop
    refine (htend.congr' ?_)
    filter_upwards [Filter.eventually_ge_atTop M] with K hK
    rw [intervalIntegral.integral_of_le (by exact_mod_cast hK : (M:ℝ) ≤ (K:ℝ))]
  -- Limit of Σ ω: telescoping Σ_{Ico M K} ω n = (M^{-s} − K^{-s})/s → M^{-s}/s.
  have hsum_omega_tend : Tendsto (fun K : ℕ => ∑ n ∈ Finset.Ico M K, omegaW s n)
      atTop (𝓝 ((M : ℂ) ^ (-s) / s)) := by
    -- Σ_{Ico M K} ω n = ∫_{Ioc M K} t^{-s-1}  → ∫_{Ioi M} = M^{-s}/s.
    have hcellII : ∀ k : ℕ, 1 ≤ k →
        IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (-s - 1)) volume (k : ℝ) ((k : ℝ) + 1) := by
      intro k hk
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.cpow continuous_ofReal.continuousOn continuousOn_const
      intro t ht
      rw [Set.uIcc_of_le (by linarith)] at ht
      exact Complex.ofReal_mem_slitPlane.mpr (lt_of_lt_of_le (by exact_mod_cast hk) ht.1)
    have hsumeq : ∀ K : ℕ, M ≤ K →
        ∑ n ∈ Finset.Ico M K, omegaW s n = ∫ t in Ioc (M : ℝ) (K : ℝ), (t : ℂ) ^ (-s - 1) := by
      intro K hK
      have hadj := intervalIntegral.sum_integral_adjacent_intervals_Ico
        (a := fun k : ℕ => (k : ℝ)) (f := fun t : ℝ => (t : ℂ) ^ (-s - 1)) hK
        (by intro k hk; rw [Set.mem_Ico] at hk
            rw [show ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 from by push_cast; ring]
            exact hcellII k (by omega))
      rw [intervalIntegral.integral_of_le (by exact_mod_cast hK : (M:ℝ) ≤ (K:ℝ))] at hadj
      rw [← hadj]
      apply Finset.sum_congr rfl (fun k hk => ?_)
      rw [Finset.mem_Ico] at hk
      rw [omegaW, show ((k + 1 : ℕ) : ℝ) = (k:ℝ) + 1 from by push_cast; ring,
          ← intervalIntegral.integral_of_le (by linarith : (k:ℝ) ≤ (k:ℝ)+1)]
    have hintIoiM : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s - 1)) (Ioi (M : ℝ)) := by
      apply integrableOn_Ioi_cpow_of_lt _ (by exact_mod_cast (by omega : 0 < M) : (0:ℝ) < (M:ℝ))
      simp [Complex.sub_re, Complex.neg_re, Complex.one_re]; linarith
    have htend := MeasureTheory.intervalIntegral_tendsto_integral_Ioi (M : ℝ) hintIoiM
      tendsto_natCast_atTop_atTop
    rw [integral_cpow_tail s hσ (by intro h; rw [h] at hσ; simp at hσ) hM] at htend
    refine htend.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop M] with K hK
    rw [intervalIntegral.integral_of_le (by exact_mod_cast hK : (M:ℝ) ≤ (K:ℝ)),
        ← hsumeq K hK]
  -- Combine
  have := (hint_tend.sub (hsum_omega_tend.const_mul (cmean χ)))
  rw [Btail]
  refine this.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop M] with K hK
  rw [hsplit K hK]

/-- **The mean-zero tail bound (gains one power of `M`).**
    `‖Btail χ s M‖ ≤ C·M^{-σ-1}` for `Re s > 0`, `M ≥ 1`, with `C` independent of `M`. -/
theorem norm_Btail_le (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (s : ℂ) (hσ : 0 < s.re) (M : ℕ) (hM : 1 ≤ M) :
    ‖Btail χ s M‖ ≤ Cprime χ * (2 + ‖s + 1‖ * (1 + 1 / (s.re + 1))) * (M : ℝ) ^ (-s.re - 1) := by
  -- The truncated sums converge to Btail and each is bounded uniformly.
  have htend := (meanzero_sum_tendsto χ hχ s hσ M hM).norm
  have hbound : ∀ K : ℕ, ‖∑ n ∈ Finset.Ico M K, (Asum χ n - cmean χ) * omegaW s n‖
      ≤ Cprime χ * (2 + ‖s + 1‖ * (1 + 1 / (s.re + 1))) * (M : ℝ) ^ (-s.re - 1) :=
    fun K => norm_meanzero_sum_le χ hχ s hσ M K hM
  exact le_of_tendsto htend (Eventually.of_forall hbound)

/-- **The exact closure-ledger identity (mean-zero refinement).** For `Re s > 0`, `M ≥ 1`:
    `L_M(s) − L(s) = (A(M) − L(0,χ))·M^{-s} + R'_M(s)`, where the refined leading constant is the
    fibre imbalance against the channel constant `L(0,χ) = cmean`, FREE of the height `Im s`, and
    `R'_M(s) = −s·Btail χ s M` is one power of `M` smaller. -/
theorem closure_ledger_exact_identity (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (s : ℂ) (hσ : 0 < s.re) (M : ℕ) (hM : 1 ≤ M) :
    LM χ s M - DirichletCharacter.LFunction χ s
      = (Asum χ M - cmean χ) * (M : ℂ) ^ (-s) + (-s) * Btail χ s M := by
  have hs : s ≠ 0 := by intro h; rw [h] at hσ; simp at hσ
  rw [closure_ledger_identity χ hχ s hσ M hM, Rrem, Btail]
  -- Rrem = -s·tail;  Btail = tail - cmean·M^{-s}/s.  So -s·tail = -s·Btail - cmean·M^{-s}.
  field_simp
  ring

/-! ### Identifying the channel constant: `cmean = LFunction χ 0`

  From `cChar_eq_LFunction` and `1^{-s} = 1`: `LFunction χ s = cmean + s·Btail χ s 1` for
  `Re s > 0`.  As `s = ε ↓ 0` (real), the LHS → `LFunction χ 0` (entire ⇒ continuous) and the
  RHS → `cmean + 0` (because `Btail χ ε 1` stays bounded by the mean-zero cancellation). So
  `cmean = LFunction χ 0` — no Bernoulli/Hurwitz values needed. -/

/-- `LFunction χ s = cmean + s·Btail χ s 1` for `Re s > 0`. -/
theorem LFunction_eq_cmean_add (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (s : ℂ) (hσ : 0 < s.re) :
    DirichletCharacter.LFunction χ s = cmean χ + s * Btail χ s 1 := by
  have hs : s ≠ 0 := by intro h; rw [h] at hσ; simp at hσ
  rw [← cChar_eq_LFunction χ hχ s hσ, cChar, Btail]
  -- s·tail = cmean + s·(tail - cmean·(1^{-s}/s)); 1^{-s} = 1.
  rw [show ((1 : ℕ) : ℂ) ^ (-s) = 1 from by norm_num,
      show ((1 : ℕ) : ℝ) = (1 : ℝ) from by norm_num]
  field_simp
  ring

/-- The remainder `Btail χ ε 1` is bounded as `ε ↓ 0` along the positive reals.
    (Uniform mean-zero bound: `‖Btail χ ε 1‖ ≤ C` with `C` independent of small `ε > 0`.) -/
theorem Btail_one_bddAbove (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ‖Btail χ (ε : ℂ) 1‖ ≤ C := by
  -- From norm_Btail_le at M = 1: ‖Btail χ s 1‖ ≤ Cprime·(2 + ‖s+1‖(1+1/(σ+1)))·1.
  refine ⟨Cprime χ * (2 + (2 : ℝ) * (1 + 1 / 1)), fun ε hε hε1 => ?_⟩
  have hσ : 0 < (ε : ℂ).re := by simpa using hε
  have hb := norm_Btail_le χ hχ (ε : ℂ) hσ 1 le_rfl
  rw [show ((1 : ℕ) : ℝ) ^ (-(ε : ℂ).re - 1) = 1 from by norm_num, mul_one] at hb
  refine le_trans hb ?_
  -- Cprime·(2 + ‖ε+1‖(1+1/(ε+1))) ≤ Cprime·(2 + 2·(1+1/1)), since ε ≤ 1 ⇒ ‖ε+1‖ ≤ 2, 1/(ε+1) ≤ 1.
  apply mul_le_mul_of_nonneg_left _ (by rw [Cprime]; positivity)
  have hεre : (ε : ℂ).re = ε := by simp
  rw [hεre]
  have h1 : ‖(ε : ℂ) + 1‖ ≤ 2 := by
    rw [show (ε : ℂ) + 1 = ((ε + 1 : ℝ) : ℂ) from by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  have h2 : 1 / (ε + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have h3 : (0:ℝ) ≤ 1 + 1 / (ε + 1) := by positivity
  nlinarith [norm_nonneg ((ε : ℂ) + 1), h1, h2, h3]

/-- **The channel constant equals the L-value at 0: `cmean χ = LFunction χ 0`.**
    Proved by taking `s = 1/(n+1) ↓ 0` in `LFunction χ s = cmean + s·Btail χ s 1`: the LHS → `L(0,χ)`
    by continuity, and `s·Btail → 0` because `Btail` stays bounded (mean-zero cancellation). -/
theorem cmean_eq_LFunction_zero (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) :
    cmean χ = DirichletCharacter.LFunction χ 0 := by
  obtain ⟨C, hC⟩ := Btail_one_bddAbove χ hχ
  -- The sequence ε_n = 1/(n+1) → 0 in ℝ, with 0 < ε_n ≤ 1.
  set ε : ℕ → ℝ := fun n => 1 / (n + 1) with hε
  have hεpos : ∀ n, 0 < ε n := fun n => by rw [hε]; positivity
  have hεle : ∀ n, ε n ≤ 1 := fun n => by
    rw [hε]; rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hεt0 : Tendsto ε atTop (𝓝 0) := by
    rw [hε]; exact tendsto_one_div_add_atTop_nhds_zero_nat
  -- s_n := (ε n : ℂ) → 0 in ℂ
  have hst0 : Tendsto (fun n => (ε n : ℂ)) atTop (𝓝 (0 : ℂ)) := by
    rw [show (0 : ℂ) = ((0 : ℝ) : ℂ) from by norm_num]
    exact (Complex.continuous_ofReal.tendsto 0).comp hεt0
  -- LHS: LFunction χ (ε n) → LFunction χ 0  (continuity of the entire LFunction)
  have hLHS : Tendsto (fun n => DirichletCharacter.LFunction χ (ε n : ℂ)) atTop
      (𝓝 (DirichletCharacter.LFunction χ 0)) :=
    ((LFunction_differentiableAt χ hχ 0).continuousAt.tendsto).comp hst0
  -- RHS: cmean + (ε n)·Btail χ (ε n) 1 → cmean + 0
  have hsBtail : Tendsto (fun n => (ε n : ℂ) * Btail χ (ε n : ℂ) 1) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hbnd : ∀ n, ‖(ε n : ℂ) * Btail χ (ε n : ℂ) 1‖ ≤ ε n * C := by
      intro n
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hεpos n)]
      exact mul_le_mul_of_nonneg_left (hC (ε n) (hεpos n) (hεle n)) (hεpos n).le
    have hεC : Tendsto (fun n => ε n * C) atTop (𝓝 0) := by
      rw [show (0 : ℝ) = 0 * C from by ring]; exact hεt0.mul_const C
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hεC
      (Eventually.of_forall (fun n => norm_nonneg _)) (Eventually.of_forall hbnd)
  have hRHS : Tendsto (fun n => cmean χ + (ε n : ℂ) * Btail χ (ε n : ℂ) 1) atTop
      (𝓝 (cmean χ)) := by
    have h := (tendsto_const_nhds (x := cmean χ) (f := atTop)).add hsBtail
    simpa using h
  -- The two sequences agree (LFunction_eq_cmean_add at s = ε n), so limits coincide.
  have heq : (fun n => DirichletCharacter.LFunction χ (ε n : ℂ))
      = fun n => cmean χ + (ε n : ℂ) * Btail χ (ε n : ℂ) 1 := by
    funext n
    exact LFunction_eq_cmean_add χ hχ (ε n : ℂ) (by simpa using hεpos n)
  rw [heq] at hLHS
  exact tendsto_nhds_unique hRHS hLHS

/-- **THE EXACT, HEIGHT-FREE CLOSURE LEDGER (headline).**  At a zero `L(s) = 0` with `Re s > 0`,
    the height-rescaled partial sum `L_M(s)·M^s` converges to the fibre imbalance against the
    channel constant `L(0,χ)`, at rate `O(M^{-1})`:
      `‖L_M(s)·M^s − (A(M) − L(0,χ))‖ ≤ C·M^{-1}`   for all `M ≥ 1`,
    with `C` independent of `M`.  The limiting object `A(M) − L(0,χ)` is **free of the height
    `Im s`** — the height enters only through the unit phase `M^{-s}` (here cancelled by `M^s`).
    `L(0,χ) = cmean χ = −B_{1,χ}` is the generalized-Bernoulli channel constant. -/
theorem closure_ledger_exact (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (s : ℂ) (hσ : 0 < s.re)
    (hzero : DirichletCharacter.LFunction χ s = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 1 ≤ M →
      ‖LM χ s M * (M : ℂ) ^ s - (Asum χ M - DirichletCharacter.LFunction χ 0)‖
        ≤ C * (M : ℝ) ^ (-(1 : ℝ)) := by
  have hs : s ≠ 0 := by intro h; rw [h] at hσ; simp at hσ
  set Ccoef := Cprime χ * (2 + ‖s + 1‖ * (1 + 1 / (s.re + 1))) with hCcoef
  refine ⟨‖s‖ * Ccoef + 1, by rw [hCcoef, Cprime]; positivity, fun M hM => ?_⟩
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hMne : (M : ℂ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have hpow1 : (0 : ℝ) < (M : ℝ) ^ (-(1 : ℝ)) := Real.rpow_pos_of_pos hMpos _
  -- At a zero: L_M·M^s − (A(M) − L(0,χ)) = (-s)·Btail·M^s, using cmean = L(0,χ).
  have hid := closure_ledger_exact_identity χ hχ s hσ M hM
  rw [hzero, sub_zero] at hid
  rw [← cmean_eq_LFunction_zero χ hχ]
  have hcancel : LM χ s M * (M : ℂ) ^ s - (Asum χ M - cmean χ) = (-s) * Btail χ s M * (M : ℂ) ^ s := by
    rw [hid, add_mul, mul_assoc ((Asum χ M - cmean χ)), ← Complex.cpow_add _ _ hMne,
        neg_add_cancel, Complex.cpow_zero, mul_one]
    ring
  rw [hcancel]
  -- ‖(-s)·Btail·M^s‖ = ‖s‖·‖Btail‖·M^σ ≤ ‖s‖·(Ccoef·M^{-σ-1})·M^σ = ‖s‖·Ccoef·M^{-1}.
  rw [norm_mul, norm_mul, norm_neg]
  have hcpowS : ‖(M : ℂ) ^ s‖ = (M : ℝ) ^ s.re := Complex.norm_natCast_cpow_of_pos (by omega) s
  rw [hcpowS]
  have hBt : ‖Btail χ s M‖ ≤ Ccoef * (M : ℝ) ^ (-s.re - 1) := norm_Btail_le χ hχ s hσ M hM
  have hkey : ‖s‖ * ‖Btail χ s M‖ * (M : ℝ) ^ s.re ≤ ‖s‖ * Ccoef * (M : ℝ) ^ (-(1:ℝ)) := by
    have hstep : ‖s‖ * ‖Btail χ s M‖ * (M : ℝ) ^ s.re
        ≤ ‖s‖ * (Ccoef * (M : ℝ) ^ (-s.re - 1)) * (M : ℝ) ^ s.re := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hMpos.le _)
      exact mul_le_mul_of_nonneg_left hBt (norm_nonneg _)
    refine le_trans hstep ?_
    rw [mul_assoc ‖s‖, mul_assoc Ccoef, ← Real.rpow_add hMpos,
        show -s.re - 1 + s.re = -(1:ℝ) from by ring, ← mul_assoc]
  refine le_trans hkey ?_
  have : (0:ℝ) ≤ ‖s‖ * Ccoef := by rw [hCcoef, Cprime]; positivity
  nlinarith [hpow1, this]

/-- **On-line √N corollary.**  On the critical line `s = ½ + t·i`, the rescaling `‖M^s‖ = √M`,
    so at a zero the `√N`-weighted closure error converges to the fibre imbalance:
      `‖L_M(½+t·i)‖·√M ≤ ‖A(M) − L(0,χ)‖ + C/√M`   for all `M ≥ 1`.
    This is the user's `E(N,t)·√N → |A(N) − L(0,χ)|`: the `√N` is exactly the `M^{1/2}` from `σ = ½`. -/
theorem closure_ledger_onLine (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (t : ℝ)
    (hzero : DirichletCharacter.LFunction χ (1 / 2 + (t : ℂ) * Complex.I) = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 1 ≤ M →
      ‖LM χ (1 / 2 + (t : ℂ) * Complex.I) M‖ * Real.sqrt M
        ≤ ‖Asum χ M - DirichletCharacter.LFunction χ 0‖ + C / Real.sqrt M := by
  set s : ℂ := 1 / 2 + (t : ℂ) * Complex.I with hs
  have hsre : s.re = 1 / 2 := by
    rw [hs]; simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hσ : 0 < s.re := by rw [hsre]; norm_num
  obtain ⟨C, hC, hbound⟩ := closure_ledger_exact χ hχ s hσ hzero
  refine ⟨C, hC, fun M hM => ?_⟩
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hsqrt : Real.sqrt M = (M : ℝ) ^ s.re := by
    rw [hsre, Real.sqrt_eq_rpow]
  -- ‖L_M‖·√M = ‖L_M·M^s‖.  Bound ≤ ‖A−L(0)‖ + ‖L_M·M^s − (A−L(0))‖ ≤ ‖A−L(0)‖ + C·M^{-1}.
  have hcpow : ‖(M : ℂ) ^ s‖ = Real.sqrt M := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega), hsqrt]
  have hsplit : ‖LM χ s M‖ * Real.sqrt M = ‖LM χ s M * (M : ℂ) ^ s‖ := by
    rw [norm_mul, hcpow]
  rw [hsplit]
  have htri : ‖LM χ s M * (M : ℂ) ^ s‖
      ≤ ‖Asum χ M - DirichletCharacter.LFunction χ 0‖
        + ‖LM χ s M * (M : ℂ) ^ s - (Asum χ M - DirichletCharacter.LFunction χ 0)‖ :=
    norm_le_insert' (LM χ s M * (M : ℂ) ^ s) (Asum χ M - DirichletCharacter.LFunction χ 0)
  -- ‖... ‖ ≤ C·M^{-1} ≤ C/√M since M^{-1} ≤ 1/√M for M ≥ 1.
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have htail : ‖LM χ s M * (M : ℂ) ^ s - (Asum χ M - DirichletCharacter.LFunction χ 0)‖
      ≤ C / Real.sqrt M := by
    refine le_trans (hbound M hM) ?_
    rw [Real.rpow_neg_one, div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_left _ hC.le
    rw [inv_le_inv₀ hMpos (Real.sqrt_pos.mpr hMpos)]
    calc Real.sqrt M ≤ Real.sqrt (M * M) := by
          apply Real.sqrt_le_sqrt; nlinarith [hMR]
      _ = M := by rw [Real.sqrt_mul_self hMpos.le]
  linarith [htri, htail]

/-! ### The channel constant in closed form: `cmean = −(1/N)·Σ_a a.val·χ(a)` (generalized Bernoulli) -/

omit [NeZero N] in
/-- The unnormalised running-sum aggregate: `Σ_{k<n} Asum χ k = Σ_{m<n} (n − m)·χ m`,
    for every upper limit `n` (induction; each `χ m` is counted `n − m` times). -/
theorem sum_Asum_range_eq (χ : DirichletCharacter ℂ N) (n : ℕ) :
    ∑ k ∈ Finset.range n, Asum χ k
      = ∑ m ∈ Finset.range n, ((n : ℂ) - (m : ℂ)) * χ (m : ZMod N) := by
  induction n with
  | zero => simp
  | succ p ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    -- Asum χ p = Σ_{m<p} χ m + χ p.
    rw [show Asum χ p = ∑ m ∈ Finset.range (p + 1), χ (m : ZMod N) from by
          rw [Asum, Nat.range_succ_eq_Icc_zero], Finset.sum_range_succ]
    -- RHS top term (p+1-p)χ p = χ p; expand RHS body (p+1-m) = (p-m)+1.
    have hbody : ∑ m ∈ Finset.range p, ((↑(p + 1) : ℂ) - (m : ℂ)) * χ (m : ZMod N)
        = ∑ m ∈ Finset.range p, ((p : ℂ) - (m : ℂ)) * χ (m : ZMod N)
          + ∑ m ∈ Finset.range p, χ (m : ZMod N) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl (fun m _ => by push_cast; ring)
    rw [hbody]
    have htop : ((↑(p + 1) : ℂ) - (p : ℂ)) = 1 := by push_cast; ring
    rw [htop, one_mul]
    ring

/-- `Σ_{m<N} g((m:ZMod N)) = Σ_{a:ZMod N} g a` — reindexing `range N ≃ ZMod N` (`a ↦ a.val`). -/
theorem sum_range_eq_sum_zmod (g : ZMod N → ℂ) :
    ∑ m ∈ Finset.range N, g (m : ZMod N) = ∑ a : ZMod N, g a := by
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  refine Finset.sum_nbij' (fun m => (m : ZMod N)) (fun a => a.val) ?_ ?_ ?_ ?_ ?_
  · intro m _; exact Finset.mem_univ _
  · intro a _; rw [Finset.mem_range]; exact ZMod.val_lt a
  · intro m hm; rw [Finset.mem_range] at hm
    show ((m : ZMod N)).val = m; rw [ZMod.val_natCast_of_lt hm]
  · intro a _; show ((a.val : ℕ) : ZMod N) = a; rw [ZMod.natCast_val, ZMod.cast_id]
  · intro m _; rfl

/-- **Closed form of the channel constant (generalized Bernoulli `−B_{1,χ}`).**
    `cmean χ = LFunction χ 0 = −(1/N)·Σ_{a:ZMod N} a.val·χ(a)`. -/
theorem cmean_closed_form (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) :
    cmean χ = -(1 / N) * ∑ a : ZMod N, (a.val : ℂ) * χ a := by
  have hNne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [cmean, sum_Asum_range_eq χ N]
  -- Σ_{m<N}(N-m)χ m = N·Σχ - Σ m·χ m = -Σ m·χ m  (since Σχ = 0).
  have hsplit : ∑ m ∈ Finset.range N, ((N : ℂ) - (m : ℂ)) * χ (m : ZMod N)
      = (N : ℂ) * (∑ m ∈ Finset.range N, χ (m : ZMod N))
        - ∑ m ∈ Finset.range N, (m : ℂ) * χ (m : ZMod N) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl (fun m _ => by ring)
  rw [hsplit, sum_range_eq_sum_zmod (fun a => χ a), MulChar.sum_eq_zero_of_ne_one hχ, mul_zero, zero_sub]
  -- Σ_{m<N} m·χ m = Σ_a a.val·χ a  (reindex; m = a.val for m < N).
  rw [show ∑ m ∈ Finset.range N, (m : ℂ) * χ (m : ZMod N)
        = ∑ a : ZMod N, (a.val : ℂ) * χ a from by
      rw [← sum_range_eq_sum_zmod (fun a => (a.val : ℂ) * χ a)]
      apply Finset.sum_congr rfl (fun m hm => ?_)
      rw [Finset.mem_range] at hm
      rw [ZMod.val_natCast_of_lt hm]]
  field_simp

/-! ## Section 7: The hypothesis is non-vacuous — χ₃ instance & concrete quantized constant

  The zero-period-sum hypothesis `∑ j, χ j = 0` holds for every non-principal character; here
  is the repo's running example `χ₃` (`χ₃(0,1,2) = 0,1,−1`), with the channel constant
  `L(0,χ₃) = 1/3` and the data-mined quantized fibre imbalance `A(M) − L(0,χ₃) ∈ {−1/3, 2/3}`. -/

/-- `χ₃` has zero period sum, so the closure ledger applies to `L(·,χ₃)`. -/
theorem chi3_sum_zero : ∑ j : ZMod 3, ChiThree.χ3 j = 0 := by
  rw [show (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} from by decide,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
      ChiThree.χ3_zero, ChiThree.χ3_one, ChiThree.χ3_two]
  ring

/-- `χ₃` is non-principal (`χ₃(2) = −1 ≠ 1`), so the unconditional ledger applies to it
    (the repo's `ChiThree.χ3_ne_one`). -/
theorem chi3_ne_one : ChiThree.χ3 ≠ 1 := ChiThree.χ3_ne_one

/-- The closure-ledger rate bound, instantiated for `χ₃`. -/
theorem rate_bound_chi3 (s : ℂ) (hσ : 0 < s.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 1 ≤ M →
      ‖LM ChiThree.χ3 s M - DirichletCharacter.LFunction ChiThree.χ3 s‖
        ≤ C * (M : ℝ) ^ (-s.re) :=
  rate_bound ChiThree.χ3 chi3_ne_one s hσ

/-- **The χ₃ channel constant: `cmean χ₃ = LFunction χ₃ 0 = 1/3`** — the generalized Bernoulli
    `−B_{1,χ₃} = −(1/3)(1·1 + 2·(−1)) = 1/3`, matching the numerics. -/
theorem cmean_chi3 : cmean ChiThree.χ3 = 1 / 3 := by
  rw [cmean_closed_form ChiThree.χ3 chi3_ne_one,
      show (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} from by decide,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [show ((0 : ZMod 3)).val = 0 from by decide, show ((1 : ZMod 3)).val = 1 from by decide,
      show ((2 : ZMod 3)).val = 2 from by decide,
      ChiThree.χ3_zero, ChiThree.χ3_one, ChiThree.χ3_two]
  norm_num

/-- `LFunction χ₃ 0 = 1/3`. -/
theorem LFunction_chi3_zero : DirichletCharacter.LFunction ChiThree.χ3 0 = 1 / 3 := by
  rw [← cmean_eq_LFunction_zero ChiThree.χ3 chi3_ne_one, cmean_chi3]

/-- **Quantization of the χ₃ running sum:** `Asum χ₃ M ∈ {0, 1}` for every `M`
    (it is `1` exactly when `M ≡ 1 (mod 3)`, else `0`). -/
theorem Asum_chi3_quantized (M : ℕ) : Asum ChiThree.χ3 M = 0 ∨ Asum ChiThree.χ3 M = 1 := by
  -- A(M) = A(M % 3) by periodicity; check the 3 residues.
  have hred : Asum ChiThree.χ3 M = Asum ChiThree.χ3 (M % 3) := by
    conv_lhs => rw [← Nat.div_add_mod M 3]
    induction M / 3 with
    | zero => simp
    | succ q ih =>
      rw [show 3 * (q + 1) + M % 3 = (3 * q + M % 3) + 3 from by ring,
          Asum_add_period ChiThree.χ3 chi3_ne_one, ih]
  rw [hred]
  have h3 : M % 3 < 3 := Nat.mod_lt M (by norm_num)
  interval_cases h : (M % 3)
  · left; rw [show Asum ChiThree.χ3 0 = ChiThree.χ3 0 from by
      rw [Asum, show Finset.Icc 0 0 = {0} from rfl, Finset.sum_singleton]; norm_num,
      ChiThree.χ3_zero]
  · right
    rw [show Asum ChiThree.χ3 1 = ChiThree.χ3 0 + ChiThree.χ3 1 from by
      rw [Asum, show Finset.Icc 0 1 = {0, 1} from by decide,
          Finset.sum_insert (by decide), Finset.sum_singleton]; push_cast; ring]
    rw [ChiThree.χ3_zero, ChiThree.χ3_one]; norm_num
  · left
    rw [show Asum ChiThree.χ3 2 = ChiThree.χ3 0 + ChiThree.χ3 1 + ChiThree.χ3 2 from by
      rw [Asum, show Finset.Icc 0 2 = {0, 1, 2} from by decide,
          Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
      push_cast; ring]
    rw [ChiThree.χ3_zero, ChiThree.χ3_one, ChiThree.χ3_two]; norm_num

/-- **The quantized channel constant for χ₃:** the fibre imbalance `A(M) − L(0,χ₃)` takes only
    the two values `−1/3` and `2/3`; hence the on-line closure error scale `‖A(M) − L(0,χ₃)‖`
    is `1/3` or `2/3`. This is the data-mined quantized constant. -/
theorem closure_constant_chi3 (M : ℕ) :
    Asum ChiThree.χ3 M - DirichletCharacter.LFunction ChiThree.χ3 0 = -(1/3) ∨
    Asum ChiThree.χ3 M - DirichletCharacter.LFunction ChiThree.χ3 0 = 2/3 := by
  rw [LFunction_chi3_zero]
  rcases Asum_chi3_quantized M with h | h
  · left; rw [h]; norm_num
  · right; rw [h]; norm_num

/-! ## Section 8: The quantized channel constant — character-agnostic

  `A(M) − L(0,χ₃) ∈ {−1/3, 2/3}` (`closure_constant_chi3`) is the `N = 3` instance of a general
  fact: for EVERY non-principal character (`∑ⱼ χ j = 0`), the closure constant `A(M) − L(0,χ)` is
  **periodic in `M` with period `N`** — because the running character sum is (`Asum_add_period`) —
  hence takes at most `N` distinct values, the period imbalances `{A(j) − L(0,χ) : j < N}`. The
  quantization is character-agnostic; only the concrete value set is per-character. -/

/-- The running character sum reduces mod `N`: `A(M) = A(M % N)` (periodicity, `Asum_add_period`). -/
theorem Asum_mod (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (M : ℕ) :
    Asum χ M = Asum χ (M % N) := by
  conv_lhs => rw [← Nat.div_add_mod M N]
  induction M / N with
  | zero => simp
  | succ q ih =>
    rw [show N * (q + 1) + M % N = (N * q + M % N) + N from by ring,
        Asum_add_period χ hχ, ih]

/-- **The channel constant is periodic with period `N`** (every non-principal character):
    `A(M+N) − L(0,χ) = A(M) − L(0,χ)`. The height-free closure scale repeats every `N`. -/
theorem closure_constant_periodic (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (M : ℕ) :
    Asum χ (M + N) - DirichletCharacter.LFunction χ 0
      = Asum χ M - DirichletCharacter.LFunction χ 0 := by
  rw [Asum_add_period χ hχ]

/-- **Quantization of the channel constant, for every non-principal character.** The closure
    constant `A(M) − L(0,χ)` takes only finitely many values: it lies in the image of one period
    window `{A(j) − L(0,χ) : j < N}` (at most `N` values). The χ₃ case `{−1/3, 2/3}`
    (`closure_constant_chi3`) is the `N = 3` instance of this. -/
theorem closure_constant_mem_image (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (M : ℕ) :
    Asum χ M - DirichletCharacter.LFunction χ 0
      ∈ (Finset.range N).image
          (fun j => Asum χ j - DirichletCharacter.LFunction χ 0) := by
  rw [Asum_mod χ hχ M]
  exact Finset.mem_image_of_mem _
    (Finset.mem_range.mpr (Nat.mod_lt M (Nat.pos_of_ne_zero (NeZero.ne N))))

/-- **Uniform magnitude bound on the channel constant** (every non-principal character):
    `‖A(M) − L(0,χ)‖ ≤ N + ‖L(0,χ)‖`, independent of `M` and the height. The on-line closure
    error scale is bounded by the character-sum amplitude (Pólya–Vinogradov, here just `‖A‖ ≤ N`). -/
theorem norm_closure_constant_le (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (M : ℕ) :
    ‖Asum χ M - DirichletCharacter.LFunction χ 0‖
      ≤ (N : ℝ) + ‖DirichletCharacter.LFunction χ 0‖ :=
  le_trans (norm_sub_le _ _) (add_le_add (norm_Asum_le χ hχ M) le_rfl)

end DirichletClosureLedger
