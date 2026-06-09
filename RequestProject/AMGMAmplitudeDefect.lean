import Mathlib

/-!
# The AM–GM Amplitude Defect: the on-line floor and the off-line excess

This file proves one clean, fully unconditional fact about an amplitude envelope, with no
reference to RH or to `riemannZeta`. The parameter `β` should be read as the real part of a
(conjugate pair of) zero(s): `β = 1/2` is "on-line", `β ≠ 1/2` is "off-line".

The point is **not** total amplitude energy. It is the **delta** between two things:

* the **floor** — the minimum envelope amplitude, attained when everything is on-line
  (`β = 1/2`), namely the balanced value `E_bal(r) = 2 · r^(1/2)`; and
* the **excess from being off-line** — how far the off-line envelope sits *above* that floor.

That delta is the defect

  `D(β, r) = E_off(β, r) - E_bal(r)`,   where  `E_off(β, r) = r^β + r^(1-β)`.

AM–GM (`a + b ≥ 2√(ab)` with `a = r^β`, `b = r^(1-β)`, `ab = r`) gives the whole story:

* `D ≥ 0` always — the balanced value is a genuine floor (`E_bal_le_E_off`, `D_nonneg`);
* `D = 0` **exactly** on-line (`online_no_defect`, and the floor is attained there:
  `E_off_half`, `E_off_ge_online`);
* `D > 0` strictly off-line (`offline_defect_pos`), because the defect is the square
  `D = (r^(β/2) - r^((1-β)/2))²` (`D_eq_sq`), which is zero iff the two half-powers agree,
  iff `β = 1/2`;
* the sharp characterization: `D(β,r) = 0 ↔ β = 1/2` (`D_eq_zero_iff`, for `r > 0, r ≠ 1`).

The same defect written through the even ("cosine") channel is
`D(β,r) = 2 r^(1/2)·(cosh((β-1/2)·log r) - 1)` (`coshDefect_eq`): on-line the cosh argument is
`0`, so the cosine channel is balanced and the delta vanishes; off-line the argument leaves `0`,
cosh exceeds `1`, and the delta is strictly positive.

Section 2 records that this off-line excess, modelled as a sequence growing like `n^α`
(`α = β - 1/2 > 0`), is uncancellable: it **diverges** and survives every standard damping.
-/

open Filter Topology BigOperators Finset
open scoped Real

noncomputable section

namespace AMGMAmplitudeDefect

/-! ## §1. The defect is the delta above the on-line floor -/

/-- The balanced (all-on-line) envelope `E_bal(r) = 2 · r^(1/2)`. This is the floor. -/
def E_bal (r : ℝ) : ℝ := 2 * r ^ (1 / 2 : ℝ)

/-- The envelope at real part `β` (a conjugate pair): `E_off(β, r) = r^β + r^(1-β)`. -/
def E_off (β r : ℝ) : ℝ := r ^ β + r ^ (1 - β)

/-- The amplitude **defect** = the delta of the envelope above the on-line floor. -/
def D (β r : ℝ) : ℝ := E_off β r - E_bal r

/-- The same defect through the even ("cosine") channel:
    `2 r^(1/2)·(cosh((β-1/2)·log r) - 1)`. -/
def coshDefect (β r : ℝ) : ℝ :=
  2 * r ^ (1 / 2 : ℝ) * (Real.cosh ((β - 1 / 2) * Real.log r) - 1)

/-- Unfolded form of the defect. -/
theorem D_eq (β r : ℝ) : D β r = r ^ β + r ^ (1 - β) - 2 * r ^ (1 / 2 : ℝ) := by
  unfold D E_off E_bal; ring

/-- **AM–GM gap identity**: the defect is a perfect square (needs `r > 0`). -/
theorem D_eq_sq (β : ℝ) {r : ℝ} (hr : 0 < r) :
    D β r = (r ^ (β / 2) - r ^ ((1 - β) / 2)) ^ 2 := by
  rw [D_eq]
  have e1 : (r ^ (β / 2)) ^ 2 = r ^ β := by rw [sq, ← Real.rpow_add hr]; congr 1; ring
  have e2 : (r ^ ((1 - β) / 2)) ^ 2 = r ^ (1 - β) := by rw [sq, ← Real.rpow_add hr]; congr 1; ring
  have e3 : r ^ (β / 2) * r ^ ((1 - β) / 2) = r ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hr]; congr 1; ring
  rw [sub_sq, e1, e2, mul_assoc, e3]; ring

/-- The cosine-channel form equals the defect (needs `r > 0`). -/
theorem coshDefect_eq (β : ℝ) {r : ℝ} (hr : 0 < r) : coshDefect β r = D β r := by
  rw [D_eq]
  unfold coshDefect
  rw [Real.cosh_eq]
  have e1 : (β - 1 / 2) * Real.log r = Real.log r * (β - 1 / 2) := by ring
  have e2 : -(Real.log r * (β - 1 / 2)) = Real.log r * (1 / 2 - β) := by ring
  rw [e1, e2, ← Real.rpow_def_of_pos hr (β - 1 / 2), ← Real.rpow_def_of_pos hr (1 / 2 - β)]
  have h1 : r ^ (1 / 2 : ℝ) * r ^ (β - 1 / 2 : ℝ) = r ^ β := by
    rw [← Real.rpow_add hr]; congr 1; ring
  have h2 : r ^ (1 / 2 : ℝ) * r ^ (1 / 2 - β : ℝ) = r ^ (1 - β) := by
    rw [← Real.rpow_add hr]; congr 1; ring
  have expand :
      2 * r ^ (1 / 2 : ℝ) * ((r ^ (β - 1 / 2 : ℝ) + r ^ (1 / 2 - β : ℝ)) / 2 - 1)
        = r ^ (1 / 2 : ℝ) * r ^ (β - 1 / 2 : ℝ)
          + r ^ (1 / 2 : ℝ) * r ^ (1 / 2 - β : ℝ) - 2 * r ^ (1 / 2 : ℝ) := by ring
  rw [expand, h1, h2]

/-- **The defect is never negative** — the balanced value really is a floor (`r > 0`). -/
theorem D_nonneg (β : ℝ) {r : ℝ} (hr : 0 < r) : 0 ≤ D β r := by
  rw [D_eq_sq β hr]; exact sq_nonneg _

/-- The on-line envelope **equals** the floor (the minimum is attained on-line). -/
theorem E_off_half (r : ℝ) : E_off (1 / 2 : ℝ) r = E_bal r := by
  unfold E_off E_bal
  have h : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rw [h]; ring

/-- **On-line ⟹ no defect**: `β = 1/2 ⟹ D = 0`. The delta vanishes exactly on the line. -/
theorem online_no_defect (r : ℝ) : D (1 / 2 : ℝ) r = 0 := by
  unfold D; rw [E_off_half]; ring

/-- The floor is a genuine lower bound: `E_bal r ≤ E_off β r` for every `β` (`r > 0`). -/
theorem E_bal_le_E_off (β : ℝ) {r : ℝ} (hr : 0 < r) : E_bal r ≤ E_off β r := by
  have := D_nonneg β hr; unfold D at this; linarith

/-- **The minimum amplitude is the on-line one**: every `β` sits at or above the on-line value. -/
theorem E_off_ge_online (β : ℝ) {r : ℝ} (hr : 0 < r) :
    E_off (1 / 2 : ℝ) r ≤ E_off β r := by
  rw [E_off_half]; exact E_bal_le_E_off β hr

/-- Key: off the line (`r > 0`, `r ≠ 1`, `β ≠ 1/2`) the two half-powers differ. -/
theorem rpow_half_ne_of_offline {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) {β : ℝ}
    (hβ : β ≠ 1 / 2) : r ^ (β / 2) ≠ r ^ ((1 - β) / 2) := by
  rw [Real.rpow_def_of_pos hr, Real.rpow_def_of_pos hr]
  intro h
  have hlog : Real.log r * (β / 2) = Real.log r * ((1 - β) / 2) := Real.exp_eq_exp.mp h
  have hlogr : Real.log r ≠ 0 := by
    intro h0
    rcases Real.log_eq_zero.mp h0 with h' | h' | h'
    · exact hr.ne' h'
    · exact hr1 h'
    · rw [h'] at hr; norm_num at hr
  have : β / 2 = (1 - β) / 2 := mul_left_cancel₀ hlogr hlog
  exact hβ (by linarith)

/-- **Off-line ⟹ strictly positive defect** (`r > 0`, `r ≠ 1`, `β ≠ 1/2`).
    The excess over the floor is real and cannot be made zero off the line. -/
theorem offline_defect_pos {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) {β : ℝ} (hβ : β ≠ 1 / 2) :
    0 < D β r := by
  rw [D_eq_sq β hr]
  exact sq_pos_of_ne_zero (sub_ne_zero.mpr (rpow_half_ne_of_offline hr hr1 hβ))

/-- **Sharp characterization**: the defect vanishes *exactly* on the line (`r > 0`, `r ≠ 1`). -/
theorem D_eq_zero_iff {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) (β : ℝ) :
    D β r = 0 ↔ β = 1 / 2 := by
  constructor
  · intro h
    by_contra hβ
    exact (offline_defect_pos hr hr1 hβ).ne' h
  · rintro rfl; exact online_no_defect r

/-- The defect is symmetric under `β ↔ 1 - β` (the conjugate pairing). -/
theorem D_symm (β r : ℝ) : D β r = D (1 - β) r := by
  unfold D E_off; ring_nf

/-! ## §2. The off-line excess diverges and cannot be cancelled

An off-line zero (`β = 1/2 + α`, `α > 0`) injects an excess whose envelope `r^β = r^(1/2)·r^α`
**grows with scale**. Model it as `Da : ℕ → ℝ` with `Da n ≥ C · n^α`, `C, α > 0`. Then the excess
is uncancellable: it diverges and survives every standard damping. -/

/-- A growing amplitude defect: a non-negative sequence with `Da n ≥ C · n^α`, `C, α > 0`. -/
structure GrowingDefect where
  Da : ℕ → ℝ
  α : ℝ
  C : ℝ
  hα_pos : 0 < α
  hC_pos : 0 < C
  hDa_nonneg : ∀ n, 0 ≤ Da n
  hDa_growth : ∀ n : ℕ, 1 ≤ n → C * (n : ℝ) ^ α ≤ Da n

namespace GrowingDefect

/-- The growth envelope diverges. -/
theorem envelope_tendsto_atTop (g : GrowingDefect) :
    Tendsto (fun n : ℕ => g.C * (n : ℝ) ^ g.α) atTop atTop :=
  Filter.Tendsto.const_mul_atTop g.hC_pos
    (tendsto_rpow_atTop g.hα_pos |>.comp tendsto_natCast_atTop_atTop)

/-- The defect itself diverges to `+∞`. -/
theorem tendsto_atTop (g : GrowingDefect) : Tendsto g.Da atTop atTop := by
  refine Filter.tendsto_atTop_mono' _ ?_ g.envelope_tendsto_atTop
  exact Filter.eventually_atTop.mpr ⟨1, fun n hn => g.hDa_growth n hn⟩

/-- **It diverges:** `∑ Da` is not summable. -/
theorem not_summable (g : GrowingDefect) : ¬ Summable g.Da := by
  have hge : ∀ n ≥ 1, g.Da n ≥ g.C * (n : ℝ) ^ g.α := fun n hn => g.hDa_growth n hn
  have hns : ¬ Summable (fun n : ℕ => (g.C : ℝ) * (n : ℝ) ^ g.α) := by
    rw [summable_mul_left_iff] <;> norm_num [g.hC_pos.ne']
    linarith [g.hα_pos]
  contrapose! hns
  rw [← summable_nat_add_iff 1] at *
  exact Summable.of_nonneg_of_le
    (fun n => mul_nonneg g.hC_pos.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (fun n => hge _ (Nat.succ_pos _)) hns

/-- The terms do not tend to `0`. -/
theorem not_tendsto_zero (g : GrowingDefect) : ¬ Tendsto g.Da atTop (nhds 0) :=
  fun h => not_tendsto_atTop_of_tendsto_nhds h g.tendsto_atTop

/-- The defect is unbounded above. -/
theorem not_bddAbove (g : GrowingDefect) : ¬ BddAbove (Set.range g.Da) := by
  rintro ⟨M, hM⟩
  obtain ⟨n, hn⟩ := (g.tendsto_atTop.eventually_gt_atTop M).exists
  exact absurd (hM (Set.mem_range_self n)) (not_le_of_gt hn)

/-- Adding the defect to **any** convergent sequence destroys convergence. -/
theorem destroys_convergence (g : GrowingDefect) (f : ℕ → ℝ) (L : ℝ)
    (hf : Tendsto f atTop (nhds L)) :
    ¬ ∃ M : ℝ, Tendsto (fun n => f n + g.Da n) atTop (nhds M) := by
  rintro ⟨M, hM⟩
  exact not_tendsto_atTop_of_tendsto_nhds hM (Filter.Tendsto.add_atTop hf g.tendsto_atTop)

/-- **AM–GM amplification:** even `√Da` is not summable — no square-root damping tames it. -/
theorem sqrt_not_summable (g : GrowingDefect) :
    ¬ Summable (fun n => Real.sqrt (g.Da n)) := by
  have hsg : ∀ n : ℕ, 1 ≤ n → Real.sqrt (g.Da n) ≥ Real.sqrt g.C * (n : ℝ) ^ (g.α / 2) := by
    intro n hn
    have hsd : Real.sqrt (g.Da n) ≥ Real.sqrt (g.C * (n : ℝ) ^ g.α) :=
      Real.sqrt_le_sqrt (g.hDa_growth n hn)
    refine hsd.trans' (le_of_eq ?_)
    rw [Real.sqrt_mul g.hC_pos.le, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
      ← Real.rpow_mul (by positivity)]
    ring_nf
  have hdiv : ¬ Summable (fun n : ℕ => Real.sqrt g.C * (n : ℝ) ^ (g.α / 2)) := by
    rw [summable_mul_left_iff] <;> norm_num [Real.sqrt_ne_zero'.mpr g.hC_pos]
    linarith [g.hα_pos]
  contrapose! hdiv
  rw [← summable_nat_add_iff 1] at *
  exact Summable.of_nonneg_of_le (fun n => by positivity)
    (fun n => hsg _ le_add_self) hdiv

end GrowingDefect

/-! ## §3. The radial energy balance: prime-side defect = zero-side radial energy

The per-pair amplitude defect `D(β,r)` of §1 vanishes **exactly** on-line (`D_eq_zero_iff`), and its
small-`(β−½)` density is the **radial energy** `(β−½)²` (the leading cosh coefficient via
`coshDefect_eq`: `D = 2r^{1/2}(cosh((β−½)log r) − 1)`, whose second-order term is
`r^{1/2}(log r)²·(β−½)²`). Summed over a family of zeros `ρ` with multiplicity `m` and **strictly
positive** weight `w`, that density is the **zero-side radial energy**

  `ZeroRadialEnergy = Σ_ρ m_ρ · w_ρ · (Re ρ − ½)²`.

It is `≥ 0`, and (for `m, w > 0`) it is `0` **iff every `Re ρ = ½`** — so `ZeroRadialEnergy = 0` is
exactly "the family is entirely on-line" (over the actual nontrivial zeros, that is GRH; it is **not**
free).

The **energy-balance** target `PrimeRadialDefect = ZeroRadialEnergy` equates this zero-side detector to
the prime-side defect. It is recorded here as a *predicate* (`RadialEnergyBalanced`) on a **given**
`primeDefect` — the identity an energy-balance argument must *earn*, **not** a definitional relabel of
the zero energy (`primeDefect` is a free parameter, never `:= ZeroRadialEnergy`). The payoff lemma is
the honest reduction: if the balance holds **and** the prime defect is `0` (the AM–GM on-line floor,
established on the prime side with no zero input), then every zero is on-line. The remaining content is
exactly (a) earning the balance with a genuinely prime-side `primeDefect`, and (b) `primeDefect = 0`
from the prime floor — neither of which may assume `Re ρ = ½`. -/

variable {ι : Type*}

/-- **The zero-side radial energy** `Σ_ρ m_ρ · w_ρ · (Re ρ − ½)²` over a finite family of zeros
    `ρ : ι → ℂ`, with multiplicity `m` and weight `w`. Its vanishing locus is the critical line. -/
def ZeroRadialEnergy (s : Finset ι) (m w : ι → ℝ) (ρ : ι → ℂ) : ℝ :=
  ∑ i ∈ s, m i * w i * ((ρ i).re - 1 / 2) ^ 2

/-- `ZeroRadialEnergy ≥ 0` for non-negative multiplicity and weight (a sum of squares). -/
theorem ZeroRadialEnergy_nonneg {s : Finset ι} {m w : ι → ℝ} {ρ : ι → ℂ}
    (hm : ∀ i ∈ s, 0 ≤ m i) (hw : ∀ i ∈ s, 0 ≤ w i) :
    0 ≤ ZeroRadialEnergy s m w ρ :=
  Finset.sum_nonneg fun i hi => mul_nonneg (mul_nonneg (hm i hi) (hw i hi)) (sq_nonneg _)

/-- **`ZeroRadialEnergy = 0 ⟺ every zero on-line`** (strictly positive multiplicity and weight). The
    zero-side radial energy is the on-line detector: it vanishes exactly when `Re ρ = ½` for all `ρ`. -/
theorem ZeroRadialEnergy_eq_zero_iff {s : Finset ι} {m w : ι → ℝ} {ρ : ι → ℂ}
    (hm : ∀ i ∈ s, 0 < m i) (hw : ∀ i ∈ s, 0 < w i) :
    ZeroRadialEnergy s m w ρ = 0 ↔ ∀ i ∈ s, (ρ i).re = 1 / 2 := by
  unfold ZeroRadialEnergy
  rw [Finset.sum_eq_zero_iff_of_nonneg fun i hi =>
    mul_nonneg (mul_nonneg (hm i hi).le (hw i hi).le) (sq_nonneg _)]
  refine ⟨fun h i hi => ?_, fun h i hi => ?_⟩
  · have hpos : 0 < m i * w i := mul_pos (hm i hi) (hw i hi)
    have hsq : ((ρ i).re - 1 / 2) ^ 2 = 0 := by
      rcases mul_eq_zero.mp (h i hi) with h1 | h1
      · exact absurd h1 hpos.ne'
      · exact h1
    have hlin : (ρ i).re - 1 / 2 = 0 := by rw [pow_two] at hsq; exact mul_self_eq_zero.mp hsq
    linarith
  · rw [h i hi]; ring

/-- **The zero-side amplitude defect** `Σ_ρ m_ρ · w_ρ · D(Re ρ, r)` — the §1 AM–GM amplitude excess
    `D(β,r) = r^β + r^{1−β} − 2r^{1/2}` carried over the family of zeros at scale `r`. -/
def ZeroAmplitudeDefect (s : Finset ι) (m w : ι → ℝ) (ρ : ι → ℂ) (r : ℝ) : ℝ :=
  ∑ i ∈ s, m i * w i * D ((ρ i).re) r

/-- `ZeroAmplitudeDefect ≥ 0` (`r > 0`, non-negative multiplicity and weight). -/
theorem ZeroAmplitudeDefect_nonneg {s : Finset ι} {m w : ι → ℝ} {ρ : ι → ℂ} {r : ℝ}
    (hr : 0 < r) (hm : ∀ i ∈ s, 0 ≤ m i) (hw : ∀ i ∈ s, 0 ≤ w i) :
    0 ≤ ZeroAmplitudeDefect s m w ρ r :=
  Finset.sum_nonneg fun i hi => mul_nonneg (mul_nonneg (hm i hi) (hw i hi)) (D_nonneg _ hr)

/-- **`ZeroAmplitudeDefect = 0 ⟺ every zero on-line`** (`r > 0`, `r ≠ 1`, strictly positive `m, w`). -/
theorem ZeroAmplitudeDefect_eq_zero_iff {s : Finset ι} {m w : ι → ℝ} {ρ : ι → ℂ} {r : ℝ}
    (hr : 0 < r) (hr1 : r ≠ 1) (hm : ∀ i ∈ s, 0 < m i) (hw : ∀ i ∈ s, 0 < w i) :
    ZeroAmplitudeDefect s m w ρ r = 0 ↔ ∀ i ∈ s, (ρ i).re = 1 / 2 := by
  unfold ZeroAmplitudeDefect
  rw [Finset.sum_eq_zero_iff_of_nonneg fun i hi =>
    mul_nonneg (mul_nonneg (hm i hi).le (hw i hi).le) (D_nonneg _ hr)]
  refine ⟨fun h i hi => ?_, fun h i hi => ?_⟩
  · have hpos : 0 < m i * w i := mul_pos (hm i hi) (hw i hi)
    have hD : D ((ρ i).re) r = 0 := by
      rcases mul_eq_zero.mp (h i hi) with h1 | h1
      · exact absurd h1 hpos.ne'
      · exact h1
    exact (D_eq_zero_iff hr hr1 _).mp hD
  · rw [(D_eq_zero_iff hr hr1 _).mpr (h i hi), mul_zero]

/-- **The two zero-side defects are the same detector** (`r > 0`, `r ≠ 1`, strictly positive `m, w`):
    the amplitude defect and the radial energy vanish **together**, both exactly when every `Re ρ = ½`.

    Caveat (Rule Two — exact, not a relabel): they are **not** equal as functions. `ZeroAmplitudeDefect`
    is the full `D(β,r) = 2r^{1/2}(cosh((β−½)log r) − 1)`; `ZeroRadialEnergy`'s density `(β−½)²` is only
    its leading coefficient. What they share — and all that "no off-line zeros" needs — is the vanishing
    locus. So the honest identity is this `⟺`, not `ZeroRadialEnergy = ZeroAmplitudeDefect`. -/
theorem ZeroAmplitudeDefect_zero_iff_ZeroRadialEnergy_zero {s : Finset ι} {m w : ι → ℝ}
    {ρ : ι → ℂ} {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) (hm : ∀ i ∈ s, 0 < m i) (hw : ∀ i ∈ s, 0 < w i) :
    ZeroAmplitudeDefect s m w ρ r = 0 ↔ ZeroRadialEnergy s m w ρ = 0 := by
  rw [ZeroAmplitudeDefect_eq_zero_iff hr hr1 hm hw, ZeroRadialEnergy_eq_zero_iff hm hw]

/-- **The radial energy balance** `PrimeRadialDefect = ZeroRadialEnergy` — the prime-side defect
    equals the zero-side radial energy. Stated as a predicate on a *given* `primeDefect` (the AM–GM
    amplitude excess aggregated over the prime fibers), so this is the energy-balance **identity** to
    be earned, not a definitional relabel of the zero energy. -/
def RadialEnergyBalanced (primeDefect : ℝ) (s : Finset ι) (m w : ι → ℝ) (ρ : ι → ℂ) : Prop :=
  primeDefect = ZeroRadialEnergy s m w ρ

/-- **Balance + vanishing prime defect ⟹ no off-line zeros.** If the prime-side defect equals the
    zero-side radial energy (`RadialEnergyBalanced`) and the prime defect is `0`, then every zero is on
    the critical line (strictly positive multiplicity and weight). This is the energy-balance route to
    "no off-line zeros": the prime side carries no radial excess, so neither can the zero side. The
    content is the two hypotheses — the earned balance and `primeDefect = 0` — neither of which assumes
    `Re ρ = ½`. -/
theorem online_of_balanced_of_primeDefect_zero {primeDefect : ℝ} {s : Finset ι}
    {m w : ι → ℝ} {ρ : ι → ℂ} (hm : ∀ i ∈ s, 0 < m i) (hw : ∀ i ∈ s, 0 < w i)
    (hbal : RadialEnergyBalanced primeDefect s m w ρ) (h0 : primeDefect = 0) :
    ∀ i ∈ s, (ρ i).re = 1 / 2 := by
  have hz : ZeroRadialEnergy s m w ρ = 0 := by
    have heq : primeDefect = ZeroRadialEnergy s m w ρ := hbal
    rw [← heq]; exact h0
  exact (ZeroRadialEnergy_eq_zero_iff hm hw).mp hz

/-- **The §1 amplitude defect and the radial-energy density share their zero locus.** For `r > 0`,
    `r ≠ 1`, the prime-side AM–GM defect `D(β,r)` vanishes iff the radial-energy density `(β−½)²` does
    (both iff `β = ½`). This is why `(Re ρ − ½)²` is the right per-zero radial summand: it is the
    vanishing fingerprint of the prime amplitude defect carried into the energy. -/
theorem D_eq_zero_iff_radialDensity_zero {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) (β : ℝ) :
    D β r = 0 ↔ (β - 1 / 2) ^ 2 = 0 := by
  rw [D_eq_zero_iff hr hr1, pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0), sub_eq_zero]

end AMGMAmplitudeDefect

end
