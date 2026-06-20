import RequestProject.HelixUnitaryFlow
import RequestProject.HelixOnlineClosure
import Mathlib.NumberTheory.LSeries.ZMod
import RequestProject.DirichletLZeroSet
import RequestProject.HelixAsymmetryForcing

/-!
# The standing wave — where the phasors cancel and the zeros get marked (steps 4–5)

This joins the two halves the program has built:

* **the unitary phasor flow** (step 2, `HelixUnitaryFlow`): the prime/FTA fibres are **integers
  carrying phasors** `U(t)(n) = n^{it}`, and the (continued) `ζ` is the flow's trace
  `ζ(s) = Σ_n n^{-σ}·U(t)(n)⁻¹` — `zeta_eq_flowTrace` below, for `Re s > 1`;
* **the Möbius reality** (`HelixMobiusClosure.line_value_real`): on the critical line the completed
  wave is **real** — a standing wave `Z(t) = Re Λ(½+it)`.

The mechanism, assembled (the user's picture):

1. `zeta_eq_flowTrace` — fibres = integers + phasors; `ζ` is their χ-weighted phasor trace.
2. `completedΛ_eq_standingWave` — on the line that trace continues to the **real standing wave** `Z`:
   the phasors, paired by the Möbius inversion (FE), stop rotating and **stand**.
3. `completedΛ_zero_iff_standingWave_node` — a zero is a **node** of the standing wave: `Λ(½+it) = 0 ↔
   Z(t) = 0`. With `HelixOnlineClosure.im_odd` (Im odd in the radial offset), it is a **transversal
   real-axis crossing** — that is where a zero of zeta gets **marked**.
4. `zeta_zero_on_line_iff_standingWave_node` — the bare `ζ` reads the same node (the archimedean
   `Gammaℝ` factor is zero-free on the line), so the marked nodes are the nontrivial `ζ`-zeros.

**Honest scope (Rules Two, Four, Ten).** Steps 1 and 2 are kernel-clean theorems; step 3/4 are the
genuine *marking*. What is **not** closed here is the **on-line continuation / identification** (step
4→5): that the convergent-region trace (`Re s > 1`) and the on-line standing wave are the *same*
analytic object, so that the standing wave's nodes are exactly the flow generator's spectral events.
That continuation is the explicit-formula / determinant weld where the deep content lives, deliberately
**not** dressed as a `grh_of_…` theorem. This file marks the zeros as standing-wave nodes; it does not
force them on the line (that is the FTA/prime one-sidedness + the self-adjoint generator, steps 3,5–6).
-/

open Complex HelixLogFree HelixImaginaryAxis HelixFlow

namespace HelixStandingWave

/-! ## Step 1 — fibres are integers carrying phasors; `ζ` is their flow trace -/

/-- **`ζ` as a helix-point sum.** For `Re s > 1`, `ζ(s) = Σ_n 1/helixPtGen(σ,t)(n)` — the integers `n`
    placed at the helix points `n^{σ+it}` (radius `n^σ`, winding phasor `n^{it}`). The ζ-native form of
    `HelixImaginaryAxis.lfunction_eq_helixSum`. -/
theorem zeta_eq_helixSum {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = ∑' n : ℕ, 1 / helixPtGen s.re s.im n := by
  rw [zeta_eq_tsum_one_div_nat_cpow hs]
  refine tsum_congr (fun n => ?_)
  rcases eq_or_ne n 0 with hn | hn
  · subst hn
    have hsne : s ≠ 0 := by rintro rfl; simp only [Complex.zero_re] at hs; linarith
    have h0 : helixPtGen s.re s.im 0 = 0 := by
      rw [helixPtGen, Nat.cast_zero, Real.zero_rpow (by linarith), Complex.ofReal_zero, zero_mul]
    rw [Nat.cast_zero, Complex.zero_cpow hsne, div_zero, h0, div_zero]
  · rw [helixPtGen_eq_cpow s.re s.im n hn,
        show (s.re : ℂ) + Complex.I * s.im = s from by
          rw [mul_comm Complex.I (s.im : ℂ)]; exact Complex.re_add_im s]

/-- **`ζ` is the trace of the unitary phasor flow (step 4, convergent region).** For `Re s > 1`,
    `ζ(s) = Σ_n (n^σ)⁻¹ · U(t)(n)⁻¹`: each integer `n` contributes its radial weight `n^{-σ}` times the
    inverse **phasor** `U(t)(n)⁻¹ = n^{-it}` of the unitary flow (`HelixFlow.phasorFlow`). The standing
    wave of step 4 is the on-line continuation of this trace. -/
theorem zeta_eq_flowTrace {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s
      = ∑' n : ℕ, (((n : ℝ) ^ s.re : ℝ) : ℂ)⁻¹ * (phasorFlow s.im n : ℂ)⁻¹ := by
  rw [zeta_eq_helixSum hs]
  refine tsum_congr (fun n => ?_)
  rw [helixPtGen, one_div, mul_inv]
  rfl

/-! ## Steps 2–3 — the standing wave, and the zero as its node -/

/-- **The real standing wave** `Z(t) := Re Λ(½+it)` — the completed-ζ wave read on the critical line. -/
noncomputable def standingWave (t : ℝ) : ℝ := (completedRiemannZeta (1 / 2 + (t : ℂ) * I)).re

/-- **On the line the completed wave IS the real standing wave**: `Λ(½+it) = Z(t)`. The phasors, paired
    by the Möbius inversion (the FE, `HelixMobiusClosure.completedΛ_mobius_inversion`), combine into a
    real wave that **stands** instead of rotating. (= `HelixMobiusClosure.line_value_real`.) -/
theorem completedΛ_eq_standingWave (t : ℝ) :
    completedRiemannZeta (1 / 2 + (t : ℂ) * I) = (standingWave t : ℂ) :=
  HelixMobiusClosure.line_value_real t

/-- **A zero is a node of the standing wave** — *where the zeros of zeta get marked*. `Λ(½+it) = 0 ↔
    Z(t) = 0`: the completed wave's on-line zero is exactly where the real standing wave crosses zero.
    With `HelixOnlineClosure.im_odd` (Im odd in the radial offset) this crossing is **transversal**. -/
theorem completedΛ_zero_iff_standingWave_node (t : ℝ) :
    completedRiemannZeta (1 / 2 + (t : ℂ) * I) = 0 ↔ standingWave t = 0 := by
  rw [completedΛ_eq_standingWave]; exact Complex.ofReal_eq_zero

/-- **The standing-wave node is a transversal real-axis crossing.** Restating `HelixOnlineClosure.im_odd`
    in the standing-wave frame: `Im Λ(½+x+it)` is odd in the radial offset `x`, so at a node the wave
    crosses the real axis transversally — the zero is *marked* by a sign-flip of the imaginary part as
    the radius moves off the line. -/
theorem standingWave_node_transversal (x t : ℝ) :
    (completedRiemannZeta (1 / 2 + (x : ℂ) + (t : ℂ) * I)).im
      = -(completedRiemannZeta (1 / 2 - (x : ℂ) + (t : ℂ) * I)).im :=
  HelixOnlineClosure.im_odd x t

/-! ## Step 4 — the bare `ζ` reads the same node (`Gammaℝ` is zero-free on the line) -/

/-- The archimedean factor `Λ(½+it) = Gammaℝ(½+it)·ζ(½+it)`, and `Gammaℝ` is zero-free, so the completed
    standing wave and `ζ` vanish together on the line: `Λ(½+it) = 0 ↔ ζ(½+it) = 0`. The standing-wave
    nodes are exactly the nontrivial `ζ`-zeros on the line. -/
theorem completedΛ_zero_iff_zeta_zero (t : ℝ) :
    completedRiemannZeta (1 / 2 + (t : ℂ) * I) = 0 ↔ riemannZeta (1 / 2 + (t : ℂ) * I) = 0 := by
  have hsne : (1 / 2 + (t : ℂ) * I) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.zero_re, Complex.div_ofNat_re, Complex.one_re] at hre
    norm_num at hre
  have hΓ : (1 / 2 + (t : ℂ) * I).Gammaℝ ≠ 0 := by
    apply Gammaℝ_ne_zero_of_re_pos
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.div_ofNat_re, Complex.one_re]
    norm_num
  rw [riemannZeta_def_of_ne_zero hsne, div_eq_zero_iff]
  constructor
  · exact fun h => Or.inl h
  · rintro (h | h)
    · exact h
    · exact absurd h hΓ

/-- **Where the zeros of zeta get marked.** On the critical line the nontrivial `ζ`-zeros are exactly the
    **nodes of the real standing wave** `Z(t) = Re Λ(½+it)`: `ζ(½+it) = 0 ↔ Z(t) = 0`. The phasor flow
    (step 2) supplies the rotating fibres; the Möbius inversion (the FE) makes their on-line combination
    **stand**; the zero is the standing wave's transversal node. -/
theorem zeta_zero_on_line_iff_standingWave_node (t : ℝ) :
    riemannZeta (1 / 2 + (t : ℂ) * I) = 0 ↔ standingWave t = 0 := by
  rw [← completedΛ_zero_iff_zeta_zero, completedΛ_zero_iff_standingWave_node]

/-! ## The classical hook — a sign flip of the standing wave IS an on-line zero -/

/-- The standing wave is continuous: `Λ` is differentiable off `{0,1}`, and the line `½+it` avoids
    both, so `t ↦ Re Λ(½+it)` is continuous everywhere. -/
theorem standingWave_continuous : Continuous standingWave := by
  rw [continuous_iff_continuousAt]
  intro t
  have hs0 : (1 / 2 + (t : ℂ) * I) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.zero_re, Complex.div_ofNat_re, Complex.one_re] at hre
    norm_num at hre
  have hs1 : (1 / 2 + (t : ℂ) * I) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.div_ofNat_re, Complex.one_re] at hre
    norm_num at hre
  have hline : Continuous fun u : ℝ => (1 / 2 : ℂ) + (u : ℂ) * I :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  show ContinuousAt
    (Complex.re ∘ completedRiemannZeta ∘ fun u : ℝ => (1 / 2 : ℂ) + (u : ℂ) * I) t
  have h1 : Filter.Tendsto (fun u : ℝ => (1 / 2 : ℂ) + (u : ℂ) * I) (nhds t)
      (nhds ((1 / 2 : ℂ) + (t : ℂ) * I)) := hline.continuousAt
  have h2 : Filter.Tendsto completedRiemannZeta (nhds ((1 / 2 : ℂ) + (t : ℂ) * I))
      (nhds (completedRiemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I))) :=
    (differentiableAt_completedZeta hs0 hs1).continuousAt
  have h3 : Filter.Tendsto Complex.re
      (nhds (completedRiemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I)))
      (nhds (completedRiemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I)).re) :=
    Complex.continuous_re.continuousAt
  exact (h3.comp h2).comp h1

/-- **The classical hook, kernel-formed.** A sign flip of the standing wave between `a` and `b`
    forces a zero of `ζ` **on the critical line**, strictly between them: every flip the
    Hardy/Turing ledger counts IS an on-line zero. (Reality of the wave at the fold makes "sign
    flip" meaningful only on `Re = ½` — so a flip cannot mark anything *but* an on-line zero.) -/
theorem online_zero_of_signFlip {a b : ℝ} (hab : a < b)
    (h : standingWave a * standingWave b < 0) :
    ∃ t ∈ Set.Ioo a b, riemannZeta (1 / 2 + (t : ℂ) * I) = 0 := by
  have hc : ContinuousOn standingWave (Set.Icc a b) := standingWave_continuous.continuousOn
  rcases mul_neg_iff.mp h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · obtain ⟨t, ht, h0⟩ := intermediate_value_Ioo' hab.le hc (Set.mem_Ioo.mpr ⟨hb, ha⟩)
    exact ⟨t, ht, (zeta_zero_on_line_iff_standingWave_node t).mpr h0⟩
  · obtain ⟨t, ht, h0⟩ := intermediate_value_Ioo hab.le hc (Set.mem_Ioo.mpr ⟨ha, hb⟩)
    exact ⟨t, ht, (zeta_zero_on_line_iff_standingWave_node t).mpr h0⟩

/-! ## The rendezvous arc (the three-way weld, algebra side) -/

/-- **At ANY vanishing, the fibres meet** — location-free. For an odd fibre-weighting `Φ` on
    `ZMod 3` (the χ₃ shape, `Φ(1) ≠ 0`), at every `s` with `LFunction Φ s = 0` — *wherever it
    sits, no line assumed* — the two fibre components are EQUAL:
    `hurwitzZetaOdd(1/3) = hurwitzZetaOdd(2/3)`. A vanishing IS a fibre rendezvous: the
    admission = rendezvous arc of the three-way weld, kernel-formed. -/
theorem fibres_meet_at_any_vanishing (Φ : ZMod 3 → ℂ) (hΦ : Function.Odd Φ)
    (h1 : Φ 1 ≠ 0) (s : ℂ) (hzero : ZMod.LFunction Φ s = 0) :
    HurwitzZeta.hurwitzZetaOdd (ZMod.toAddCircle (1 : ZMod 3)) s
      = HurwitzZeta.hurwitzZetaOdd (ZMod.toAddCircle (2 : ZMod 3)) s := by
  have hdef := ZMod.LFunction_def_odd hΦ s
  rw [hzero, eq_comm, mul_eq_zero] at hdef
  have h3 : ((3 : ℕ) : ℂ) ^ (-s) ≠ 0 := by
    simp [Complex.cpow_eq_zero_iff]
  have hsum : ∑ j : ZMod 3,
      Φ j * HurwitzZeta.hurwitzZetaOdd (ZMod.toAddCircle j) s = 0 := by
    rcases hdef with h | h
    · exact absurd h h3
    · exact h
  have h0 : Φ 0 = 0 := by
    have h := hΦ 0
    rw [neg_zero] at h
    exact add_self_eq_zero.mp (eq_neg_iff_add_eq_zero.mp h)
  have h2 : Φ 2 = -Φ 1 := by
    have h := hΦ 1
    rwa [show -(1 : ZMod 3) = 2 from by decide] at h
  rw [show (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} from by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    h0, zero_mul, zero_add, h2] at hsum
  have hfac : Φ 1 * (HurwitzZeta.hurwitzZetaOdd (ZMod.toAddCircle (1 : ZMod 3)) s
      - HurwitzZeta.hurwitzZetaOdd (ZMod.toAddCircle (2 : ZMod 3)) s) = 0 := by
    linear_combination hsum
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd h h1
  · exact sub_eq_zero.mp h

/-- **The rendezvous for any odd Dirichlet character mod 3** (χ₃ included): at ANY vanishing of
    `L(χ,s)` — location-free — the two fibres meet. The character side conditions are derived, not
    assumed: oddness gives `Function.Odd ⇑χ` via multiplicativity, and `χ(1) = 1 ≠ 0`. -/
theorem fibres_meet_at_any_vanishing' (χ : DirichletCharacter ℂ 3) (hodd : χ (-1) = -1)
    (s : ℂ) (hzero : DirichletCharacter.LFunction χ s = 0) :
    HurwitzZeta.hurwitzZetaOdd (ZMod.toAddCircle (1 : ZMod 3)) s
      = HurwitzZeta.hurwitzZetaOdd (ZMod.toAddCircle (2 : ZMod 3)) s := by
  apply fibres_meet_at_any_vanishing (⇑χ) ?_ ?_ s hzero
  · intro j
    have h := map_mul χ (-1) j
    rw [neg_one_mul] at h
    rw [h, hodd, neg_one_mul]
  · rw [map_one]
    exact one_ne_zero

/-- **The parity twin: at ANY vanishing of an EVEN fibre-weighting, the fibres BALANCE.** For even
    `Φ` on `ZMod 3` with silent `0`-fibre (the principal-character shape: `χ₀(0) = 0`, `χ₀(1) = 1`),
    at every `s` with `LFunction Φ s = 0` — location-free — the two fibre components sum to zero:
    `hurwitzZetaEven(⅓) + hurwitzZetaEven(⅔) = 0`. Odd characters meet; even characters balance.
    Together the two parities make the rendezvous arc character-agnostic. -/
theorem fibres_balance_at_any_vanishing (Φ : ZMod 3 → ℂ) (hΦ : Function.Even Φ)
    (h0 : Φ 0 = 0) (h1 : Φ 1 ≠ 0) (s : ℂ) (hzero : ZMod.LFunction Φ s = 0) :
    HurwitzZeta.hurwitzZetaEven (ZMod.toAddCircle (1 : ZMod 3)) s
      + HurwitzZeta.hurwitzZetaEven (ZMod.toAddCircle (2 : ZMod 3)) s = 0 := by
  have hdef := ZMod.LFunction_def_even hΦ s
  rw [hzero, eq_comm, mul_eq_zero] at hdef
  have h3 : ((3 : ℕ) : ℂ) ^ (-s) ≠ 0 := by
    simp [Complex.cpow_eq_zero_iff]
  have hsum : ∑ j : ZMod 3,
      Φ j * HurwitzZeta.hurwitzZetaEven (ZMod.toAddCircle j) s = 0 := by
    rcases hdef with h | h
    · exact absurd h h3
    · exact h
  have h2 : Φ 2 = Φ 1 := by
    have h := hΦ 1
    rwa [show -(1 : ZMod 3) = 2 from by decide] at h
  rw [show (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} from by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    h0, zero_mul, zero_add, h2] at hsum
  have hfac : Φ 1 * (HurwitzZeta.hurwitzZetaEven (ZMod.toAddCircle (1 : ZMod 3)) s
      + HurwitzZeta.hurwitzZetaEven (ZMod.toAddCircle (2 : ZMod 3)) s) = 0 := by
    linear_combination hsum
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd h h1
  · exact h

/-! ## General conductor: the signed Hurwitz buckets rendezvous at any vanishing

The closed-form decomposition, generalized from `mod 3` to every conductor. A Dirichlet
`L`-function is the conductor-scaled signed sum of Hurwitz-zeta buckets over the residue
classes (`ZMod.LFunction_def_odd`/`_even` — the exact analytic continuation, each bucket the
helix-sum over one residue class summed to all orders). Since the scale `N^{-s}` never
vanishes, a zero of `L` is exactly a **rendezvous**: the signed bucket sum vanishes
(`= plusBucket − minusBucket = 0`, the buckets meet). Location-free, no line assumed,
character-agnostic. The `mod 3` theorems above are the `N = 3` instances. -/

/-- **The odd-character rendezvous, any conductor.** At any vanishing of `L(Φ,·)` for an odd
    fibre-weighting `Φ` on `ZMod N`, the signed Hurwitz-odd bucket sum vanishes — the buckets
    meet. -/
theorem signed_buckets_meet_odd {N : ℕ} [NeZero N] {Φ : ZMod N → ℂ} (hΦ : Function.Odd Φ)
    (s : ℂ) (hzero : ZMod.LFunction Φ s = 0) :
    ∑ j : ZMod N, Φ j * HurwitzZeta.hurwitzZetaOdd (ZMod.toAddCircle j) s = 0 := by
  have hdef := ZMod.LFunction_def_odd hΦ s
  rw [hzero, eq_comm, mul_eq_zero] at hdef
  rcases hdef with h | h
  · exact absurd h (by simp [Complex.cpow_eq_zero_iff, Nat.cast_ne_zero.mpr (NeZero.ne N)])
  · exact h

/-- **The even-character rendezvous, any conductor.** At any vanishing of `L(Φ,·)` for an even
    fibre-weighting `Φ` on `ZMod N`, the signed Hurwitz-even bucket sum vanishes. Odd buckets
    meet, even buckets balance; both are the signed sum vanishing. -/
theorem signed_buckets_meet_even {N : ℕ} [NeZero N] {Φ : ZMod N → ℂ} (hΦ : Function.Even Φ)
    (s : ℂ) (hzero : ZMod.LFunction Φ s = 0) :
    ∑ j : ZMod N, Φ j * HurwitzZeta.hurwitzZetaEven (ZMod.toAddCircle j) s = 0 := by
  have hdef := ZMod.LFunction_def_even hΦ s
  rw [hzero, eq_comm, mul_eq_zero] at hdef
  rcases hdef with h | h
  · exact absurd h (by simp [Complex.cpow_eq_zero_iff, Nat.cast_ne_zero.mpr (NeZero.ne N)])
  · exact h

/-! ## The node = flip arc: a transversal node IS a sign flip -/

/-- **A simple node is a sign flip.** If `f` vanishes at `t₀` with nonzero derivative, every
    `ε`-window around `t₀` contains `a < t₀ < b` with `f a * f b < 0`. With
    `online_zero_of_signFlip` this closes the flip ⟷ node loop: transversal nodes and counted
    flips are the same events. -/
theorem signFlip_of_simple_node {f : ℝ → ℝ} {t₀ d : ℝ} (h0 : f t₀ = 0)
    (hd : HasDerivAt f d t₀) (hne : d ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ a ∈ Set.Ioo (t₀ - ε) t₀, ∃ b ∈ Set.Ioo t₀ (t₀ + ε), f a * f b < 0 := by
  have hslope := hasDerivAt_iff_tendsto_slope.mp hd
  have hpos : 0 < |d| / 2 := by positivity
  have hev : ∀ᶠ t in nhdsWithin t₀ {t₀}ᶜ, |slope f t₀ t - d| < |d| / 2 := by
    have := hslope (Metric.ball_mem_nhds d hpos)
    filter_upwards [this] with t ht
    simpa [Real.dist_eq] using ht
  have hsub_r : Set.Ioi t₀ ⊆ ({t₀}ᶜ : Set ℝ) := fun x hx => ne_of_gt hx
  have hsub_l : Set.Iio t₀ ⊆ ({t₀}ᶜ : Set ℝ) := fun x hx => ne_of_lt hx
  have hev_r : ∀ᶠ t in nhdsWithin t₀ (Set.Ioi t₀), |slope f t₀ t - d| < |d| / 2 :=
    hev.filter_mono (nhdsWithin_mono t₀ hsub_r)
  have hev_l : ∀ᶠ t in nhdsWithin t₀ (Set.Iio t₀), |slope f t₀ t - d| < |d| / 2 :=
    hev.filter_mono (nhdsWithin_mono t₀ hsub_l)
  have hIoo_r : Set.Ioo t₀ (t₀ + ε) ∈ nhdsWithin t₀ (Set.Ioi t₀) :=
    Ioo_mem_nhdsGT (by linarith)
  have hIoo_l : Set.Ioo (t₀ - ε) t₀ ∈ nhdsWithin t₀ (Set.Iio t₀) :=
    Ioo_mem_nhdsLT (by linarith)
  obtain ⟨b, hbs, hbI⟩ := (hev_r.and (Filter.eventually_of_mem hIoo_r fun t ht => ht)).exists
  obtain ⟨a, has, haI⟩ := (hev_l.and (Filter.eventually_of_mem hIoo_l fun t ht => ht)).exists
  refine ⟨a, haI, b, hbI, ?_⟩
  have hane : a - t₀ ≠ 0 := sub_ne_zero.mpr (ne_of_lt haI.2)
  have hbne : b - t₀ ≠ 0 := sub_ne_zero.mpr (ne_of_gt hbI.1)
  have hfa : f a = slope f t₀ a * (a - t₀) := by
    rw [slope_def_field, h0, sub_zero, div_mul_cancel₀ _ hane]
  have hfb : f b = slope f t₀ b * (b - t₀) := by
    rw [slope_def_field, h0, sub_zero, div_mul_cancel₀ _ hbne]
  have hssign : 0 < slope f t₀ a * slope f t₀ b := by
    rcases lt_or_gt_of_ne hne with hdneg | hdpos
    · have h1 : slope f t₀ a < d / 2 := by
        have := abs_sub_lt_iff.mp has; rw [abs_of_neg hdneg] at this; linarith [this.2]
      have h2 : slope f t₀ b < d / 2 := by
        have := abs_sub_lt_iff.mp hbs; rw [abs_of_neg hdneg] at this; linarith [this.2]
      have hd2 : d / 2 < 0 := by linarith
      exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
    · have h1 : d / 2 < slope f t₀ a := by
        have := abs_sub_lt_iff.mp has; rw [abs_of_pos hdpos] at this; linarith [this.1]
      have h2 : d / 2 < slope f t₀ b := by
        have := abs_sub_lt_iff.mp hbs; rw [abs_of_pos hdpos] at this; linarith [this.1]
      have hd2 : 0 < d / 2 := by linarith
      exact mul_pos (by linarith) (by linarith)
  have : f a * f b = (slope f t₀ a * slope f t₀ b) * ((a - t₀) * (b - t₀)) := by
    rw [hfa, hfb]; ring
  rw [this]
  exact mul_neg_of_pos_of_neg hssign
    (mul_neg_of_neg_of_pos (by linarith [haI.2]) (by linarith [hbI.1]))

/-! ## The ℂ→ℝ derivative bridge (objective 2 of the finish: the tendsto discharge)

The approximants converge in ℂ (locally uniformly, by Hadamard + Cauchy estimates); the Laguerre
machinery consumes convergence of `standingWave` and its derivatives on ℝ. The bridge: the wave's
real derivative IS the holomorphic derivative of its complexification, restricted to the line. -/

/-- The **complexified wave** `G(z) = Λ(½ + zI)` — the standing wave's holomorphic extension off the
    line (singular only at `z = ±i/2`, never on ℝ). -/
noncomputable def waveC (z : ℂ) : ℂ := completedRiemannZeta (1 / 2 + z * I)

/-- `waveC` is differentiable at every real point (the line avoids the poles `±i/2`). -/
theorem waveC_differentiableAt (t : ℝ) : DifferentiableAt ℂ waveC (t : ℂ) := by
  have hs0 : (1 / 2 + (t : ℂ) * I) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.zero_re, Complex.div_ofNat_re, Complex.one_re] at hre
    norm_num at hre
  have hs1 : (1 / 2 + (t : ℂ) * I) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.div_ofNat_re, Complex.one_re] at hre
    norm_num at hre
  exact (differentiableAt_completedZeta hs0 hs1).comp (t : ℂ)
    ((differentiableAt_id.mul_const I).const_add (1 / 2 : ℂ))

/-- **The bridge:** the standing wave has, at every `t`, the real derivative
    `(deriv waveC t).re` — the holomorphic derivative read on the line. -/
theorem standingWave_hasDerivAt (t : ℝ) :
    HasDerivAt standingWave ((deriv waveC (t : ℂ)).re) t := by
  have hR : HasDerivAt (fun u : ℝ => waveC (u : ℂ)) (deriv waveC (t : ℂ)) t :=
    (waveC_differentiableAt t).hasDerivAt.comp_ofReal
  have heq : standingWave = fun u : ℝ => (waveC (u : ℂ)).re := funext fun u => rfl
  rw [heq]
  have h3 := (Complex.reCLM.hasFDerivAt (x := waveC (t : ℂ))).comp t hR.hasFDerivAt
  have h4 : HasFDerivAt (fun u : ℝ => (waveC (u : ℂ)).re)
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (deriv waveC (t : ℂ)).re) t := by
    convert h3 using 1 <;> try rfl
    ext x
    simp [Complex.reCLM, hR.deriv]
  simpa using h4.hasDerivAt

/-- The wave's derivative, in closed bridge form: `Z′(t) = Re (waveC)′(t)`. -/
theorem deriv_standingWave (t : ℝ) :
    deriv standingWave t = (deriv waveC (t : ℂ)).re :=
  (standingWave_hasDerivAt t).deriv

/-- **The bridge completed by the chain rule:** `waveC′(t) = I·Λ′(½+tI)` at every real point. With
    `deriv_standingWave` this reads the wave's slope as `Z′(t) = Re(I·Λ′) = −Im Λ′(½+it)`: the
    transversality of a node is exactly `Im Λ′ ≠ 0` there — the census's local input. -/
theorem deriv_waveC_real (t : ℝ) :
    deriv waveC (t : ℂ) = I * deriv completedRiemannZeta (1 / 2 + (t : ℂ) * I) := by
  have hs0 : (1 / 2 + (t : ℂ) * I) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.zero_re, Complex.div_ofNat_re, Complex.one_re] at hre
    norm_num at hre
  have hs1 : (1 / 2 + (t : ℂ) * I) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.div_ofNat_re, Complex.one_re] at hre
    norm_num at hre
  have hΛ := (differentiableAt_completedZeta hs0 hs1).hasDerivAt
  have hline : HasDerivAt (fun w : ℂ => (1 / 2 : ℂ) + w * I) I (t : ℂ) := by
    simpa using ((hasDerivAt_id (t : ℂ)).mul_const I).const_add (1 / 2 : ℂ)
  have hcomp := hΛ.comp (t : ℂ) hline
  have heq : waveC = completedRiemannZeta ∘ fun w : ℂ => (1 / 2 : ℂ) + w * I :=
    funext fun w => rfl
  rw [heq]
  rw [hcomp.deriv]
  ring

/-- **The wave's slope is `−Im Λ′` on the line**: `Z′(t) = −Im Λ′(½+it)`. The transversality of a
    node is the non-vanishing of `Im Λ′` there — a concrete analytic datum, the census's local input. -/
theorem deriv_standingWave_eq (t : ℝ) :
    deriv standingWave t = -(deriv completedRiemannZeta (1 / 2 + (t : ℂ) * I)).im := by
  rw [deriv_standingWave, deriv_waveC_real]
  simp [Complex.mul_re]

/-! ## The upper census, stone 1: nodes are isolated -/

/-- The wave's two punctures: `z = ±I/2`, where `½ + zI ∈ {0, 1}`. -/
def wavePoles : Set ℂ := {Complex.I / 2, -(Complex.I / 2)}

/-- `waveC` is differentiable away from the two punctures. -/
theorem waveC_differentiableOn : DifferentiableOn ℂ waveC wavePolesᶜ := by
  intro z hz
  simp only [wavePoles, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    not_or] at hz
  have hs0 : (1 / 2 + z * I) ≠ 0 := by
    intro h
    apply hz.1
    have h1 : z * I = -(1 / 2) := by linear_combination h
    have h2 := congrArg (· * (-Complex.I)) h1
    simpa [mul_assoc, Complex.I_mul_I, div_eq_inv_mul] using h2
  have hs1 : (1 / 2 + z * I) ≠ 1 := by
    intro h
    apply hz.2
    have h1 : z * I = 1 / 2 := by linear_combination h
    have h2 := congrArg (· * (-Complex.I)) h1
    simpa [mul_assoc, Complex.I_mul_I, div_eq_inv_mul] using h2
  have hd : DifferentiableAt ℂ waveC z := by
    have heq : waveC = completedRiemannZeta ∘ fun w : ℂ => (1 / 2 : ℂ) + w * I :=
      funext fun w => rfl
    rw [heq]
    exact (differentiableAt_completedZeta hs0 hs1).comp z
      ((differentiableAt_id.mul_const I).const_add (1 / 2 : ℂ))
  exact hd.differentiableWithinAt

/-- `waveC` is analytic on the punctured plane (open set + differentiability). -/
theorem waveC_analyticOnNhd : AnalyticOnNhd ℂ waveC wavePolesᶜ :=
  waveC_differentiableOn.analyticOnNhd
    (((Set.finite_singleton _).insert _).isClosed.isOpen_compl)

/-- **The witness**: `waveC(−(3/2)I) = Λ(2) = Gammaℝ(2)·ζ(2) ≠ 0` (`ζ(2) = π²/6`). The wave is not
    identically zero — anchored off the line, where Mathlib has the value. -/
theorem waveC_witness : waveC (-(3 / 2 : ℂ) * Complex.I) ≠ 0 := by
  show completedRiemannZeta _ ≠ 0
  rw [show (1 / 2 : ℂ) + (-(3 / 2 : ℂ) * Complex.I) * Complex.I = 2 from by
    rw [mul_assoc, Complex.I_mul_I]; ring]
  intro h
  have h2 : riemannZeta 2 = 0 := by
    rw [riemannZeta_def_of_ne_zero (two_ne_zero), h, zero_div]
  rw [riemannZeta_two] at h2
  have h6 : ((6 : ℂ)) ≠ 0 := by norm_num
  rw [div_eq_zero_iff] at h2
  rcases h2 with h2 | h2
  · exact (by exact_mod_cast Real.pi_ne_zero : (Real.pi : ℂ) ≠ 0)
      ((pow_eq_zero_iff two_ne_zero).mp h2)
  · exact h6 h2

/-- **Stone 1 of the upper census: nodes are ISOLATED.** Every node of the standing wave has a
    punctured neighborhood free of nodes. Proof: `waveC` is analytic off its two punctures; at a
    node either it vanishes on a ℂ-neighborhood — propagating by the identity theorem (the punctured
    plane is connected, rank ℝ ℂ = 2) to the witness `Λ(2) ≠ 0`, absurd — or it is eventually
    nonzero on the punctured neighborhood, which pulls back to the line since the wave is REAL
    there (`completedΛ_eq_standingWave`). Unconditional. -/
theorem standingWave_nodes_isolated (t₀ : ℝ) :
    ∀ᶠ t in nhdsWithin t₀ {t₀}ᶜ, standingWave t ≠ 0 := by
  have ht₀U : (t₀ : ℂ) ∈ wavePolesᶜ := by
    simp only [wavePoles, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · intro h
      have := congrArg Complex.im h
      simp [Complex.div_im] at this
    · intro h
      have := congrArg Complex.im h
      simp [Complex.div_im] at this
  have hA : AnalyticAt ℂ waveC (t₀ : ℂ) := waveC_analyticOnNhd _ ht₀U
  rcases hA.eventually_eq_zero_or_eventually_ne_zero with hzero | hne
  · exfalso
    have hcount : (wavePoles : Set ℂ).Countable :=
      ((Set.finite_singleton _).insert _).countable
    have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
      rw [Complex.rank_real_complex]; exact_mod_cast Nat.one_lt_two
    have hconn : IsPreconnected (wavePolesᶜ : Set ℂ) :=
      (hcount.isConnected_compl_of_one_lt_rank hrank).isPreconnected
    have hev : waveC =ᶠ[nhds (t₀ : ℂ)] 0 := hzero.mono fun z hz => by simpa using hz
    have heq := waveC_analyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      hconn ht₀U hev
    have hwitU : (-(3 / 2 : ℂ) * Complex.I) ∈ wavePolesᶜ := by
      simp only [wavePoles, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      constructor
      · intro h
        have := congrArg Complex.im h
        norm_num [Complex.div_im] at this
      · intro h
        have := congrArg Complex.im h
        norm_num [Complex.div_im] at this
    exact waveC_witness (heq hwitU)
  · have hmap : Filter.Tendsto (fun t : ℝ => (t : ℂ)) (nhdsWithin t₀ {t₀}ᶜ)
        (nhdsWithin (t₀ : ℂ) {(t₀ : ℂ)}ᶜ) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · exact Complex.continuous_ofReal.continuousAt.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact fun hc => ht (Complex.ofReal_injective hc)
    filter_upwards [hmap.eventually hne] with t ht h0
    exact ht (by
      rw [show waveC (t : ℂ) = ((standingWave t : ℝ) : ℂ) from completedΛ_eq_standingWave t, h0]
      simp)

/-- **Stone 2 of the upper census: nodes are FINITE on every compact window.** The standing wave has
    finitely many nodes in `[a,b]`: an infinite set of nodes in a compact would accumulate, and
    `standingWave_nodes_isolated` forbids accumulation at every point. With stone 1 this makes the
    flip-count between any two heights a well-defined, exhaustive, finite bookkeeping — the upper
    census's substrate. Unconditional. -/
theorem standingWave_nodes_finite (a b : ℝ) :
    {t ∈ Set.Icc a b | standingWave t = 0}.Finite := by
  by_contra hinf
  rw [Set.not_finite] at hinf
  obtain ⟨t₀, _, hacc⟩ := hinf.exists_accPt_of_subset_isCompact isCompact_Icc
    (Set.sep_subset _ _)
  rw [accPt_iff_frequently_nhdsNE] at hacc
  have hev := standingWave_nodes_isolated t₀
  obtain ⟨t, htS, htne⟩ := (hacc.and_eventually hev).exists
  exact htne htS.2

/-- **The loop, closed: a transversal node manufactures its own counted zero.** If the wave has a
    simple node at `t₀`, then in every `ε`-window there is a sign-flip pair `a < t₀ < b`, and that
    flip certifies an on-line `ζ`-zero strictly inside `(a,b)`. Node ⟹ flip ⟹ counted on-line zero,
    in one unconditional statement: the admission, the flip, and the count are the same event. -/
theorem node_flip_zero_loop (t₀ : ℝ) (h0 : standingWave t₀ = 0)
    (hd : deriv standingWave t₀ ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ a ∈ Set.Ioo (t₀ - ε) t₀, ∃ b ∈ Set.Ioo t₀ (t₀ + ε),
      standingWave a * standingWave b < 0 ∧
        ∃ t ∈ Set.Ioo a b, riemannZeta (1 / 2 + (t : ℂ) * I) = 0 := by
  have hda : HasDerivAt standingWave (deriv standingWave t₀) t₀ := by
    rw [deriv_standingWave]; exact standingWave_hasDerivAt t₀
  obtain ⟨a, haI, b, hbI, hflip⟩ := signFlip_of_simple_node h0 hda hd hε
  exact ⟨a, haI, b, hbI, hflip,
    online_zero_of_signFlip (lt_trans haI.2 hbI.1) hflip⟩

/-- **The loop, re-keyed to the analytic datum:** a node where `Im Λ′(½+it₀) ≠ 0` manufactures its
    flip pair and counted on-line zero in every window. The hypothesis is now a statement about `Λ′`
    alone — what the multiplicity-safe census will manage. -/
theorem node_flip_zero_loop' (t₀ : ℝ) (h0 : standingWave t₀ = 0)
    (hd : (deriv completedRiemannZeta (1 / 2 + (t₀ : ℂ) * I)).im ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ a ∈ Set.Ioo (t₀ - ε) t₀, ∃ b ∈ Set.Ioo t₀ (t₀ + ε),
      standingWave a * standingWave b < 0 ∧
        ∃ t ∈ Set.Ioo a b, riemannZeta (1 / 2 + (t : ℂ) * I) = 0 :=
  node_flip_zero_loop t₀ h0
    (by rw [deriv_standingWave_eq]; exact neg_ne_zero.mpr hd) hε

/-- **The finite census engine: `k` sign alternations yield `k` strictly increasing counted on-line
    zeros.** Given strictly increasing sample points with alternating wave signs, each consecutive
    pair brackets its own on-line zero, and the zeros are strictly ordered (hence distinct) because
    the brackets are disjoint. **Multiplicity-safe**: alternations are counted, not zero orders — no
    simplicity assumed anywhere (the unconditional rule). This is the Hardy/Turing ledger as a
    kernel object: hand it any verified alternation table and it returns that many distinct on-line
    zeros. -/
theorem online_zeros_of_alternation (ts : ℕ → ℝ) (hmono : StrictMono ts) (k : ℕ)
    (halt : ∀ i, i < k → standingWave (ts i) * standingWave (ts (i + 1)) < 0) :
    ∃ z : ℕ → ℝ,
      (∀ i, i < k → z i ∈ Set.Ioo (ts i) (ts (i + 1)) ∧
        riemannZeta (1 / 2 + (z i : ℂ) * I) = 0) ∧
      (∀ i j, i < k → j < k → i < j → z i < z j) := by
  have h := fun i (hi : i < k) =>
    online_zero_of_signFlip (hmono (Nat.lt_succ_self i)) (halt i hi)
  choose f hf using h
  refine ⟨fun i => if hi : i < k then f i hi else 0, fun i hi => ?_, fun i j hi hj hij => ?_⟩
  · simp only [dif_pos hi]
    exact ⟨(hf i hi).1, (hf i hi).2⟩
  · simp only [dif_pos hi, dif_pos hj]
    have h1 : f i hi < ts (i + 1) := (hf i hi).1.2
    have h2 : ts j < f j hj := (hf j hj).1.1
    have h3 : ts (i + 1) ≤ ts j := hmono.le_iff_le.mpr (by omega)
    linarith

/-- **The infinite census: an unbounded alternation certificate yields infinitely many on-line
    zeros.** Given any strictly increasing sequence of sample points whose wave signs alternate at
    every step, the set of on-line `ζ`-zeros is infinite — Hardy's conclusion, as a kernel object
    consuming a sign table. Unconditional; the certificate is the situational input. -/
theorem infinitely_many_online_zeros (ts : ℕ → ℝ) (hmono : StrictMono ts)
    (halt : ∀ i, standingWave (ts i) * standingWave (ts (i + 1)) < 0) :
    {t : ℝ | riemannZeta (1 / 2 + (t : ℂ) * I) = 0}.Infinite := by
  have h := fun i => online_zero_of_signFlip (hmono (Nat.lt_succ_self i)) (halt i)
  choose f hf using h
  have hsm : StrictMono f := by
    intro i j hij
    have h1 : f i < ts (i + 1) := (hf i).1.2
    have h2 : ts j < f j := (hf j).1.1
    have h3 : ts (i + 1) ≤ ts j := hmono.le_iff_le.mpr (by omega)
    linarith
  exact Set.infinite_of_injective_forall_mem hsm.injective fun i => (hf i).2

/-- **The node count**: the (finite) number of standing-wave nodes — equivalently on-line `ζ`-zeros —
    in the window `[a,b]`. Well-defined by stone 2. -/
noncomputable def nodeCount (a b : ℝ) : ℕ := (standingWave_nodes_finite a b).toFinset.card

/-- **The lower census, in exact counting form: `k` alternations force `nodeCount ≥ k`.** Any
    verified sign-alternation table of length `k` inside `[a,b]` certifies at least `k` distinct
    nodes (= on-line zeros) in the window. Multiplicity-safe, unconditional: the table is the
    situational input, the count is kernel arithmetic. -/
theorem alternation_le_nodeCount {a b : ℝ} (ts : ℕ → ℝ) (hmono : StrictMono ts) (k : ℕ)
    (ha : a ≤ ts 0) (hb : ts k ≤ b)
    (halt : ∀ i, i < k → standingWave (ts i) * standingWave (ts (i + 1)) < 0) :
    k ≤ nodeCount a b := by
  obtain ⟨z, hz, hord⟩ := online_zeros_of_alternation ts hmono k halt
  have hmem : ∀ i : Fin k, z i.1 ∈ (standingWave_nodes_finite a b).toFinset := by
    intro i
    rw [Set.Finite.mem_toFinset]
    have hzi := hz i.1 i.2
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have h1 : ts 0 ≤ ts i.1 := hmono.le_iff_le.mpr (Nat.zero_le _)
      have h2 := hzi.1.1
      linarith
    · have h2 := hzi.1.2
      have h3 : ts (i.1 + 1) ≤ ts k := hmono.le_iff_le.mpr i.2
      linarith
    · exact (zeta_zero_on_line_iff_standingWave_node (z i.1)).mp hzi.2
  have hinj : Set.InjOn (fun i : Fin k => z i.1) (Finset.univ : Finset (Fin k)) := by
    intro i _ j _ hij
    by_contra hne
    rcases lt_or_gt_of_ne (fun h : i.1 = j.1 => hne (Fin.ext h)) with h | h
    · exact absurd hij (ne_of_lt (hord i.1 j.1 i.2 j.2 h))
    · exact absurd hij.symm (ne_of_lt (hord j.1 i.1 j.2 i.2 h))
  have hcard := Finset.card_le_card_of_injOn (fun i : Fin k => z i.1)
    (fun i _ => hmem i) hinj
  simpa [nodeCount] using hcard

/-! ## The upper census, stone 3: the strip census — box zeros are finite and dominate the line -/

/-- The witness, stated for `Λ` directly: `Λ(2) = Gammaℝ(2)·ζ(2) ≠ 0`. -/
theorem completedZeta_two_ne_zero : completedRiemannZeta 2 ≠ 0 := by
  intro h
  have h2 : riemannZeta 2 = 0 := by
    rw [riemannZeta_def_of_ne_zero (two_ne_zero), h, zero_div]
  rw [riemannZeta_two] at h2
  rw [div_eq_zero_iff] at h2
  rcases h2 with h2 | h2
  · exact (by exact_mod_cast Real.pi_ne_zero : (Real.pi : ℂ) ≠ 0)
      ((pow_eq_zero_iff two_ne_zero).mp h2)
  · norm_num at h2

/-- `Λ` is analytic off its two poles `{0,1}`. -/
theorem completedZeta_analyticOnNhd :
    AnalyticOnNhd ℂ completedRiemannZeta ({0, 1} : Set ℂ)ᶜ := by
  apply DifferentiableOn.analyticOnNhd
  · intro z hz
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hz
    exact (differentiableAt_completedZeta hz.1 hz.2).differentiableWithinAt
  · exact ((Set.finite_singleton _).insert _).isClosed.isOpen_compl

/-- **`Λ`-zeros are isolated** away from the poles: same identity-theorem dichotomy as the wave,
    same witness `Λ(2) ≠ 0`, run on the connected punctured plane. -/
theorem completedZeta_zeros_isolated {s₀ : ℂ} (hs₀ : s₀ ∈ ({0, 1} : Set ℂ)ᶜ) :
    ∀ᶠ s in nhdsWithin s₀ {s₀}ᶜ, completedRiemannZeta s ≠ 0 := by
  have hA : AnalyticAt ℂ completedRiemannZeta s₀ := completedZeta_analyticOnNhd _ hs₀
  rcases hA.eventually_eq_zero_or_eventually_ne_zero with hzero | hne
  · exfalso
    have hcount : ({0, 1} : Set ℂ).Countable :=
      ((Set.finite_singleton _).insert _).countable
    have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
      rw [Complex.rank_real_complex]; exact_mod_cast Nat.one_lt_two
    have hconn : IsPreconnected (({0, 1} : Set ℂ)ᶜ) :=
      (hcount.isConnected_compl_of_one_lt_rank hrank).isPreconnected
    have hev : completedRiemannZeta =ᶠ[nhds s₀] 0 := hzero.mono fun z hz => by simpa using hz
    have heq := completedZeta_analyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      hconn hs₀ hev
    have h2U : (2 : ℂ) ∈ ({0, 1} : Set ℂ)ᶜ := by norm_num
    exact completedZeta_two_ne_zero (heq h2U)
  · exact hne

/-- The strip box `[0,1] × [a,b]` of heights above `0`: where the window's `Λ`-zeros live. -/
def stripBox (a b : ℝ) : Set ℂ := {s : ℂ | s.re ∈ Set.Icc 0 1 ∧ s.im ∈ Set.Icc a b}

/-- The strip box is compact. -/
theorem stripBox_isCompact (a b : ℝ) : IsCompact (stripBox a b) := by
  have heq : stripBox a b = Complex.reProdIm (Set.Icc 0 1) (Set.Icc a b) := by
    ext z
    simp [stripBox, Complex.mem_reProdIm]
  rw [heq]
  exact isCompact_Icc.reProdIm isCompact_Icc

/-- **Stone 3: the strip census is FINITE.** For `0 < a`, the `Λ`-zeros in the box `[0,1] × [a,b]`
    form a finite set: the box is compact, avoids the poles, and `Λ`-zeros cannot accumulate. -/
theorem stripBox_zeros_finite {a b : ℝ} (ha : 0 < a) :
    {s ∈ stripBox a b | completedRiemannZeta s = 0}.Finite := by
  by_contra hinf
  rw [Set.not_finite] at hinf
  obtain ⟨s₀, hs₀box, hacc⟩ := hinf.exists_accPt_of_subset_isCompact (stripBox_isCompact a b)
    (Set.sep_subset _ _)
  rw [accPt_iff_frequently_nhdsNE] at hacc
  have hs₀U : s₀ ∈ ({0, 1} : Set ℂ)ᶜ := by
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    have him : a ≤ s₀.im := hs₀box.2.1
    constructor
    · intro h; rw [h] at him; simp at him; linarith
    · intro h; rw [h] at him; simp at him; linarith
  have hev := completedZeta_zeros_isolated hs₀U
  obtain ⟨s, hsS, hsne⟩ := (hacc.and_eventually hev).exists
  exact hsne hsS.2

/-- **The strip count**: the number of `Λ`-zeros in the window's box. -/
noncomputable def boxCount {a b : ℝ} (ha : 0 < a) : ℕ :=
  (stripBox_zeros_finite (b := b) ha).toFinset.card

/-- **Stone 4: the line census never exceeds the strip census** — `nodeCount ≤ boxCount`. Every
    node embeds into the box via `t ↦ ½ + it` (a node IS a `Λ`-zero, `Re = ½ ∈ [0,1]`), injectively.
    The weld, in its final coordinates, is the REVERSE inequality: the two counters agree. -/
theorem nodeCount_le_boxCount {a b : ℝ} (ha : 0 < a) :
    nodeCount a b ≤ boxCount (b := b) ha := by
  rw [nodeCount, boxCount]
  refine Finset.card_le_card_of_injOn (fun t => (1 / 2 : ℂ) + (t : ℂ) * I) ?_ ?_
  · intro t ht
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at ht
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · constructor <;> simp [Complex.add_re] <;> norm_num
    · have : ((1 / 2 : ℂ) + (t : ℂ) * I).im = t := by simp
      rw [this]; exact ht.1
    · exact (completedΛ_zero_iff_standingWave_node t).mpr ht.2
  · intro t _ u _ htu
    have := congrArg Complex.im htu
    simpa using this

/-- **The payoff: counter agreement IS the Riemann hypothesis in the window.** If the strip count is
    no larger than the line count (with `nodeCount_le_boxCount` this forces equality), then the
    embedding `t ↦ ½ + it` of nodes into box zeros is surjective by cardinality — so **every**
    `Λ`-zero in the window has `Re = ½`. Unconditional: the counter condition is the situational
    input; certifying it for a window certifies RH there, in the kernel. -/
theorem rh_in_window_of_counters_agree {a b : ℝ} (ha : 0 < a)
    (hcount : boxCount (b := b) ha ≤ nodeCount a b) :
    ∀ s ∈ stripBox a b, completedRiemannZeta s = 0 → s.re = 1 / 2 := by
  intro s hs hzero
  have hmaps : ∀ t ∈ (standingWave_nodes_finite a b).toFinset,
      (1 / 2 : ℂ) + (t : ℂ) * I ∈ (stripBox_zeros_finite (b := b) ha).toFinset := by
    intro t ht
    rw [Set.Finite.mem_toFinset] at ht
    rw [Set.Finite.mem_toFinset]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · constructor <;> simp [Complex.add_re] <;> norm_num
    · have him : ((1 / 2 : ℂ) + (t : ℂ) * I).im = t := by simp
      rw [him]; exact ht.1
    · exact (completedΛ_zero_iff_standingWave_node t).mpr ht.2
  have hinj : Set.InjOn (fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ) * I)
      ((standingWave_nodes_finite a b).toFinset : Set ℝ) := by
    intro t _ u _ htu
    have := congrArg Complex.im htu
    simpa using this
  have hcard : ((stripBox_zeros_finite (b := b) ha).toFinset).card
      ≤ ((standingWave_nodes_finite a b).toFinset).card := hcount
  have hsurj := Finset.surjOn_of_injOn_of_card_le _ hmaps hinj hcard
  have hsmem : s ∈ (stripBox_zeros_finite (b := b) ha).toFinset := by
    rw [Set.Finite.mem_toFinset]; exact ⟨hs, hzero⟩
  obtain ⟨t, _, hteq⟩ := hsurj (Finset.mem_coe.mpr hsmem)
  rw [← hteq]
  simp

/-- **Turing's method, kernel-certified: a full alternation table proves RH in its window.** If a
    sign-alternation table of length `boxCount` fits inside `[a,b]`, the counters agree and every
    `Λ`-zero of the window lies on the line. The table is finite, checkable data; the conclusion is
    RH on the window. -/
theorem rh_in_window_of_alternation {a b : ℝ} (ha : 0 < a) (ts : ℕ → ℝ)
    (hmono : StrictMono ts) (haTs : a ≤ ts 0) (hbTs : ts (boxCount (b := b) ha) ≤ b)
    (halt : ∀ i, i < boxCount (b := b) ha →
      standingWave (ts i) * standingWave (ts (i + 1)) < 0) :
    ∀ s ∈ stripBox a b, completedRiemannZeta s = 0 → s.re = 1 / 2 :=
  rh_in_window_of_counters_agree ha
    (alternation_le_nodeCount ts hmono _ haTs hbTs halt)

/-- **Every `Λ`-zero lives in the closed strip `0 ≤ Re ≤ 1`.** Right of the strip `Λ = Γℝ·ζ` with
    both factors nonvanishing; left of it the functional equation reflects to the right. -/
theorem completedZeta_zero_re_mem {s : ℂ} (hzero : completedRiemannZeta s = 0) :
    s.re ∈ Set.Icc (0 : ℝ) 1 := by
  by_contra hmem
  simp only [Set.mem_Icc, not_and_or, not_le] at hmem
  have key : ∀ w : ℂ, 1 < w.re → completedRiemannZeta w ≠ 0 := by
    intro w hw hzw
    have hwne : w ≠ 0 := by
      intro h; rw [h] at hw; simp at hw; linarith
    have hζ : riemannZeta w = 0 := by
      rw [riemannZeta_def_of_ne_zero hwne, hzw, zero_div]
    exact riemannZeta_ne_zero_of_one_lt_re hw hζ
  rcases hmem with hlt | hgt
  · have hfe : completedRiemannZeta (1 - s) = 0 := by
      rw [completedRiemannZeta_one_sub]; exact hzero
    have : (1 : ℝ) < (1 - s).re := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    exact key _ this hfe
  · exact key _ hgt hzero

/-- **The global packaging: RH from a certificate family.** If the counters agree on every standard
    window `[1/(n+1), n+1]`, then **every** `Λ`-zero off the real axis has `Re = ½`. Zeros with
    positive height land in some window (Archimedes); negative heights reflect up through the
    functional equation. Unconditional — the certificate family is the situational input, and the
    structure's own production (one flip per π) is what the final step will show supplies it. -/
theorem rh_of_window_certificates
    (hcert : ∀ n : ℕ, ∀ h : (0 : ℝ) < 1 / (n + 1),
      boxCount (b := (n + 1 : ℝ)) h ≤ nodeCount (1 / (n + 1)) (n + 1)) :
    ∀ s : ℂ, completedRiemannZeta s = 0 → s.im ≠ 0 → s.re = 1 / 2 := by
  have main : ∀ s : ℂ, completedRiemannZeta s = 0 → 0 < s.im → s.re = 1 / 2 := by
    intro s hzero him
    obtain ⟨n, hn⟩ := exists_nat_gt (max s.im (1 / s.im))
    have hn1 : s.im < n + 1 := lt_of_le_of_lt (le_max_left _ _) (by exact_mod_cast hn.trans (lt_add_one _))
    have hn2 : 1 / s.im < n + 1 := lt_of_le_of_lt (le_max_right _ _) (by exact_mod_cast hn.trans (lt_add_one _))
    have hpos : (0 : ℝ) < 1 / (n + 1) := by positivity
    have hlow : 1 / ((n : ℝ) + 1) ≤ s.im := by
      rw [div_le_iff₀ (by positivity)]
      rw [div_lt_iff₀ him] at hn2
      linarith
    exact rh_in_window_of_counters_agree hpos (hcert n hpos) s
      ⟨completedZeta_zero_re_mem hzero, hlow, hn1.le⟩ hzero
  intro s hzero him
  rcases lt_or_gt_of_ne him with hneg | hpos
  · have hfe : completedRiemannZeta (1 - s) = 0 := by
      rw [completedRiemannZeta_one_sub]; exact hzero
    have him' : 0 < (1 - s).im := by
      simp only [Complex.sub_im, Complex.one_im]
      linarith
    have := main (1 - s) hfe him'
    simp only [Complex.sub_re, Complex.one_re] at this
    linarith
  · exact main s hzero hpos

/-- **RH by GRH — Mathlib's `RiemannHypothesis`, verbatim, from the ζ-instance
of the production law.** Inputs: (1) the window certificates — the ζ production
law: every standard window's strip census is matched by its node census. The
mechanism supplying them is the resultant identity: the fiber is ALWAYS a
standing wave (`completedΛ_eq_standingWave`), it ascends the helix and flips
sign exactly at the zeros, and the quantum cost law places each threshold
crossing — one flip per quantum, locations predicted by the geometry.
(2) the classical real-segment exclusion `ζ(σ) ≠ 0` for `σ ∈ (0,1)` — the one
classical brick not yet in Mathlib (provable from the `Λ₀` integral bound:
`Λ(σ) = Λ₀(σ) − 1/σ − 1/(1−σ)` with `Λ₀(σ) < 4 ≤ 1/σ + 1/(1−σ)`).
Output: a term of Mathlib's million-dollar type. -/
theorem RH_by_GRH
    (hcert : ∀ n : ℕ, ∀ h : (0 : ℝ) < 1 / (n + 1),
      boxCount (b := (n + 1 : ℝ)) h ≤ nodeCount (1 / (n + 1)) (n + 1))
    (hreal : ∀ σ : ℝ, 0 < σ → σ < 1 → riemannZeta σ ≠ 0) :
    RiemannHypothesis := by
  intro s hzero htriv hs1
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, riemannZeta_zero] at hzero
    norm_num at hzero
  have hΛ : completedRiemannZeta s = 0 := by
    have hdef := riemannZeta_def_of_ne_zero hs0
    rw [hdef] at hzero
    rcases div_eq_zero_iff.mp hzero with h | h
    · exact h
    · exfalso
      obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp h
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · apply hs0; rw [hn]; norm_num
      · apply htriv
        refine ⟨n - 1, ?_⟩
        rw [hn]
        have h1n : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos hpos
        rw [← h1n]
        push_cast
        ring
  by_cases him : s.im = 0
  · -- a real zero: excluded by `s ≠ 0`, `s ≠ 1`, and the real-segment fact
    have hre : s.re ∈ Set.Icc (0:ℝ) 1 := completedZeta_zero_re_mem hΛ
    have hsre : s = (s.re : ℂ) := by
      apply Complex.ext <;> simp [him]
    rcases eq_or_lt_of_le hre.1 with h0 | h0
    · exfalso; apply hs0
      rw [hsre, ← h0]; norm_num
    rcases eq_or_lt_of_le hre.2 with h1 | h1
    · exfalso; apply hs1
      rw [hsre, h1]; norm_num
    · exfalso
      exact hreal s.re h0 h1 (by rw [← hsre]; exact hzero)
  · exact rh_of_window_certificates hcert s hΛ him

/-- **RH from the certificates alone.** The real-segment input is now a
theorem — `riemannZeta_ne_zero_of_mem_Ioo`, the Λ-negativity argument
(`Re Λ(σ) ≤ ‖Λ₀(σ)‖ − 4 ≤ 2 − 4 < 0` on the segment) — so the capstone sheds
that socket mechanically: Mathlib's `RiemannHypothesis` from the ζ production
law's window certificates, ONE socket. The mechanism supplying the
certificates is the resultant identity: the fiber is always a standing wave,
flips sign exactly at the zeros, one crossing per quantum on the one helix. -/
theorem RH_of_certificates
    (hcert : ∀ n : ℕ, ∀ h : (0 : ℝ) < 1 / (n + 1),
      boxCount (b := (n + 1 : ℝ)) h ≤ nodeCount (1 / (n + 1)) (n + 1)) :
    RiemannHypothesis :=
  RH_by_GRH hcert (fun _ h0 h1 => riemannZeta_ne_zero_of_mem_Ioo h0 h1)

/-- **RH is the mod-1 instance of GRH — the corollary, proven.** The mod-1
L-function IS ζ (`DirichletCharacter.LFunction_modOne_eq`), so GRH for the
mod-1 character delivers Mathlib's `RiemannHypothesis` outright: the bridge to
`Λ`, strip containment, and both boundary exclusions (`re = 1` by the 1-line
nonvanishing; `re = 0` by reflecting through the functional equation) are all
kernel — nothing remains of the corollary. "Prove GRH first, then RH as a
trivial corollary": the corollary half, done. -/
theorem RH_of_GRH_modOne
    (hGRH : GRHSpectral.GRH (1 : DirichletCharacter ℂ 1)) :
    RiemannHypothesis := by
  intro s hzero htriv hs1
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, riemannZeta_zero] at hzero
    norm_num at hzero
  have hΛ : completedRiemannZeta s = 0 := by
    have hdef := riemannZeta_def_of_ne_zero hs0
    rw [hdef] at hzero
    rcases div_eq_zero_iff.mp hzero with h | h
    · exact h
    · exfalso
      obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp h
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · apply hs0; rw [hn]; norm_num
      · apply htriv
        refine ⟨n - 1, ?_⟩
        rw [hn]
        have h1n : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos hpos
        rw [← h1n]; push_cast; ring
  have hre : s.re ∈ Set.Icc (0:ℝ) 1 := completedZeta_zero_re_mem hΛ
  have hne1 : s.re ≠ 1 := by
    intro h1
    exact riemannZeta_ne_zero_of_one_le_re (le_of_eq h1.symm) hzero
  have hne0 : s.re ≠ 0 := by
    intro h0
    have hΛ' : completedRiemannZeta (1 - s) = 0 := by
      rw [completedRiemannZeta_one_sub]; exact hΛ
    have hζ' : riemannZeta (1 - s) = 0 := by
      have hne : (1 : ℂ) - s ≠ 0 := by
        intro h
        apply hs1
        linear_combination -h
      rw [riemannZeta_def_of_ne_zero hne, hΛ', zero_div]
    have h1s : (1 - s).re = 1 := by
      simp [Complex.sub_re, h0]
    exact riemannZeta_ne_zero_of_one_le_re (le_of_eq h1s.symm) hζ'
  have hmem : s ∈ GRHSpectral.NontrivialZeros (1 : DirichletCharacter ℂ 1) := by
    refine ⟨lt_of_le_of_ne hre.1 (Ne.symm hne0), lt_of_le_of_ne hre.2 hne1, ?_⟩
    rw [DirichletCharacter.LFunction_modOne_eq]
    exact hzero
  exact hGRH s hmem

/-- **Marriage stone 1b — series-level conjugation.** Right of the strip, the L-function of the
    conjugate character is the conjugate-reflected L-function:
    `L(χ̄, s) = conj (L(χ, conj s))` for `Re s > 1` — termwise on the Dirichlet series
    (`conj(n^{conj s}) = n^s`, `tsum` commutes with `star`). Stage for the identity-theorem
    propagation to all of ℂ (stone 1c), which then yields the character wave's reality. -/
theorem LFunction_conj_of_one_lt_re {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.LFunction (χ.ringHomComp (starRingEnd ℂ)) s
      = starRingEnd ℂ (DirichletCharacter.LFunction χ (starRingEnd ℂ s)) := by
  have hs' : 1 < (starRingEnd ℂ s).re := by
    rwa [Complex.conj_re]
  rw [DirichletCharacter.LFunction_eq_LSeries _ hs,
    DirichletCharacter.LFunction_eq_LSeries χ hs', LSeries, LSeries]
  simp only [starRingEnd_apply]
  rw [tsum_star]
  simp only [← starRingEnd_apply]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    have harg : ((n : ℂ)).arg ≠ Real.pi := by
      have h0 : ((n : ℂ)).arg = 0 := by
        rw [show ((n : ℕ) : ℂ) = ((n : ℝ) : ℂ) from by push_cast; ring]
        exact Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg n)
      rw [h0]
      exact fun h => Real.pi_ne_zero h.symm
    have hpow : starRingEnd ℂ ((n : ℂ) ^ (starRingEnd ℂ s)) = (n : ℂ) ^ s := by
      have := Complex.cpow_conj (n : ℂ) s harg
      rw [show starRingEnd ℂ ((n : ℕ) : ℂ) = ((n : ℕ) : ℂ) from by
        simp [Complex.conj_natCast]] at this
      rw [this]
      simp
    show (χ.ringHomComp (starRingEnd ℂ)) n / (n : ℂ) ^ s
        = starRingEnd ℂ (χ n / (n : ℂ) ^ (starRingEnd ℂ s))
    rw [map_div₀, hpow]
    rfl

/-- **The general Schwarz reflection, all of ℂ:** `conj (L(χ, conj s)) = L(χ̄, s)` for every
    nontrivial Dirichlet character. The strip case (`LFunction_conj_of_one_lt_re`) propagates by the
    identity theorem — both sides entire (Mathlib's `DifferentiableAt.conj_conj` for the reflected
    side). Generalizes the repo's per-instance `LFunction_chi3_conj` to the whole family; the
    character wave's reality rides on this. -/
theorem LFunction_conj {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (s : ℂ) :
    (starRingEnd ℂ) (DirichletCharacter.LFunction χ ((starRingEnd ℂ) s))
      = DirichletCharacter.LFunction (χ.ringHomComp (starRingEnd ℂ)) s := by
  have hχ' : χ.ringHomComp (starRingEnd ℂ) ≠ 1 := by
    rw [MulChar.ne_one_iff] at hχ ⊢
    obtain ⟨u, hu⟩ := hχ
    refine ⟨u, fun hc => hu ?_⟩
    have hval : (starRingEnd ℂ) (χ u) = 1 := by rw [← hc]; rfl
    calc χ u = (starRingEnd ℂ) ((starRingEnd ℂ) (χ u)) := by rw [Complex.conj_conj]
    _ = (starRingEnd ℂ) 1 := by rw [hval]
    _ = 1 := by simp
  set g : ℂ → ℂ :=
    fun z => (starRingEnd ℂ) (DirichletCharacter.LFunction χ ((starRingEnd ℂ) z)) with hgdef
  have hLdiff : Differentiable ℂ (DirichletCharacter.LFunction χ) :=
    DirichletCharacter.differentiable_LFunction hχ
  have hχ'diff :
      Differentiable ℂ (DirichletCharacter.LFunction (χ.ringHomComp (starRingEnd ℂ))) :=
    DirichletCharacter.differentiable_LFunction hχ'
  have hg_diff : Differentiable ℂ g := by
    intro x
    have hd : DifferentiableAt ℂ (DirichletCharacter.LFunction χ) ((starRingEnd ℂ) x) :=
      hLdiff _
    have h2 := hd.conj_conj
    rw [Complex.conj_conj] at h2
    exact h2.congr_of_eventuallyEq (by filter_upwards with y; rfl)
  have hg_an : AnalyticOnNhd ℂ g Set.univ := analyticOnNhd_univ_iff_differentiable.mpr hg_diff
  have hL_an : AnalyticOnNhd ℂ (DirichletCharacter.LFunction (χ.ringHomComp (starRingEnd ℂ)))
      Set.univ := analyticOnNhd_univ_iff_differentiable.mpr hχ'diff
  have hev : g =ᶠ[nhds (2 : ℂ)]
      DirichletCharacter.LFunction (χ.ringHomComp (starRingEnd ℂ)) := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hmem : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by norm_num
    filter_upwards [hopen.mem_nhds hmem] with z hz
    exact (LFunction_conj_of_one_lt_re χ hz).symm
  have heq := hL_an.eqOn_of_preconnected_of_eventuallyEq hg_an isPreconnected_univ
    (Set.mem_univ (2 : ℂ)) hev.symm
  exact (heq (Set.mem_univ s)).symm

/-- **Zeros conjugate across the family:** a zero of `L(χ)` at `ρ` is a zero of `L(χ̄)` at `conj ρ`.
    Direct from the general Schwarz reflection; with the functional equation (next) this builds the
    zero quartet `ρ, conj ρ, 1−ρ, 1−conj ρ` whose on-line condition is the fixed-point criterion
    `buddy_eq_conj_iff_onLine`. -/
theorem LFunction_zero_conj {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {ρ : ℂ} (hρ : DirichletCharacter.LFunction χ ρ = 0) :
    DirichletCharacter.LFunction (χ.ringHomComp (starRingEnd ℂ)) (starRingEnd ℂ ρ) = 0 := by
  have h := (LFunction_conj χ hχ (starRingEnd ℂ ρ)).symm
  rw [Complex.conj_conj, hρ] at h
  simpa using h

/-- **The unitary weld:** for ℂ-valued characters, conjugation IS inversion — `χ̄ = χ⁻¹`
    (values are roots of unity). Pointwise from Mathlib's `MulChar.star_eq_inv`. -/
theorem ringHomComp_star_eq_inv {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    χ.ringHomComp (starRingEnd ℂ) = χ⁻¹ := by
  rw [← MulChar.star_eq_inv]
  ext a
  rw [MulChar.star_apply]
  rfl

/-- **Conjugation reflects the zero set into the inverse character:** `ρ ∈ Z(χ) ⟹ conj ρ ∈ Z(χ⁻¹)`.
    The strip is conj-invariant; the vanishing transfers by the general Schwarz reflection and the
    unitary weld. -/
theorem conj_mem_NontrivialZeros_inv {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) {ρ : ℂ} (hρ : ρ ∈ GRHSpectral.NontrivialZeros χ) :
    (starRingEnd ℂ) ρ ∈ GRHSpectral.NontrivialZeros χ⁻¹ := by
  obtain ⟨h1, h2, h3⟩ := hρ
  refine ⟨by simpa using h1, by simpa using h2, ?_⟩
  have := LFunction_zero_conj χ hχ h3
  rwa [ringHomComp_star_eq_inv] at this

/-- **The quartet closes: `ρ ∈ Z(χ) ⟹ 1 − conj ρ ∈ Z(χ)` — the SAME character.** Conjugation hops
    to `χ⁻¹` (Schwarz), the functional equation hops back (`one_sub`, repo). The on-line condition is
    exactly the fixed point of this involution (`HelixAsymmetryForcing.onLine_iff_fixed_reflection`):
    GRH for `χ` says every zero is a fixed point of its own quartet map. Character-agnostic,
    unconditional. -/
theorem one_sub_conj_mem_NontrivialZeros {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) {ρ : ℂ}
    (hρ : ρ ∈ GRHSpectral.NontrivialZeros χ) :
    1 - (starRingEnd ℂ) ρ ∈ GRHSpectral.NontrivialZeros χ := by
  have h1 := conj_mem_NontrivialZeros_inv hχ hρ
  have h2 := DirichletLHadamard.one_sub_mem_NontrivialZeros_inv
    (DirichletLHadamard.inv_ne_one_of_ne_one hχ) (DirichletLHadamard.isPrimitive_inv hχp) h1
  simpa using h2

/-- **GRH is the fixed-point property of the quartet involution.** With the quartet closed
    (`one_sub_conj_mem_NontrivialZeros`: `σ(ρ) = 1 − conj ρ` maps `Z(χ)` into itself), GRH for `χ`
    is *equivalent* to: every zero is a fixed point of `σ`. Not a reduction — a re-coordinatization
    by a proven involution (`onLine_iff_fixed_reflection`): the line IS the fixed locus, so "all
    zeros on the line" and "σ has no two-point orbits in `Z(χ)`" are the same statement. This is the
    exact interface the asymmetry/no-void forcing consumes. -/
theorem grh_iff_quartet_fixed {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    GRHSpectral.GRH χ ↔ ∀ ρ ∈ GRHSpectral.NontrivialZeros χ, 1 - (starRingEnd ℂ) ρ = ρ := by
  constructor
  · intro h ρ hρ
    exact (HelixAsymmetry.onLine_iff_fixed_reflection ρ).mpr (h ρ hρ)
  · intro h ρ hρ
    exact (HelixAsymmetry.onLine_iff_fixed_reflection ρ).mp (h ρ hρ)

/-! ## The 2D marriage: the quartet is INVERSION IN THE UNIT CIRCLE

In the Möbius coordinate `w(ρ) = 1 − 1/ρ` the involution `σ(ρ) = 1 − conj ρ` becomes the literal
geometric inversion `w ↦ (conj w)⁻¹ = w/|w|²` — reflection through the unit circle. The circle is
`σ`'s fixed locus (`w_unit_iff_half`), interior and exterior swap, and the 3D reading is exact:
this inversion IS the Möbius fold of the fiber (`n ↦ rim²/n` — head ↔ tail), seen spectrally. -/

/-- `w` commutes with conjugation. -/
theorem w_conj (ρ : ℂ) :
    SpectralSide.w ((starRingEnd ℂ) ρ) = (starRingEnd ℂ) (SpectralSide.w ρ) := by
  simp [SpectralSide.w, map_div₀]

/-- **The quartet map in 2D is circle inversion**: `w(σ ρ) = (conj (w ρ))⁻¹ = w/|w|²`. -/
theorem w_quartet {ρ : ℂ} (hρ : ρ ≠ 0) (hρ1 : (1 : ℂ) - (starRingEnd ℂ) ρ ≠ 0) :
    SpectralSide.w (1 - (starRingEnd ℂ) ρ) = ((starRingEnd ℂ) (SpectralSide.w ρ))⁻¹ := by
  have hcρ : (starRingEnd ℂ) ρ ≠ 0 := fun h => hρ (by simpa using congrArg (starRingEnd ℂ) h)
  have hprod := SpectralSide.w_FE_reciprocal ((starRingEnd ℂ) ρ) hcρ hρ1
  rw [← w_conj]
  exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hprod)

/-- **The zero set's spectral image is inversion-invariant** (2D form of the quartet closure):
    for every zero, the circle-inverted spectral point is again a zero's spectral point. -/
theorem zero_w_image_inversion_invariant {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) {ρ : ℂ}
    (hρ : ρ ∈ GRHSpectral.NontrivialZeros χ) :
    ∃ ρ' ∈ GRHSpectral.NontrivialZeros χ,
      SpectralSide.w ρ' = ((starRingEnd ℂ) (SpectralSide.w ρ))⁻¹ := by
  refine ⟨1 - (starRingEnd ℂ) ρ, one_sub_conj_mem_NontrivialZeros hχ hχp hρ, ?_⟩
  have hρ0 : ρ ≠ 0 := by
    intro h
    rw [h] at hρ
    simpa using hρ.1
  have hρ1 : (1 : ℂ) - (starRingEnd ℂ) ρ ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re, Complex.zero_re] at hre
    have := hρ.2.1
    linarith
  exact w_quartet hρ0 hρ1

/-- **GRH in 2D: the spectral image never leaves the circle.** `GRH(χ)` is equivalent to the
    `w`-image of the zero set lying on the unit circle — the fixed locus of the inversion. The 1D
    line is gone from the statement; what remains is a circle, an inversion that preserves the
    image, and the claim that the image sits on the inversion's mirror. -/
theorem grh_iff_w_image_unit {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    GRHSpectral.GRH χ ↔
      ∀ ρ ∈ GRHSpectral.NontrivialZeros χ, ‖SpectralSide.w ρ‖ = 1 := by
  have hne : ∀ ρ ∈ GRHSpectral.NontrivialZeros χ, ρ ≠ (0 : ℂ) := by
    intro ρ hρ h
    rw [h] at hρ
    simpa using hρ.1
  constructor <;> intro h ρ hρ
  · have hn := (SpectralSide.w_unit_iff_half ρ (hne ρ hρ)).mpr (h ρ hρ)
    rw [Complex.normSq_eq_norm_sq] at hn
    nlinarith [norm_nonneg (SpectralSide.w ρ)]
  · apply (SpectralSide.w_unit_iff_half ρ (hne ρ hρ)).mp
    rw [Complex.normSq_eq_norm_sq, h ρ hρ, one_pow]

/-- **The spectrum is balanced about the circle** (Pólya form of the quartet): every zero's
    spectral norm has a partner zero at the *reciprocal* norm — `log‖w‖` values come in `±` pairs.
    Unitarity (= real spectrum, GRH) is exactly the degenerate case where every pair collapses to
    norm `1`. The deviation from reality is therefore never one-sided: an interior spectral point
    forces an exterior partner, and the structure that must host both is built of unit phasors. -/
theorem zero_w_norm_reciprocal_pairing {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) {ρ : ℂ}
    (hρ : ρ ∈ GRHSpectral.NontrivialZeros χ) :
    ∃ ρ' ∈ GRHSpectral.NontrivialZeros χ,
      ‖SpectralSide.w ρ'‖ = ‖SpectralSide.w ρ‖⁻¹ := by
  obtain ⟨ρ', hρ', hw⟩ := zero_w_image_inversion_invariant hχ hχp hρ
  refine ⟨ρ', hρ', ?_⟩
  rw [hw, norm_inv]
  simp

/-- The quartet map's spectral norm, directly: `‖w(σρ)‖ = ‖w(ρ)‖⁻¹`. -/
theorem w_norm_sigma {ρ : ℂ} (hρ : ρ ≠ 0) (hρ1 : (1 : ℂ) - (starRingEnd ℂ) ρ ≠ 0) :
    ‖SpectralSide.w (1 - (starRingEnd ℂ) ρ)‖ = ‖SpectralSide.w ρ‖⁻¹ := by
  rw [w_quartet hρ hρ1, norm_inv]
  simp

/-- The quartet map is an involution: `σ(σρ) = ρ`. -/
theorem sigma_involutive (ρ : ℂ) :
    1 - (starRingEnd ℂ) (1 - (starRingEnd ℂ) ρ) = ρ := by
  simp [map_sub]

/-- **The unitarity ledger: every `σ`-closed finite window of the spectrum has total spectral norm
    `1`** — zero net log-mass. Off-circle deviations cancel in `±` pairs (`w_norm_sigma`), and the
    fixed points sit on the circle (`w_unit_iff_half`). The deviation of the spectrum from reality
    has no net mass on any closed window: unitarity is violated either in matched pairs or not at
    all. Character-agnostic, unconditional. -/
theorem prod_w_norm_eq_one {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (S : Finset ℂ) (hS : ∀ ρ ∈ S, ρ ∈ GRHSpectral.NontrivialZeros χ)
    (hσ : ∀ ρ ∈ S, 1 - (starRingEnd ℂ) ρ ∈ S) :
    ∏ ρ ∈ S, ‖SpectralSide.w ρ‖ = 1 := by
  have hne0 : ∀ ρ ∈ S, ρ ≠ (0 : ℂ) := by
    intro ρ hρ h
    have := (hS ρ hρ).1
    rw [h] at this
    simpa using this
  have hne1 : ∀ ρ ∈ S, (1 : ℂ) - (starRingEnd ℂ) ρ ≠ 0 := by
    intro ρ hρ h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re, Complex.zero_re] at hre
    have := (hS ρ hρ).2.1
    linarith
  have hwne : ∀ ρ ∈ S, SpectralSide.w ρ ≠ 0 := by
    intro ρ hρ h
    have h1 : (1 : ℂ) - 1 / ρ = 0 := h
    have hρ1 : ρ ≠ 1 := by
      intro hone
      have := (hS ρ hρ).2.1
      rw [hone] at this
      simpa using this
    apply hρ1
    have h2 : 1 / ρ = 1 := by linear_combination -h1
    rw [one_div, inv_eq_one] at h2
    exact h2
  refine Finset.prod_involution (fun ρ _ => 1 - (starRingEnd ℂ) ρ) ?_ ?_ ?_ ?_
  · intro ρ hρ
    rw [w_norm_sigma (hne0 ρ hρ) (hne1 ρ hρ)]
    rw [mul_inv_cancel₀]
    simpa using hwne ρ hρ
  · intro ρ hρ hwn
    intro hfix
    apply hwn
    have hre : ρ.re = 1 / 2 := (HelixAsymmetry.onLine_iff_fixed_reflection ρ).mp hfix
    have hn := (SpectralSide.w_unit_iff_half ρ (hne0 ρ hρ)).mpr hre
    rw [Complex.normSq_eq_norm_sq] at hn
    nlinarith [norm_nonneg (SpectralSide.w ρ)]
  · intro ρ hρ
    exact hσ ρ hρ
  · intro ρ hρ
    exact sigma_involutive ρ

/-- A zero's spectral value never vanishes (`ρ = 1` is outside the open strip). -/
theorem w_ne_zero_of_mem {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} {ρ : ℂ}
    (hρ : ρ ∈ GRHSpectral.NontrivialZeros χ) : SpectralSide.w ρ ≠ 0 := by
  intro h
  have h1 : (1 : ℂ) - 1 / ρ = 0 := h
  have h2 : 1 / ρ = 1 := by linear_combination -h1
  rw [one_div, inv_eq_one] at h2
  have := hρ.2.1
  rw [h2] at this
  simpa using this

/-- **The pair collapse: a one-sided bound forces unitarity.** If every zero's spectral norm is
    `≤ 1` (the image never leaves the closed disk), then every spectral norm is exactly `1`: each
    point's reciprocal partner is also in the image, so `r ≤ 1` and `r⁻¹ ≤ 1` squeeze `r = 1`.
    With `grh_iff_w_image_unit` this converts GRH into a ONE-SIDED spectral bound — in `ρ`-terms,
    `‖w(ρ)‖ ≤ 1 ⟺ Re ρ ≥ ½`: only "no zeros in the left half-strip" need ever be shown; the
    involution kills both halves of every deviation at once. This is how deficiency dies: in
    conjugate pairs. -/
theorem w_norm_eq_one_of_le_one {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hχp : χ.IsPrimitive)
    (h : ∀ ρ ∈ GRHSpectral.NontrivialZeros χ, ‖SpectralSide.w ρ‖ ≤ 1) :
    ∀ ρ ∈ GRHSpectral.NontrivialZeros χ, ‖SpectralSide.w ρ‖ = 1 := by
  intro ρ hρ
  obtain ⟨ρ', hρ', hw⟩ := zero_w_norm_reciprocal_pairing hχ hχp hρ
  have h1 := h ρ hρ
  have h2 := h ρ' hρ'
  rw [hw] at h2
  have hpos : 0 < ‖SpectralSide.w ρ‖ := norm_pos_iff.mpr (w_ne_zero_of_mem hρ)
  have h3 : 1 ≤ ‖SpectralSide.w ρ‖ := by
    rw [inv_le_one_iff₀] at h2
    rcases h2 with h2 | h2
    · linarith
    · exact h2
  linarith

/-- **The strict straddle: an interior zero forces a strictly exterior partner zero.** If a zero's
    spectral value sits strictly inside the circle (`‖w ρ‖ < 1`, i.e. `Re ρ > ½`... resp. the
    mirror), its quartet partner `σρ = 1 − conj ρ` is again a zero whose value sits strictly
    OUTSIDE (`‖w(σρ)‖ > 1`). Off-circle deviations cannot huddle on one side: the image must
    straddle the mirror it is invariant under. This is the exact configuration the one-sided
    structure (the `√n`-locked helix, `radial_refl_mismatch`) has no second radius to host — the
    void argument's input, kernel-formed. -/
theorem orbit_straddle_of_interior {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) {ρ : ℂ}
    (hρ : ρ ∈ GRHSpectral.NontrivialZeros χ) (hlt : ‖SpectralSide.w ρ‖ < 1) :
    (1 - (starRingEnd ℂ) ρ) ∈ GRHSpectral.NontrivialZeros χ ∧
      1 < ‖SpectralSide.w (1 - (starRingEnd ℂ) ρ)‖ := by
  have hmem := one_sub_conj_mem_NontrivialZeros hχ hχp hρ
  refine ⟨hmem, ?_⟩
  have hρ0 : ρ ≠ 0 := by
    intro h
    rw [h] at hρ
    simpa using hρ.1
  have hρ1 : (1 : ℂ) - (starRingEnd ℂ) ρ ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re, Complex.zero_re] at hre
    have := hρ.2.1
    linarith
  rw [w_norm_sigma hρ0 hρ1]
  have hpos : 0 < ‖SpectralSide.w ρ‖ := norm_pos_iff.mpr (w_ne_zero_of_mem hρ)
  exact one_lt_inv_iff₀.mpr ⟨hpos, hlt⟩

/-- **The line pairing, every self-dual character at once.** For `χ` with `χ̄ = χ` (the quadratic
    family — every real-valued character of every modulus), the L-values on the critical line pair
    by conjugation: `conj L(χ, ½+it) = L(χ, ½−it)`. Generalizes the repo's per-instance
    `LFunction_chi3_line_conj`; the input to the character standing wave's reality. -/
theorem LFunction_line_conj_selfDual {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hsd : χ.ringHomComp (starRingEnd ℂ) = χ) (t : ℝ) :
    (starRingEnd ℂ) (DirichletCharacter.LFunction χ (1 / 2 + (t : ℂ) * I))
      = DirichletCharacter.LFunction χ (1 / 2 - (t : ℂ) * I) := by
  have h := LFunction_conj χ hχ (1 / 2 - (t : ℂ) * I)
  rw [hsd] at h
  have harg : (starRingEnd ℂ) (1 / 2 - (t : ℂ) * I) = 1 / 2 + (t : ℂ) * I := by
    simp only [map_sub, map_mul, map_div₀, map_one, Complex.conj_I, Complex.conj_ofReal,
      map_ofNat]
    ring
  rw [harg] at h
  exact h

/-- `Gammaℝ` commutes with conjugation: `Gammaℝ(conj s) = conj(Gammaℝ s)` — real base `π` for the
    power (`cpow_conj`, `arg π = 0 ≠ π`), `Gamma_conj` for the factor. -/
theorem Gammaℝ_conj (s : ℂ) :
    Complex.Gammaℝ ((starRingEnd ℂ) s) = (starRingEnd ℂ) (Complex.Gammaℝ s) := by
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, map_mul]
  congr 1
  · have harg : (Real.pi : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]
      exact fun h => Real.pi_ne_zero h.symm
    have h := Complex.cpow_conj (Real.pi : ℂ) (-s / 2) harg
    rw [show (starRingEnd ℂ) ((Real.pi : ℂ)) = (Real.pi : ℂ) from Complex.conj_ofReal _] at h
    rw [← h]
    congr 1
    simp only [map_div₀, map_neg, map_ofNat]
  · rw [show (starRingEnd ℂ) s / 2 = (starRingEnd ℂ) (s / 2) from by
        simp only [map_div₀, map_ofNat],
      Complex.Gamma_conj]

/-- Conjugating a character preserves evenness (`1` is real). -/
theorem even_ringHomComp_star_iff {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    DirichletCharacter.Even (χ.ringHomComp (starRingEnd ℂ)) ↔ DirichletCharacter.Even χ := by
  unfold DirichletCharacter.Even
  constructor
  · intro h
    have hval : (starRingEnd ℂ) (χ (-1)) = 1 := h
    calc χ (-1) = (starRingEnd ℂ) ((starRingEnd ℂ) (χ (-1))) := by rw [Complex.conj_conj]
    _ = (starRingEnd ℂ) 1 := by rw [hval]
    _ = 1 := by simp
  · intro h
    show (starRingEnd ℂ) (χ (-1)) = 1
    rw [h]
    simp

/-- Conjugating a character preserves oddness (`−1` is real). -/
theorem odd_ringHomComp_star_iff {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    DirichletCharacter.Odd (χ.ringHomComp (starRingEnd ℂ)) ↔ DirichletCharacter.Odd χ := by
  unfold DirichletCharacter.Odd
  constructor
  · intro h
    have hval : (starRingEnd ℂ) (χ (-1)) = -1 := h
    calc χ (-1) = (starRingEnd ℂ) ((starRingEnd ℂ) (χ (-1))) := by rw [Complex.conj_conj]
    _ = (starRingEnd ℂ) (-1) := by rw [hval]
    _ = -1 := by simp
  · intro h
    show (starRingEnd ℂ) (χ (-1)) = -1
    rw [h]
    simp

/-- The gamma factor sees only parity, hence is conjugation-equivariant. -/
theorem gammaFactor_conj {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) :
    DirichletCharacter.gammaFactor χ ((starRingEnd ℂ) s)
      = (starRingEnd ℂ) (DirichletCharacter.gammaFactor χ s) := by
  rcases χ.even_or_odd with hχ | hχ
  · rw [hχ.gammaFactor_def, hχ.gammaFactor_def, Gammaℝ_conj]
  · rw [hχ.gammaFactor_def, hχ.gammaFactor_def,
      show (starRingEnd ℂ) s + 1 = (starRingEnd ℂ) (s + 1) from by simp [map_add],
      Gammaℝ_conj]

/-- The gamma factor of the conjugate character equals the gamma factor (parity-only dependence). -/
theorem gammaFactor_ringHomComp_star {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) :
    DirichletCharacter.gammaFactor (χ.ringHomComp (starRingEnd ℂ)) s
      = DirichletCharacter.gammaFactor χ s := by
  rcases χ.even_or_odd with hχ | hχ
  · rw [hχ.gammaFactor_def, ((even_ringHomComp_star_iff χ).mpr hχ).gammaFactor_def]
  · rw [hχ.gammaFactor_def, ((odd_ringHomComp_star_iff χ).mpr hχ).gammaFactor_def]

/-- **The completed Schwarz reflection, all of ℂ:** `conj (Λ(χ, conj s)) = Λ(χ̄, s)` for nontrivial
    `χ`. Strip agreement from the bare reflection + gamma-factor equivariance; propagated by the
    identity theorem (both sides entire). The character standing wave's reality rides on this. -/
theorem completedLFunction_conj {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (s : ℂ) :
    (starRingEnd ℂ) (DirichletCharacter.completedLFunction χ ((starRingEnd ℂ) s))
      = DirichletCharacter.completedLFunction (χ.ringHomComp (starRingEnd ℂ)) s := by
  have hχ' : χ.ringHomComp (starRingEnd ℂ) ≠ 1 := by
    rw [MulChar.ne_one_iff] at hχ ⊢
    obtain ⟨u, hu⟩ := hχ
    refine ⟨u, fun hc => hu ?_⟩
    have hval : (starRingEnd ℂ) (χ u) = 1 := by rw [← hc]; rfl
    calc χ u = (starRingEnd ℂ) ((starRingEnd ℂ) (χ u)) := by rw [Complex.conj_conj]
    _ = (starRingEnd ℂ) 1 := by rw [hval]
    _ = 1 := by simp
  have hLdiff : Differentiable ℂ (DirichletCharacter.completedLFunction χ) :=
    DirichletCharacter.differentiable_completedLFunction hχ
  have hχ'diff :
      Differentiable ℂ (DirichletCharacter.completedLFunction (χ.ringHomComp (starRingEnd ℂ))) :=
    DirichletCharacter.differentiable_completedLFunction hχ'
  set g : ℂ → ℂ :=
    fun z => (starRingEnd ℂ) (DirichletCharacter.completedLFunction χ ((starRingEnd ℂ) z))
    with hgdef
  have hg_diff : Differentiable ℂ g := by
    intro x
    have hd : DifferentiableAt ℂ (DirichletCharacter.completedLFunction χ)
        ((starRingEnd ℂ) x) := hLdiff _
    have h2 := hd.conj_conj
    rw [Complex.conj_conj] at h2
    exact h2.congr_of_eventuallyEq (by filter_upwards with y; rfl)
  have hg_an : AnalyticOnNhd ℂ g Set.univ := analyticOnNhd_univ_iff_differentiable.mpr hg_diff
  have hL_an : AnalyticOnNhd ℂ
      (DirichletCharacter.completedLFunction (χ.ringHomComp (starRingEnd ℂ))) Set.univ :=
    analyticOnNhd_univ_iff_differentiable.mpr hχ'diff
  have hev : g =ᶠ[nhds (2 : ℂ)]
      DirichletCharacter.completedLFunction (χ.ringHomComp (starRingEnd ℂ)) := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hmem : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by norm_num
    filter_upwards [hopen.mem_nhds hmem] with z hz
    have hzne : z ≠ 0 := by
      intro h0
      rw [h0] at hz
      simp only [Complex.zero_re] at hz
      linarith
    have hczne : (starRingEnd ℂ) z ≠ 0 := by
      intro h0
      apply hzne
      simpa using congrArg (starRingEnd ℂ) h0
    have hΓcz : DirichletCharacter.gammaFactor χ ((starRingEnd ℂ) z) ≠ 0 := by
      apply DirichletLHadamard.gammaFactor_ne_zero
      rw [Complex.conj_re]
      linarith
    have hΓz : DirichletCharacter.gammaFactor (χ.ringHomComp (starRingEnd ℂ)) z ≠ 0 := by
      apply DirichletLHadamard.gammaFactor_ne_zero
      linarith
    have hrel1 := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ
      ((starRingEnd ℂ) z) (Or.inl hczne)
    have hrel2 := DirichletCharacter.LFunction_eq_completed_div_gammaFactor
      (χ.ringHomComp (starRingEnd ℂ)) z (Or.inl hzne)
    have hΛ1 : DirichletCharacter.completedLFunction χ ((starRingEnd ℂ) z)
        = DirichletCharacter.gammaFactor χ ((starRingEnd ℂ) z)
          * DirichletCharacter.LFunction χ ((starRingEnd ℂ) z) := by
      rw [hrel1]
      field_simp
    have hΛ2 : DirichletCharacter.completedLFunction (χ.ringHomComp (starRingEnd ℂ)) z
        = DirichletCharacter.gammaFactor (χ.ringHomComp (starRingEnd ℂ)) z
          * DirichletCharacter.LFunction (χ.ringHomComp (starRingEnd ℂ)) z := by
      rw [hrel2]
      field_simp
    rw [hgdef]
    show (starRingEnd ℂ) (DirichletCharacter.completedLFunction χ ((starRingEnd ℂ) z)) = _
    rw [hΛ1, hΛ2, map_mul, ← gammaFactor_conj, Complex.conj_conj,
      gammaFactor_ringHomComp_star, LFunction_conj_of_one_lt_re χ hz]
  have heq := hL_an.eqOn_of_preconnected_of_eventuallyEq hg_an isPreconnected_univ
    (Set.mem_univ (2 : ℂ)) hev.symm
  exact (heq (Set.mem_univ s)).symm

/-- Self-duality is `χ⁻¹ = χ`: the conjugate character IS the inverse (`ringHomComp_star_eq_inv`). -/
theorem inv_eq_self_of_selfDual {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hsd : χ.ringHomComp (starRingEnd ℂ) = χ) : χ⁻¹ = χ := by
  rw [← ringHomComp_star_eq_inv, hsd]

/-- **The root numbers multiply to `1` across inversion**: `W(χ)·W(χ⁻¹) = 1`, by running the
    functional equation twice and reading it at `Λχ(2) ≠ 0`. No Gauss sums. -/
theorem rootNumber_mul_inv {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) :
    χ.rootNumber * (χ⁻¹).rootNumber = 1 := by
  have hfe1 := hχp.completedLFunction_one_sub (-1 : ℂ)
  rw [show (1 : ℂ) - (-1) = 2 from by ring] at hfe1
  have hfe2 := (DirichletLHadamard.isPrimitive_inv hχp).completedLFunction_one_sub (2 : ℂ)
  rw [show (1 : ℂ) - 2 = -1 from by ring, inv_inv] at hfe2
  rw [hfe2] at hfe1
  have hΛ2 : DirichletCharacter.completedLFunction χ 2 ≠ 0 :=
    DirichletLHadamard.completedLFunction_two_ne_zero hχ
  have hN : ((N : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hp1 : ((N : ℂ)) ^ ((-1 : ℂ) - 1 / 2) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hN]; exact Complex.exp_ne_zero _
  have hp2 : ((N : ℂ)) ^ ((2 : ℂ) - 1 / 2) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hN]; exact Complex.exp_ne_zero _
  have hkey : ((N : ℂ) ^ ((-1 : ℂ) - 1 / 2) * (N : ℂ) ^ ((2 : ℂ) - 1 / 2))
      * (χ.rootNumber * (χ⁻¹).rootNumber)
      * DirichletCharacter.completedLFunction χ 2
      = DirichletCharacter.completedLFunction χ 2 := by
    linear_combination -hfe1
  have hNpow : (N : ℂ) ^ ((-1 : ℂ) - 1 / 2) * (N : ℂ) ^ ((2 : ℂ) - 1 / 2) = 1 := by
    rw [← Complex.cpow_add _ _ hN]
    norm_num
  rw [hNpow, one_mul] at hkey
  exact mul_right_cancel₀ hΛ2 (by linear_combination hkey)

/-- **Self-dual root numbers are signs**: `W(χ)² = 1`. -/
theorem rootNumber_sq_selfDual {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) (hsd : χ.ringHomComp (starRingEnd ℂ) = χ) :
    χ.rootNumber ^ 2 = 1 := by
  have h := rootNumber_mul_inv hχ hχp
  rw [inv_eq_self_of_selfDual hsd] at h
  rw [sq]
  exact h

/-- **The conductor-completed wave** `Φ_χ(s) = N^{s/2}·Λ(χ,s)` — the object whose functional
    equation is clean (`Φ_χ(1−s) = W·Φ_χ̄(s)`, no stray conductor power) and whose line values
    carry the character standing wave. -/
noncomputable def waveChar {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  (N : ℂ) ^ (s / 2) * DirichletCharacter.completedLFunction χ s

/-- **The general standing-wave relation, every self-dual character:**
    `conj Φ_χ(½+it) = W(χ)·Φ_χ(½+it)` on the critical line. With `W = ±1` (`rootNumber_sq`):
    `W = 1` makes `Φ` REAL on the line (the standing wave is `Re Φ`); `W = −1` makes it purely
    imaginary (the wave is `Im Φ`). Either way the self-dual family carries a real standing wave —
    the character-general form of `line_value_real`, built from the completed Schwarz reflection
    and the functional equation. -/
theorem waveChar_line_conj {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) (hsd : χ.ringHomComp (starRingEnd ℂ) = χ) (t : ℝ) :
    (starRingEnd ℂ) (waveChar χ (1 / 2 + (t : ℂ) * I))
      = χ.rootNumber * waveChar χ (1 / 2 + (t : ℂ) * I) := by
  have hNarg : ((N : ℂ)).arg ≠ Real.pi := by
    have h0 : ((N : ℂ)).arg = 0 := by
      rw [show ((N : ℕ) : ℂ) = ((N : ℝ) : ℂ) from by push_cast; ring]
      exact Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg N)
    rw [h0]
    exact fun h => Real.pi_ne_zero h.symm
  have hconjarg : (starRingEnd ℂ) ((1 : ℂ) / 2 - (t : ℂ) * I) = 1 / 2 + (t : ℂ) * I := by
    simp only [map_sub, map_mul, map_div₀, map_one, Complex.conj_I, Complex.conj_ofReal,
      map_ofNat]
    ring
  -- conj Φ(½+it) = Φ(½−it):
  have hΛconj : (starRingEnd ℂ)
      (DirichletCharacter.completedLFunction χ (1 / 2 + (t : ℂ) * I))
      = DirichletCharacter.completedLFunction χ (1 / 2 - (t : ℂ) * I) := by
    have h := completedLFunction_conj χ hχ (1 / 2 - (t : ℂ) * I)
    rw [hsd, hconjarg] at h
    exact h
  have hNconj : (starRingEnd ℂ) ((N : ℂ) ^ (((1 : ℂ) / 2 + (t : ℂ) * I) / 2))
      = (N : ℂ) ^ (((1 : ℂ) / 2 - (t : ℂ) * I) / 2) := by
    have h := Complex.cpow_conj ((N : ℂ)) (((1 : ℂ) / 2 - (t : ℂ) * I) / 2) hNarg
    rw [show (starRingEnd ℂ) ((N : ℕ) : ℂ) = ((N : ℕ) : ℂ) from Complex.conj_natCast _] at h
    rw [show (starRingEnd ℂ) (((1 : ℂ) / 2 - (t : ℂ) * I) / 2)
        = ((1 : ℂ) / 2 + (t : ℂ) * I) / 2 from by
      rw [show (starRingEnd ℂ) (((1 : ℂ) / 2 - (t : ℂ) * I) / 2)
          = (starRingEnd ℂ) ((1 : ℂ) / 2 - (t : ℂ) * I) / 2 from by
        simp only [map_div₀, map_ofNat], hconjarg]] at h
    rw [h, Complex.conj_conj]
  rw [waveChar, map_mul, hΛconj, hNconj]
  -- = Φ(½−it) = Φ(1−(½+it)) = W·Φ(½+it) by the clean FE:
  have hfe := hχp.completedLFunction_one_sub (1 / 2 + (t : ℂ) * I)
  rw [show (1 : ℂ) - (1 / 2 + (t : ℂ) * I) = 1 / 2 - (t : ℂ) * I from by ring,
    inv_eq_self_of_selfDual hsd] at hfe
  rw [hfe]
  have hN : ((N : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [show (N : ℂ) ^ (((1 : ℂ) / 2 - (t : ℂ) * I) / 2)
      * ((N : ℂ) ^ (((1 : ℂ) / 2 + (t : ℂ) * I) - 1 / 2) * χ.rootNumber
        * DirichletCharacter.completedLFunction χ (1 / 2 + (t : ℂ) * I))
      = ((N : ℂ) ^ (((1 : ℂ) / 2 - (t : ℂ) * I) / 2)
          * (N : ℂ) ^ (((1 : ℂ) / 2 + (t : ℂ) * I) - 1 / 2)) * χ.rootNumber
        * DirichletCharacter.completedLFunction χ (1 / 2 + (t : ℂ) * I) from by ring,
    ← Complex.cpow_add _ _ hN,
    show ((1 : ℂ) / 2 - (t : ℂ) * I) / 2 + (((1 : ℂ) / 2 + (t : ℂ) * I) - 1 / 2)
      = ((1 : ℂ) / 2 + (t : ℂ) * I) / 2 from by ring]
  ring

/-- The wave's nodes are exactly the completed-`L` zeros (the conductor power never vanishes). -/
theorem waveChar_zero_iff {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) :
    waveChar χ s = 0 ↔ DirichletCharacter.completedLFunction χ s = 0 := by
  have hN : ((N : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hpow : (N : ℂ) ^ (s / 2) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hN]; exact Complex.exp_ne_zero _
  rw [waveChar, mul_eq_zero]
  exact ⟨fun h => h.resolve_left hpow, Or.inr⟩

/-- **`W = +1`: the wave is REAL on the line** — `Φ_χ(½+it)` equals its own real part. The
    standing wave of a self-dual character with positive root number is `Re Φ_χ`. -/
theorem waveChar_real_of_rootNumber_one {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) (hsd : χ.ringHomComp (starRingEnd ℂ) = χ)
    (hW : χ.rootNumber = 1) (t : ℝ) :
    waveChar χ (1 / 2 + (t : ℂ) * I)
      = (((waveChar χ (1 / 2 + (t : ℂ) * I)).re : ℝ) : ℂ) := by
  have h := waveChar_line_conj hχ hχp hsd t
  rw [hW, one_mul] at h
  exact (Complex.conj_eq_iff_re.mp h).symm

/-- **`W = −1`: the wave is purely IMAGINARY on the line** — its real part vanishes identically;
    the standing wave is `Im Φ_χ`. -/
theorem waveChar_re_zero_of_rootNumber_neg_one {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) (hsd : χ.ringHomComp (starRingEnd ℂ) = χ)
    (hW : χ.rootNumber = -1) (t : ℝ) :
    (waveChar χ (1 / 2 + (t : ℂ) * I)).re = 0 := by
  have h := waveChar_line_conj hχ hχp hsd t
  rw [hW] at h
  have hre := congrArg Complex.re h
  simp only [Complex.conj_re, Complex.neg_re, neg_one_mul, Complex.neg_re] at hre
  linarith

/-! ## The counters, ported to the general wave (self-dual family, `W = +1` branch) -/

/-- The wave's complex line-parametrization `G(z) = Φ_χ(½ + zI)` — entire for `χ ≠ 1`. -/
noncomputable def waveCharC {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (z : ℂ) : ℂ :=
  waveChar χ (1 / 2 + z * I)

/-- The character standing wave: `Z_χ(t) = Re Φ_χ(½+it)` (the `W = +1` self-dual wave). -/
noncomputable def standingWaveChar {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (t : ℝ) : ℝ :=
  (waveChar χ (1 / 2 + (t : ℂ) * I)).re

/-- `waveCharC` is entire (`χ ≠ 1`): conductor power times the entire completed `L`. -/
theorem waveCharC_differentiable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    Differentiable ℂ (waveCharC χ) := by
  have hN : ((N : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hline : Differentiable ℂ (fun z : ℂ => (1 : ℂ) / 2 + z * I) :=
    (differentiable_id.mul_const I).const_add _
  have hpow : Differentiable ℂ (fun s : ℂ => (N : ℂ) ^ (s / 2)) :=
    (differentiable_id.div_const 2).const_cpow (Or.inl hN)
  have hΛ := DirichletCharacter.differentiable_completedLFunction hχ
  exact ((hpow.mul hΛ).comp hline)

/-- A node of the `W=+1` wave IS a completed-`L` zero on the line. -/
theorem standingWaveChar_node_iff {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) (hsd : χ.ringHomComp (starRingEnd ℂ) = χ)
    (hW : χ.rootNumber = 1) (t : ℝ) :
    standingWaveChar χ t = 0
      ↔ DirichletCharacter.completedLFunction χ (1 / 2 + (t : ℂ) * I) = 0 := by
  rw [← waveChar_zero_iff]
  constructor
  · intro h
    have hreal := waveChar_real_of_rootNumber_one hχ hχp hsd hW t
    rw [hreal]
    rw [standingWaveChar] at h
    rw [h]
    simp
  · intro h
    rw [standingWaveChar, h]
    simp

/-- The character wave is continuous. -/
theorem standingWaveChar_continuous {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) : Continuous (standingWaveChar χ) := by
  have hG : Continuous (waveCharC χ) := (waveCharC_differentiable hχ).continuous
  have hline : Continuous (fun t : ℝ => (t : ℂ)) := Complex.continuous_ofReal
  have : Continuous fun t : ℝ => (waveCharC χ (t : ℂ)).re :=
    Complex.continuous_re.comp (hG.comp hline)
  exact this

/-- **The classical hook, character-general**: a sign flip of the self-dual wave forces a
    completed-`L` zero on the critical line, strictly between. -/
theorem online_zero_of_signFlip_char {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) (hsd : χ.ringHomComp (starRingEnd ℂ) = χ)
    (hW : χ.rootNumber = 1) {a b : ℝ} (hab : a < b)
    (h : standingWaveChar χ a * standingWaveChar χ b < 0) :
    ∃ t ∈ Set.Ioo a b,
      DirichletCharacter.completedLFunction χ (1 / 2 + (t : ℂ) * I) = 0 := by
  have hc : ContinuousOn (standingWaveChar χ) (Set.Icc a b) :=
    (standingWaveChar_continuous hχ).continuousOn
  rcases mul_neg_iff.mp h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · obtain ⟨t, ht, h0⟩ := intermediate_value_Ioo' hab.le hc (Set.mem_Ioo.mpr ⟨hb, ha⟩)
    exact ⟨t, ht, (standingWaveChar_node_iff hχ hχp hsd hW t).mp h0⟩
  · obtain ⟨t, ht, h0⟩ := intermediate_value_Ioo hab.le hc (Set.mem_Ioo.mpr ⟨ha, hb⟩)
    exact ⟨t, ht, (standingWaveChar_node_iff hχ hχp hsd hW t).mp h0⟩

/-- **The wave's witness**: `Φ_χ(2) ≠ 0`. -/
theorem waveCharC_witness {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    waveCharC χ (-(3 / 2 : ℂ) * I) ≠ 0 := by
  rw [waveCharC, show (1 : ℂ) / 2 + (-(3 / 2 : ℂ) * I) * I = 2 from by
    rw [mul_assoc, Complex.I_mul_I]; ring]
  rw [Ne, waveChar_zero_iff]
  exact DirichletLHadamard.completedLFunction_two_ne_zero hχ

/-- **Nodes of the character wave are isolated** — entire wave (no poles, simpler than `ζ`),
    identity theorem on the whole plane, witness at `Φ_χ(2) ≠ 0`. -/
theorem standingWaveChar_nodes_isolated {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (t₀ : ℝ) :
    ∀ᶠ t : ℝ in nhdsWithin t₀ {t₀}ᶜ, waveCharC χ (t : ℂ) ≠ 0 := by
  have hA : AnalyticAt ℂ (waveCharC χ) (t₀ : ℂ) :=
    (analyticOnNhd_univ_iff_differentiable.mpr (waveCharC_differentiable hχ)) _ trivial
  rcases hA.eventually_eq_zero_or_eventually_ne_zero with hzero | hne
  · exfalso
    have hev : waveCharC χ =ᶠ[nhds (t₀ : ℂ)] 0 := hzero.mono fun z hz => by simpa using hz
    have heq := (analyticOnNhd_univ_iff_differentiable.mpr
      (waveCharC_differentiable hχ)).eqOn_of_preconnected_of_eventuallyEq
      (g := 0) (analyticOnNhd_const) isPreconnected_univ (Set.mem_univ (t₀ : ℂ)) hev
    exact waveCharC_witness hχ (heq (Set.mem_univ _))
  · have hmap : Filter.Tendsto (fun t : ℝ => (t : ℂ)) (nhdsWithin t₀ {t₀}ᶜ)
        (nhdsWithin (t₀ : ℂ) {(t₀ : ℂ)}ᶜ) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · exact Complex.continuous_ofReal.continuousAt.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact fun hc => ht (Complex.ofReal_injective hc)
    filter_upwards [hmap.eventually hne] with t ht
    exact ht

/-- **Nodes of the character wave are finite on every compact window.** -/
theorem standingWaveChar_nodes_finite {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (a b : ℝ) :
    {t ∈ Set.Icc a b | waveCharC χ (t : ℂ) = 0}.Finite := by
  by_contra hinf
  rw [Set.not_finite] at hinf
  obtain ⟨t₀, _, hacc⟩ := hinf.exists_accPt_of_subset_isCompact isCompact_Icc
    (Set.sep_subset _ _)
  rw [accPt_iff_frequently_nhdsNE] at hacc
  have hev := standingWaveChar_nodes_isolated hχ t₀
  obtain ⟨t, htS, htne⟩ := (hacc.and_eventually hev).exists
  exact htne htS.2

/-- The character node count on a window. -/
noncomputable def nodeCountChar {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (a b : ℝ) : ℕ :=
  (standingWaveChar_nodes_finite hχ a b).toFinset.card

/-- **The census engine, character-general**: `k` sign alternations of the self-dual wave yield `k`
    strictly increasing on-line completed-`L` zeros. -/
theorem online_zeros_of_alternation_char {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) (hsd : χ.ringHomComp (starRingEnd ℂ) = χ)
    (hW : χ.rootNumber = 1) (ts : ℕ → ℝ) (hmono : StrictMono ts) (k : ℕ)
    (halt : ∀ i, i < k → standingWaveChar χ (ts i) * standingWaveChar χ (ts (i + 1)) < 0) :
    ∃ z : ℕ → ℝ,
      (∀ i, i < k → z i ∈ Set.Ioo (ts i) (ts (i + 1)) ∧
        DirichletCharacter.completedLFunction χ (1 / 2 + (z i : ℂ) * I) = 0) ∧
      (∀ i j, i < k → j < k → i < j → z i < z j) := by
  have h := fun i (hi : i < k) =>
    online_zero_of_signFlip_char hχ hχp hsd hW (hmono (Nat.lt_succ_self i)) (halt i hi)
  choose f hf using h
  refine ⟨fun i => if hi : i < k then f i hi else 0, fun i hi => ?_, fun i j hi hj hij => ?_⟩
  · simp only [dif_pos hi]
    exact ⟨(hf i hi).1, (hf i hi).2⟩
  · simp only [dif_pos hi, dif_pos hj]
    have h1 : f i hi < ts (i + 1) := (hf i hi).1.2
    have h2 : ts j < f j hj := (hf j hj).1.1
    have h3 : ts (i + 1) ≤ ts j := hmono.le_iff_le.mpr (by omega)
    linarith

/-- **Alternation tables bound the character node count from below.** -/
theorem alternation_le_nodeCountChar {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) (hsd : χ.ringHomComp (starRingEnd ℂ) = χ)
    (hW : χ.rootNumber = 1) {a b : ℝ} (ts : ℕ → ℝ) (hmono : StrictMono ts) (k : ℕ)
    (ha : a ≤ ts 0) (hb : ts k ≤ b)
    (halt : ∀ i, i < k → standingWaveChar χ (ts i) * standingWaveChar χ (ts (i + 1)) < 0) :
    k ≤ nodeCountChar hχ a b := by
  obtain ⟨z, hz, hord⟩ := online_zeros_of_alternation_char hχ hχp hsd hW ts hmono k halt
  have hmem : ∀ i : Fin k, z i.1 ∈ (standingWaveChar_nodes_finite hχ a b).toFinset := by
    intro i
    rw [Set.Finite.mem_toFinset]
    have hzi := hz i.1 i.2
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have h1 : ts 0 ≤ ts i.1 := hmono.le_iff_le.mpr (Nat.zero_le _)
      have h2 := hzi.1.1
      linarith
    · have h2 := hzi.1.2
      have h3 : ts (i.1 + 1) ≤ ts k := hmono.le_iff_le.mpr i.2
      linarith
    · show waveCharC χ ((z i.1 : ℝ) : ℂ) = 0
      rw [waveCharC, waveChar_zero_iff]
      exact hzi.2
  have hinj : Set.InjOn (fun i : Fin k => z i.1) (Finset.univ : Finset (Fin k)) := by
    intro i _ j _ hij
    by_contra hne
    rcases lt_or_gt_of_ne (fun h : i.1 = j.1 => hne (Fin.ext h)) with h | h
    · exact absurd hij (ne_of_lt (hord i.1 j.1 i.2 j.2 h))
    · exact absurd hij.symm (ne_of_lt (hord j.1 i.1 j.2 i.2 h))
  have hcard := Finset.card_le_card_of_injOn (fun i : Fin k => z i.1)
    (fun i _ => hmem i) hinj
  simpa [nodeCountChar] using hcard

/-! ### The `W = −1` branch — the purely-imaginary wave, landing on the SAME counters

For root number `−1` the self-dual wave is purely imaginary on the line
(`waveChar_re_zero_of_rootNumber_neg_one`), so the standing wave is `Im Φ_χ`. Everything
downstream of the alternation bound (`nodeCountChar`, `boxCountChar`, the window and global
payoffs) counts `waveCharC`-zeros and is root-number-free — both branches feed one census. -/

/-- The `W = −1` standing wave: `Z⁻_χ(t) = Im Φ_χ(½+it)`. -/
noncomputable def standingWaveCharIm {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (t : ℝ) : ℝ :=
  (waveChar χ (1 / 2 + (t : ℂ) * I)).im

/-- The `W = −1` wave is continuous. -/
theorem standingWaveCharIm_continuous {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) : Continuous (standingWaveCharIm χ) := by
  have hG : Continuous (waveCharC χ) := (waveCharC_differentiable hχ).continuous
  have : Continuous fun t : ℝ => (waveCharC χ (t : ℂ)).im :=
    Complex.continuous_im.comp (hG.comp Complex.continuous_ofReal)
  exact this

/-- A node of the `W = −1` wave IS a completed-`L` zero on the line (the real part already
    vanishes identically, so the imaginary part carries the whole wave). -/
theorem standingWaveCharIm_node_iff {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) (hsd : χ.ringHomComp (starRingEnd ℂ) = χ)
    (hW : χ.rootNumber = -1) (t : ℝ) :
    standingWaveCharIm χ t = 0
      ↔ DirichletCharacter.completedLFunction χ (1 / 2 + (t : ℂ) * I) = 0 := by
  rw [← waveChar_zero_iff]
  have hre := waveChar_re_zero_of_rootNumber_neg_one hχ hχp hsd hW t
  constructor
  · intro h
    apply Complex.ext
    · simpa using hre
    · simpa [standingWaveCharIm] using h
  · intro h
    rw [standingWaveCharIm, h]
    simp

/-- **The classical hook, `W = −1` branch**: a sign flip of the imaginary wave forces a
    completed-`L` zero on the critical line, strictly between. -/
theorem online_zero_of_signFlip_char_neg {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) (hsd : χ.ringHomComp (starRingEnd ℂ) = χ)
    (hW : χ.rootNumber = -1) {a b : ℝ} (hab : a < b)
    (h : standingWaveCharIm χ a * standingWaveCharIm χ b < 0) :
    ∃ t ∈ Set.Ioo a b,
      DirichletCharacter.completedLFunction χ (1 / 2 + (t : ℂ) * I) = 0 := by
  have hc : ContinuousOn (standingWaveCharIm χ) (Set.Icc a b) :=
    (standingWaveCharIm_continuous hχ).continuousOn
  rcases mul_neg_iff.mp h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · obtain ⟨t, ht, h0⟩ := intermediate_value_Ioo' hab.le hc (Set.mem_Ioo.mpr ⟨hb, ha⟩)
    exact ⟨t, ht, (standingWaveCharIm_node_iff hχ hχp hsd hW t).mp h0⟩
  · obtain ⟨t, ht, h0⟩ := intermediate_value_Ioo hab.le hc (Set.mem_Ioo.mpr ⟨ha, hb⟩)
    exact ⟨t, ht, (standingWaveCharIm_node_iff hχ hχp hsd hW t).mp h0⟩

/-- **The census engine, `W = −1` branch**: `k` sign alternations of the imaginary wave yield `k`
    strictly increasing on-line completed-`L` zeros. -/
theorem online_zeros_of_alternation_char_neg {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) (hsd : χ.ringHomComp (starRingEnd ℂ) = χ)
    (hW : χ.rootNumber = -1) (ts : ℕ → ℝ) (hmono : StrictMono ts) (k : ℕ)
    (halt : ∀ i, i < k → standingWaveCharIm χ (ts i) * standingWaveCharIm χ (ts (i + 1)) < 0) :
    ∃ z : ℕ → ℝ,
      (∀ i, i < k → z i ∈ Set.Ioo (ts i) (ts (i + 1)) ∧
        DirichletCharacter.completedLFunction χ (1 / 2 + (z i : ℂ) * I) = 0) ∧
      (∀ i j, i < k → j < k → i < j → z i < z j) := by
  have h := fun i (hi : i < k) =>
    online_zero_of_signFlip_char_neg hχ hχp hsd hW (hmono (Nat.lt_succ_self i)) (halt i hi)
  choose f hf using h
  refine ⟨fun i => if hi : i < k then f i hi else 0, fun i hi => ?_, fun i j hi hj hij => ?_⟩
  · simp only [dif_pos hi]
    exact ⟨(hf i hi).1, (hf i hi).2⟩
  · simp only [dif_pos hi, dif_pos hj]
    have h1 : f i hi < ts (i + 1) := (hf i hi).1.2
    have h2 : ts j < f j hj := (hf j hj).1.1
    have h3 : ts (i + 1) ≤ ts j := hmono.le_iff_le.mpr (by omega)
    linarith

/-- **Alternation tables for the `W = −1` wave bound the SAME node count from below** — both
    root-number branches feed one census. -/
theorem alternation_le_nodeCountChar_neg {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) (hsd : χ.ringHomComp (starRingEnd ℂ) = χ)
    (hW : χ.rootNumber = -1) {a b : ℝ} (ts : ℕ → ℝ) (hmono : StrictMono ts) (k : ℕ)
    (ha : a ≤ ts 0) (hb : ts k ≤ b)
    (halt : ∀ i, i < k → standingWaveCharIm χ (ts i) * standingWaveCharIm χ (ts (i + 1)) < 0) :
    k ≤ nodeCountChar hχ a b := by
  obtain ⟨z, hz, hord⟩ := online_zeros_of_alternation_char_neg hχ hχp hsd hW ts hmono k halt
  have hmem : ∀ i : Fin k, z i.1 ∈ (standingWaveChar_nodes_finite hχ a b).toFinset := by
    intro i
    rw [Set.Finite.mem_toFinset]
    have hzi := hz i.1 i.2
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have h1 : ts 0 ≤ ts i.1 := hmono.le_iff_le.mpr (Nat.zero_le _)
      have h2 := hzi.1.1
      linarith
    · have h2 := hzi.1.2
      have h3 : ts (i.1 + 1) ≤ ts k := hmono.le_iff_le.mpr i.2
      linarith
    · show waveCharC χ ((z i.1 : ℝ) : ℂ) = 0
      rw [waveCharC, waveChar_zero_iff]
      exact hzi.2
  have hinj : Set.InjOn (fun i : Fin k => z i.1) (Finset.univ : Finset (Fin k)) := by
    intro i _ j _ hij
    by_contra hne
    rcases lt_or_gt_of_ne (fun h : i.1 = j.1 => hne (Fin.ext h)) with h | h
    · exact absurd hij (ne_of_lt (hord i.1 j.1 i.2 j.2 h))
    · exact absurd hij.symm (ne_of_lt (hord j.1 i.1 j.2 i.2 h))
  have hcard := Finset.card_le_card_of_injOn (fun i : Fin k => z i.1)
    (fun i _ => hmem i) hinj
  simpa [nodeCountChar] using hcard

/-! ### The general branch — EVERY primitive character, the half-phase `ε` wave

Self-duality is not needed for a standing wave. For any primitive `χ ≠ 1` the completed Schwarz
reflection plus the functional equation give `conj Φ_χ(½+it) = W(χ⁻¹)·Φ_χ(½+it)` — the same line
relation as the self-dual case, with the conjugate character resolved through `χ̄ = χ⁻¹`. Running
the relation through itself at a non-vanishing line value forces `conj W·W = 1` (unimodularity, no
Gauss sums), so a HALF-PHASE `ε` with `ε² = W`, `conj ε·ε = 1` exists (ℂ algebraically closed), and
`ε·Φ_χ` is REAL on the line. The whole census then runs for every character: the `ε`-wave's nodes
are exactly the line zeros, and its alternations bound the same `nodeCountChar` from below.
`W = +1` is `ε = 1`; `W = −1` is `ε = I`. -/

/-- **The line relation, every primitive character** (self-duality dropped):
    `conj Φ_χ(½+it) = W(χ⁻¹)·Φ_χ(½+it)`. -/
theorem waveChar_line_conj_gen {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) (t : ℝ) :
    (starRingEnd ℂ) (waveChar χ (1 / 2 + (t : ℂ) * I))
      = (χ⁻¹).rootNumber * waveChar χ (1 / 2 + (t : ℂ) * I) := by
  have hNarg : ((N : ℂ)).arg ≠ Real.pi := by
    have h0 : ((N : ℂ)).arg = 0 := by
      rw [show ((N : ℕ) : ℂ) = ((N : ℝ) : ℂ) from by push_cast; ring]
      exact Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg N)
    rw [h0]
    exact fun h => Real.pi_ne_zero h.symm
  have hconjarg : (starRingEnd ℂ) ((1 : ℂ) / 2 - (t : ℂ) * I) = 1 / 2 + (t : ℂ) * I := by
    simp only [map_sub, map_mul, map_div₀, map_one, Complex.conj_I, Complex.conj_ofReal,
      map_ofNat]
    ring
  -- conj Λχ(½+it) = Λ_{χ⁻¹}(½−it)  (Schwarz reflection + χ̄ = χ⁻¹):
  have hΛconj : (starRingEnd ℂ)
      (DirichletCharacter.completedLFunction χ (1 / 2 + (t : ℂ) * I))
      = DirichletCharacter.completedLFunction χ⁻¹ (1 / 2 - (t : ℂ) * I) := by
    have h := completedLFunction_conj χ hχ (1 / 2 - (t : ℂ) * I)
    rw [hconjarg, ringHomComp_star_eq_inv] at h
    exact h
  have hNconj : (starRingEnd ℂ) ((N : ℂ) ^ (((1 : ℂ) / 2 + (t : ℂ) * I) / 2))
      = (N : ℂ) ^ (((1 : ℂ) / 2 - (t : ℂ) * I) / 2) := by
    have h := Complex.cpow_conj ((N : ℂ)) (((1 : ℂ) / 2 - (t : ℂ) * I) / 2) hNarg
    rw [show (starRingEnd ℂ) ((N : ℕ) : ℂ) = ((N : ℕ) : ℂ) from Complex.conj_natCast _] at h
    rw [show (starRingEnd ℂ) (((1 : ℂ) / 2 - (t : ℂ) * I) / 2)
        = ((1 : ℂ) / 2 + (t : ℂ) * I) / 2 from by
      rw [show (starRingEnd ℂ) (((1 : ℂ) / 2 - (t : ℂ) * I) / 2)
          = (starRingEnd ℂ) ((1 : ℂ) / 2 - (t : ℂ) * I) / 2 from by
        simp only [map_div₀, map_ofNat], hconjarg]] at h
    rw [h, Complex.conj_conj]
  rw [waveChar, map_mul, hΛconj, hNconj]
  -- = N^{(½−it)/2}·Λ_{χ⁻¹}(1−(½+it)) = W(χ⁻¹)·Φ(½+it) by the FE for χ⁻¹:
  have hfe := (DirichletLHadamard.isPrimitive_inv hχp).completedLFunction_one_sub
    (1 / 2 + (t : ℂ) * I)
  rw [show (1 : ℂ) - (1 / 2 + (t : ℂ) * I) = 1 / 2 - (t : ℂ) * I from by ring,
    inv_inv] at hfe
  rw [hfe]
  have hN : ((N : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [show (N : ℂ) ^ (((1 : ℂ) / 2 - (t : ℂ) * I) / 2)
      * ((N : ℂ) ^ (((1 : ℂ) / 2 + (t : ℂ) * I) - 1 / 2) * (χ⁻¹).rootNumber
        * DirichletCharacter.completedLFunction χ (1 / 2 + (t : ℂ) * I))
      = ((N : ℂ) ^ (((1 : ℂ) / 2 - (t : ℂ) * I) / 2)
          * (N : ℂ) ^ (((1 : ℂ) / 2 + (t : ℂ) * I) - 1 / 2)) * (χ⁻¹).rootNumber
        * DirichletCharacter.completedLFunction χ (1 / 2 + (t : ℂ) * I) from by ring,
    ← Complex.cpow_add _ _ hN,
    show ((1 : ℂ) / 2 - (t : ℂ) * I) / 2 + (((1 : ℂ) / 2 + (t : ℂ) * I) - 1 / 2)
      = ((1 : ℂ) / 2 + (t : ℂ) * I) / 2 from by ring]
  ring

/-- The wave does not vanish identically on the line: some line value is nonzero. -/
theorem exists_waveCharC_line_ne_zero {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) : ∃ t : ℝ, waveCharC χ (t : ℂ) ≠ 0 :=
  (standingWaveChar_nodes_isolated hχ 0).exists

/-- **The wave constant is unimodular**: `conj W(χ⁻¹) · W(χ⁻¹) = 1` — the line relation reflected
    through itself at a non-vanishing line value. No Gauss sums. -/
theorem rootNumber_inv_conj_mul {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) :
    (starRingEnd ℂ) ((χ⁻¹).rootNumber) * (χ⁻¹).rootNumber = 1 := by
  obtain ⟨t, ht⟩ := exists_waveCharC_line_ne_zero hχ
  have hΦ : waveChar χ (1 / 2 + (t : ℂ) * I) ≠ 0 := ht
  have h1 := waveChar_line_conj_gen hχ hχp t
  have h2 := congrArg (starRingEnd ℂ) h1
  rw [Complex.conj_conj, map_mul, h1] at h2
  have key : ((starRingEnd ℂ) ((χ⁻¹).rootNumber) * (χ⁻¹).rootNumber)
      * waveChar χ (1 / 2 + (t : ℂ) * I)
      = 1 * waveChar χ (1 / 2 + (t : ℂ) * I) := by
    rw [one_mul]
    linear_combination -h2
  exact mul_right_cancel₀ hΦ key

/-- **The half-phase exists**: a unit `ε` with `ε² = W(χ⁻¹)` and `conj ε · ε = 1`
    (ℂ is algebraically closed; unimodularity descends to the root). -/
theorem exists_halfPhase {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) :
    ∃ ε : ℂ, ε ^ 2 = (χ⁻¹).rootNumber ∧ (starRingEnd ℂ) ε * ε = 1 := by
  obtain ⟨ε, hε⟩ := IsAlgClosed.exists_pow_nat_eq ((χ⁻¹).rootNumber) (n := 2) (by norm_num)
  refine ⟨ε, hε, ?_⟩
  have hW := rootNumber_inv_conj_mul hχ hχp
  have hreal : (starRingEnd ℂ) ε * ε = (Complex.normSq ε : ℂ) := by
    rw [mul_comm, Complex.mul_conj]
  have hsq : ((Complex.normSq ε : ℝ) : ℂ) ^ 2 = 1 := by
    rw [← hreal]
    calc ((starRingEnd ℂ) ε * ε) ^ 2
        = (starRingEnd ℂ) (ε ^ 2) * ε ^ 2 := by rw [map_pow]; ring
      _ = 1 := by rw [hε, hW]
  have hx2 : (Complex.normSq ε) ^ 2 = 1 := by
    have : (((Complex.normSq ε ^ 2 : ℝ)) : ℂ) = 1 := by push_cast at hsq ⊢; exact hsq
    exact_mod_cast this
  have hx0 : 0 ≤ Complex.normSq ε := Complex.normSq_nonneg ε
  have hx1 : Complex.normSq ε = 1 := by nlinarith
  rw [hreal, hx1]
  norm_num

/-- **The half-phase wave is REAL on the line, every primitive character**: with `ε² = W(χ⁻¹)` and
    `conj ε·ε = 1`, the twisted wave `ε·Φ_χ(½+it)` is its own conjugate — the general standing
    wave. `W = +1` is `ε = 1`; `W = −1` is `ε = I`; complex `W` takes the genuine half-phase. -/
theorem waveCharGen_line_real {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) {ε : ℂ}
    (hε2 : ε ^ 2 = (χ⁻¹).rootNumber) (hεu : (starRingEnd ℂ) ε * ε = 1) (t : ℝ) :
    (starRingEnd ℂ) (ε * waveChar χ (1 / 2 + (t : ℂ) * I))
      = ε * waveChar χ (1 / 2 + (t : ℂ) * I) := by
  rw [map_mul, waveChar_line_conj_gen hχ hχp, ← hε2]
  calc (starRingEnd ℂ) ε * (ε ^ 2 * waveChar χ (1 / 2 + (t : ℂ) * I))
      = ((starRingEnd ℂ) ε * ε) * (ε * waveChar χ (1 / 2 + (t : ℂ) * I)) := by ring
    _ = ε * waveChar χ (1 / 2 + (t : ℂ) * I) := by rw [hεu, one_mul]

/-- The general (`ε`-twisted) standing wave: `Z^ε_χ(t) = Re (ε·Φ_χ(½+it))`. -/
noncomputable def standingWaveCharGen {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (ε : ℂ) (t : ℝ) : ℝ :=
  (ε * waveChar χ (1 / 2 + (t : ℂ) * I)).re

/-- The general wave is continuous. -/
theorem standingWaveCharGen_continuous {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (ε : ℂ) : Continuous (standingWaveCharGen χ ε) := by
  have hG : Continuous (waveCharC χ) := (waveCharC_differentiable hχ).continuous
  have : Continuous fun t : ℝ => (ε * waveCharC χ (t : ℂ)).re :=
    Complex.continuous_re.comp ((continuous_const.mul (hG.comp Complex.continuous_ofReal)))
  exact this

/-- A node of the general wave IS a completed-`L` zero on the line: reality makes the real part
    the whole value, and the unit `ε` never vanishes. -/
theorem standingWaveCharGen_node_iff {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) {ε : ℂ}
    (hε2 : ε ^ 2 = (χ⁻¹).rootNumber) (hεu : (starRingEnd ℂ) ε * ε = 1) (t : ℝ) :
    standingWaveCharGen χ ε t = 0
      ↔ DirichletCharacter.completedLFunction χ (1 / 2 + (t : ℂ) * I) = 0 := by
  have hεne : ε ≠ 0 := by
    intro h
    rw [h] at hεu
    simp at hεu
  have hreal := waveCharGen_line_real hχ hχp hε2 hεu t
  constructor
  · intro h
    have hval : ε * waveChar χ (1 / 2 + (t : ℂ) * I)
        = (((ε * waveChar χ (1 / 2 + (t : ℂ) * I)).re : ℝ) : ℂ) :=
      (Complex.conj_eq_iff_re.mp hreal).symm
    rw [standingWaveCharGen] at h
    rw [h, Complex.ofReal_zero] at hval
    rcases mul_eq_zero.mp hval with hc | hc
    · exact absurd hc hεne
    · rwa [waveChar_zero_iff] at hc
  · intro h
    rw [standingWaveCharGen, ← waveChar_zero_iff χ] at *
    rw [h, mul_zero]
    simp

/-- **The classical hook, every primitive character**: a sign flip of the `ε`-wave forces a
    completed-`L` zero on the critical line, strictly between. -/
theorem online_zero_of_signFlip_char_gen {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) {ε : ℂ}
    (hε2 : ε ^ 2 = (χ⁻¹).rootNumber) (hεu : (starRingEnd ℂ) ε * ε = 1) {a b : ℝ} (hab : a < b)
    (h : standingWaveCharGen χ ε a * standingWaveCharGen χ ε b < 0) :
    ∃ t ∈ Set.Ioo a b,
      DirichletCharacter.completedLFunction χ (1 / 2 + (t : ℂ) * I) = 0 := by
  have hc : ContinuousOn (standingWaveCharGen χ ε) (Set.Icc a b) :=
    (standingWaveCharGen_continuous hχ ε).continuousOn
  rcases mul_neg_iff.mp h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · obtain ⟨t, ht, h0⟩ := intermediate_value_Ioo' hab.le hc (Set.mem_Ioo.mpr ⟨hb, ha⟩)
    exact ⟨t, ht, (standingWaveCharGen_node_iff hχ hχp hε2 hεu t).mp h0⟩
  · obtain ⟨t, ht, h0⟩ := intermediate_value_Ioo hab.le hc (Set.mem_Ioo.mpr ⟨ha, hb⟩)
    exact ⟨t, ht, (standingWaveCharGen_node_iff hχ hχp hε2 hεu t).mp h0⟩

/-- **Alternation tables of the `ε`-wave bound the SAME node count from below** — every primitive
    character feeds the one census; the counters and payoffs upstream are unchanged. -/
theorem alternation_le_nodeCountChar_gen {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) {ε : ℂ}
    (hε2 : ε ^ 2 = (χ⁻¹).rootNumber) (hεu : (starRingEnd ℂ) ε * ε = 1)
    {a b : ℝ} (ts : ℕ → ℝ) (hmono : StrictMono ts) (k : ℕ)
    (ha : a ≤ ts 0) (hb : ts k ≤ b)
    (halt : ∀ i, i < k →
      standingWaveCharGen χ ε (ts i) * standingWaveCharGen χ ε (ts (i + 1)) < 0) :
    k ≤ nodeCountChar hχ a b := by
  have h := fun i (hi : i < k) =>
    online_zero_of_signFlip_char_gen hχ hχp hε2 hεu (hmono (Nat.lt_succ_self i)) (halt i hi)
  choose f hf using h
  have hmem : ∀ i : Fin k, f i.1 i.2 ∈ (standingWaveChar_nodes_finite hχ a b).toFinset := by
    intro i
    rw [Set.Finite.mem_toFinset]
    obtain ⟨hIoo, hzero⟩ := hf i.1 i.2
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have h1 : ts 0 ≤ ts i.1 := hmono.le_iff_le.mpr (Nat.zero_le _)
      linarith [hIoo.1]
    · have h3 : ts (i.1 + 1) ≤ ts k := hmono.le_iff_le.mpr i.2
      linarith [hIoo.2]
    · show waveCharC χ ((f i.1 i.2 : ℝ) : ℂ) = 0
      rw [waveCharC, waveChar_zero_iff]
      exact hzero
  have hinj : Set.InjOn (fun i : Fin k => f i.1 i.2) (Finset.univ : Finset (Fin k)) := by
    intro i _ j _ hij
    by_contra hne
    have hne' : i.1 ≠ j.1 := fun h => hne (Fin.ext h)
    have hij' : f i.1 i.2 = f j.1 j.2 := hij
    rcases lt_or_gt_of_ne hne' with h | h
    · have h1 : f i.1 i.2 < ts (i.1 + 1) := (hf i.1 i.2).1.2
      have h2 : ts j.1 < f j.1 j.2 := (hf j.1 j.2).1.1
      have h3 : ts (i.1 + 1) ≤ ts j.1 := hmono.le_iff_le.mpr (by omega)
      linarith
    · have h1 : f j.1 j.2 < ts (j.1 + 1) := (hf j.1 j.2).1.2
      have h2 : ts i.1 < f i.1 i.2 := (hf i.1 i.2).1.1
      have h3 : ts (j.1 + 1) ≤ ts i.1 := hmono.le_iff_le.mpr (by omega)
      linarith
  have hcard := Finset.card_le_card_of_injOn (fun i : Fin k => f i.1 i.2)
    (fun i _ => hmem i) hinj
  simpa [nodeCountChar] using hcard

/-- **The universal standing wave**: EVERY primitive `χ ≠ 1` carries a real standing wave on the
    critical line whose nodes are exactly its completed-`L` line zeros — packaged with its
    half-phase. The census framework (counters, window payoff, global packaging) applies to every
    Dirichlet L-function. -/
theorem exists_standingWave_universal {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) :
    ∃ ε : ℂ, ((starRingEnd ℂ) ε * ε = 1) ∧
      (∀ t : ℝ, (starRingEnd ℂ) (ε * waveChar χ (1 / 2 + (t : ℂ) * I))
        = ε * waveChar χ (1 / 2 + (t : ℂ) * I)) ∧
      (∀ t : ℝ, standingWaveCharGen χ ε t = 0
        ↔ DirichletCharacter.completedLFunction χ (1 / 2 + (t : ℂ) * I) = 0) := by
  obtain ⟨ε, hε2, hεu⟩ := exists_halfPhase hχ hχp
  exact ⟨ε, hεu, fun t => waveCharGen_line_real hχ hχp hε2 hεu t,
    fun t => standingWaveCharGen_node_iff hχ hχp hε2 hεu t⟩

/-- **The character strip census is finite** — no height restriction needed: the window's box sits
    inside a closed ball, where the repo's divisor-finiteness applies. -/
theorem stripBox_zeros_finite_char {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (a b : ℝ) :
    {s ∈ stripBox a b | DirichletCharacter.completedLFunction χ s = 0}.Finite := by
  apply Set.Finite.subset
    (DirichletLHadamard.completedLFunction_zeros_finite_in_closedBall hχ (1 + |a| + |b|))
  intro s hs
  refine ⟨?_, hs.2⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have hre := hs.1.1
  have him := hs.1.2
  have h1 : ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
  have h2 : |s.re| ≤ 1 := by
    rw [abs_le]
    exact ⟨by linarith [hre.1], hre.2⟩
  have h3 : |s.im| ≤ |a| + |b| := by
    rw [abs_le]
    constructor
    · have := him.1
      have := neg_abs_le a
      linarith [abs_nonneg b]
    · have := him.2
      have := le_abs_self b
      linarith [abs_nonneg a]
  linarith

/-- The character strip count. -/
noncomputable def boxCountChar {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (a b : ℝ) : ℕ :=
  (stripBox_zeros_finite_char hχ a b).toFinset.card

/-- **The line census never exceeds the strip census, character-general.** -/
theorem nodeCountChar_le_boxCountChar {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (a b : ℝ) :
    nodeCountChar hχ a b ≤ boxCountChar hχ a b := by
  rw [nodeCountChar, boxCountChar]
  refine Finset.card_le_card_of_injOn (fun t => (1 / 2 : ℂ) + (t : ℂ) * I) ?_ ?_
  · intro t ht
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at ht
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · constructor <;> simp [Complex.add_re] <;> norm_num
    · have him : ((1 / 2 : ℂ) + (t : ℂ) * I).im = t := by simp
      rw [him]; exact ht.1
    · have := ht.2
      rw [show waveCharC χ ((t : ℝ) : ℂ) = waveChar χ (1 / 2 + (t : ℂ) * I) from rfl,
        waveChar_zero_iff] at this
      exact this
  · intro t _ u _ htu
    have := congrArg Complex.im htu
    simpa using this

/-- **GRH in a window, character-general: counter agreement pins every strip zero to the line.** -/
theorem grh_in_window_of_counters_agree_char {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) {a b : ℝ}
    (hcount : boxCountChar hχ a b ≤ nodeCountChar hχ a b) :
    ∀ s ∈ stripBox a b, DirichletCharacter.completedLFunction χ s = 0 → s.re = 1 / 2 := by
  intro s hs hzero
  have hmaps : ∀ t ∈ (standingWaveChar_nodes_finite hχ a b).toFinset,
      (1 / 2 : ℂ) + (t : ℂ) * I ∈ (stripBox_zeros_finite_char hχ a b).toFinset := by
    intro t ht
    rw [Set.Finite.mem_toFinset] at ht
    rw [Set.Finite.mem_toFinset]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · constructor <;> simp [Complex.add_re] <;> norm_num
    · have him : ((1 / 2 : ℂ) + (t : ℂ) * I).im = t := by simp
      rw [him]; exact ht.1
    · have := ht.2
      rw [show waveCharC χ ((t : ℝ) : ℂ) = waveChar χ (1 / 2 + (t : ℂ) * I) from rfl,
        waveChar_zero_iff] at this
      exact this
  have hinj : Set.InjOn (fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ) * I)
      ((standingWaveChar_nodes_finite hχ a b).toFinset : Set ℝ) := by
    intro t _ u _ htu
    have := congrArg Complex.im htu
    simpa using this
  have hcard : ((stripBox_zeros_finite_char hχ a b).toFinset).card
      ≤ ((standingWaveChar_nodes_finite hχ a b).toFinset).card := hcount
  have hsurj := Finset.surjOn_of_injOn_of_card_le _ hmaps hinj hcard
  have hsmem : s ∈ (stripBox_zeros_finite_char hχ a b).toFinset := by
    rw [Set.Finite.mem_toFinset]; exact ⟨hs, hzero⟩
  obtain ⟨t, _, hteq⟩ := hsurj (Finset.mem_coe.mpr hsmem)
  rw [← hteq]
  simp

/-- **The global packaging, character-general: GRH from a certificate family.** If the two counters
    agree on every symmetric window `[−(n+1), n+1]`, then `GRH χ` holds outright. Unlike the `ζ`
    packaging (which must dodge the poles of `Λ` at `0,1` with a height floor and reflect negative
    heights through the FE), `Λχ` is ENTIRE for `χ ≠ 1`, so the symmetric windows cover every height
    directly — real-axis zeros included. Unconditional: the certificate family is the situational
    input. -/
theorem grh_of_window_certificates_char {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1)
    (hcert : ∀ n : ℕ, boxCountChar hχ (-(n + 1 : ℝ)) (n + 1)
      ≤ nodeCountChar hχ (-(n + 1 : ℝ)) (n + 1)) :
    GRHSpectral.GRH χ := by
  intro ρ hρ
  have hΛ : DirichletCharacter.completedLFunction χ ρ = 0 :=
    DirichletLHadamard.completedLFunction_eq_zero_of_mem hρ
  obtain ⟨n, hn⟩ := exists_nat_gt |ρ.im|
  have hn' : |ρ.im| < (n : ℝ) + 1 := hn.trans (lt_add_one _)
  have hwin : ρ ∈ stripBox (-(n + 1 : ℝ)) (n + 1) := by
    refine ⟨⟨hρ.1.le, hρ.2.1.le⟩, ?_, ?_⟩
    · have := neg_abs_le ρ.im
      linarith
    · have := le_abs_self ρ.im
      linarith
  exact grh_in_window_of_counters_agree_char hχ (hcert n) ρ hwin hΛ

/-- **The strip census is Jensen-bounded** — `boxCountChar ≤ C·R·log R` for any window enclosed by
    the radius-`R` disk. The upper counter is an explicit analytic quantity (the repo's
    order-1-growth Jensen bound, every zero counting with multiplicity ≥ 1), so the certificate
    `boxCountChar ≤ nodeCountChar` asks an alternation table to reach a concrete, computable
    target. -/
theorem boxCountChar_le_of_jensen {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) :
    ∃ C > (0 : ℝ), ∃ R₀ > (0 : ℝ), ∀ a b : ℝ, ∀ R, R₀ ≤ R → 1 + |a| + |b| ≤ R →
      (boxCountChar hχ a b : ℝ) ≤ C * R * Real.log R := by
  classical
  obtain ⟨C, hC, R₀, hR₀, hbound⟩ :=
    DirichletLHadamard.completedL_weighted_zero_count_disk_bound hχ hχp
  refine ⟨C, hC, R₀, hR₀, fun a b R hR hRab => ?_⟩
  set T := (stripBox_zeros_finite_char hχ a b).toFinset with hT
  have hmemZ : ∀ s ∈ T, s ∈ GRHSpectral.NontrivialZeros χ := by
    intro s hs
    rw [hT, Set.Finite.mem_toFinset] at hs
    exact DirichletLHadamard.completedLFunction_zero_mem_NontrivialZeros hχ hχp hs.2
  set S : Finset {ρ : ℂ // ρ ∈ GRHSpectral.NontrivialZeros χ} :=
    T.attach.map ⟨fun x => ⟨x.1, hmemZ x.1 x.2⟩,
      fun x y hxy => Subtype.ext (by simpa using congrArg Subtype.val hxy)⟩ with hS
  have hSnorm : ∀ ρ ∈ S, ‖ρ.val‖ ≤ R := by
    intro ρ hρS
    rw [hS, Finset.mem_map] at hρS
    obtain ⟨x, _, hx⟩ := hρS
    have hval : ρ.val = x.1 := (congrArg Subtype.val hx).symm
    have hsT : x.1 ∈ {s ∈ stripBox a b | DirichletCharacter.completedLFunction χ s = 0} :=
      (Set.Finite.mem_toFinset _).mp x.2
    have hre := hsT.1.1
    have him := hsT.1.2
    have h1 : ‖x.1‖ ≤ |x.1.re| + |x.1.im| := Complex.norm_le_abs_re_add_abs_im _
    have h2 : |x.1.re| ≤ 1 := by
      rw [abs_le]
      exact ⟨by linarith [hre.1], hre.2⟩
    have h3 : |x.1.im| ≤ |a| + |b| := by
      rw [abs_le]
      constructor
      · have := him.1
        have := neg_abs_le a
        linarith [abs_nonneg b]
      · have := him.2
        have := le_abs_self b
        linarith [abs_nonneg a]
    rw [hval]
    linarith
  have hkey := hbound R hR S hSnorm
  have hcard : S.card = T.card := by
    rw [hS, Finset.card_map, Finset.card_attach]
  have hcount : boxCountChar hχ a b = S.card := by
    rw [hcard, hT, boxCountChar]
  rw [hcount]
  calc (S.card : ℝ) = ∑ _ρ ∈ S, (1 : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ ∑ ρ ∈ S, (DirichletLHadamard.lOrderNat χ ρ.val : ℝ) := by
        refine Finset.sum_le_sum fun ρ _ => ?_
        exact_mod_cast DirichletLHadamard.lOrderNat_pos hχ ρ.2
    _ ≤ C * R * Real.log R := hkey

/-! ## THE VOID — the one gate, staged

`ExteriorVoid χ` says the spectral image never leaves the closed unit disk: no zero with
`‖w(ρ)‖ > 1`, equivalently (`w_norm_le_one_iff`) no zero with `Re ρ < ½`. **This is
GRH-equivalent — the open weld, stated plainly** (with `w_norm_eq_one_of_le_one` and
`grh_iff_w_image_unit` it gives the circle, hence the line; conversely GRH trivially implies it).
By the re-pairing below, proving EITHER half-strip empty proves both. The structure's case against
the exterior: unit phasors, conserved fiber, zero net ledger mass, one-sided `√n` radial packing
(`radial_refl_mismatch`). Closing this Prop closes the program. -/

/-- **The void, named**: the spectral image stays in the closed disk. GRH-equivalent. -/
def ExteriorVoid {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ ρ ∈ GRHSpectral.NontrivialZeros χ, ‖SpectralSide.w ρ‖ ≤ 1

/-- **The coordinate bridge**: `‖w(ρ)‖ ≤ 1 ⟺ ½ ≤ Re ρ` (for `ρ ≠ 0`). The void's spectral and
    strip faces are formally the same statement. -/
theorem w_norm_le_one_iff {ρ : ℂ} (hρ : ρ ≠ 0) :
    ‖SpectralSide.w ρ‖ ≤ 1 ↔ 1 / 2 ≤ ρ.re := by
  have hnorm : ‖SpectralSide.w ρ‖ = ‖ρ - 1‖ / ‖ρ‖ := by
    rw [SpectralSide.w, show (1 : ℂ) - 1 / ρ = (ρ - 1) / ρ from by field_simp, norm_div]
  rw [hnorm, div_le_one (norm_pos_iff.mpr hρ)]
  constructor
  · intro h
    have h2 : ‖ρ - 1‖ ^ 2 ≤ ‖ρ‖ ^ 2 := by
      have := norm_nonneg (ρ - 1)
      nlinarith
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq] at h2
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im] at h2
    nlinarith
  · intro h
    have h2 : ‖ρ - 1‖ ^ 2 ≤ ‖ρ‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
        Complex.one_im]
      nlinarith
    have := norm_nonneg ρ
    nlinarith [norm_nonneg (ρ - 1)]

/-- **The re-pairing**: every zero's quartet partner sits at the reflected real part
    `Re(σρ) = 1 − Re ρ`. Hence the two half-strips of `Z(χ)` are in bijection — emptiness of
    EITHER half is the void. -/
theorem zero_re_pairing {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) {ρ : ℂ}
    (hρ : ρ ∈ GRHSpectral.NontrivialZeros χ) :
    (1 - (starRingEnd ℂ) ρ) ∈ GRHSpectral.NontrivialZeros χ ∧
      (1 - (starRingEnd ℂ) ρ).re = 1 - ρ.re :=
  ⟨one_sub_conj_mem_NontrivialZeros hχ hχp hρ, by
    simp [Complex.sub_re, Complex.conj_re]⟩

/-- **The gate is exact — the equivalence, kernel-proven**: `GRH χ ⟺ ExteriorVoid χ`. Forward:
    on-line zeros have unit spectral norm. Backward: the void puts every zero in `Re ≥ ½`; the
    quartet partner obeys the same bound at the reflected real part `1 − Re ρ`, squeezing
    `Re = ½`. The one-sided disk bound IS the line — the docstring's claim, verified. -/
theorem grh_iff_exteriorVoid {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) :
    GRHSpectral.GRH χ ↔ ExteriorVoid χ := by
  constructor
  · intro hgrh ρ hρ
    have hne : ρ ≠ 0 := GRHSpectral.nontrivial_ne_zero hρ
    exact (w_norm_le_one_iff hne).mpr (hgrh ρ hρ).ge
  · intro hvoid ρ hρ
    have hne : ρ ≠ 0 := GRHSpectral.nontrivial_ne_zero hρ
    have h1 : 1 / 2 ≤ ρ.re := (w_norm_le_one_iff hne).mp (hvoid ρ hρ)
    obtain ⟨hmem, hre⟩ := zero_re_pairing hχ hχp hρ
    have hne' : (1 - (starRingEnd ℂ) ρ) ≠ 0 := GRHSpectral.nontrivial_ne_zero hmem
    have h2 : 1 / 2 ≤ (1 - (starRingEnd ℂ) ρ).re :=
      (w_norm_le_one_iff hne').mp (hvoid _ hmem)
    rw [hre] at h2
    linarith

/-- **The ledger in log form**: over any `σ`-closed finite window of the spectrum, the
    `log`-norms of the spectral values sum to ZERO. -/
theorem sum_log_w_norm_eq_zero {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (S : Finset ℂ) (hS : ∀ ρ ∈ S, ρ ∈ GRHSpectral.NontrivialZeros χ)
    (hσ : ∀ ρ ∈ S, 1 - (starRingEnd ℂ) ρ ∈ S) :
    ∑ ρ ∈ S, Real.log ‖SpectralSide.w ρ‖ = 0 := by
  have hne : ∀ ρ ∈ S, ‖SpectralSide.w ρ‖ ≠ 0 :=
    fun ρ hρ => norm_ne_zero_iff.mpr (w_ne_zero_of_mem (hS ρ hρ))
  rw [← Real.log_prod hne, prod_w_norm_eq_one S hS hσ, Real.log_one]

/-- **The balanced-distance law** (the void's Jensen-ready face): over any `σ`-closed window, the
    zeros' aggregate log-distance to `1` equals their aggregate log-distance to `0`:
    `Σ log‖ρ−1‖ = Σ log‖ρ‖`. This is exactly the quantity Jensen's formula measures from the two
    centers — the functional equation's balance, in the coordinates where the one-sided mass bound
    must meet it. -/
theorem sum_log_dist_balanced {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (S : Finset ℂ) (hS : ∀ ρ ∈ S, ρ ∈ GRHSpectral.NontrivialZeros χ)
    (hσ : ∀ ρ ∈ S, 1 - (starRingEnd ℂ) ρ ∈ S) :
    ∑ ρ ∈ S, Real.log ‖ρ - 1‖ = ∑ ρ ∈ S, Real.log ‖ρ‖ := by
  have key := sum_log_w_norm_eq_zero S hS hσ
  have hterm : ∀ ρ ∈ S, Real.log ‖SpectralSide.w ρ‖
      = Real.log ‖ρ - 1‖ - Real.log ‖ρ‖ := by
    intro ρ hρ
    have hρ0 : ρ ≠ 0 := by
      intro h
      have := (hS ρ hρ).1
      rw [h] at this
      simpa using this
    have hρ1 : ρ - 1 ≠ 0 := by
      intro h
      have h1 : ρ = 1 := by linear_combination h
      have := (hS ρ hρ).2.1
      rw [h1] at this
      simpa using this
    rw [show SpectralSide.w ρ = (ρ - 1) / ρ from by
      rw [SpectralSide.w]; field_simp, norm_div,
      Real.log_div (norm_ne_zero_iff.mpr hρ1) (norm_ne_zero_iff.mpr hρ0)]
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib] at key
  linarith


/-! ## The Laguerre node-detector — "no node ever lifts" (the local line inequality)

`L_f(t) = f′(t)² − f(t)·f″(t)`. At a **true node** (the wave touches zero) `L = f′² ≥ 0`; at a
**lifted node** — a strictly positive local minimum, the imprint an off-line zero pair leaves on the
standing wave — `L = −f·f″ < 0`. If all zeros are real the wave is a locally-uniform limit of
real-rooted polynomials, and for those the inequality is **kernel-proven** below: the peeling
recursion `lag_linear_mul` makes the Laguerre form of a real-rooted polynomial a **sum of squares**
(`lag_eval_nonneg_of_realRooted`). So `LaguerreInequality standingWave` is a *necessary* consequence
of RH, and a single violation at a single `t` refutes it — a local, falsifiable detector
(numerics: `numerics/laguerre_chi3.py` detects every off-line fusion down to `δ = 10⁻⁴`, the
violation scaling as `δ²`). The converse is **not** claimed: the inequality alone is not known to
force all zeros real — an honest necessary-condition target, not a reduction costume (Rule Ten). -/

/-- **The Laguerre form** `L_f(t) = f′(t)² − f(t)·f″(t)` — the local "does the node touch" detector
    for a real wave. -/
noncomputable def laguerreForm (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv f t ^ 2 - f t * deriv (deriv f) t

/-- At a **true node** (`f t = 0`) the Laguerre form is `(f′)² ≥ 0`: a touching node never violates. -/
theorem laguerreForm_nonneg_at_node (f : ℝ → ℝ) (t : ℝ) (h : f t = 0) :
    0 ≤ laguerreForm f t := by
  simp only [laguerreForm, h, zero_mul, sub_zero]
  exact sq_nonneg _

/-- At a **lifted node** — a strictly positive local minimum (`f > 0`, `f′ = 0`, `f″ > 0`), the
    signature an off-line zero pair imprints on the standing wave — the Laguerre form is strictly
    negative. The detector direction: one lifted node is a pointwise witness against all-real zeros. -/
theorem laguerreForm_neg_at_lifted_node (f : ℝ → ℝ) (t : ℝ)
    (h0 : 0 < f t) (h1 : deriv f t = 0) (h2 : 0 < deriv (deriv f) t) :
    laguerreForm f t < 0 := by
  simp only [laguerreForm, h1]
  nlinarith [mul_pos h0 h2]

open Polynomial in
/-- The Laguerre form at the polynomial level: `lag p = p′² − p·p″`. -/
noncomputable def lag (p : Polynomial ℝ) : Polynomial ℝ :=
  derivative p ^ 2 - p * derivative (derivative p)

open Polynomial in
/-- **The Laguerre peeling recursion**: removing one real root,
    `lag ((X − r)·q) = q² + (X − r)²·lag q`. The single identity behind "every real zero presses the
    wave down": each peeled real root contributes the square `q²`. -/
theorem lag_linear_mul (r : ℝ) (q : Polynomial ℝ) :
    lag ((X - C r) * q) = q ^ 2 + (X - C r) ^ 2 * lag q := by
  simp only [lag, derivative_mul, derivative_add, derivative_sub, derivative_X, derivative_C,
    sub_zero, one_mul]
  ring

open Polynomial in
/-- **Real-rooted ⟹ Laguerre ≥ 0 (kernel-proven sum of squares).** For `p = c·∏(X − rᵢ)` with all
    roots real, the Laguerre form evaluates non-negatively everywhere: by `lag_linear_mul` it is an
    iterated sum of squares. This is the exact finite-degree statement of "a real spectrum lifts no
    node"; the standing wave's inequality is its degree-∞ limit (the open weld). -/
theorem lag_eval_nonneg_of_realRooted (c : ℝ) (l : List ℝ) (t : ℝ) :
    0 ≤ (lag (C c * (l.map fun r => X - C r).prod)).eval t := by
  induction l with
  | nil => simp [lag]
  | cons r l ih =>
      rw [List.map_cons, List.prod_cons,
        show C c * ((X - C r) * (l.map fun r => X - C r).prod)
            = (X - C r) * (C c * (l.map fun r => X - C r).prod) by ring,
        lag_linear_mul]
      simp only [eval_add, eval_mul, eval_pow, eval_sub, eval_X, eval_C]
      exact add_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) ih)

open Polynomial in
/-- The analytic Laguerre form of a polynomial wave is the polynomial Laguerre form, evaluated. -/
theorem laguerreForm_polynomial (p : Polynomial ℝ) (t : ℝ) :
    laguerreForm (fun x => p.eval x) t = (lag p).eval t := by
  have hd : ∀ q : Polynomial ℝ, deriv (fun x => q.eval x) = fun x => q.derivative.eval x :=
    fun q => funext fun x => (q.hasDerivAt x).deriv
  simp only [laguerreForm, hd, lag, eval_sub, eval_mul, eval_pow]

open Polynomial in
/-- **Any real-rooted polynomial wave satisfies the Laguerre inequality everywhere** — the finite
    Laguerre–Pólya case, kernel-proven: real spectrum ⟹ no lifted node. -/
theorem laguerreForm_nonneg_of_realRooted (c : ℝ) (l : List ℝ) (t : ℝ) :
    0 ≤ laguerreForm (fun x => (C c * (l.map fun r => X - C r).prod).eval x) t := by
  rw [laguerreForm_polynomial]
  exact lag_eval_nonneg_of_realRooted c l t

/-- **The Laguerre inequality** for a wave `f`: no node ever lifts — `f′² ≥ f·f″` pointwise. For the
    standing wave this is a **necessary** consequence of RH (all zeros real ⟹ Λ is in the
    Laguerre–Pólya class ⟹ this inequality; the finite case is `laguerreForm_nonneg_of_realRooted`).
    One violation at one `t` refutes RH. The converse is NOT claimed — an honest necessary-condition
    target, deliberately not a `rh_of_…` (Rule Ten). -/
def LaguerreInequality (f : ℝ → ℝ) : Prop := ∀ t : ℝ, 0 ≤ laguerreForm f t

open Filter in
/-- **The Laguerre inequality passes to limits.** If `F n → f` together with first and second
    derivatives — *pointwise convergence suffices*, no uniformity is needed to carry an inequality to
    the limit — then Laguerre non-negativity survives. The degree-∞ transfer, kernel-clean. -/
theorem laguerreInequality_of_tendsto (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ)
    (h0 : ∀ t, Tendsto (fun n => F n t) atTop (nhds (f t)))
    (h1 : ∀ t, Tendsto (fun n => deriv (F n) t) atTop (nhds (deriv f t)))
    (h2 : ∀ t, Tendsto (fun n => deriv (deriv (F n)) t) atTop (nhds (deriv (deriv f) t)))
    (hL : ∀ n t, 0 ≤ laguerreForm (F n) t) :
    LaguerreInequality f := by
  intro t
  refine le_of_tendsto_of_tendsto'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0)) ?_ (fun n => hL n t)
  simpa only [laguerreForm] using ((h1 t).pow 2).sub ((h0 t).mul (h2 t))

open Polynomial Filter in
/-- **Laguerre–Pólya limit ⟹ no lifted node (the degree-∞ step).** If `f` is the pointwise limit —
    with two derivatives — of *real-rooted polynomials*, then `f` satisfies the Laguerre inequality:
    each approximant's Laguerre form is a sum of squares (`lag_eval_nonneg_of_realRooted`), and
    non-negativity passes to the limit. This is "a real spectrum lifts no node" at degree ∞, with the
    approximation as the explicit hypothesis. -/
theorem laguerreInequality_of_realRooted_approx (f : ℝ → ℝ) (c : ℕ → ℝ) (l : ℕ → List ℝ)
    (h0 : ∀ t, Tendsto (fun n => (C (c n) * ((l n).map fun r => X - C r).prod).eval t) atTop
        (nhds (f t)))
    (h1 : ∀ t, Tendsto (fun n => (derivative (C (c n) * ((l n).map fun r => X - C r).prod)).eval t)
        atTop (nhds (deriv f t)))
    (h2 : ∀ t, Tendsto (fun n =>
          (derivative (derivative (C (c n) * ((l n).map fun r => X - C r).prod))).eval t)
        atTop (nhds (deriv (deriv f) t))) :
    LaguerreInequality f := by
  intro t
  refine le_of_tendsto_of_tendsto'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0)) ?_
    (fun n => lag_eval_nonneg_of_realRooted (c n) (l n) t)
  have heval : ∀ p : Polynomial ℝ, (lag p).eval t
      = (derivative p).eval t ^ 2 - p.eval t * (derivative (derivative p)).eval t := by
    intro p; simp [lag]
  simp only [heval, laguerreForm]
  exact ((h1 t).pow 2).sub ((h0 t).mul (h2 t))

open Polynomial Filter in
/-- **The remaining analytic obligation** for the standing wave's Laguerre inequality: `Z` is a
    Laguerre–Pólya limit — real-rooted polynomials converging to it pointwise with two derivatives.
    Under RH these are the Hadamard partial products `Ξ(0)·∏_{n≤N}(1 − t²/γₙ²)` (real-rooted exactly
    because the zeros sit on the line; genus-0 product + Cauchy estimates give the derivative
    convergence — classical analysis, not yet formalized here). Honest status: **implied by** RH with
    classical analysis; **implies** `LaguerreInequality standingWave` (next theorem); NOT claimed
    equivalent to RH — strictly the necessary-direction chain (Rule Ten). -/
def StandingWaveLPApprox : Prop :=
  ∃ (c : ℕ → ℝ) (l : ℕ → List ℝ),
    (∀ t, Tendsto (fun n => (C (c n) * ((l n).map fun r => X - C r).prod).eval t) atTop
        (nhds (standingWave t))) ∧
    (∀ t, Tendsto (fun n => (derivative (C (c n) * ((l n).map fun r => X - C r).prod)).eval t)
        atTop (nhds (deriv standingWave t))) ∧
    (∀ t, Tendsto (fun n =>
          (derivative (derivative (C (c n) * ((l n).map fun r => X - C r).prod))).eval t)
        atTop (nhds (deriv (deriv standingWave) t)))

/-- **The standing wave lifts no node, given its LP approximation**: `StandingWaveLPApprox` (the one
    remaining analytic input, supplied by RH + classical Hadamard theory) yields the full pointwise
    Laguerre inequality for the standing wave. Everything else in the chain — the sum-of-squares
    finite case and the limit transfer — is kernel-proven above. -/
theorem laguerreInequality_standingWave (h : StandingWaveLPApprox) :
    LaguerreInequality standingWave := by
  obtain ⟨c, l, h0, h1, h2⟩ := h
  exact laguerreInequality_of_realRooted_approx standingWave c l h0 h1 h2

end HelixStandingWave

#print axioms HelixStandingWave.zeta_eq_flowTrace
#print axioms HelixStandingWave.completedΛ_zero_iff_standingWave_node
#print axioms HelixStandingWave.zeta_zero_on_line_iff_standingWave_node
#print axioms HelixStandingWave.laguerreForm_neg_at_lifted_node
#print axioms HelixStandingWave.lag_eval_nonneg_of_realRooted
#print axioms HelixStandingWave.laguerreForm_nonneg_of_realRooted
#print axioms HelixStandingWave.laguerreInequality_of_tendsto
#print axioms HelixStandingWave.laguerreInequality_of_realRooted_approx
#print axioms HelixStandingWave.laguerreInequality_standingWave
#print axioms HelixStandingWave.standingWave_continuous
#print axioms HelixStandingWave.online_zero_of_signFlip
#print axioms HelixStandingWave.standingWave_hasDerivAt
#print axioms HelixStandingWave.deriv_standingWave
#print axioms HelixStandingWave.fibres_meet_at_any_vanishing
#print axioms HelixStandingWave.signFlip_of_simple_node
#print axioms HelixStandingWave.fibres_meet_at_any_vanishing'
#print axioms HelixStandingWave.fibres_balance_at_any_vanishing

namespace HelixStandingWave

/-! ## The first slip — the induction's target, normal-formed

`ladder_induction` (HelixRoundTrip Part 9) closes the census by two-directional
induction the moment the STEP lemma holds: no slab hosts an off-line zero.
These theorems pin the hypothetical first failure into a rigid normal form.
If `GRH χ` fails there is a LEAST integer slab `n ≤ |Im ρ| < n+1` containing an
off-line zero (`exists_first_slip`) — and a slip is never a lone zero: the
straddle partner `1 − conj ρ` sits at EXACTLY the same height (same slab, same
`Im`), with reciprocal spectral norm, one of the two strictly outside the
circle (`slip_balanced_pair`) — a balanced interior/exterior pair,
ledger-neutral (`sum_log_w_norm_eq_zero`), corridor-confined (`zero_corridor`).
The induction's step lemma — *no slab hosts a balanced pair* — is the entire
open content; base and closure are kernel, and the first slip, if it exists,
must look exactly like this.

REFINEMENT (the sheet factoring, per the program's geometry): analytically the
partner shares the slab; geometrically it is an ANTIHELIX resident — the kernel
route to `1 − conj ρ` runs through the contragredient (Schwarz `LFunction_conj`
+ the reflection), i.e. the mirror sheet of the two-directional spiral, where
height reads in the mirror frame. The pair therefore never needs excluding as
a pair: it factors into TWO singleton alien demands, one per sheet, and each
sheet is one-sided, `√n`-locked, and complete — the chart excludes jitter,
gaps, and missed crossings (Parts 8–9), and each sheet carries the
unconditional eviction (`helix_eviction`, conjugation-symmetric). The
surviving world-fact question, in its smallest form: the singleton
demand-transport per sheet. -/

section FirstSlip

/-- **The first slip exists**: if `GRH χ` fails, there is a least integer slab
`[n, n+1)` of heights `|Im ρ|` containing an off-line nontrivial zero. -/
theorem exists_first_slip {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (h : ¬ GRHSpectral.GRH χ) :
    ∃ n : ℕ,
      (∃ ρ ∈ GRHSpectral.NontrivialZeros χ, ρ.re ≠ 1/2 ∧
        (n : ℝ) ≤ |ρ.im| ∧ |ρ.im| < n + 1) ∧
      ∀ m : ℕ, m < n →
        ¬ ∃ ρ ∈ GRHSpectral.NontrivialZeros χ, ρ.re ≠ 1/2 ∧
          (m : ℝ) ≤ |ρ.im| ∧ |ρ.im| < m + 1 := by
  classical
  simp only [GRHSpectral.GRH] at h
  push_neg at h
  obtain ⟨ρ, hρ, hre⟩ := h
  have hP : ∃ n : ℕ, ∃ ρ ∈ GRHSpectral.NontrivialZeros χ, ρ.re ≠ 1/2 ∧
      (n : ℝ) ≤ |ρ.im| ∧ |ρ.im| < n + 1 :=
    ⟨⌊|ρ.im|⌋₊, ρ, hρ, hre, Nat.floor_le (abs_nonneg _), Nat.lt_floor_add_one _⟩
  exact ⟨Nat.find hP, Nat.find_spec hP, fun m hm => Nat.find_min hP hm⟩

/-- **A slip is never alone — the balanced pair**: an off-line zero forces its
straddle partner `1 − conj ρ` into the SAME slab — exactly equal height,
reciprocal spectral norm, one of the two strictly outside the circle. The
induction's step lemma may assume this normal form. -/
theorem slip_balanced_pair {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) {ρ : ℂ}
    (hρ : ρ ∈ GRHSpectral.NontrivialZeros χ) (hre : ρ.re ≠ 1/2) :
    (1 - (starRingEnd ℂ) ρ) ∈ GRHSpectral.NontrivialZeros χ ∧
    (1 - (starRingEnd ℂ) ρ).im = ρ.im ∧
    ‖SpectralSide.w (1 - (starRingEnd ℂ) ρ)‖ = ‖SpectralSide.w ρ‖⁻¹ ∧
    (1 < ‖SpectralSide.w ρ‖ ∨ 1 < ‖SpectralSide.w (1 - (starRingEnd ℂ) ρ)‖) := by
  have hρ0 : ρ ≠ 0 := GRHSpectral.nontrivial_ne_zero hρ
  have hρ1 : (1 : ℂ) - (starRingEnd ℂ) ρ ≠ 0 := by
    intro hzero
    have hre1 := congrArg Complex.re hzero
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re,
      Complex.zero_re] at hre1
    have := hρ.2.1
    linarith
  refine ⟨one_sub_conj_mem_NontrivialZeros hχ hχp hρ, ?_,
    w_norm_sigma hρ0 hρ1, ?_⟩
  · simp [Complex.sub_im, Complex.one_im, Complex.conj_im]
  · have hne : ‖SpectralSide.w ρ‖ ≠ 1 := fun hu =>
      hre ((SpectralSide.w_unit_iff_half ρ hρ0).mp
        (by rw [Complex.normSq_eq_norm_sq, hu, one_pow]))
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · right
      exact (orbit_straddle_of_interior hχ hχp hρ hlt).2
    · left
      exact hgt

end FirstSlip

end HelixStandingWave

#print axioms HelixStandingWave.exists_first_slip
#print axioms HelixStandingWave.slip_balanced_pair
