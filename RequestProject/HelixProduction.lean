import RequestProject.HelixStandingWave
import RequestProject.DirichletClosureLedger
import RequestProject.HelixDualOperator
import RequestProject.HelixFlowClosureLedger

/-!
# The production program (route 3) — zero events ARE the source's real-height flips

The program, in the repo's mechanism language and its census coordinates:

```
LocalZeroFlip:        zero event ↔ harmonic/flip event       — THEOREMS below, odd-order safe
RuleEightProduction:  each admission produces one flip        ⎫  census split: box census =
SourceComplete:       all admissions come from the source     ⎭  line census + off-line census
⟹  all zero events are real-height flips  ⟹  Re ρ = ½
```

* **LocalZeroFlip**: an entire wave that is real on the real axis flips sign across every real
  zero of finite ODD analytic order (`signFlip_of_odd_order`), and the universal character wave
  is such a wave (`standingWaveCharGen_flip_of_odd_order`). Multiplicity-safe — upgrades the
  simple-zero hook.
* **The census split** (`boxCountChar_eq_nodeCountChar_add_offLineCountChar`): window by window,
  unconditionally, `strip census = line census + off-line census`. The line part is EXACTLY the
  node set (`onLine_filter_card_eq_nodeCountChar` — a bijection, both directions). So the whole
  program is one number: **`offLineCountChar χ a b` — kill it.** Each window where it dies is a
  window where every zero event is a real-height flip. The mechanism that kills it: the source
  flow is unitary, `source_noDrift` is σ-free, and the one-sided helix has no radius for an
  off-line partner (`radial_refl_mismatch`).

No Props, no conditionals: everything in this file is an unconditional theorem about counts.
-/

open Complex Filter Topology

namespace HelixProduction

/-! ## Part 1 — LocalZeroFlip: the odd-order flip engine -/

/-- **The odd-order flip engine** (LocalZeroFlip, multiplicity-safe). An entire function that is
    REAL on the real axis changes sign across every real zero of finite odd analytic order:
    locally `G(z) = (z−t₀)^m·g(z)` with `g(t₀) ≠ 0`; reality forces `g(t₀)` real, and odd `m`
    makes the factor `(t−t₀)^m` flip while `Re g` holds its sign. The local face of
    "admission = flip" with no simplicity assumption. -/
theorem signFlip_of_odd_order {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    (hreal : ∀ t : ℝ, (G (t : ℂ)).im = 0) {t₀ : ℝ} {m : ℕ}
    (hord : analyticOrderAt G (t₀ : ℂ) = m) (hodd : Odd m) :
    ∀ ε > 0, ∃ a ∈ Set.Ioo (t₀ - ε) t₀, ∃ b ∈ Set.Ioo t₀ (t₀ + ε),
      (G (a : ℂ)).re * (G (b : ℂ)).re < 0 := by
  intro ε hε
  have hA : AnalyticAt ℂ G (t₀ : ℂ) :=
    (analyticOnNhd_univ_iff_differentiable.mpr hG) _ (Set.mem_univ _)
  obtain ⟨g, hg, hg0, hev⟩ := (hA.analyticOrderAt_eq_natCast).mp hord
  -- the factorization, restricted to the real axis (full neighbourhood)
  have hevR : ∀ᶠ t : ℝ in 𝓝 t₀, G (t : ℂ) = ((t : ℂ) - (t₀ : ℂ)) ^ m • g (t : ℂ) :=
    Complex.continuous_ofReal.continuousAt.eventually hev
  -- g is real at t₀: divide the factorization by the real factor on the punctured axis
  have hgim : (g (t₀ : ℂ)).im = 0 := by
    have hmap : Filter.Tendsto (fun t : ℝ => (t : ℂ)) (nhdsWithin t₀ {t₀}ᶜ)
        (nhdsWithin (t₀ : ℂ) {(t₀ : ℂ)}ᶜ) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · exact Complex.continuous_ofReal.continuousAt.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact fun hc => ht (Complex.ofReal_injective hc)
    have hevP : ∀ᶠ t : ℝ in nhdsWithin t₀ {t₀}ᶜ, (g (t : ℂ)).im = 0 := by
      filter_upwards [hmap.eventually (hev.filter_mono nhdsWithin_le_nhds),
        self_mem_nhdsWithin] with t hfac ht
      have htne : (t : ℝ) - t₀ ≠ 0 := sub_ne_zero.mpr ht
      have hpow_ne : ((t - t₀ : ℝ)) ^ m ≠ 0 := pow_ne_zero _ htne
      have hcast : ((t : ℂ) - (t₀ : ℂ)) ^ m = (((t - t₀ : ℝ) ^ m : ℝ) : ℂ) := by
        push_cast; ring
      rw [hcast, smul_eq_mul] at hfac
      have hgval : g (t : ℂ) = G (t : ℂ) / (((t - t₀ : ℝ) ^ m : ℝ) : ℂ) := by
        rw [hfac]
        exact (mul_div_cancel_left₀ _ (by exact_mod_cast hpow_ne)).symm
      rw [hgval, Complex.div_ofReal_im, hreal t, zero_div]
    have hcont : Filter.Tendsto (fun t : ℝ => (g (t : ℂ)).im) (nhdsWithin t₀ {t₀}ᶜ)
        (𝓝 ((g (t₀ : ℂ)).im)) :=
      (Complex.continuous_im.continuousAt.comp
        (hg.continuousAt.comp Complex.continuous_ofReal.continuousAt)).tendsto.mono_left
        nhdsWithin_le_nhds
    have hzero : Filter.Tendsto (fun t : ℝ => (g (t : ℂ)).im) (nhdsWithin t₀ {t₀}ᶜ)
        (𝓝 (0 : ℝ)) := by
      rw [Filter.tendsto_congr' hevP]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hcont hzero
  have hgre : (g (t₀ : ℂ)).re ≠ 0 := by
    intro h
    exact hg0 (Complex.ext h hgim)
  -- the real part of g holds a strict sign on a neighbourhood
  have hgcont : ContinuousAt (fun t : ℝ => (g (t : ℂ)).re) t₀ :=
    Complex.continuous_re.continuousAt.comp
      (hg.continuousAt.comp Complex.continuous_ofReal.continuousAt)
  -- extract a single δ-window where the factorization holds and Re g keeps its sign
  rcases lt_or_gt_of_ne hgre with hneg | hpos
  · -- (g t₀).re < 0
    have hsign : ∀ᶠ t : ℝ in 𝓝 t₀, (g (t : ℂ)).re < 0 :=
      hgcont (eventually_lt_nhds hneg)
    obtain ⟨δ, hδ, hδP⟩ := Metric.eventually_nhds_iff.mp (hevR.and hsign)
    set η := min (δ / 2) (ε / 2) with hη
    have hη0 : 0 < η := by positivity
    have hηδ : η < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hηε : η < ε := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    refine ⟨t₀ - η, ⟨by linarith, by linarith⟩, t₀ + η, ⟨by linarith, by linarith⟩, ?_⟩
    have ha := hδP (show dist (t₀ - η) t₀ < δ by
      rw [Real.dist_eq, show t₀ - η - t₀ = -η from by ring, abs_neg, abs_of_pos hη0]
      exact hηδ)
    have hb := hδP (show dist (t₀ + η) t₀ < δ by
      rw [Real.dist_eq, show t₀ + η - t₀ = η from by ring, abs_of_pos hη0]
      exact hηδ)
    have hacast : (((t₀ - η : ℝ) : ℂ) - (t₀ : ℂ)) ^ m = (((-η : ℝ) ^ m : ℝ) : ℂ) := by
      push_cast; ring
    have hbcast : (((t₀ + η : ℝ) : ℂ) - (t₀ : ℂ)) ^ m = (((η : ℝ) ^ m : ℝ) : ℂ) := by
      push_cast; ring
    rw [ha.1, hacast, smul_eq_mul, Complex.re_ofReal_mul]
    rw [hb.1, hbcast, smul_eq_mul, Complex.re_ofReal_mul]
    have hpowa : ((-η : ℝ)) ^ m < 0 := hodd.pow_neg (by linarith)
    have hpowb : (0 : ℝ) < η ^ m := pow_pos hη0 m
    have hga := ha.2
    have hgb := hb.2
    have hterm_a : 0 < (-η : ℝ) ^ m * (g ((t₀ - η : ℝ) : ℂ)).re :=
      mul_pos_of_neg_of_neg hpowa hga
    have hterm_b : (η : ℝ) ^ m * (g ((t₀ + η : ℝ) : ℂ)).re < 0 :=
      mul_neg_of_pos_of_neg hpowb hgb
    exact mul_neg_of_pos_of_neg hterm_a hterm_b
  · -- 0 < (g t₀).re
    have hsign : ∀ᶠ t : ℝ in 𝓝 t₀, 0 < (g (t : ℂ)).re :=
      hgcont (eventually_gt_nhds hpos)
    obtain ⟨δ, hδ, hδP⟩ := Metric.eventually_nhds_iff.mp (hevR.and hsign)
    set η := min (δ / 2) (ε / 2) with hη
    have hη0 : 0 < η := by positivity
    have hηδ : η < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hηε : η < ε := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    refine ⟨t₀ - η, ⟨by linarith, by linarith⟩, t₀ + η, ⟨by linarith, by linarith⟩, ?_⟩
    have ha := hδP (show dist (t₀ - η) t₀ < δ by
      rw [Real.dist_eq, show t₀ - η - t₀ = -η from by ring, abs_neg, abs_of_pos hη0]
      exact hηδ)
    have hb := hδP (show dist (t₀ + η) t₀ < δ by
      rw [Real.dist_eq, show t₀ + η - t₀ = η from by ring, abs_of_pos hη0]
      exact hηδ)
    have hacast : (((t₀ - η : ℝ) : ℂ) - (t₀ : ℂ)) ^ m = (((-η : ℝ) ^ m : ℝ) : ℂ) := by
      push_cast; ring
    have hbcast : (((t₀ + η : ℝ) : ℂ) - (t₀ : ℂ)) ^ m = (((η : ℝ) ^ m : ℝ) : ℂ) := by
      push_cast; ring
    rw [ha.1, hacast, smul_eq_mul, Complex.re_ofReal_mul]
    rw [hb.1, hbcast, smul_eq_mul, Complex.re_ofReal_mul]
    have hpowa : ((-η : ℝ)) ^ m < 0 := hodd.pow_neg (by linarith)
    have hpowb : (0 : ℝ) < η ^ m := pow_pos hη0 m
    have hga := ha.2
    have hgb := hb.2
    have hterm_a : (-η : ℝ) ^ m * (g ((t₀ - η : ℝ) : ℂ)).re < 0 :=
      mul_neg_of_neg_of_pos hpowa hga
    have hterm_b : 0 < (η : ℝ) ^ m * (g ((t₀ + η : ℝ) : ℂ)).re :=
      mul_pos hpowb hgb
    exact mul_neg_of_neg_of_pos hterm_a hterm_b

/-- **LocalZeroFlip for the universal character wave**: the `ε`-twisted wave of ANY primitive
    `χ ≠ 1` flips sign across every line zero of finite odd analytic order. Admission of odd
    order ⟹ flip, no simplicity assumed — the local identity of the production program, on the
    repo's own wave. -/
theorem standingWaveCharGen_flip_of_odd_order {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) {ε : ℂ}
    (hε2 : ε ^ 2 = (χ⁻¹).rootNumber) (hεu : (starRingEnd ℂ) ε * ε = 1)
    {t₀ : ℝ} {m : ℕ}
    (hord : analyticOrderAt (fun z => ε * HelixStandingWave.waveCharC χ z) (t₀ : ℂ) = m)
    (hodd : Odd m) :
    ∀ e > 0, ∃ a ∈ Set.Ioo (t₀ - e) t₀, ∃ b ∈ Set.Ioo t₀ (t₀ + e),
      HelixStandingWave.standingWaveCharGen χ ε a
        * HelixStandingWave.standingWaveCharGen χ ε b < 0 := by
  have hG : Differentiable ℂ (fun z => ε * HelixStandingWave.waveCharC χ z) :=
    (HelixStandingWave.waveCharC_differentiable hχ).const_mul ε
  have hreal : ∀ t : ℝ, ((fun z => ε * HelixStandingWave.waveCharC χ z) (t : ℂ)).im = 0 := by
    intro t
    have h := HelixStandingWave.waveCharGen_line_real hχ hχp hε2 hεu t
    have := Complex.conj_eq_iff_im.mp h
    simpa [HelixStandingWave.waveCharC] using this
  exact signFlip_of_odd_order hG hreal hord hodd

/-! ## Part 2 — the census split: the program as one number -/

/-- **The off-line census**: the number of strip zero events in the window that sit off the
    critical line. The production program's entire remaining content is: this number is `0`,
    for every window. -/
noncomputable def offLineCountChar {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (a b : ℝ) : ℕ :=
  ((HelixStandingWave.stripBox_zeros_finite_char hχ a b).toFinset.filter
    (fun s => s.re ≠ 1 / 2)).card

/-- **The on-line strip events ARE the wave's nodes** — a bijection via the height, both
    directions, unconditional: an on-line zero event at height `t` is a node at `t`, and a node
    at `t` is the on-line zero event `½ + it`. -/
theorem onLine_filter_card_eq_nodeCountChar {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (a b : ℝ) :
    ((HelixStandingWave.stripBox_zeros_finite_char hχ a b).toFinset.filter
      (fun s => s.re = 1 / 2)).card = HelixStandingWave.nodeCountChar hχ a b := by
  rw [HelixStandingWave.nodeCountChar]
  apply Finset.card_bij (fun s _ => s.im)
  · -- the height of an on-line event is a node
    intro s hs
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hs
    obtain ⟨⟨⟨_, him⟩, hzero⟩, hhalf⟩ := hs
    rw [Set.Finite.mem_toFinset]
    refine ⟨him, ?_⟩
    show HelixStandingWave.waveCharC χ ((s.im : ℝ) : ℂ) = 0
    rw [HelixStandingWave.waveCharC, HelixStandingWave.waveChar_zero_iff]
    have hs_eq : (1 : ℂ) / 2 + (s.im : ℂ) * I = s := by
      apply Complex.ext
      · simp [hhalf]
      · simp
    rw [hs_eq]
    exact hzero
  · -- injective: equal heights and both on the line
    intro s hs u hu hsu
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hs hu
    exact Complex.ext (by rw [hs.2, hu.2]) hsu
  · -- surjective: every node is an on-line event
    intro t ht
    rw [Set.Finite.mem_toFinset] at ht
    obtain ⟨htab, hnode⟩ := ht
    refine ⟨(1 : ℂ) / 2 + (t : ℂ) * I, ?_, by simp⟩
    rw [Finset.mem_filter, Set.Finite.mem_toFinset]
    have hzero : DirichletCharacter.completedLFunction χ ((1 : ℂ) / 2 + (t : ℂ) * I) = 0 := by
      have := hnode
      rwa [show HelixStandingWave.waveCharC χ ((t : ℝ) : ℂ)
          = HelixStandingWave.waveChar χ (1 / 2 + (t : ℂ) * I) from rfl,
        HelixStandingWave.waveChar_zero_iff] at this
    refine ⟨⟨⟨?_, ?_⟩, hzero⟩, by simp⟩
    · constructor <;> simp <;> norm_num
    · have him : ((1 : ℂ) / 2 + (t : ℂ) * I).im = t := by simp
      rw [him]
      exact htab

/-- **The census split, unconditional, every window**:
    `strip census = line census + off-line census`. The strip events partition by the line; the
    on-line part is the node count exactly. The program in one identity: drive the last term to
    zero and every zero event is a real-height flip. -/
theorem boxCountChar_eq_nodeCountChar_add_offLineCountChar {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (a b : ℝ) :
    HelixStandingWave.boxCountChar hχ a b
      = HelixStandingWave.nodeCountChar hχ a b + offLineCountChar hχ a b := by
  rw [HelixStandingWave.boxCountChar, offLineCountChar,
    ← onLine_filter_card_eq_nodeCountChar hχ a b]
  exact (Finset.filter_card_add_filter_neg_card_eq_card
    (p := fun s : ℂ => s.re = 1 / 2)).symm

/-! ## Part 3 — the refusal of the lone off-line event: twins, and an even census

Origination (`Origination.lean`): a zero has no `L`-free existence — every zero event is PRODUCED
by the prime-built structure, and there are exactly two prime-built representations (the helix
winding, the 1-D von Mangoldt field). The buddy map `s ↦ 1 − conj s` shows the production cost of
an off-line event is DOUBLE: the structure must simultaneously produce a second, distinct off-line
event at the same height (`offLine_event_has_partner`), so the off-line census is even in every
window (`offLineCountChar_even`), and killing it means only refusing the first TWIN PAIR
(`offLineCountChar_eq_zero_of_lt_two`). The geometric refusal of that pair is exactly what the
one-sided radial law already states at the readout level: `HelixAsymmetry.radial_refl_mismatch` —
off the line, the buddy's radius `n^{1−σ}` is a slot the `√n`-packed helix does not have. Welding
that refusal to the census is the program's remaining work. -/

/-- **No lone off-line event**: every off-line zero event in a window comes with a DISTINCT
    off-line partner at the same height — its reflection twin `1 − conj s`. The production cost of
    leaving the line is double occupancy at one height. -/
theorem offLine_event_has_partner {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) {a b : ℝ} {s : ℂ}
    (hbox : s ∈ HelixStandingWave.stripBox a b)
    (hzero : DirichletCharacter.completedLFunction χ s = 0) (hoff : s.re ≠ 1 / 2) :
    ∃ s' : ℂ, s' ≠ s ∧ s' ∈ HelixStandingWave.stripBox a b ∧
      DirichletCharacter.completedLFunction χ s' = 0 ∧ s'.re ≠ 1 / 2 ∧ s'.im = s.im := by
  have hmemZ : s ∈ GRHSpectral.NontrivialZeros χ :=
    DirichletLHadamard.completedLFunction_zero_mem_NontrivialZeros hχ hχp hzero
  have hσmem : (1 - (starRingEnd ℂ) s) ∈ GRHSpectral.NontrivialZeros χ :=
    HelixStandingWave.one_sub_conj_mem_NontrivialZeros hχ hχp hmemZ
  have hσre : (1 - (starRingEnd ℂ) s).re = 1 - s.re := by
    simp [Complex.sub_re, Complex.conj_re]
  have hσim : (1 - (starRingEnd ℂ) s).im = s.im := by
    simp [Complex.sub_im, Complex.conj_im]
  refine ⟨1 - (starRingEnd ℂ) s, ?_, ⟨?_, ?_⟩, ?_, ?_, hσim⟩
  · intro hfix
    exact hoff ((HelixAsymmetry.onLine_iff_fixed_reflection s).mp hfix)
  · rw [hσre]
    exact ⟨by linarith [hσmem.1, hσre], by linarith [hσmem.2.1, hσre]⟩
  · rw [hσim]
    exact hbox.2
  · exact DirichletLHadamard.completedLFunction_eq_zero_of_mem hσmem
  · rw [hσre]
    intro h
    apply hoff
    linarith

/-- **The off-line census is EVEN, every window**: the reflection twin pairing
    `s ↦ 1 − conj s` is an involution on the off-line events with no fixed point (a fixed point IS
    the line, `onLine_iff_fixed_reflection`). Off-line events die in pairs. -/
theorem offLineCountChar_even {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) (a b : ℝ) :
    Even (offLineCountChar hχ a b) := by
  rw [offLineCountChar]
  set T := ((HelixStandingWave.stripBox_zeros_finite_char hχ a b).toFinset.filter
    (fun s => s.re ≠ 1 / 2)) with hT
  have hmemT : ∀ s ∈ T, 1 - (starRingEnd ℂ) s ∈ T := by
    intro s hs
    rw [hT, Finset.mem_filter, Set.Finite.mem_toFinset] at hs
    obtain ⟨⟨hbox, hzero⟩, hoff⟩ := hs
    have hmemZ : s ∈ GRHSpectral.NontrivialZeros χ :=
      DirichletLHadamard.completedLFunction_zero_mem_NontrivialZeros hχ hχp hzero
    have hσmem : (1 - (starRingEnd ℂ) s) ∈ GRHSpectral.NontrivialZeros χ :=
      HelixStandingWave.one_sub_conj_mem_NontrivialZeros hχ hχp hmemZ
    have hσre : (1 - (starRingEnd ℂ) s).re = 1 - s.re := by
      simp [Complex.sub_re, Complex.conj_re]
    have hσim : (1 - (starRingEnd ℂ) s).im = s.im := by
      simp [Complex.sub_im, Complex.conj_im]
    rw [hT, Finset.mem_filter, Set.Finite.mem_toFinset]
    refine ⟨⟨⟨?_, ?_⟩, DirichletLHadamard.completedLFunction_eq_zero_of_mem hσmem⟩, ?_⟩
    · rw [hσre]
      exact ⟨by linarith [hσmem.1, hσre], by linarith [hσmem.2.1, hσre]⟩
    · rw [hσim]
      exact hbox.2
    · rw [hσre]
      intro h
      apply hoff
      linarith
  have hsum : ∑ _x ∈ T, (1 : ZMod 2) = 0 := by
    refine Finset.sum_involution (fun s _ => 1 - (starRingEnd ℂ) s) ?_ ?_ ?_ ?_
    · intro s _
      decide
    · intro s hs _
      intro hfix
      rw [hT, Finset.mem_filter] at hs
      exact hs.2 ((HelixAsymmetry.onLine_iff_fixed_reflection s).mp hfix)
    · intro s hs
      exact hmemT s hs
    · intro s _
      exact HelixStandingWave.sigma_involutive s
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  have hdvd : 2 ∣ T.card := (CharP.cast_eq_zero_iff (ZMod 2) 2 T.card).mp hsum
  exact even_iff_two_dvd.mpr hdvd

/-- **Killing the count = refusing one twin pair**: an even count below `2` is `0`. The whole
    off-line census of a window vanishes as soon as the structure refuses a single reflection
    pair — the precise target `radial_refl_mismatch` aims at. -/
theorem offLineCountChar_eq_zero_of_lt_two {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) {a b : ℝ}
    (h : offLineCountChar hχ a b < 2) :
    offLineCountChar hχ a b = 0 := by
  obtain ⟨r, hr⟩ := offLineCountChar_even hχ hχp a b
  omega

/-! ## Part 4 — per-window energy accounting: quantized, priced, budgeted, conservative

Each singularity's energy is already kernel-formal and QUANTIZED: at every zero the trace
`−L'/L` has a simple pole of residue `−n` with `n = ord ≥ 1`, and the fibre side and the spectral
side carry the SAME energy `n²` (`EnergyBalance.sole_origin`, `EnergyBalance.energy_match_at_zero`,
through the balance identity `EnergyBalance.geometric_eq_spectral` — the prime fibre chain IS the
spectral readout). The ledger below prices each window in those quanta:

* every zero event costs at least one quantum (`boxCountChar_le_windowEnergyChar`);
* the ledger splits exactly over the line (`windowEnergyChar_eq_line_add_offLine`);
* an off-line excursion is taxed DOUBLE — the twin pair costs at least two quanta at one height
  (`two_le_offLineEnergyChar_of_event`);
* and the window's total budget is finite and explicit (`windowEnergyChar_le_jensen`).

Strict and conservative, with no slack for an uncosted mode: the energy originates on the primes
and nowhere else (`Origination.zeros_originate_only_from_primes`,
`Origination.vonMangoldt_supported_on_primePowers`), every fibre quantum is non-negative
(`HelixThreeFourOne.primeWindingEnergy_nonneg`), and the two sides balance identically
(`EnergyBalance.energy_balance`). -/

/-- **The window's total spectral energy**: the multiplicity-weighted census — each zero event
    priced at its quantum `ord ρ ≥ 1`, the residue of the trace's pole there. -/
noncomputable def windowEnergyChar {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (a b : ℝ) : ℕ :=
  ∑ s ∈ (HelixStandingWave.stripBox_zeros_finite_char hχ a b).toFinset,
    DirichletLHadamard.lOrderNat χ s

/-- The on-line energy ledger. -/
noncomputable def lineEnergyChar {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (a b : ℝ) : ℕ :=
  ∑ s ∈ (HelixStandingWave.stripBox_zeros_finite_char hχ a b).toFinset.filter
    (fun s => s.re = 1 / 2), DirichletLHadamard.lOrderNat χ s

/-- The off-line energy ledger. -/
noncomputable def offLineEnergyChar {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (a b : ℝ) : ℕ :=
  ∑ s ∈ (HelixStandingWave.stripBox_zeros_finite_char hχ a b).toFinset.filter
    (fun s => s.re ≠ 1 / 2), DirichletLHadamard.lOrderNat χ s

/-- **The energy ledger splits exactly over the line**: window energy = line energy + off-line
    energy. Conservation has no third account. -/
theorem windowEnergyChar_eq_line_add_offLine {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (a b : ℝ) :
    windowEnergyChar hχ a b = lineEnergyChar hχ a b + offLineEnergyChar hχ a b := by
  rw [windowEnergyChar, lineEnergyChar, offLineEnergyChar]
  exact (Finset.sum_filter_add_sum_filter_not _ (fun s : ℂ => s.re = 1 / 2) _).symm

/-- **Every zero event costs at least one quantum**: the census is dominated by the energy. -/
theorem boxCountChar_le_windowEnergyChar {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) (a b : ℝ) :
    HelixStandingWave.boxCountChar hχ a b ≤ windowEnergyChar hχ a b := by
  rw [HelixStandingWave.boxCountChar, windowEnergyChar, Finset.card_eq_sum_ones]
  refine Finset.sum_le_sum fun s hs => ?_
  rw [Set.Finite.mem_toFinset] at hs
  exact DirichletLHadamard.lOrderNat_pos hχ
    (DirichletLHadamard.completedLFunction_zero_mem_NontrivialZeros hχ hχp hs.2)

/-- **The twin tax**: a single off-line event in a window forces off-line energy ≥ 2 — the event
    and its reflection twin each cost at least one quantum, at the same height. Leaving the line
    is never priced below two quanta. -/
theorem two_le_offLineEnergyChar_of_event {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) {a b : ℝ} {s : ℂ}
    (hbox : s ∈ HelixStandingWave.stripBox a b)
    (hzero : DirichletCharacter.completedLFunction χ s = 0) (hoff : s.re ≠ 1 / 2) :
    2 ≤ offLineEnergyChar hχ a b := by
  obtain ⟨s', hne, hbox', hzero', hoff', _⟩ :=
    offLine_event_has_partner hχ hχp hbox hzero hoff
  have hsmem : s ∈ (HelixStandingWave.stripBox_zeros_finite_char hχ a b).toFinset.filter
      (fun s => s.re ≠ 1 / 2) := by
    rw [Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨⟨hbox, hzero⟩, hoff⟩
  have hs'mem : s' ∈ (HelixStandingWave.stripBox_zeros_finite_char hχ a b).toFinset.filter
      (fun s => s.re ≠ 1 / 2) := by
    rw [Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨⟨hbox', hzero'⟩, hoff'⟩
  have hsub : ({s, s'} : Finset ℂ)
      ⊆ (HelixStandingWave.stripBox_zeros_finite_char hχ a b).toFinset.filter
        (fun s => s.re ≠ 1 / 2) := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hsmem
    · rw [Finset.mem_singleton.mp hx]
      exact hs'mem
  have hpair : ∑ x ∈ ({s, s'} : Finset ℂ), DirichletLHadamard.lOrderNat χ x
      = DirichletLHadamard.lOrderNat χ s + DirichletLHadamard.lOrderNat χ s' :=
    Finset.sum_pair (Ne.symm hne)
  have h1 : 1 ≤ DirichletLHadamard.lOrderNat χ s :=
    DirichletLHadamard.lOrderNat_pos hχ
      (DirichletLHadamard.completedLFunction_zero_mem_NontrivialZeros hχ hχp hzero)
  have h2 : 1 ≤ DirichletLHadamard.lOrderNat χ s' :=
    DirichletLHadamard.lOrderNat_pos hχ
      (DirichletLHadamard.completedLFunction_zero_mem_NontrivialZeros hχ hχp hzero')
  calc 2 ≤ DirichletLHadamard.lOrderNat χ s + DirichletLHadamard.lOrderNat χ s' := by omega
    _ = ∑ x ∈ ({s, s'} : Finset ℂ), DirichletLHadamard.lOrderNat χ x := hpair.symm
    _ ≤ offLineEnergyChar hχ a b := Finset.sum_le_sum_of_subset hsub

/-- **The window's energy budget is finite and explicit**: total spectral energy in a window is
    at most `C·R·log R` for any enclosing radius — the order-1 growth law pricing the whole
    ledger. There is no room for unboundedly many quanta in a window: every mode is paid for out
    of a budget the primes' growth fixes. -/
theorem windowEnergyChar_le_jensen {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) :
    ∃ C > (0 : ℝ), ∃ R₀ > (0 : ℝ), ∀ a b : ℝ, ∀ R, R₀ ≤ R → 1 + |a| + |b| ≤ R →
      (windowEnergyChar hχ a b : ℝ) ≤ C * R * Real.log R := by
  classical
  obtain ⟨C, hC, R₀, hR₀, hbound⟩ :=
    DirichletLHadamard.completedL_weighted_zero_count_disk_bound hχ hχp
  refine ⟨C, hC, R₀, hR₀, fun a b R hR hRab => ?_⟩
  set T := (HelixStandingWave.stripBox_zeros_finite_char hχ a b).toFinset with hT
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
    have hsT : x.1 ∈ {s ∈ HelixStandingWave.stripBox a b |
        DirichletCharacter.completedLFunction χ s = 0} :=
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
  have hsum_eq : (windowEnergyChar hχ a b : ℝ)
      = ∑ ρ ∈ S, (DirichletLHadamard.lOrderNat χ ρ.val : ℝ) := by
    rw [windowEnergyChar, hS, Finset.sum_map]
    push_cast
    rw [← Finset.sum_attach T (fun s => (DirichletLHadamard.lOrderNat χ s : ℝ))]
    rfl
  rw [hsum_eq]
  exact hkey

/-! ## Part 5 — new harmonics cost exactly what is paid -/

/-- **New harmonics cost what is paid — the exact pricing identity, per window.** Anchor the
    ledger at the window's midline `c = 2 + i·(a+b)/2`, where the fibre field provably never
    vanishes. For EVERY radius `R > 0`: the boundary payment — the circle-average of
    `log ‖Λ_χ‖` over the circle of radius `R` — EQUALS the ground value plus the sum over every
    mode inside, each priced at its quantum times its depth, `ord(u) · log (R/‖c−u‖)`. An
    identity, not a bound: no surplus, no deficit, deeper modes cost more, and each new harmonic
    admitted inside the circle raises the cost side by exactly what the boundary pays for it.
    Unconditional — every `χ ≠ 1`, every window anchor, every radius. -/
theorem harmonics_cost_eq_paid {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (a b : ℝ) {R : ℝ} (hR : 0 < R) :
    Real.circleAverage (fun s => Real.log ‖DirichletCharacter.completedLFunction χ s‖)
        (2 + ((a + b) / 2 : ℝ) * I) R
      = ∑ᶠ u, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall (2 + ((a + b) / 2 : ℝ) * I) |R|)) u
          * Real.log (R * ‖(2 + ((a + b) / 2 : ℝ) * I) - u‖⁻¹)
        + Real.log ‖DirichletCharacter.completedLFunction χ
            (2 + ((a + b) / 2 : ℝ) * I)‖ := by
  apply DirichletLHadamard.completedL_jensen_at_center hχ ?_ R hR
  apply DirichletLHadamard.completedLFunction_ne_zero_of_one_le_re hχ
  have hre : ((2 : ℂ) + ((a + b) / 2 : ℝ) * I).re = 2 := by simp
  rw [hre]
  norm_num

/-! ## Part 6 — the off-line premium: the economy never sells the pair at the line's rate

The pricing identity (`harmonics_cost_eq_paid`) prices each mode at `ord · log(R/dist)`. The twin
theorem forces an off-line event to buy TWO modes at one height. Here is the strict economics:
anchored at that height, the twins' anchor-distances satisfy `(2−β)(1+β) = 9/4 − (β−½)² < 9/4` —
their geometric mean is strictly inside the on-line distance — so the pair's combined price
strictly exceeds twice the on-line price at the same height, at every radius. Off-line is not
just taxed double (two quanta), it is charged a strict premium per quantum. The helix geometry
forces the energy economy: there is no rate anywhere at which the off-line pair is affordable at
the line's price. -/

/-- **The premium, algebra core**: `(2−β)(1+β) = 9/4 − (β−½)² < 9/4` strictly, off the line. -/
theorem offline_pair_premium_sq {β : ℝ} (hβ : β ≠ 1 / 2) :
    (2 - β) * (1 + β) < 9 / 4 := by
  have hne : β - 1 / 2 ≠ 0 := sub_ne_zero.mpr hβ
  have h : 0 < (β - 1 / 2) ^ 2 := by positivity
  nlinarith [h]

/-- **The premium, distance form**: with the ledger anchored at the twins' own height
    (`c = 2 + iy`), the product of the twins' anchor-distances is strictly below the square of
    the on-line point's anchor-distance. -/
theorem offline_pair_premium_dist {β y : ℝ} (h0 : 0 < β) (h1 : β < 1) (hβ : β ≠ 1 / 2) :
    ‖((2 : ℂ) + (y : ℂ) * I) - ((β : ℂ) + (y : ℂ) * I)‖
      * ‖((2 : ℂ) + (y : ℂ) * I) - (((1 - β : ℝ) : ℂ) + (y : ℂ) * I)‖
      < ‖((2 : ℂ) + (y : ℂ) * I) - (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ^ 2 := by
  have e1 : ((2 : ℂ) + (y : ℂ) * I) - ((β : ℂ) + (y : ℂ) * I) = (((2 - β : ℝ)) : ℂ) := by
    push_cast
    ring
  have e2 : ((2 : ℂ) + (y : ℂ) * I) - (((1 - β : ℝ) : ℂ) + (y : ℂ) * I)
      = (((1 + β : ℝ)) : ℂ) := by
    push_cast
    ring
  have e3 : ((2 : ℂ) + (y : ℂ) * I) - (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)
      = (((3 / 2 : ℝ)) : ℂ) := by
    push_cast
    ring
  rw [e1, e2, e3, Complex.norm_real, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ 2 - β),
    Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + β),
    Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2)]
  have := offline_pair_premium_sq hβ
  nlinarith [this]

/-- **The off-line premium on prices, every radius**: anchored at the height, the twin pair's
    combined price strictly exceeds twice the on-line price at that height. The forced pair is
    never affordable at the line's rate — the strict economics of leaving the line. -/
theorem offline_pair_price_premium {β y R : ℝ} (h0 : 0 < β) (h1 : β < 1)
    (hβ : β ≠ 1 / 2) (hR : 0 < R) :
    2 * Real.log (R * ‖((2 : ℂ) + (y : ℂ) * I) - (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖⁻¹)
      < Real.log (R * ‖((2 : ℂ) + (y : ℂ) * I) - ((β : ℂ) + (y : ℂ) * I)‖⁻¹)
        + Real.log (R * ‖((2 : ℂ) + (y : ℂ) * I) - (((1 - β : ℝ) : ℂ) + (y : ℂ) * I)‖⁻¹) := by
  have e1 : ((2 : ℂ) + (y : ℂ) * I) - ((β : ℂ) + (y : ℂ) * I) = (((2 - β : ℝ)) : ℂ) := by
    push_cast
    ring
  have e2 : ((2 : ℂ) + (y : ℂ) * I) - (((1 - β : ℝ) : ℂ) + (y : ℂ) * I)
      = (((1 + β : ℝ)) : ℂ) := by
    push_cast
    ring
  have e3 : ((2 : ℂ) + (y : ℂ) * I) - (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)
      = (((3 / 2 : ℝ)) : ℂ) := by
    push_cast
    ring
  rw [e1, e2, e3, Complex.norm_real, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ 2 - β),
    Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + β),
    Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2)]
  have h2β : (0 : ℝ) < 2 - β := by linarith
  have h1β : (0 : ℝ) < 1 + β := by linarith
  have hL : (0 : ℝ) < R * (3 / 2 : ℝ)⁻¹ := by positivity
  have hkey := offline_pair_premium_sq hβ
  have hlt : (R * (3 / 2 : ℝ)⁻¹) ^ 2 < (R * (2 - β)⁻¹) * (R * (1 + β)⁻¹) := by
    have hR2 : (0 : ℝ) < R ^ 2 := by positivity
    have hprod : (0 : ℝ) < (2 - β) * (1 + β) := by positivity
    have hinv : ((3 / 2 : ℝ) ^ 2)⁻¹ < ((2 - β) * (1 + β))⁻¹ :=
      (inv_lt_inv₀ (by positivity) hprod).mpr (by nlinarith [hkey])
    calc (R * (3 / 2 : ℝ)⁻¹) ^ 2 = R ^ 2 * ((3 / 2 : ℝ) ^ 2)⁻¹ := by
          rw [mul_pow]
          ring_nf
      _ < R ^ 2 * ((2 - β) * (1 + β))⁻¹ := mul_lt_mul_of_pos_left hinv hR2
      _ = (R * (2 - β)⁻¹) * (R * (1 + β)⁻¹) := by
          rw [mul_inv]
          ring
  calc 2 * Real.log (R * (3 / 2 : ℝ)⁻¹)
      = Real.log ((R * (3 / 2 : ℝ)⁻¹) ^ 2) := by
        rw [Real.log_pow]
        push_cast
        ring
    _ < Real.log ((R * (2 - β)⁻¹) * (R * (1 + β)⁻¹)) := Real.log_lt_log (by positivity) hlt
    _ = Real.log (R * (2 - β)⁻¹) + Real.log (R * (1 + β)⁻¹) := by
        rw [Real.log_mul (by positivity) (by positivity)]

/-- **The pair's cost is paid out of the slack — the accounting weld.** For any off-line zero
    event `s`, anchor the ledger at its own height (`c = 2 + i·Im s`) and take any radius
    `R > 2`: the priced cost of the forced twin pair is bounded by the PAYMENT minus the ground
    value — the slack. Every other mode's price is non-negative, so the pair must be funded from
    what the boundary pays over the ground state. Contrapositive, as arithmetic: any window-anchor
    where the slack falls below the pair's floor price `2·log(R/2)` (the premium theorem prices
    the pair strictly above the line's rate) hosts NO off-line event at that height. -/
theorem offline_pair_cost_le_slack {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) {s : ℂ}
    (hzero : DirichletCharacter.completedLFunction χ s = 0) (hoff : s.re ≠ 1 / 2)
    {R : ℝ} (hR : 2 < R) :
    Real.log (R * ‖((2 : ℂ) + (s.im : ℝ) * I) - s‖⁻¹)
      + Real.log (R * ‖((2 : ℂ) + (s.im : ℝ) * I) - (1 - (starRingEnd ℂ) s)‖⁻¹)
      ≤ Real.circleAverage
          (fun z => Real.log ‖DirichletCharacter.completedLFunction χ z‖)
          ((2 : ℂ) + (s.im : ℝ) * I) R
        - Real.log ‖DirichletCharacter.completedLFunction χ ((2 : ℂ) + (s.im : ℝ) * I)‖ := by
  set c : ℂ := (2 : ℂ) + (s.im : ℝ) * I with hc_def
  have hRpos : (0 : ℝ) < R := by linarith
  -- the anchor is in nonvanishing territory
  have hcre : c.re = 2 := by simp [hc_def]
  have hc_ne : DirichletCharacter.completedLFunction χ c ≠ 0 :=
    DirichletLHadamard.completedLFunction_ne_zero_of_one_le_re hχ (by rw [hcre]; norm_num)
  -- strip data for s and the twin
  have hmemZ : s ∈ GRHSpectral.NontrivialZeros χ :=
    DirichletLHadamard.completedLFunction_zero_mem_NontrivialZeros hχ hχp hzero
  set s' : ℂ := 1 - (starRingEnd ℂ) s with hs'_def
  have hs'memZ : s' ∈ GRHSpectral.NontrivialZeros χ :=
    HelixStandingWave.one_sub_conj_mem_NontrivialZeros hχ hχp hmemZ
  have hs'zero : DirichletCharacter.completedLFunction χ s' = 0 :=
    DirichletLHadamard.completedLFunction_eq_zero_of_mem hs'memZ
  have hs_ne_s' : s ≠ s' := by
    intro h
    exact hoff ((HelixAsymmetry.onLine_iff_fixed_reflection s).mp h.symm)
  -- anchor distances: real, explicit, < 2
  have hdist_s : c - s = (((2 - s.re : ℝ)) : ℂ) := by
    rw [hc_def]
    apply Complex.ext <;> simp
  have hdist_s' : c - s' = (((1 + s.re : ℝ)) : ℂ) := by
    rw [hc_def, hs'_def]
    apply Complex.ext <;> simp <;> ring
  have hre0 : 0 < s.re := hmemZ.1
  have hre1 : s.re < 1 := hmemZ.2.1
  have hnorm_s : ‖c - s‖ = 2 - s.re := by
    rw [hdist_s, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hnorm_s' : ‖c - s'‖ = 1 + s.re := by
    rw [hdist_s', Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  -- both twins are inside the ball
  have habsR : |R| = R := abs_of_pos hRpos
  have hs_mem : s ∈ Metric.closedBall c |R| := by
    rw [Metric.mem_closedBall, dist_comm, dist_eq_norm, hnorm_s, habsR]
    linarith
  have hs'_mem : s' ∈ Metric.closedBall c |R| := by
    rw [Metric.mem_closedBall, dist_comm, dist_eq_norm, hnorm_s', habsR]
    linarith
  -- analytic/meromorphic frame and the divisor
  have hAnal : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall c |R|) :=
    fun z _ => DirichletLHadamard.completedLFunction_analyticAt hχ z
  have hMero : MeromorphicOn (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall c |R|) := hAnal.meromorphicOn
  set D := MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
    (Metric.closedBall c |R|) with hD_def
  have hD_nn : ∀ u, 0 ≤ D u := fun u => MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAnal u
  have hDs : (1 : ℤ) ≤ D s :=
    DirichletLHadamard.completedL_divisor_ge_one_of_zero hχ hMero s hs_mem hzero
  have hDs' : (1 : ℤ) ≤ D s' :=
    DirichletLHadamard.completedL_divisor_ge_one_of_zero hχ hMero s' hs'_mem hs'zero
  -- term non-negativity over the whole plane
  have h_term_nn : ∀ u, 0 ≤ (D u : ℝ) * Real.log (R * ‖c - u‖⁻¹) := by
    intro u
    by_cases hu : u ∈ Metric.closedBall c |R|
    · by_cases huc : u = c
      · simp [huc]
      · have h_norm_pos : 0 < ‖c - u‖ := by
          rw [norm_pos_iff, sub_ne_zero]
          exact fun h => huc h.symm
        have hu_le : ‖c - u‖ ≤ R := by
          rw [Metric.mem_closedBall, dist_comm, dist_eq_norm, habsR] at hu
          exact hu
        have hlog_nn : 0 ≤ Real.log (R * ‖c - u‖⁻¹) := by
          apply Real.log_nonneg
          rw [show R * ‖c - u‖⁻¹ = R / ‖c - u‖ from by ring, le_div_iff₀ h_norm_pos]
          linarith
        exact mul_nonneg (by exact_mod_cast hD_nn u) hlog_nn
    · have hD0 := D.apply_eq_zero_of_notMem hu
      simp [hD0]
  -- the twins' prices are strictly positive, so both carry support
  have hprice_s_pos : 0 < Real.log (R * ‖c - s‖⁻¹) := by
    apply Real.log_pos
    rw [hnorm_s, show R * (2 - s.re)⁻¹ = R / (2 - s.re) from by ring,
      lt_div_iff₀ (by linarith), one_mul]
    linarith
  have hprice_s'_pos : 0 < Real.log (R * ‖c - s'‖⁻¹) := by
    apply Real.log_pos
    rw [hnorm_s', show R * (1 + s.re)⁻¹ = R / (1 + s.re) from by ring,
      lt_div_iff₀ (by linarith), one_mul]
    linarith
  -- the priced finsum dominates the pair's terms
  have h_fs : (Function.support fun u => (D u : ℝ) * Real.log (R * ‖c - u‖⁻¹)).Finite := by
    apply (D.finiteSupport (isCompact_closedBall c |R|)).subset
    intro u hu
    simp only [Function.mem_support] at hu ⊢
    intro hd
    apply hu
    rw [hd]
    simp
  have h_pair_le : (D s : ℝ) * Real.log (R * ‖c - s‖⁻¹)
      + (D s' : ℝ) * Real.log (R * ‖c - s'‖⁻¹)
      ≤ ∑ᶠ u, (D u : ℝ) * Real.log (R * ‖c - u‖⁻¹) := by
    rw [finsum_eq_sum _ h_fs]
    have hsum : ∑ u ∈ ({s, s'} : Finset ℂ), (D u : ℝ) * Real.log (R * ‖c - u‖⁻¹)
        = (D s : ℝ) * Real.log (R * ‖c - s‖⁻¹) + (D s' : ℝ) * Real.log (R * ‖c - s'‖⁻¹) :=
      Finset.sum_pair hs_ne_s'
    rw [← hsum]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro u hu
      rw [Set.Finite.mem_toFinset, Function.mem_support]
      rcases Finset.mem_insert.mp hu with rfl | hu
      · intro h
        rcases mul_eq_zero.mp h with hd | hl
        · rw [show ((D u : ℝ) = 0) ↔ D u = 0 from by exact_mod_cast Int.cast_eq_zero] at hd
          omega
        · linarith [hprice_s_pos, hl]
      · rw [Finset.mem_singleton.mp hu]
        intro h
        rcases mul_eq_zero.mp h with hd | hl
        · rw [show ((D s' : ℝ) = 0) ↔ D s' = 0 from by exact_mod_cast Int.cast_eq_zero] at hd
          omega
        · linarith [hprice_s'_pos, hl]
    · intro u _ _
      exact h_term_nn u
  -- the pair's coefficients are ≥ 1 and prices ≥ 0
  have h_price_le_term : Real.log (R * ‖c - s‖⁻¹) + Real.log (R * ‖c - s'‖⁻¹)
      ≤ (D s : ℝ) * Real.log (R * ‖c - s‖⁻¹) + (D s' : ℝ) * Real.log (R * ‖c - s'‖⁻¹) := by
    have h1 : Real.log (R * ‖c - s‖⁻¹) ≤ (D s : ℝ) * Real.log (R * ‖c - s‖⁻¹) := by
      nlinarith [hprice_s_pos, (by exact_mod_cast hDs : (1 : ℝ) ≤ (D s : ℝ))]
    have h2 : Real.log (R * ‖c - s'‖⁻¹) ≤ (D s' : ℝ) * Real.log (R * ‖c - s'‖⁻¹) := by
      nlinarith [hprice_s'_pos, (by exact_mod_cast hDs' : (1 : ℝ) ≤ (D s' : ℝ))]
    linarith
  -- the exact payment identity closes the account
  have hpay := DirichletLHadamard.completedL_jensen_at_center hχ hc_ne R hRpos
  rw [hpay]
  have := le_trans h_price_le_term h_pair_le
  linarith

/-- **An off-line event forces surplus payment — the floor, unconditional.** If any off-line zero
    exists at height `y`, then at that height's anchor, for EVERY radius `R > 2`, the slack
    (payment minus ground) strictly exceeds the floor `2·log(R/2)`: both twins sit within
    distance `2` of the anchor, so each is priced strictly above `log(R/2)`, and the pair is paid
    out of the slack (`offline_pair_cost_le_slack`). Contrapositive, as arithmetic: any height
    anchor whose slack is ever measured `≤ 2·log(R/2)` hosts no off-line event — the economy's
    kill criterion is one number per height. -/
theorem slack_gt_of_offline {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) {s : ℂ}
    (hzero : DirichletCharacter.completedLFunction χ s = 0) (hoff : s.re ≠ 1 / 2)
    {R : ℝ} (hR : 2 < R) :
    2 * Real.log (R / 2)
      < Real.circleAverage
          (fun z => Real.log ‖DirichletCharacter.completedLFunction χ z‖)
          ((2 : ℂ) + (s.im : ℝ) * I) R
        - Real.log ‖DirichletCharacter.completedLFunction χ ((2 : ℂ) + (s.im : ℝ) * I)‖ := by
  set c : ℂ := (2 : ℂ) + (s.im : ℝ) * I with hc_def
  have hmemZ : s ∈ GRHSpectral.NontrivialZeros χ :=
    DirichletLHadamard.completedLFunction_zero_mem_NontrivialZeros hχ hχp hzero
  have hre0 : 0 < s.re := hmemZ.1
  have hre1 : s.re < 1 := hmemZ.2.1
  have hdist_s : c - s = (((2 - s.re : ℝ)) : ℂ) := by
    rw [hc_def]
    apply Complex.ext <;> simp
  have hdist_s' : c - (1 - (starRingEnd ℂ) s) = (((1 + s.re : ℝ)) : ℂ) := by
    rw [hc_def]
    apply Complex.ext <;> simp <;> ring
  have hnorm_s : ‖c - s‖ = 2 - s.re := by
    rw [hdist_s, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hnorm_s' : ‖c - (1 - (starRingEnd ℂ) s)‖ = 1 + s.re := by
    rw [hdist_s', Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hfloor_s : Real.log (R / 2) < Real.log (R * ‖c - s‖⁻¹) := by
    rw [hnorm_s, show R * (2 - s.re)⁻¹ = R / (2 - s.re) from by ring]
    apply Real.log_lt_log (by positivity)
    apply div_lt_div_of_pos_left (by linarith) (by linarith)
    linarith
  have hfloor_s' : Real.log (R / 2) < Real.log (R * ‖c - (1 - (starRingEnd ℂ) s)‖⁻¹) := by
    rw [hnorm_s', show R * (1 + s.re)⁻¹ = R / (1 + s.re) from by ring]
    apply Real.log_lt_log (by positivity)
    apply div_lt_div_of_pos_left (by linarith) (by linarith)
    linarith
  have hslack := offline_pair_cost_le_slack hχ hχp hzero hoff hR
  rw [← hc_def] at hslack
  linarith

/-! ## Part 7 — the budget is an `L`-budget: the archimedean account funds nothing

The slack was defined through the completed field `Λ = γ·L`. Here the ledger localizes: on any
ball staying right of the imaginary axis, the Γ-factor is analytic and nonvanishing, so it
contributes ZERO modes to the priced sum — the slack of `Λ` EQUALS the slack of `L`
(`slack_eq_L_slack`). There is no archimedean account for an off-line event to draw on. And the
`L`-budget is then capped explicitly by the ledger's polynomial growth bound
(`circleAverage_log_L_le`): the whole payment at any anchor is at most `log (N(‖c‖+R)/(Re c − R))`.
What remains of the program after this cap is exclusively the LINE's share of the payment — the
production rate — since every other account is now either exactly zero or explicitly bounded. -/

/-- `Γℝ` is analytic wherever `Re > 0` (inverse of the entire `Γℝ⁻¹`, nonvanishing there). -/
theorem Gammaℝ_analyticAt_of_re_pos {u : ℂ} (hu : 0 < u.re) :
    AnalyticAt ℂ Complex.Gammaℝ u := by
  have hinv : AnalyticAt ℂ (fun s => (Complex.Gammaℝ s)⁻¹) u :=
    (analyticOnNhd_univ_iff_differentiable.mpr Complex.differentiable_Gammaℝ_inv) u
      (Set.mem_univ u)
  have hne : (Complex.Gammaℝ u)⁻¹ ≠ 0 :=
    inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos hu)
  have h2 := hinv.inv hne
  have heq : (fun s => (Complex.Gammaℝ s)⁻¹)⁻¹ = Complex.Gammaℝ := by
    funext s
    simp [Pi.inv_apply, inv_inv]
  rwa [heq] at h2

/-- The Γ-factor is analytic wherever `Re > 0` (both parity branches). -/
theorem gammaFactor_analyticAt_of_re_pos {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    {u : ℂ} (hu : 0 < u.re) :
    AnalyticAt ℂ χ.gammaFactor u := by
  rcases χ.even_or_odd with h | h
  · have heq : χ.gammaFactor = fun s => Complex.Gammaℝ s :=
      funext fun s => h.gammaFactor_def s
    rw [heq]
    exact Gammaℝ_analyticAt_of_re_pos hu
  · have heq : χ.gammaFactor = fun s => Complex.Gammaℝ (s + 1) :=
      funext fun s => h.gammaFactor_def s
    rw [heq]
    have h1 : 0 < (u + 1).re := by
      rw [Complex.add_re, Complex.one_re]
      linarith
    have hinner : AnalyticAt ℂ (fun z : ℂ => z + 1) u :=
      (analyticAt_id).add analyticAt_const
    have hcomp := AnalyticAt.comp (f := fun z : ℂ => z + 1) (x := u)
      (Gammaℝ_analyticAt_of_re_pos h1) hinner
    exact hcomp

/-- **The archimedean account funds nothing — the slack localizes to `L`.** On any ball staying
    right of the imaginary axis, `Λ = γ·L` with `γ` analytic and nonvanishing, so the divisors of
    `Λ` and `L` agree everywhere on the ball, and the two Jensen identities subtract to the SAME
    slack: payment minus ground for `Λ` equals payment minus ground for `L`. Every quantum the
    off-line pair must draw is an `L`-quantum. -/
theorem slack_eq_L_slack {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) {c : ℂ} {R : ℝ} (hR0 : 0 < R) (hRc : R < c.re)
    (hΛc : DirichletCharacter.completedLFunction χ c ≠ 0) :
    Real.circleAverage (fun z => Real.log ‖DirichletCharacter.completedLFunction χ z‖) c R
      - Real.log ‖DirichletCharacter.completedLFunction χ c‖
    = Real.circleAverage (fun z => Real.log ‖DirichletCharacter.LFunction χ z‖) c R
      - Real.log ‖DirichletCharacter.LFunction χ c‖ := by
  have habsR : |R| = R := abs_of_pos hR0
  -- every point of the ball is right of the axis
  have hre_ball : ∀ u ∈ Metric.closedBall c |R|, 0 < u.re := by
    intro u hu
    rw [Metric.mem_closedBall, dist_comm, dist_eq_norm, habsR] at hu
    have habs : |(c - u).re| ≤ ‖c - u‖ := Complex.abs_re_le_norm _
    have hre : (c - u).re = c.re - u.re := by simp [Complex.sub_re]
    rw [hre] at habs
    have := (abs_le.mp (le_trans habs hu)).2
    linarith
  have hcre : 0 < c.re := by linarith
  have hc0 : c ≠ 0 := fun h => by rw [h, Complex.zero_re] at hcre; exact lt_irrefl 0 hcre
  -- the pointwise factorization Λ = γ·L on Re > 0, and L(c) ≠ 0
  have hfac : ∀ z : ℂ, 0 < z.re →
      DirichletCharacter.completedLFunction χ z
        = χ.gammaFactor z * DirichletCharacter.LFunction χ z := by
    intro z hz
    have hz0 : z ≠ 0 := fun h => by rw [h, Complex.zero_re] at hz; exact lt_irrefl 0 hz
    have hrel := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ z (Or.inl hz0)
    have hγ : χ.gammaFactor z ≠ 0 := DirichletLHadamard.gammaFactor_ne_zero hz
    rw [hrel]
    field_simp
  have hLc : DirichletCharacter.LFunction χ c ≠ 0 := by
    intro h
    apply hΛc
    rw [hfac c hcre, h, mul_zero]
  -- analytic frames
  have hAnalΛ : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall c |R|) :=
    fun z _ => DirichletLHadamard.completedLFunction_analyticAt hχ z
  have hMeroΛ : MeromorphicOn (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall c |R|) := hAnalΛ.meromorphicOn
  have hLDiff : Differentiable ℂ (DirichletCharacter.LFunction χ) := by
    intro z
    exact DirichletClosureLedger.LFunction_differentiableAt χ hχ z
  have hAnalL : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ)
      (Metric.closedBall c |R|) := fun z _ =>
    (hLDiff.differentiableOn.analyticOnNhd isOpen_univ) z (Set.mem_univ z)
  have hMeroL : MeromorphicOn (DirichletCharacter.LFunction χ)
      (Metric.closedBall c |R|) := hAnalL.meromorphicOn
  -- the divisors agree on the ball
  have hdiv : ∀ u,
      MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall c |R|) u
      = MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
        (Metric.closedBall c |R|) u := by
    intro u
    by_cases hu : u ∈ Metric.closedBall c |R|
    · have hure : 0 < u.re := hre_ball u hu
      have hγa : AnalyticAt ℂ χ.gammaFactor u := gammaFactor_analyticAt_of_re_pos hure
      have hγne : χ.gammaFactor u ≠ 0 := DirichletLHadamard.gammaFactor_ne_zero hure
      have hLa : AnalyticAt ℂ (DirichletCharacter.LFunction χ) u :=
        hAnalL u hu
      have hΛa : AnalyticAt ℂ (DirichletCharacter.completedLFunction χ) u :=
        DirichletLHadamard.completedLFunction_analyticAt hχ u
      have hev : DirichletCharacter.completedLFunction χ
          =ᶠ[nhds u] fun z => χ.gammaFactor z * DirichletCharacter.LFunction χ z := by
        filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
          (show (0 : ℝ) < u.re from hure)] with z hz
        exact hfac z hz
      have hord : analyticOrderAt (DirichletCharacter.completedLFunction χ) u
          = analyticOrderAt (DirichletCharacter.LFunction χ) u := by
        rw [analyticOrderAt_congr hev,
          show (fun z => χ.gammaFactor z * DirichletCharacter.LFunction χ z)
            = χ.gammaFactor * DirichletCharacter.LFunction χ from rfl,
          analyticOrderAt_mul hγa hLa,
          show analyticOrderAt χ.gammaFactor u = 0 from by
            rw [analyticOrderAt_eq_zero]
            right
            exact hγne,
          zero_add]
      rw [MeromorphicOn.divisor_apply hMeroΛ hu, MeromorphicOn.divisor_apply hMeroL hu,
        hΛa.meromorphicOrderAt_eq, hLa.meromorphicOrderAt_eq, hord]
    · rw [(MeromorphicOn.divisor _ _).apply_eq_zero_of_notMem hu,
        (MeromorphicOn.divisor _ _).apply_eq_zero_of_notMem hu]
  -- the two Jensen identities
  have hJΛ := DirichletLHadamard.completedL_jensen_at_center hχ hΛc R hR0
  have hJL : Real.circleAverage
      (fun z => Real.log ‖DirichletCharacter.LFunction χ z‖) c R
      = ∑ᶠ u, (MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
          (Metric.closedBall c |R|)) u * Real.log (R * ‖c - u‖⁻¹)
        + Real.log ‖DirichletCharacter.LFunction χ c‖ := by
    have hJensen := MeromorphicOn.circleAverage_log_norm hR0.ne' hMeroL
    have hc_mem : c ∈ Metric.closedBall c |R| := by
      simp [Metric.mem_closedBall]
    have hLa : AnalyticAt ℂ (DirichletCharacter.LFunction χ) c := hAnalL c hc_mem
    have hDiv0 : (MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
        (Metric.closedBall c |R|)) c = 0 := by
      rw [MeromorphicOn.divisor_apply hMeroL hc_mem]
      have hAnalOrd : analyticOrderAt (DirichletCharacter.LFunction χ) c = 0 := by
        rw [analyticOrderAt_eq_zero]
        right
        exact hLc
      rw [hLa.meromorphicOrderAt_eq, hAnalOrd]
      rfl
    have hTrail : meromorphicTrailingCoeffAt (DirichletCharacter.LFunction χ) c
        = DirichletCharacter.LFunction χ c :=
      hLa.meromorphicTrailingCoeffAt_of_ne_zero hLc
    rw [hJensen, hDiv0, hTrail]
    push_cast
    ring_nf
  -- the priced finsums agree, so the slacks agree
  have hfinsum : (∑ᶠ u, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall c |R|)) u * Real.log (R * ‖c - u‖⁻¹) : ℝ)
      = ∑ᶠ u, (MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
        (Metric.closedBall c |R|)) u * Real.log (R * ‖c - u‖⁻¹) := by
    apply finsum_congr
    intro u
    rw [hdiv u]
  rw [hJΛ, hJL]
  rw [hfinsum]
  ring

/-- **The explicit budget cap.** At any anchor right of the axis (`R < Re c`), the whole payment —
    the circle-average of `log ‖L‖` — is at most `log (N·(‖c‖+R)/(Re c − R))`: the ledger's
    polynomial growth law prices the entire boundary. With `slack_eq_L_slack`, every account an
    off-line event could draw on is now either exactly zero (archimedean) or explicitly capped. -/
theorem circleAverage_log_L_le {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) {c : ℂ} {R : ℝ} (hR0 : 0 < R) (hRc : R < c.re) :
    Real.circleAverage (fun z => Real.log ‖DirichletCharacter.LFunction χ z‖) c R
      ≤ Real.log ((N : ℝ) * (‖c‖ + R) / (c.re - R)) := by
  have habsR : |R| = R := abs_of_pos hR0
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hcnorm : c.re ≤ ‖c‖ := le_trans (le_abs_self _) (Complex.abs_re_le_norm c)
  have hbound_pos : (0 : ℝ) < (N : ℝ) * (‖c‖ + R) / (c.re - R) := by
    apply div_pos
    · have : (0 : ℝ) < ‖c‖ + R := by
        have : (0 : ℝ) < c.re := by linarith
        linarith
      positivity
    · linarith
  have hbound_ge_one : (1 : ℝ) ≤ (N : ℝ) * (‖c‖ + R) / (c.re - R) := by
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < c.re - R)]
    have h1 : c.re - R ≤ ‖c‖ + R := by linarith
    nlinarith [hN1, h1, (show (0 : ℝ) < ‖c‖ + R by nlinarith)]
  have hLDiff : Differentiable ℂ (DirichletCharacter.LFunction χ) := by
    intro z
    exact DirichletClosureLedger.LFunction_differentiableAt χ hχ z
  have hAnalSph : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ)
      (Metric.sphere c |R|) := fun z _ =>
    (hLDiff.differentiableOn.analyticOnNhd isOpen_univ) z (Set.mem_univ z)
  have hCI : CircleIntegrable
      (fun z => Real.log ‖DirichletCharacter.LFunction χ z‖) c R :=
    circleIntegrable_log_norm_meromorphicOn hAnalSph.meromorphicOn
  apply Real.circleAverage_mono_on_of_le_circle hCI
  intro z hz
  rw [Metric.mem_sphere, dist_comm, dist_eq_norm, habsR] at hz
  have habs : |(c - z).re| ≤ ‖c - z‖ := Complex.abs_re_le_norm _
  have hre : (c - z).re = c.re - z.re := by simp [Complex.sub_re]
  rw [hre, hz] at habs
  have hzre : c.re - R ≤ z.re := by
    have := (abs_le.mp habs).2
    linarith
  have hzre0 : 0 < z.re := by linarith
  have hznorm : ‖z‖ ≤ ‖c‖ + R := by
    calc ‖z‖ = ‖c + (z - c)‖ := by ring_nf
      _ ≤ ‖c‖ + ‖z - c‖ := norm_add_le _ _
      _ = ‖c‖ + R := by rw [← norm_neg (z - c), neg_sub, hz]
  rcases eq_or_lt_of_le (norm_nonneg (DirichletCharacter.LFunction χ z)) with h0 | hpos
  · rw [← h0, Real.log_zero]
    exact Real.log_nonneg hbound_ge_one
  · have hmain := DirichletClosureLedger.norm_LFunction_le_half_plane χ hχ z hzre0
    apply Real.log_le_log hpos
    calc ‖DirichletCharacter.LFunction χ z‖ ≤ (N : ℝ) * ‖z‖ / z.re := hmain
      _ ≤ (N : ℝ) * (‖c‖ + R) / (c.re - R) := by
          gcongr

/-! ## Part 8 — the currency is geometric, and the off-line datum is inexpressible

The program's currency: height at a loop of radius `√n`, on a helix of fixed pitch — the energy
OF the geometry. The prime-built fibers produce exactly that energy, nothing more, nothing less
(`EnergyBalance.energy_balance`, `sole_origin`: prime side = spectral side, residue = quantum).
Zero locations do not pre-exist the geometry — a zero is a cancellation event ON the helix and has
no `L`-free existence (`Origination.zeros_dependentlyOriginated`).

In this currency, an off-line zero is not a forbidden value — it is NOT A VALUE. Its amplitude
datum `n ↦ n^β`, `β ≠ ½`, is overdetermined already at TWO integers: the helix's one deformation
freedom (the pitch/scale `a`) can match `n^β` at a single integer, and the second integer then
forces `β = ½` (`offline_amplitude_inexpressible`). Like division by zero, the expression "the
helix point of an off-line zero" has no denotation; the helix expresses exactly the `½`-law and
nothing else (`helix_amplitude_half_law`). What remains for the sync — that the `iy` projection
loss re-expands to the cost of each next harmonic for the entire height range — is the census
number `offLineCountChar = 0`, window by window: the admissions the geometry produces are all the
admissions there are. -/

/-- **The off-line amplitude law has no helix expression — at any pitch.** The helix's single
    deformation freedom (the scale `a > 0`) can fit `a·√n = n^β` at ONE integer; requiring it at
    `n = 2` AND `n = 4` already forces `β = ½`. For `β ≠ ½` the system is inconsistent: the
    off-line datum is overdetermined, with no `(pitch, exponent)` solution — not a constrained
    value but no value at all. -/
theorem offline_amplitude_inexpressible {a β : ℝ} (hβ : β ≠ 1 / 2) :
    ¬ (a * Real.sqrt 2 = (2 : ℝ) ^ β ∧ a * Real.sqrt 4 = (4 : ℝ) ^ β) := by
  rintro ⟨h2, h4⟩
  rw [Real.sqrt_eq_rpow] at h2
  have hs4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 from by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [hs4] at h4
  have h4' : (4 : ℝ) ^ β = (2 : ℝ) ^ β * (2 : ℝ) ^ β := by
    rw [show (4 : ℝ) = 2 * 2 from by norm_num,
      Real.mul_rpow (by norm_num) (by norm_num)]
  rw [h4'] at h4
  have hxpos : (0 : ℝ) < (2 : ℝ) ^ β := Real.rpow_pos_of_pos (by norm_num) β
  have hsq : (2 : ℝ) ^ ((1 : ℝ) / 2) * (2 : ℝ) ^ ((1 : ℝ) / 2) = 2 := by
    rw [← Real.rpow_add (by norm_num)]
    norm_num
  have hstep : a * 2 = (2 : ℝ) ^ β * (2 : ℝ) ^ ((1 : ℝ) / 2) := by
    calc a * 2 = a * ((2 : ℝ) ^ ((1 : ℝ) / 2) * (2 : ℝ) ^ ((1 : ℝ) / 2)) := by rw [hsq]
      _ = (a * (2 : ℝ) ^ ((1 : ℝ) / 2)) * (2 : ℝ) ^ ((1 : ℝ) / 2) := by ring
      _ = (2 : ℝ) ^ β * (2 : ℝ) ^ ((1 : ℝ) / 2) := by rw [h2]
  have hcancel : (2 : ℝ) ^ β = (2 : ℝ) ^ ((1 : ℝ) / 2) :=
    mul_left_cancel₀ hxpos.ne' (h4.symm.trans hstep)
  rcases lt_trichotomy β ((1 : ℝ) / 2) with hlt | heq | hgt
  · exact absurd hcancel (ne_of_lt ((Real.rpow_lt_rpow_left_iff
      (by norm_num : (1 : ℝ) < 2)).2 hlt))
  · exact hβ heq
  · exact absurd hcancel (ne_of_gt ((Real.rpow_lt_rpow_left_iff
      (by norm_num : (1 : ℝ) < 2)).2 hgt))

/-- **The helix expresses exactly the `½`-law**: every point of the constructed helix, at every
    phase assignment, has amplitude `n^{1/2}` — the one amplitude law the geometry denotes. -/
theorem helix_amplitude_half_law (θ : ℕ → ℝ) (n : ℕ) :
    ‖HelixLogFree.helixPt θ n‖ = (n : ℝ) ^ ((1 : ℝ) / 2) := by
  rw [HelixLogFree.norm_helixPt, Real.sqrt_eq_rpow]

/-! ## Part 9 — no secrets: the ladder determines the function

The construction is public (`Config`), the readout is a closed formula in the winding (the gauge
identity), and the rungs are its resonances (`resonates_at_zeros`) — Config ⟹ function ⟹ ladder.
Here is the return arrow, closing the triangle: **the ladder determines the function** — any two
completed fields with the same rungs at the same multiplicities (even over different conductors)
have the same resolvent trace and log-derivatives differing by one gauge constant. Each rung's
energy is its residue (`sole_origin`), so the ladder IS the cumulative energy record of the
construction, and the record is faithful: nothing about the analytic object is hidden from the
ladder, and no rung can be added to or removed from a ladder without changing the function it
determines. There is no glue in which a secret off-line rung could live without being a different
function — of a different ladder — visibly. -/

/-- **Same ladder, same trace**: two characters (any conductors) whose nontrivial zeros agree as a
    set with matching multiplicities have IDENTICAL dual resolvent traces, everywhere. -/
theorem ladder_determines_trace {N₁ N₂ : ℕ} [NeZero N₁] [NeZero N₂]
    {χ₁ : DirichletCharacter ℂ N₁} {χ₂ : DirichletCharacter ℂ N₂}
    (hset : GRHSpectral.NontrivialZeros χ₁ = GRHSpectral.NontrivialZeros χ₂)
    (hord : ∀ ρ ∈ GRHSpectral.NontrivialZeros χ₁,
      DirichletLHadamard.lOrderNat χ₁ ρ = DirichletLHadamard.lOrderNat χ₂ ρ) (s : ℂ) :
    HelixDualOperator.dualResolventTrace χ₁ s = HelixDualOperator.dualResolventTrace χ₂ s := by
  unfold HelixDualOperator.dualResolventTrace
  rw [hset]
  refine tsum_congr fun ρ => ?_
  have hmem : ρ.val ∈ GRHSpectral.NontrivialZeros χ₁ := by
    rw [hset]
    exact ρ.property
  rw [hord ρ.val hmem]

/-- **The ladder determines the function** (up to one gauge constant): any two primitive
    non-principal characters with the same rungs at the same multiplicities have log-derivatives
    of their completed fields differing by a single constant, everywhere off the ladder. The zero
    ladder is a faithful, public encoding of the analytic object — no secrets. -/
theorem ladder_determines_logDeriv {N₁ N₂ : ℕ} [NeZero N₁] [NeZero N₂]
    {χ₁ : DirichletCharacter ℂ N₁} {χ₂ : DirichletCharacter ℂ N₂}
    (hχ₁ : χ₁ ≠ 1) (hχp₁ : χ₁.IsPrimitive) (hχ₂ : χ₂ ≠ 1) (hχp₂ : χ₂.IsPrimitive)
    (hset : GRHSpectral.NontrivialZeros χ₁ = GRHSpectral.NontrivialZeros χ₂)
    (hord : ∀ ρ ∈ GRHSpectral.NontrivialZeros χ₁,
      DirichletLHadamard.lOrderNat χ₁ ρ = DirichletLHadamard.lOrderNat χ₂ ρ) :
    ∃ c : ℂ, ∀ s ∉ GRHSpectral.NontrivialZeros χ₁,
      logDeriv (DirichletCharacter.completedLFunction χ₁) s
        = c + logDeriv (DirichletCharacter.completedLFunction χ₂) s := by
  obtain ⟨A₁, h₁⟩ := HelixDualOperator.dualResolventTrace_eq_logDeriv χ₁ hχ₁ hχp₁
  obtain ⟨A₂, h₂⟩ := HelixDualOperator.dualResolventTrace_eq_logDeriv χ₂ hχ₂ hχp₂
  refine ⟨A₁ - A₂, fun s hs => ?_⟩
  have hs₂ : s ∉ GRHSpectral.NontrivialZeros χ₂ := by
    rw [← hset]
    exact hs
  rw [h₁ s hs, h₂ s hs₂, ladder_determines_trace hset hord s]
  ring

/-! ## Part 10 — the induction frame: minimal criminal atop a fully-synced history

The ladder is climbed by induction. The carrier: `offLineCountChar`, monotone in the window
(`offLineCountChar_mono`). The well-ordering: zero events in any window are finite, so if ANY
off-line event exists there is a FIRST one — minimal `|height|` — and strictly below it every
event is on the line (`exists_minimal_offline`). On every window strictly below the criminal, the
off-line census vanishes and the counters agree exactly (`offLineCountChar_eq_zero_below_minimal`,
`counters_agree_below_minimal`): the history beneath the first criminal is fully synced — the
ladder below IS the production schedule, verified.

The induction step left to prove is now in its sharpest form: the first criminal must arrive as a
TWIN PAIR at one height (`offLine_event_has_partner`), costing two quanta at a strict premium
(`two_le_offLineEnergyChar_of_event`, `offline_pair_price_premium`), funded only from the slack
(`offline_pair_cost_le_slack`), with an amplitude the geometry cannot denote
(`offline_amplitude_inexpressible`) — atop a history that the public construction fully
determines (`ladder_determines_logDeriv`) and has already produced flip-for-rung. -/

/-- **The off-line census is monotone in the window.** -/
theorem offLineCountChar_mono {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) {a b a' b' : ℝ} (ha : a' ≤ a) (hb : b ≤ b') :
    offLineCountChar hχ a b ≤ offLineCountChar hχ a' b' := by
  apply Finset.card_le_card
  intro s hs
  rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hs ⊢
  obtain ⟨⟨⟨hre, him⟩, hzero⟩, hoff⟩ := hs
  exact ⟨⟨⟨hre, ⟨le_trans ha him.1, le_trans him.2 hb⟩⟩, hzero⟩, hoff⟩

/-- **The minimal criminal**: if any off-line zero event exists, there is a FIRST one — of
    minimal `|height|` among all off-line events. Below it, the ladder is clean. -/
theorem exists_minimal_offline {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) {ρ₀ : ℂ}
    (h₀ : DirichletCharacter.completedLFunction χ ρ₀ = 0) (hρ₀ : ρ₀.re ≠ 1 / 2) :
    ∃ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 ∧ ρ.re ≠ 1 / 2 ∧
      ∀ z : ℂ, DirichletCharacter.completedLFunction χ z = 0 → z.re ≠ 1 / 2 →
        |ρ.im| ≤ |z.im| := by
  set T₀ : ℝ := |ρ₀.im| with hT₀
  set S : Finset ℂ :=
    (HelixStandingWave.stripBox_zeros_finite_char hχ (-T₀) T₀).toFinset.filter
      (fun s => s.re ≠ 1 / 2) with hS
  have hmem_of : ∀ z : ℂ, DirichletCharacter.completedLFunction χ z = 0 → z.re ≠ 1 / 2 →
      |z.im| ≤ T₀ → z ∈ S := by
    intro z hz hzre hzT
    have hmemZ : z ∈ GRHSpectral.NontrivialZeros χ :=
      DirichletLHadamard.completedLFunction_zero_mem_NontrivialZeros hχ hχp hz
    rw [hS, Finset.mem_filter, Set.Finite.mem_toFinset]
    refine ⟨⟨⟨⟨hmemZ.1.le, hmemZ.2.1.le⟩, ?_, ?_⟩, hz⟩, hzre⟩
    · linarith [neg_abs_le z.im]
    · linarith [le_abs_self z.im]
  have hne : S.Nonempty := ⟨ρ₀, hmem_of ρ₀ h₀ hρ₀ (le_refl _)⟩
  obtain ⟨ρ, hρS, hmin⟩ := S.exists_min_image (fun s => |s.im|) hne
  rw [hS, Finset.mem_filter, Set.Finite.mem_toFinset] at hρS
  refine ⟨ρ, hρS.1.2, hρS.2, fun z hz hzre => ?_⟩
  by_cases hzT : |z.im| ≤ T₀
  · exact hmin z (hmem_of z hz hzre hzT)
  · push_neg at hzT
    have hρT : |ρ.im| ≤ T₀ := hmin ρ₀ (hmem_of ρ₀ h₀ hρ₀ (le_refl _)) |>.trans_eq rfl
    linarith [hmin ρ₀ (hmem_of ρ₀ h₀ hρ₀ (le_refl _))]

/-- **Below the first criminal, the off-line census is zero**: every window contained strictly
    under the criminal's height carries no off-line event. -/
theorem offLineCountChar_eq_zero_below_minimal {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) {ρ : ℂ}
    (hmin : ∀ z : ℂ, DirichletCharacter.completedLFunction χ z = 0 → z.re ≠ 1 / 2 →
      |ρ.im| ≤ |z.im|)
    {a b : ℝ} (ha : -|ρ.im| < a) (hb : b < |ρ.im|) :
    offLineCountChar hχ a b = 0 := by
  rw [offLineCountChar, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro s hs
  rw [Set.Finite.mem_toFinset] at hs
  obtain ⟨⟨_, him⟩, hzero⟩ := hs
  by_contra hoff
  have hkey := hmin s hzero hoff
  have h3 : |s.im| < |ρ.im| := by
    rw [abs_lt]
    exact ⟨by linarith [him.1], by linarith [him.2]⟩
  linarith

/-- **Below the first criminal, the counters agree exactly**: the strip census equals the line
    census on every window under the criminal — the history beneath the first off-line event is
    fully synced, flip for rung. -/
theorem counters_agree_below_minimal {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) {ρ : ℂ}
    (hmin : ∀ z : ℂ, DirichletCharacter.completedLFunction χ z = 0 → z.re ≠ 1 / 2 →
      |ρ.im| ≤ |z.im|)
    {a b : ℝ} (ha : -|ρ.im| < a) (hb : b < |ρ.im|) :
    HelixStandingWave.boxCountChar hχ a b = HelixStandingWave.nodeCountChar hχ a b := by
  have h0 := offLineCountChar_eq_zero_below_minimal hχ hχp hmin ha hb
  have hsplit := boxCountChar_eq_nodeCountChar_add_offLineCountChar hχ a b
  omega

/-! ## Part 11 — the fiber is conserved: no strand ever dies, the event belongs to the whole

You can't delete values from the fiber — the fiber is a conserved object (the rendezvous theorems,
the energy balance: the prime side IS the spectral side, nothing more, nothing less). The kernel
form of that conservation at the strand level: every prime's resonator factor `1 − χ(p)p^{−ρ}` is
INVERTIBLE throughout the strip — its phasor has norm `p^{−Re ρ} < 1`, so the factor never
vanishes (`euler_strand_live`). No strand can be zeroed out, silenced, or removed; the fiber
carries no null values, anywhere.

Consequently a cancellation event cannot be attributed to any strand or any finite sub-ensemble
(`zero_event_whole_ensemble`): regrouping finitely many live, invertible factors changes nothing —
not because strands are removable, but because nothing was ever removable. The vanishing is the
interference of the WHOLE conserved fiber, exactly as the FTA winding demands: `wind_mul` ties
every strand multiplicatively, at every height, with no strip. The induction step's refusal of the
minimal criminal is therefore an obligation of the total construction — the only level at which
the event even exists. -/

/-- **No strand ever dies**: every prime's Euler factor is invertible throughout the right
    half-plane — its phasor has norm `p^{−Re ρ} < 1`. The fiber carries no null values; nothing
    in it can be zeroed out. -/
theorem euler_strand_live {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {p : ℕ} (h2p : 2 ≤ p) {ρ : ℂ} (hρre : 0 < ρ.re) :
    (1 : ℂ) - χ p * (p : ℂ) ^ (-ρ) ≠ 0 := by
  by_cases hu : IsUnit ((p : ℕ) : ZMod N)
  · have hnorm1 : ‖χ ((p : ℕ) : ZMod N)‖ = 1 := by
      rw [← hu.unit_spec]
      exact χ.unit_norm_eq_one hu.unit
    have hp0 : 0 < (p : ℕ) := by omega
    have hpow : ‖((p : ℕ) : ℂ) ^ (-ρ)‖ = ((p : ℕ) : ℝ) ^ (-ρ).re :=
      Complex.norm_natCast_cpow_of_pos hp0 _
    have hlt : ‖χ ((p : ℕ) : ZMod N) * ((p : ℕ) : ℂ) ^ (-ρ)‖ < 1 := by
      rw [norm_mul, hnorm1, one_mul, hpow]
      apply Real.rpow_lt_one_of_one_lt_of_neg
      · exact_mod_cast (by omega : 1 < p)
      · rw [Complex.neg_re]
        linarith
    intro h
    have heq : χ ((p : ℕ) : ZMod N) * ((p : ℕ) : ℂ) ^ (-ρ) = 1 := by
      linear_combination -h
    rw [heq, norm_one] at hlt
    exact lt_irrefl 1 hlt
  · rw [MulChar.map_nonunit χ hu, zero_mul, sub_zero]
    exact one_ne_zero

/-- **The event belongs to the whole ensemble**: since every strand's factor is live and
    invertible (`euler_strand_live`), regrouping any finite set of them neither creates nor
    destroys a zero event — the cancellation is not attributable to any strand or finite
    sub-ensemble; it is the interference of the whole conserved fiber. -/
theorem zero_event_whole_ensemble {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (S : Finset ℕ) (hS : ∀ p ∈ S, 2 ≤ p) {ρ : ℂ} (hρre : 0 < ρ.re) :
    (∏ p ∈ S, (1 - χ p * (p : ℂ) ^ (-ρ))) * DirichletCharacter.LFunction χ ρ = 0
      ↔ DirichletCharacter.LFunction χ ρ = 0 := by
  have hfac : ∀ p ∈ S, (1 : ℂ) - χ p * (p : ℂ) ^ (-ρ) ≠ 0 :=
    fun p hp => euler_strand_live χ (hS p hp) hρre
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h (Finset.prod_ne_zero_iff.mpr hfac)
    · exact h
  · intro h
    rw [h, mul_zero]

/-! ## Part 12 — the reality principle, trace form: a real spectrum cannot resonate off-axis

The source generator's spectrum is real (`gen_real`: `H(n) = log n`). Here is what a real
spectrum's readout CANNOT do, unconditionally: for ANY non-negative summable weights, the
resolvent trace `Σ c(n)/(log n − w)` is differentiable at every `w` off the real axis. A real
spectrum's singularities live only at real parameters — no weighting can move them off.

Against `resonates_at_zeros` (every zero IS a singularity of the trace readout), the program's
closing shape: the readout that EQUALS `−L'/L` is the kernel's own Hadamard resolvent over the
zeros' parameters (`dualResolventTrace_eq_logDeriv`), in exactly the regularized form
`Σ c·(1/(z−λ) + 1/λ)`; the reality ban for THAT form is `realSpectrum_regularized_trace`
below. The moment the representation's spectrum is exhibited as the construction's own (real)
mode parameters, the ban and the resonance annihilate at any off-line zero. -/

/-- **A real spectrum's resolvent trace has no off-axis singularity** — for any non-negative
    summable weights, `w ↦ Σ' c(n)/(log n − w)` is differentiable at every `w` with `Im w ≠ 0`.
    Reality of the spectrum is a structural ban on off-axis resonance, independent of the
    weighting. -/
theorem realSpectrum_trace_differentiableAt {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n)
    (hsum : Summable c) {w : ℂ} (hw : w.im ≠ 0) :
    DifferentiableAt ℂ (fun z : ℂ => ∑' n : ℕ, (c n : ℂ) / ((Real.log n : ℂ) - z)) w := by
  set δ : ℝ := |w.im| with hδ
  have hδ0 : 0 < δ := abs_pos.mpr hw
  set U : Set ℂ := {z : ℂ | δ / 2 < |z.im|} with hU_def
  have hU_open : IsOpen U := by
    have hcont : Continuous fun z : ℂ => |z.im| := continuous_abs.comp Complex.continuous_im
    exact isOpen_lt continuous_const hcont
  have hwU : w ∈ U := by
    show δ / 2 < |w.im|
    rw [← hδ]
    linarith
  have hden : ∀ (n : ℕ) (z : ℂ), z ∈ U → (Real.log n : ℂ) - z ≠ 0 := by
    intro n z hz h0
    have hzeq : z = ((Real.log n : ℝ) : ℂ) := by linear_combination -h0
    have hzim : z.im = 0 := by rw [hzeq, Complex.ofReal_im]
    rw [hU_def, Set.mem_setOf_eq, hzim, abs_zero] at hz
    linarith
  have hterm : ∀ n : ℕ,
      DifferentiableOn ℂ (fun z => (c n : ℂ) / ((Real.log n : ℂ) - z)) U := by
    intro n
    apply DifferentiableOn.div (differentiableOn_const _)
    · exact (differentiableOn_const _).sub differentiableOn_id
    · exact hden n
  have hbound : ∀ (n : ℕ) (z : ℂ), z ∈ U →
      ‖(c n : ℂ) / ((Real.log n : ℂ) - z)‖ ≤ c n * (δ / 2)⁻¹ := by
    intro n z hz
    have him : |((Real.log n : ℂ) - z).im| = |z.im| := by
      rw [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg]
    have hge : δ / 2 ≤ ‖(Real.log n : ℂ) - z‖ :=
      le_trans (le_of_lt hz) (him ▸ Complex.abs_im_le_norm _)
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (hc n), div_eq_mul_inv]
    have hinv : ‖(Real.log n : ℂ) - z‖⁻¹ ≤ (δ / 2)⁻¹ :=
      (inv_le_inv₀ (lt_of_lt_of_le (by positivity) hge) (by positivity)).mpr hge
    exact mul_le_mul_of_nonneg_left hinv (hc n)
  have hsum' : Summable (fun n => c n * (δ / 2)⁻¹) := hsum.mul_right _
  have hdiff := differentiableOn_tsum_of_summable_norm hsum' hterm hU_open hbound
  exact (hdiff w hwU).differentiableAt (hU_open.mem_nhds hwU)

/-! ## Part 13 — the reality ban in the kernel's own representation shape

The kernel's resolvent representation of the readout (`dualResolventTrace_eq_logDeriv`) has terms
`ord·(1/(s−ρ) + 1/ρ)` with weights summable as `Σ ord/|ρ|²`
(`summable_lOrderNat_div_norm_sq_nontrivialZeros`). Here is the reality ban in EXACTLY that
shape: for a discrete real spectrum and non-negative weights summable against `1/λ²`, the
regularized trace `Σ c·(1/(z−λ) + 1/λ)` is differentiable at every point off the real axis.
A real spectrum cannot resonate off-axis — in the very form the program's representation takes.
The two jaws now share one shape; what joins them is exhibiting the representation's spectrum as
the construction's real mode parameters. -/

/-- **The regularized reality ban.** For a real spectrum `λ` that is discrete at infinity, with
    non-negative weights summable against `1/λ²`, the Hadamard-regularized trace
    `z ↦ Σ' c(n)·(1/(z − λ n) + 1/λ n)` is differentiable at every `z` off the real axis. -/
theorem realSpectrum_regularized_trace {lam : ℕ → ℝ} {c : ℕ → ℝ}
    (hc : ∀ n, 0 ≤ c n) (hlam0 : ∀ n, lam n ≠ 0)
    (hdisc : ∀ R : ℝ, {n : ℕ | |lam n| ≤ R}.Finite)
    (hsum : Summable (fun n => c n / (lam n) ^ 2))
    {w : ℂ} (hw : w.im ≠ 0) :
    DifferentiableAt ℂ
      (fun z : ℂ => ∑' n : ℕ, (c n : ℂ) * (1 / (z - (lam n : ℂ)) + 1 / (lam n : ℂ))) w := by
  classical
  set δ : ℝ := |w.im| with hδ
  have hδ0 : 0 < δ := abs_pos.mpr hw
  set M : ℝ := ‖w‖ + 1 with hM
  have hM0 : 0 < M := by positivity
  set U : Set ℂ := {z : ℂ | δ / 2 < |z.im|} ∩ Metric.ball 0 M with hU_def
  have hU_open : IsOpen U := by
    apply IsOpen.inter
    · exact isOpen_lt continuous_const (continuous_abs.comp Complex.continuous_im)
    · exact Metric.isOpen_ball
  have hwU : w ∈ U := by
    constructor
    · show δ / 2 < |w.im|
      rw [← hδ]
      linarith
    · rw [Metric.mem_ball, dist_zero_right]
      linarith [hM ▸ le_refl M]
  -- denominators never vanish off the axis
  have hden : ∀ (n : ℕ) (z : ℂ), δ / 2 < |z.im| → z - (lam n : ℂ) ≠ 0 := by
    intro n z hz h0
    have hzeq : z = ((lam n : ℝ) : ℂ) := by linear_combination h0
    have hzim : z.im = 0 := by rw [hzeq, Complex.ofReal_im]
    rw [hzim, abs_zero] at hz
    linarith
  -- index split: the finitely many strands near the window, and the far tail
  set A : Finset ℕ := (hdisc (2 * M)).toFinset with hA
  set termF : ℕ → ℂ → ℂ :=
    fun n z => (c n : ℂ) * (1 / (z - (lam n : ℂ)) + 1 / (lam n : ℂ)) with htermF
  have hterm_diff : ∀ n : ℕ, DifferentiableOn ℂ (termF n) U := by
    intro n
    apply DifferentiableOn.const_mul
    apply DifferentiableOn.add
    · apply DifferentiableOn.div (differentiableOn_const _)
      · exact differentiableOn_id.sub (differentiableOn_const _)
      · intro z hz
        exact hden n z hz.1
    · exact differentiableOn_const _
  -- the near part: a finite sum, differentiable
  have hnear : DifferentiableOn ℂ (fun z => ∑ n ∈ A, termF n z) U :=
    DifferentiableOn.fun_sum fun n _ => hterm_diff n
  -- the far tail: uniformly dominated by 2M·c/λ²
  have hfar_bound : ∀ (n : ℕ), n ∉ A → ∀ z ∈ U,
      ‖termF n z‖ ≤ 2 * M * (c n / (lam n) ^ 2) := by
    intro n hn z hz
    have hfar : 2 * M < |lam n| := by
      by_contra h
      push_neg at h
      exact hn (by rw [hA, Set.Finite.mem_toFinset]; exact h)
    have hzM : ‖z‖ < M := by
      have := hz.2
      rwa [Metric.mem_ball, dist_zero_right] at this
    have hcomb : termF n z = (c n : ℂ) * z / ((z - (lam n : ℂ)) * (lam n : ℂ)) := by
      rw [htermF]
      have h1 : z - (lam n : ℂ) ≠ 0 := hden n z hz.1
      have h2 : ((lam n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hlam0 n
      field_simp
      ring
    rw [hcomb, norm_div, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (hc n)]
    have hlamnorm : ‖((lam n : ℝ) : ℂ)‖ = |lam n| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    have hdenlow : |lam n| / 2 ≤ ‖z - (lam n : ℂ)‖ := by
      have h1 : ‖((lam n : ℝ) : ℂ)‖ - ‖z‖ ≤ ‖z - (lam n : ℂ)‖ := by
        calc ‖((lam n : ℝ) : ℂ)‖ - ‖z‖ ≤ ‖((lam n : ℝ) : ℂ) - z‖ := norm_sub_norm_le _ _
          _ = ‖z - (lam n : ℂ)‖ := by rw [← norm_neg]; ring_nf
      rw [hlamnorm] at h1
      linarith
    have hpos1 : (0 : ℝ) < |lam n| := by linarith
    have hpos2 : (0 : ℝ) < ‖z - (lam n : ℂ)‖ :=
      norm_pos_iff.mpr (hden n z hz.1)
    rw [div_le_iff₀ (mul_pos hpos2 (by rw [hlamnorm]; exact hpos1))]
    have hkey : c n * ‖z‖ ≤ c n * M := by
      apply mul_le_mul_of_nonneg_left (le_of_lt hzM) (hc n)
    have hden_prod : |lam n| / 2 * |lam n| ≤ ‖z - (lam n : ℂ)‖ * ‖((lam n : ℝ) : ℂ)‖ := by
      rw [hlamnorm]
      apply mul_le_mul_of_nonneg_right hdenlow (le_of_lt hpos1)
    have hexp : 2 * M * (c n / (lam n) ^ 2) * (‖z - (lam n : ℂ)‖ * ‖((lam n : ℝ) : ℂ)‖)
        ≥ 2 * M * (c n / (lam n) ^ 2) * (|lam n| / 2 * |lam n|) := by
      apply mul_le_mul_of_nonneg_left hden_prod
      have hcn := hc n
      positivity
    have hsimp : 2 * M * (c n / (lam n) ^ 2) * (|lam n| / 2 * |lam n|) = M * c n := by
      have habs2 : |lam n| / 2 * |lam n| = (lam n) ^ 2 / 2 := by
        rw [div_mul_eq_mul_div, ← abs_mul, abs_mul_self]
        ring
      rw [habs2]
      have hne : ((lam n) : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 (hlam0 n)
      have hinner : c n / lam n ^ 2 * (lam n ^ 2 / 2) = c n / 2 := by
        field_simp
        rw [mul_div_assoc, div_self (hlam0 n), mul_one]
      calc 2 * M * (c n / lam n ^ 2) * (lam n ^ 2 / 2)
          = 2 * M * (c n / lam n ^ 2 * (lam n ^ 2 / 2)) := by ring
        _ = 2 * M * (c n / 2) := by rw [hinner]
        _ = M * c n := by ring
    calc c n * ‖z‖ ≤ c n * M := hkey
      _ = M * c n := by ring
      _ = 2 * M * (c n / (lam n) ^ 2) * (|lam n| / 2 * |lam n|) := hsimp.symm
      _ ≤ 2 * M * (c n / (lam n) ^ 2) * (‖z - (lam n : ℂ)‖ * ‖((lam n : ℝ) : ℂ)‖) := hexp
  -- assemble: split the tsum at A
  have hsum2 : Summable (fun n => 2 * M * (c n / (lam n) ^ 2)) := hsum.mul_left _
  have htail : DifferentiableOn ℂ
      (fun z => ∑' n : ℕ, if n ∈ A then 0 else termF n z) U := by
    apply differentiableOn_tsum_of_summable_norm hsum2
    · intro n
      by_cases hn : n ∈ A
      · simp only [if_pos hn]
        exact differentiableOn_const _
      · simp only [if_neg hn]
        exact hterm_diff n
    · exact hU_open
    · intro n z hz
      by_cases hn : n ∈ A
      · simp only [if_pos hn, norm_zero]
        have hcn := hc n
        positivity
      · simp only [if_neg hn]
        exact hfar_bound n hn z hz
  -- pointwise split of the total trace
  have hsummable_tail : ∀ z ∈ U, Summable (fun n => if n ∈ A then 0 else termF n z) := by
    intro z hz
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => ?_) hsum2
    by_cases hn : n ∈ A
    · simp only [if_pos hn, norm_zero]
      have hcn := hc n
      positivity
    · simp only [if_neg hn]
      exact hfar_bound n hn z hz
  have hsplit : ∀ z ∈ U, (∑' n : ℕ, termF n z)
      = (∑ n ∈ A, termF n z) + ∑' n : ℕ, if n ∈ A then 0 else termF n z := by
    intro z hz
    have hfin : Summable (fun n => if n ∈ A then termF n z else 0) := by
      apply summable_of_finite_support
      apply Set.Finite.subset A.finite_toSet
      intro n hn
      simp only [Function.mem_support] at hn
      by_contra hnA
      exact hn (if_neg hnA)
    have hpt : ∀ n : ℕ, termF n z
        = (if n ∈ A then termF n z else 0) + (if n ∈ A then 0 else termF n z) := by
      intro n
      by_cases hn : n ∈ A <;> simp [hn]
    calc (∑' n : ℕ, termF n z)
        = ∑' n : ℕ, ((if n ∈ A then termF n z else 0) + (if n ∈ A then 0 else termF n z)) :=
          tsum_congr hpt
      _ = (∑' n : ℕ, if n ∈ A then termF n z else 0)
          + ∑' n : ℕ, if n ∈ A then 0 else termF n z :=
          hfin.tsum_add (hsummable_tail z hz)
      _ = (∑ n ∈ A, termF n z) + ∑' n : ℕ, if n ∈ A then 0 else termF n z := by
          congr 1
          rw [tsum_eq_sum (f := fun n => if n ∈ A then termF n z else 0)
            (s := A) (fun n hn => if_neg hn)]
          exact Finset.sum_congr rfl fun n hn => if_pos hn
  have htotal : DifferentiableOn ℂ
      (fun z => ∑' n : ℕ, termF n z) U := by
    apply DifferentiableOn.congr (hnear.add htail)
    intro z hz
    exact hsplit z hz
  exact (htotal w hwU).differentiableAt (hU_open.mem_nhds hwU)

/-! ## Part 14 — traveling and standing: winding accumulates BETWEEN markers, the standing wave
happens AT them

The fiber's line readout decomposes into a TRAVELING factor and a STANDING factor
(`fiber_traveling_standing`):

```
L(½+it)  =  ε⁻¹ · Z(t) / g(t),     g(t) = N^{(½+it)/2}·γ_χ(½+it)   (never zero on the line)
```

`Z` is real — the standing component; `g` is the geometric traversal factor — the helix climb.
Between markers `Z` keeps a strict sign (`sign_constant_between_nodes`): the standing factor
contributes NO phase motion there, so every bit of winding the fiber accumulates between markers
is carried by the continuous traversal factor `1/g` — the climb up the growing loops, at the
geometry's increasing rate. AT a marker, `Z = 0`: the traveling content cancels totally and the
event is a standing wave of its own accord — the rendezvous, the resonance, the admission of the
next harmonic, after which the sign flips (the odd-order engine) and accumulation resumes.
Winding BETWEEN, standing AT. -/

/-- **The completed wave is the standing component**: `Φ_χ(½+it) = ε⁻¹ · Z(t)` with `Z` real —
    pinned to one ray, no winding of its own. -/
theorem waveChar_line_ray {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) {ε : ℂ}
    (hε2 : ε ^ 2 = (χ⁻¹).rootNumber) (hεu : (starRingEnd ℂ) ε * ε = 1) (t : ℝ) :
    HelixStandingWave.waveChar χ (1 / 2 + (t : ℂ) * I)
      = ε⁻¹ * ((HelixStandingWave.standingWaveCharGen χ ε t : ℝ) : ℂ) := by
  have hεne : ε ≠ 0 := by
    intro h
    rw [h] at hεu
    simp at hεu
  have hreal := HelixStandingWave.waveCharGen_line_real hχ hχp hε2 hεu t
  have hval : ε * HelixStandingWave.waveChar χ (1 / 2 + (t : ℂ) * I)
      = (((ε * HelixStandingWave.waveChar χ (1 / 2 + (t : ℂ) * I)).re : ℝ) : ℂ) :=
    (Complex.conj_eq_iff_re.mp hreal).symm
  have hgen : ((HelixStandingWave.standingWaveCharGen χ ε t : ℝ) : ℂ)
      = ε * HelixStandingWave.waveChar χ (1 / 2 + (t : ℂ) * I) := by
    rw [HelixStandingWave.standingWaveCharGen]
    exact hval.symm
  rw [hgen, ← mul_assoc, inv_mul_cancel₀ hεne, one_mul]

/-- **No standing event between markers**: on a marker-free interval the standing component keeps
    a strict sign — the endpoint product is strictly positive. All phase motion between markers
    belongs to the traversal factor. -/
theorem sign_constant_between_nodes {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (ε : ℂ) {t₁ t₂ : ℝ} (h12 : t₁ ≤ t₂)
    (hno : ∀ t ∈ Set.Icc t₁ t₂, HelixStandingWave.standingWaveCharGen χ ε t ≠ 0) :
    0 < HelixStandingWave.standingWaveCharGen χ ε t₁
      * HelixStandingWave.standingWaveCharGen χ ε t₂ := by
  have hc : ContinuousOn (HelixStandingWave.standingWaveCharGen χ ε) (Set.Icc t₁ t₂) :=
    (HelixStandingWave.standingWaveCharGen_continuous hχ ε).continuousOn
  rcases lt_trichotomy (HelixStandingWave.standingWaveCharGen χ ε t₁
      * HelixStandingWave.standingWaveCharGen χ ε t₂) 0 with hneg | hzero | hpos
  · exfalso
    rcases mul_neg_iff.mp hneg with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · obtain ⟨t, ht, h0⟩ := intermediate_value_Ioo' h12 hc (Set.mem_Ioo.mpr ⟨hb, ha⟩)
      exact hno t ⟨le_of_lt ht.1, le_of_lt ht.2⟩ h0
    · obtain ⟨t, ht, h0⟩ := intermediate_value_Ioo h12 hc (Set.mem_Ioo.mpr ⟨ha, hb⟩)
      exact hno t ⟨le_of_lt ht.1, le_of_lt ht.2⟩ h0
  · exfalso
    rcases mul_eq_zero.mp hzero with h | h
    · exact hno t₁ ⟨le_refl _, h12⟩ h
    · exact hno t₂ ⟨h12, le_refl _⟩ h
  · exact hpos

/-- The geometric traversal factor on the line — the helix climb's analytic face. -/
noncomputable def geomFactor {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (t : ℝ) : ℂ :=
  (N : ℂ) ^ (((1 : ℂ) / 2 + (t : ℂ) * I) / 2) * χ.gammaFactor (1 / 2 + (t : ℂ) * I)

/-- **The traversal factor never vanishes on the line** — the climb never stalls; the traveling
    phase is always live. -/
theorem geomFactor_ne_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (t : ℝ) :
    geomFactor χ t ≠ 0 := by
  apply mul_ne_zero
  · have hN : ((N : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    rw [Complex.cpow_def_of_ne_zero hN]
    exact Complex.exp_ne_zero _
  · apply DirichletLHadamard.gammaFactor_ne_zero
    simp

/-- **The traveling/standing decomposition of the fiber readout**:
    `L(½+it) = ε⁻¹ · Z(t) / g(t)` — real standing component over live geometric traversal. The
    fiber winds continuously through `1/g` between markers; at a marker `Z = 0` and the readout
    is a standing event. -/
theorem fiber_traveling_standing {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) {ε : ℂ}
    (hε2 : ε ^ 2 = (χ⁻¹).rootNumber) (hεu : (starRingEnd ℂ) ε * ε = 1) (t : ℝ) :
    DirichletCharacter.LFunction χ (1 / 2 + (t : ℂ) * I)
      = ε⁻¹ * ((HelixStandingWave.standingWaveCharGen χ ε t : ℝ) : ℂ) / geomFactor χ t := by
  have hray := waveChar_line_ray hχ hχp hε2 hεu t
  have hs0 : ((1 : ℂ) / 2 + (t : ℂ) * I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have hrel := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ
    ((1 : ℂ) / 2 + (t : ℂ) * I) (Or.inl hs0)
  have hγ : χ.gammaFactor ((1 : ℂ) / 2 + (t : ℂ) * I) ≠ 0 := by
    apply DirichletLHadamard.gammaFactor_ne_zero
    simp
  have hN : ((N : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hpow : (N : ℂ) ^ (((1 : ℂ) / 2 + (t : ℂ) * I) / 2) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hN]
    exact Complex.exp_ne_zero _
  -- waveChar = N^{s/2}·Λ and Λ = γ·L assemble into the decomposition
  have hwave : HelixStandingWave.waveChar χ (1 / 2 + (t : ℂ) * I)
      = (N : ℂ) ^ (((1 : ℂ) / 2 + (t : ℂ) * I) / 2)
        * DirichletCharacter.completedLFunction χ (1 / 2 + (t : ℂ) * I) := rfl
  rw [hrel, geomFactor]
  rw [hwave] at hray
  rw [← hray]
  exact (mul_div_mul_left _ _ hpow).symm

/-! ## Part 15 — the exponent law: a zero's radial coordinate is the chain's exact decay exponent

The geometric phasor chain cancels at every zero (`flow_chain_vanishes_at_zero`) at rate
`M^{−σ}` from above. The EXACT ledger (`flow_closure_exact`) reads, at every zero and every
height, the same fibre invariant `A(M) − L(0,χ)` — periodic in `M`, intrinsic to the fibre, with
no zero in it. Here the invariant's quantization is cashed: `inv(1) = 1 − L(0,χ)` and
`inv(N) = −L(0,χ)` cannot both vanish (`exists_invariant_ne_zero`), so along a fixed residue
progression the rescaled chain is bounded BELOW by a positive constant, and the chain's decay is
two-sided (`chain_decay_exponent`):

```
c₀·M^{−σ} − C·M^{−σ−1}  ≤  ‖S_M(s)‖  ≤  C′·M^{−σ}     (M ≡ M₀ mod N)
```

The radial coordinate of a cancellation event is therefore a GEOMETRIC OBSERVABLE — the exact
decay exponent of the helix's own chain, measured against the fibre's quantized energy floor.
"Where is the zero" is now "how fast does the constructed chain decay" — the chart the energy
picture demanded, in asymptotic form. -/

/-- **The fibre invariant is alive**: `inv(M) = A(M) − L(0,χ)` is nonzero at `M = 1` or `M = N` —
    `inv(1) = 1 − L(0,χ)` and `inv(N) = −L(0,χ)` cannot both vanish. -/
theorem exists_invariant_ne_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) :
    ∃ M₀ : ℕ, 1 ≤ M₀ ∧
      DirichletClosureLedger.Asum χ M₀ - DirichletCharacter.LFunction χ 0 ≠ 0 := by
  by_cases hL : DirichletCharacter.LFunction χ 0 = 0
  · -- the channel constant vanishes: M₀ = 1 works since A(1) = 1
    refine ⟨1, le_refl 1, ?_⟩
    have hN : N ≠ 1 := DirichletClosureLedger.modulus_ne_one χ hχ
    have hA1 : DirichletClosureLedger.Asum χ 1 = 1 := by
      rw [DirichletClosureLedger.Asum]
      rw [show Finset.Icc 0 1 = {0, 1} from rfl]
      rw [Finset.sum_insert (by norm_num), Finset.sum_singleton]
      simp [DirichletCharacter.map_zero' χ hN]
    rw [hA1, hL, sub_zero]
    exact one_ne_zero
  · -- the channel constant is nonzero: M₀ = N works since A(N) = 0
    have hNpos : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
    refine ⟨N, hNpos, ?_⟩
    have hAN : DirichletClosureLedger.Asum χ N = 0 := by
      have hper := DirichletClosureLedger.Asum_add_period χ hχ (M := 0)
      have hA0 : DirichletClosureLedger.Asum χ 0 = 0 := by
        rw [DirichletClosureLedger.Asum]
        simp [DirichletCharacter.map_zero' χ (DirichletClosureLedger.modulus_ne_one χ hχ)]
      rw [show (0 : ℕ) + N = N from by omega] at hper
      rw [hper, hA0]
    rw [hAN, zero_sub, neg_ne_zero]
    exact hL

/-- **The exponent law, lower half**: at any zero `s` (`Re s > 0`), along the progression
    `M = M₀ + kN` where the fibre invariant is alive, the chain is bounded BELOW —
    `c₀·M^{−σ} − C·M^{−σ−1} ≤ ‖S_M‖`. With `flow_chain_vanishes_at_zero`'s upper bound, the
    zero's radial coordinate `σ` is the chain's EXACT decay exponent. -/
theorem chain_decay_exponent {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) {s : ℂ} (hσ : 0 < s.re)
    (hzero : DirichletCharacter.LFunction χ s = 0) :
    ∃ (c₀ C : ℝ) (M₀ : ℕ), 0 < c₀ ∧ 0 < C ∧ 1 ≤ M₀ ∧ ∀ k : ℕ,
      c₀ * ((M₀ + N * k : ℕ) : ℝ) ^ (-s.re) - C * ((M₀ + N * k : ℕ) : ℝ) ^ (-s.re - 1)
        ≤ ‖HelixFlowClosureLedger.flowPartialSum χ s (M₀ + N * k)‖ := by
  obtain ⟨M₀, hM₀, hinv⟩ := exists_invariant_ne_zero χ hχ
  obtain ⟨C, hC, hled⟩ := HelixFlowClosureLedger.flow_closure_exact χ hχ s hσ hzero
  set inv : ℂ := DirichletClosureLedger.Asum χ M₀ - DirichletCharacter.LFunction χ 0 with hinvdef
  have hc₀ : 0 < ‖inv‖ := norm_pos_iff.mpr hinv
  refine ⟨‖inv‖, C, M₀, hc₀, hC, hM₀, fun k => ?_⟩
  -- the invariant is the same along the whole progression
  have hAperAll : ∀ j : ℕ, DirichletClosureLedger.Asum χ (M₀ + N * j)
      = DirichletClosureLedger.Asum χ M₀ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        rw [show M₀ + N * (j + 1) = (M₀ + N * j) + N from by ring,
          DirichletClosureLedger.Asum_add_period χ hχ]
        exact ih
  set M : ℕ := M₀ + N * k with hMdef
  have hM1 : 1 ≤ M := le_trans hM₀ (by omega)
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
  have hAper : DirichletClosureLedger.Asum χ M = DirichletClosureLedger.Asum χ M₀ :=
    hAperAll k
  have hled' := hled M hM1
  rw [hAper] at hled'
  -- reverse triangle: ‖S_M·M^s‖ ≥ ‖inv‖ − C/M
  have hrev : ‖inv‖ - C * (M : ℝ) ^ (-(1 : ℝ))
      ≤ ‖HelixFlowClosureLedger.flowPartialSum χ s M * (M : ℂ) ^ s‖ := by
    have h1 : ‖inv‖ - ‖HelixFlowClosureLedger.flowPartialSum χ s M * (M : ℂ) ^ s‖
        ≤ ‖HelixFlowClosureLedger.flowPartialSum χ s M * (M : ℂ) ^ s - inv‖ := by
      calc ‖inv‖ - ‖HelixFlowClosureLedger.flowPartialSum χ s M * (M : ℂ) ^ s‖
          ≤ ‖inv - HelixFlowClosureLedger.flowPartialSum χ s M * (M : ℂ) ^ s‖ :=
            norm_sub_norm_le _ _
        _ = ‖HelixFlowClosureLedger.flowPartialSum χ s M * (M : ℂ) ^ s - inv‖ := by
            rw [← norm_neg]
            ring_nf
    linarith [hled']
  -- divide through by the rescaling ‖M^s‖ = M^σ
  have hnorm_pow : ‖(M : ℂ) ^ s‖ = (M : ℝ) ^ s.re :=
    Complex.norm_natCast_cpow_of_pos hM1 s
  have hpow_pos : (0 : ℝ) < (M : ℝ) ^ s.re := Real.rpow_pos_of_pos hMpos _
  rw [norm_mul, hnorm_pow] at hrev
  -- ‖S_M‖ ≥ (‖inv‖ − C·M^{−1}) · M^{−σ}
  have hfinal : (‖inv‖ - C * (M : ℝ) ^ (-(1 : ℝ))) * (M : ℝ) ^ (-s.re)
      ≤ ‖HelixFlowClosureLedger.flowPartialSum χ s M‖ := by
    have h2 : (‖inv‖ - C * (M : ℝ) ^ (-(1 : ℝ))) * (M : ℝ) ^ (-s.re)
        ≤ (‖HelixFlowClosureLedger.flowPartialSum χ s M‖ * (M : ℝ) ^ s.re)
          * (M : ℝ) ^ (-s.re) := by
      apply mul_le_mul_of_nonneg_right hrev
      exact le_of_lt (Real.rpow_pos_of_pos hMpos _)
    calc (‖inv‖ - C * (M : ℝ) ^ (-(1 : ℝ))) * (M : ℝ) ^ (-s.re)
        ≤ (‖HelixFlowClosureLedger.flowPartialSum χ s M‖ * (M : ℝ) ^ s.re)
          * (M : ℝ) ^ (-s.re) := h2
      _ = ‖HelixFlowClosureLedger.flowPartialSum χ s M‖
          * ((M : ℝ) ^ s.re * (M : ℝ) ^ (-s.re)) := by ring
      _ = ‖HelixFlowClosureLedger.flowPartialSum χ s M‖ := by
          rw [← Real.rpow_add hMpos, add_neg_cancel, Real.rpow_zero, mul_one]
  calc ‖inv‖ * (M : ℝ) ^ (-s.re) - C * (M : ℝ) ^ (-s.re - 1)
      = (‖inv‖ - C * (M : ℝ) ^ (-(1 : ℝ))) * (M : ℝ) ^ (-s.re) := by
        have hmm : (M : ℝ) ^ (-s.re - 1)
            = (M : ℝ) ^ (-(1 : ℝ)) * (M : ℝ) ^ (-s.re) := by
          rw [← Real.rpow_add hMpos]
          ring_nf
        rw [hmm]
        ring
    _ ≤ ‖HelixFlowClosureLedger.flowPartialSum χ s M‖ := hfinal

/-! ## Part 16 — the accumulation rate: universal quantum, function-specific velocity

The cost of every harmonic is the same universal quantum (the π-jump of the ray-pinned standing
factor — the only phase event the line allows). What differs between L-functions is the RATE at
which the traversal factor accumulates phase toward each threshold. The conductor's contribution
is exact and elementary: `N^{(½+it)/2} = N^{1/4}·e^{i·(t/2)·log N}` — phase velocity
`(log N)/2` per unit height (`geomFactor_conductor_phase`). Bigger conductor, faster
accumulation, lower first resonance — the function-by-function variation of the zero heights with
a universal mechanism behind it. -/

/-- **The conductor's accumulation rate, exact**: the conductor factor of the traversal is a
    fixed amplitude `N^{1/4}` carrying phase `(t/2)·log N` — phase velocity `(log N)/2` per unit
    height, the fiber-dependent part of the rate. -/
theorem geomFactor_conductor_phase {N : ℕ} [NeZero N] (t : ℝ) :
    (N : ℂ) ^ (((1 : ℂ) / 2 + (t : ℂ) * I) / 2)
      = ((N : ℝ) ^ ((1 : ℝ) / 4) : ℝ)
        * Complex.exp (Complex.I * ((t * Real.log N / 2 : ℝ) : ℂ)) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hNC : ((N : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [Complex.cpow_def_of_ne_zero hNC]
  have hlog : Complex.log ((N : ℕ) : ℂ) = ((Real.log N : ℝ) : ℂ) := by
    rw [show ((N : ℕ) : ℂ) = (((N : ℝ)) : ℂ) from by push_cast; ring,
      Complex.ofReal_log hN0.le]
  rw [hlog]
  have hexp : ((Real.log N : ℝ) : ℂ) * (((1 : ℂ) / 2 + (t : ℂ) * I) / 2)
      = ((Real.log N / 4 : ℝ) : ℂ) + Complex.I * ((t * Real.log N / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hexp, Complex.exp_add]
  congr 1
  rw [show ((Real.log N / 4 : ℝ) : ℂ) = (((1 : ℝ) / 4 * Real.log N : ℝ) : ℂ) from by
      push_cast; ring,
    ← Complex.ofReal_exp, ← Real.exp_log (Real.rpow_pos_of_pos hN0 ((1 : ℝ) / 4)),
    Real.log_rpow hN0]

/-! ## Part 17 — the accumulator skips nothing: coherence is totality

The fiber accumulates over the integers; how an integer becomes energy is the term function
`n ↦ χ(n)·n^{−σ}·U(t)(n)⁻¹`. The experiment that pinned this — delete one integer and the exact
zero alignment collapses everywhere — is a theorem: at ANY zero, the full chain cancels
(`flow_chain_vanishes_at_zero`), but the chain with one unit integer `m` removed is bounded AWAY
from zero, eventually by `m^{−σ}/2`, with the defect EXACTLY the removed term's energy `m^{−σ}`
(`fiber_skips_nothing`). The same defect law at every zero, every height, simultaneously. The
accumulator is complete and conservative: no skipping, no decay function, no slack — coherence at
a resonance is a property of the TOTAL consumption, integer by integer, which is why removing any
one of them un-resonates everything at once. -/

/-- **The fiber can't skip an integer and stay coherent.** At any zero `s` (`Re s > 0`), the
    chain with the unit integer `m`'s term deleted misses the cancellation by exactly that term's
    energy: `m^{−σ} − C·M^{−σ} ≤ ‖S_M − term_m‖`. The full chain vanishes; every one-integer
    deletion is eventually bounded away from zero. -/
theorem fiber_skips_nothing {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) {s : ℂ} (hσ : 0 < s.re)
    (hzero : DirichletCharacter.LFunction χ s = 0) {m : ℕ} (hm : 1 ≤ m)
    (hmu : IsUnit ((m : ℕ) : ZMod N)) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 1 ≤ M →
      (m : ℝ) ^ (-s.re) - C * (M : ℝ) ^ (-s.re)
        ≤ ‖HelixFlowClosureLedger.flowPartialSum χ s M
            - χ m * (((m : ℝ) ^ s.re : ℝ) : ℂ)⁻¹
              * (HelixFlow.phasorFlow s.im m : ℂ)⁻¹‖ := by
  obtain ⟨C, hC, hbound⟩ := HelixFlowClosureLedger.flow_chain_vanishes_at_zero χ hχ s hσ hzero
  refine ⟨C, hC, fun M hM => ?_⟩
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  set term : ℂ := χ m * (((m : ℝ) ^ s.re : ℝ) : ℂ)⁻¹
    * (HelixFlow.phasorFlow s.im m : ℂ)⁻¹ with hterm_def
  have hterm_norm : ‖term‖ = (m : ℝ) ^ (-s.re) := by
    rw [hterm_def, norm_mul, norm_mul, norm_inv, norm_inv]
    have h1 : ‖χ ((m : ℕ) : ZMod N)‖ = 1 := by
      rw [← hmu.unit_spec]
      exact χ.unit_norm_eq_one hmu.unit
    have h2 : ‖(((m : ℝ) ^ s.re : ℝ) : ℂ)‖ = (m : ℝ) ^ s.re := by
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hmpos.le _)]
    have h3 : ‖(HelixFlow.phasorFlow s.im m : ℂ)‖ = 1 := Circle.norm_coe _
    rw [h1, h2, h3, one_mul, inv_one, mul_one, ← Real.rpow_neg hmpos.le]
  have hrev : ‖term‖ - ‖HelixFlowClosureLedger.flowPartialSum χ s M‖
      ≤ ‖HelixFlowClosureLedger.flowPartialSum χ s M - term‖ := by
    calc ‖term‖ - ‖HelixFlowClosureLedger.flowPartialSum χ s M‖
        ≤ ‖term - HelixFlowClosureLedger.flowPartialSum χ s M‖ := norm_sub_norm_le _ _
      _ = ‖HelixFlowClosureLedger.flowPartialSum χ s M - term‖ := norm_sub_rev _ _
  have hS := hbound M hM
  rw [hterm_norm] at hrev
  linarith

/-! ## Part 18 — the threshold-crossing law: purchases, not resonances

The model's primitives reduce to two: the accumulation function (monotone, continuous, from the
construction's constants) and the quantum (π — the only phase event the ray-pinned standing
factor admits). A "zero" is not a separate resonance phenomenon to verify: it is the PURCHASE —
the height at which the fiber's accumulated prime energy first covers the next harmonic's cost,
where the fiber vanishes and the harmonic pops out on the other side. Two laws make this formal:

* `existsUnique_threshold` — ANY continuous strictly-monotone accumulation crosses each budget
  level exactly once: the n-th purchase height exists and is unique. (The same IVT/monotonicity
  shape as the placement law `existsUnique_placed` — one lemma, used twice: integers onto the
  spiral, harmonics onto the heights.)
* `detraversed_ray_between_markers` — between purchases the de-traversed fiber `L·g` stays on ONE
  ray (its phase is frozen): every degree of phase the fiber gains while climbing is traversal,
  none is standing. Accumulation between, purchase at. -/

/-- **The threshold-crossing law**: a continuous, strictly monotone accumulation crosses each
    budget level exactly once past its start. The n-th harmonic's purchase height exists and is
    unique. -/
theorem existsUnique_threshold {E : ℝ → ℝ} (hcont : Continuous E) (hmono : StrictMono E)
    {a c : ℝ} (hac : E a ≤ c) {b : ℝ} (hab : a ≤ b) (hcb : c ≤ E b) :
    ∃! t : ℝ, a ≤ t ∧ E t = c := by
  have hivt : ∃ t ∈ Set.Icc a b, E t = c :=
    intermediate_value_Icc hab hcont.continuousOn ⟨hac, hcb⟩
  obtain ⟨t, htmem, hteq⟩ := hivt
  refine ⟨t, ⟨htmem.1, hteq⟩, ?_⟩
  rintro t' ⟨_, ht'eq⟩
  exact hmono.injective (by rw [ht'eq, hteq])

/-- **The de-traversed fiber is phase-frozen between purchases**: on a marker-free interval, the
    completed readout `L·g` at the two endpoints differs by a strictly POSITIVE real factor —
    one ray, no phase motion. All accumulation between purchases is the traversal's. -/
theorem detraversed_ray_between_markers {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) {ε : ℂ}
    (hε2 : ε ^ 2 = (χ⁻¹).rootNumber) (hεu : (starRingEnd ℂ) ε * ε = 1)
    {t₁ t₂ : ℝ} (h12 : t₁ ≤ t₂)
    (hno : ∀ t ∈ Set.Icc t₁ t₂, HelixStandingWave.standingWaveCharGen χ ε t ≠ 0) :
    ∃ r : ℝ, 0 < r ∧
      DirichletCharacter.LFunction χ (1 / 2 + (t₂ : ℂ) * I) * geomFactor χ t₂
        = (r : ℂ) * (DirichletCharacter.LFunction χ (1 / 2 + (t₁ : ℂ) * I) * geomFactor χ t₁) := by
  have hεne : ε ≠ 0 := by
    intro h
    rw [h] at hεu
    simp at hεu
  -- the de-traversed readout IS the standing component (up to the constant ε⁻¹)
  have hLg : ∀ t : ℝ, DirichletCharacter.LFunction χ (1 / 2 + (t : ℂ) * I) * geomFactor χ t
      = ε⁻¹ * ((HelixStandingWave.standingWaveCharGen χ ε t : ℝ) : ℂ) := by
    intro t
    have hdec := fiber_traveling_standing hχ hχp hε2 hεu t
    have hg := geomFactor_ne_zero χ t
    rw [hdec]
    field_simp
  set Z₁ : ℝ := HelixStandingWave.standingWaveCharGen χ ε t₁ with hZ₁
  set Z₂ : ℝ := HelixStandingWave.standingWaveCharGen χ ε t₂ with hZ₂
  have hZ₁ne : Z₁ ≠ 0 := hno t₁ ⟨le_refl _, h12⟩
  have hsign := sign_constant_between_nodes hχ ε h12 hno
  refine ⟨Z₂ / Z₁, ?_, ?_⟩
  · -- positivity of the ratio from constant sign
    rcases lt_trichotomy Z₁ 0 with h1 | h1 | h1
    · have h2 : Z₂ < 0 := by nlinarith
      exact div_pos_of_neg_of_neg h2 h1
    · exact absurd h1 hZ₁ne
    · have h2 : 0 < Z₂ := by nlinarith
      exact div_pos h2 h1
  · rw [hLg t₁, hLg t₂]
    have hcast : ((Z₂ / Z₁ : ℝ) : ℂ) * (ε⁻¹ * ((Z₁ : ℝ) : ℂ))
        = ε⁻¹ * ((Z₂ : ℝ) : ℂ) := by
      have hZ₁C : ((Z₁ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hZ₁ne
      push_cast
      field_simp
    rw [hcast]

/-! ## Part 19 — the staircase is the accumulation: `H_z = ⌊E/π⌋`

The harmonic step function is not an operator to be analyzed — it is the floor of the
accumulation in quanta. Its two laws: it can only climb (`harmonicCount_mono` — energy never
refunds), and at the n-th purchase it reads exactly `n` (`harmonicCount_at_threshold`). Together
with the crossing law (`existsUnique_threshold`: each budget level crossed exactly once) the
staircase is a deterministic readout of the accumulation — no spectral input, no resonance
primitive, pure accounting.

Calibration (measured, `numerics/fiber.py`, five non-principal channels): consecutive purchases
cost exactly one quantum (mean Δ/π = 0.98–1.01 over the first ten certified zeros), and the
apparent half-quantum first cost is NOT a birth credit — there is no birth. Continued through
t = 0 the wave runs in two directions from the midpoint: t = 0 is a crest (|V(0)| ≠ 0), sitting
at 47–51% of the central inter-node interval, and the phase span between the first negative node
and the first positive node is one FULL quantum (span/π = 1.00–1.03, all five channels). For
real characters the negative ladder mirrors the channel's own zeros; for a complex character it
is the CONJUGATE character's ladder (χ₅ order 4: first negative node ≈ −4.19 against conj-χ₅'s
first zero 4.13 by direct Hurwitz evaluation, while χ's own first zero is 6.18) — the spiral's
two directions are χ and χ̄. The abstract `E` (with `E 0 = 0`, levels at `n·π`) is the
accumulation measured from the central crest, which sits half a quantum below the first level;
the abstract counting theorems are anchor-free and unaffected. -/

/-- The harmonic count of an accumulation: accumulated energy, in quanta of π. -/
noncomputable def harmonicCount (E : ℝ → ℝ) (t : ℝ) : ℤ :=
  ⌊E t / Real.pi⌋

/-- **The staircase only climbs**: a monotone accumulation has a monotone harmonic count —
    energy is never refunded, harmonics are never withdrawn. -/
theorem harmonicCount_mono {E : ℝ → ℝ} (hE : Monotone E) :
    Monotone (harmonicCount E) := by
  intro a b hab
  unfold harmonicCount
  apply Int.floor_le_floor
  exact div_le_div_of_nonneg_right (hE hab) Real.pi_pos.le

/-- **At the n-th purchase the staircase reads exactly `n`**: when the accumulation equals
    `n·π`, the count is `n` — the harmonic pops out precisely as its budget fills. -/
theorem harmonicCount_at_threshold {E : ℝ → ℝ} {t : ℝ} {n : ℤ}
    (h : E t = n * Real.pi) :
    harmonicCount E t = n := by
  unfold harmonicCount
  rw [h, mul_div_assoc, div_self (ne_of_gt Real.pi_pos), mul_one]
  exact Int.floor_intCast n

/-! ## Part 20 — the bare-bones model, complete: Hilbert–Pólya from accumulation alone

The minimal model: an accumulation `E` — strictly monotone, continuous, zero at the start,
unbounded. Nothing else. From this alone: the LADDER exists (a unique purchase height for every
harmonic), it is REAL AND STRICTLY ORDERED by type, the STAIRCASE reads it exactly, it is
DISCRETE at infinity, and the RESOLVENT over it cannot resonate off-axis — the Hilbert–Pólya
reality principle holding for the model's spectrum BY CONSTRUCTION
(`purchase_model_complete`). The quantum π and the accumulation are the only inputs.
Instantiating `E` as a given L-function's traversal accumulation and matching the ladder to that
function's vanishings is the dictionary — the arithmetic to run and adjust against. -/

/-- A bare-bones accumulation: strictly monotone, continuous, zero at the origin, unbounded. -/
structure Accumulation where
  E : ℝ → ℝ
  mono : StrictMono E
  cont : Continuous E
  zero : E 0 = 0
  unbounded : ∀ c : ℝ, ∃ t : ℝ, 0 ≤ t ∧ c ≤ E t

namespace Accumulation

/-- **Every harmonic's purchase exists, uniquely.** -/
theorem exists_unique_purchase (A : Accumulation) (n : ℕ) :
    ∃! t : ℝ, 0 ≤ t ∧ A.E t = n * Real.pi := by
  obtain ⟨b, hb0, hbc⟩ := A.unbounded (n * Real.pi)
  have hzero : A.E 0 ≤ n * Real.pi := by
    rw [A.zero]
    positivity
  exact existsUnique_threshold A.cont A.mono hzero hb0 hbc

/-- The n-th purchase height: the unique `t ≥ 0` where the accumulation reaches `n·π`. -/
noncomputable def purchaseHeight (A : Accumulation) (n : ℕ) : ℝ :=
  (A.exists_unique_purchase n).exists.choose

/-- The defining property of the purchase height. -/
theorem purchaseHeight_spec (A : Accumulation) (n : ℕ) :
    0 ≤ A.purchaseHeight n ∧ A.E (A.purchaseHeight n) = n * Real.pi :=
  (A.exists_unique_purchase n).exists.choose_spec

/-- **The ladder is strictly ordered**: later harmonics purchase strictly higher. -/
theorem purchaseHeight_strictMono (A : Accumulation) : StrictMono A.purchaseHeight := by
  intro n m hnm
  have hn := A.purchaseHeight_spec n
  have hm := A.purchaseHeight_spec m
  have hE : A.E (A.purchaseHeight n) < A.E (A.purchaseHeight m) := by
    rw [hn.2, hm.2]
    have : (n : ℝ) < m := by exact_mod_cast hnm
    nlinarith [Real.pi_pos]
  exact (A.mono.lt_iff_lt).mp hE

/-- The zeroth purchase is at the origin. -/
theorem purchaseHeight_zero (A : Accumulation) : A.purchaseHeight 0 = 0 := by
  have h := A.purchaseHeight_spec 0
  have h0 : A.E (A.purchaseHeight 0) = A.E 0 := by
    rw [h.2, A.zero]
    simp
  exact A.mono.injective h0

/-- Every later purchase is at strictly positive height. -/
theorem purchaseHeight_pos (A : Accumulation) (n : ℕ) :
    0 < A.purchaseHeight (n + 1) := by
  have := A.purchaseHeight_strictMono (Nat.succ_pos n)
  rwa [A.purchaseHeight_zero] at this

/-- **The staircase reads the ladder exactly**: at the n-th purchase the harmonic count is `n`. -/
theorem harmonicCount_purchase (A : Accumulation) (n : ℕ) :
    harmonicCount A.E (A.purchaseHeight n) = n := by
  apply harmonicCount_at_threshold
  rw [(A.purchaseHeight_spec n).2]
  push_cast
  ring

/-- **The ladder is discrete at infinity**: only finitely many purchases below any ceiling. -/
theorem purchaseHeight_discrete (A : Accumulation) (R : ℝ) :
    {n : ℕ | |A.purchaseHeight n| ≤ R}.Finite := by
  apply Set.Finite.subset (Set.finite_Iic ⌈A.E R / Real.pi⌉₊)
  intro n hn
  simp only [Set.mem_setOf_eq] at hn
  simp only [Set.mem_Iic]
  have hspec := A.purchaseHeight_spec n
  have habs : A.purchaseHeight n ≤ R := le_trans (le_abs_self _) hn
  have hER : (n : ℝ) * Real.pi ≤ A.E R := by
    rw [← hspec.2]
    exact A.mono.monotone habs
  have hn_le : (n : ℝ) ≤ A.E R / Real.pi := by
    rw [le_div_iff₀ Real.pi_pos]
    exact hER
  have := le_trans hn_le (Nat.le_ceil _)
  exact_mod_cast this

/-- **The bare-bones model is Hilbert–Pólya complete.** From accumulation alone: (a) the ladder
    exists with `E = n·π` at each purchase; (b) it is real and strictly ordered; (c) the
    staircase reads it exactly; (d) it is discrete at infinity; (e) the resolvent trace over the
    ladder cannot resonate off the real axis, for any admissible weights — the reality principle
    by construction. -/
theorem purchase_model_complete (A : Accumulation) :
    (∀ n : ℕ, 0 ≤ A.purchaseHeight n ∧ A.E (A.purchaseHeight n) = n * Real.pi) ∧
    StrictMono A.purchaseHeight ∧
    (∀ n : ℕ, harmonicCount A.E (A.purchaseHeight n) = n) ∧
    (∀ R : ℝ, {n : ℕ | |A.purchaseHeight n| ≤ R}.Finite) ∧
    (∀ c : ℕ → ℝ, (∀ n, 0 ≤ c n) →
      Summable (fun n => c n / (A.purchaseHeight (n + 1)) ^ 2) →
      ∀ w : ℂ, w.im ≠ 0 → DifferentiableAt ℂ
        (fun z : ℂ => ∑' n : ℕ, (c n : ℂ)
          * (1 / (z - (A.purchaseHeight (n + 1) : ℂ))
            + 1 / (A.purchaseHeight (n + 1) : ℂ))) w) := by
  refine ⟨A.purchaseHeight_spec, A.purchaseHeight_strictMono, A.harmonicCount_purchase,
    A.purchaseHeight_discrete, fun c hc hsum w hw => ?_⟩
  apply realSpectrum_regularized_trace hc
    (fun n => (A.purchaseHeight_pos n).ne') ?_ hsum hw
  intro R
  have hshift : {n : ℕ | |A.purchaseHeight (n + 1)| ≤ R}
      ⊆ (fun n : ℕ => n + 1) ⁻¹' {m : ℕ | |A.purchaseHeight m| ≤ R} := by
    intro n hn
    exact hn
  apply Set.Finite.subset _ hshift
  apply Set.Finite.preimage _ (A.purchaseHeight_discrete R)
  exact Set.injOn_of_injective (add_left_injective 1)

end Accumulation

/-! ## Part 21 — the transport argument: a ghost is phase-invisible and cannot cancel

Two unconditional beams of the transport-completeness argument (Sam: an off-line zero
"doesn't survive the transport").

**Beam 1 (the line shadow).** The factor a hypothetical off-line pair `ρ, 1 − conj ρ`
contributes on the critical line is `−((Re ρ − ½)² + (t − Im ρ)²)` — REAL, strictly
negative when `Re ρ ≠ ½`, never zero, with phase pinned at `π`. An off-line pair is
invisible to every phase observable (no node, no flip, no winding, no ladder entry,
no loop) while still demanding +2 in the analytic count: it is counted but never
transported. Its only line trace is an amplitude pothole that does not touch bottom.

**Beam 2 (no silent cancellation).** A finite sum of simple-pole terms with a nonzero
weight is NOT identically zero off its poles: near a pole it blows up. So a nonempty
ghost set cannot hide inside a vanishing partial-fraction subsum — if the geometric
ladder readout and the Hadamard partial fraction (kernel-clean, unconditional, over the
actual zeros) ever produce the same trace, the off-line subsum is identically zero off
its poles, and by this lemma the ghost set is empty.

What remains between these beams and the census is exactly one identity: the geometric
(ladder) production of the trace without assuming the ladder exhausts the zeros — the
on-line, earned helix identity. These two beams make the remainder sharp: the ghost has
no phase channel to live in (Beam 1) and no cancellation to hide behind (Beam 2). -/

section Transport

open Filter Topology

/-- **Beam 1: the off-line pair's line shadow is real and negative.** For `s` on the
critical line and any `ρ`, the pair factor `(s − ρ)(s − (1 − conj ρ))` equals
`−((Re ρ − ½)² + (Im s − Im ρ)²)` — a nonpositive real. Phase contribution: constant. -/
theorem offline_pair_line_factor {s ρ : ℂ} (hs : s.re = 1 / 2) :
    (s - ρ) * (s - (1 - (starRingEnd ℂ) ρ))
      = -(((ρ.re - 1 / 2) ^ 2 + (s.im - ρ.im) ^ 2 : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.one_im, Complex.conj_re, Complex.conj_im, hs] <;>
    ring

/-- **Beam 1, sharpened: an off-line pair produces NO node on the line.** If `Re ρ ≠ ½`
its line factor never vanishes — the pair is invisible to sign flips. -/
theorem offline_pair_no_node {s ρ : ℂ} (hs : s.re = 1 / 2) (hρ : ρ.re ≠ 1 / 2) :
    (s - ρ) * (s - (1 - (starRingEnd ℂ) ρ)) ≠ 0 := by
  rw [offline_pair_line_factor hs]
  have hpos : (0 : ℝ) < (ρ.re - 1 / 2) ^ 2 + (s.im - ρ.im) ^ 2 := by
    have h1 : (0 : ℝ) < (ρ.re - 1 / 2) ^ 2 := by
      have : ρ.re - 1 / 2 ≠ 0 := sub_ne_zero.mpr hρ
      positivity
    nlinarith [sq_nonneg (s.im - ρ.im)]
  simp only [ne_eq, neg_eq_zero, Complex.ofReal_eq_zero]
  exact hpos.ne'

/-- **Beam 2: a nonempty pole sum cannot vanish identically.** If `ρ₀ ∈ F` carries a
nonzero weight, the finite partial fraction `∑_{ρ ∈ F} w ρ / (s − ρ)` is not zero for
all `s` off the poles: multiplying by `(s − ρ₀)` and letting `s → ρ₀` extracts `w ρ₀`.
A ghost set with residues cannot hide inside a vanishing subsum. -/
theorem finite_pole_sum_ne_zero {F : Finset ℂ} {w : ℂ → ℂ} {ρ₀ : ℂ}
    (hρ₀ : ρ₀ ∈ F) (hw : w ρ₀ ≠ 0) :
    ¬ (∀ s : ℂ, s ∉ (F : Set ℂ) → ∑ ρ ∈ F, w ρ / (s - ρ) = 0) := by
  intro h
  -- eventually (near ρ₀, off ρ₀) we are off ALL poles
  have hev_ne : ∀ᶠ s in 𝓝[≠] ρ₀, s ∉ (F : Set ℂ) := by
    have hcl : IsClosed ((F.erase ρ₀ : Finset ℂ) : Set ℂ) := (Set.toFinite _).isClosed
    have hmem : (((F.erase ρ₀ : Finset ℂ) : Set ℂ))ᶜ ∈ 𝓝 ρ₀ :=
      hcl.isOpen_compl.mem_nhds (by simp)
    filter_upwards [nhdsWithin_le_nhds hmem, self_mem_nhdsWithin] with s hsm hne hsF
    refine hsm ?_
    simp only [Finset.coe_erase, Set.mem_diff, Set.mem_singleton_iff]
    exact ⟨hsF, by simpa using hne⟩
  -- the regularized product tends to the residue w ρ₀ …
  have key : Tendsto (fun s : ℂ => (s - ρ₀) * ∑ ρ ∈ F, w ρ / (s - ρ))
      (𝓝[≠] ρ₀) (𝓝 (w ρ₀)) := by
    have hsplit : ∀ᶠ s in 𝓝[≠] ρ₀,
        (s - ρ₀) * ∑ ρ ∈ F, w ρ / (s - ρ)
          = w ρ₀ + (s - ρ₀) * ∑ ρ ∈ F.erase ρ₀, w ρ / (s - ρ) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hsne : s - ρ₀ ≠ 0 := sub_ne_zero.mpr (by simpa using hs)
      rw [← Finset.add_sum_erase F _ hρ₀, mul_add]
      congr 1
      field_simp
    rw [tendsto_congr' hsplit]
    have h0 : Tendsto (fun s : ℂ => s - ρ₀) (𝓝[≠] ρ₀) (𝓝 0) := by
      simpa using ((continuous_sub_right ρ₀).tendsto ρ₀).mono_left
        nhdsWithin_le_nhds
    have hG : Tendsto (fun s : ℂ => ∑ ρ ∈ F.erase ρ₀, w ρ / (s - ρ)) (𝓝[≠] ρ₀)
        (𝓝 (∑ ρ ∈ F.erase ρ₀, w ρ / (ρ₀ - ρ))) := by
      apply tendsto_finsetSum
      intro ρ hρ
      have hne : ρ₀ - ρ ≠ 0 :=
        sub_ne_zero.mpr (Ne.symm (Finset.ne_of_mem_erase hρ))
      exact (tendsto_const_nhds.div
        ((continuous_sub_right ρ).tendsto ρ₀) hne).mono_left
        nhdsWithin_le_nhds
    have := h0.mul hG
    simpa using tendsto_const_nhds.add this
  -- … but the hypothesis forces it to tend to 0
  have hzero : Tendsto (fun s : ℂ => (s - ρ₀) * ∑ ρ ∈ F, w ρ / (s - ρ))
      (𝓝[≠] ρ₀) (𝓝 0) := by
    have hev : ∀ᶠ s in 𝓝[≠] ρ₀,
        (s - ρ₀) * ∑ ρ ∈ F, w ρ / (s - ρ) = 0 := by
      filter_upwards [hev_ne] with s hs
      rw [h s hs, mul_zero]
    rw [tendsto_congr' hev]
    exact tendsto_const_nhds
  exact hw (by simpa using tendsto_nhds_unique key hzero)

/-- **The quantum-symmetry break (Sam): a ghost is an unpaid purchase.** The off-line
pair's line factor is a STRICTLY NEGATIVE REAL at every point of the line: its phase is
frozen at `π` for all heights, so across ANY window it contributes ZERO phase advance —
while the kernel's twin tax (`two_le_offLineEnergyChar_of_event`) makes the same pair
cost at least two quanta of windowed energy. Every genuine node pays exactly one
quantum of phase for its count; the ghost demands count while paying none. A
deformation hosting it would have to live purely in the radial/amplitude channel — on
the helix AND the antihelix symmetrically — against a placement law with no free radial
degrees of freedom. -/
theorem offline_pair_phase_frozen {s ρ : ℂ} (hs : s.re = 1 / 2) (hρ : ρ.re ≠ 1 / 2) :
    ((s - ρ) * (s - (1 - (starRingEnd ℂ) ρ))).im = 0 ∧
    ((s - ρ) * (s - (1 - (starRingEnd ℂ) ρ))).re < 0 := by
  rw [offline_pair_line_factor hs]
  constructor
  · simp only [Complex.neg_im, Complex.ofReal_im, neg_zero]
  · have hpos : (0 : ℝ) < (ρ.re - 1 / 2) ^ 2 + (s.im - ρ.im) ^ 2 := by
      have h1 : (0 : ℝ) < (ρ.re - 1 / 2) ^ 2 := by
        have : ρ.re - 1 / 2 ≠ 0 := sub_ne_zero.mpr hρ
        positivity
      nlinarith [sq_nonneg (s.im - ρ.im)]
    simp only [Complex.neg_re, Complex.ofReal_re]
    exact neg_lt_zero.mpr hpos

end Transport

/-! ## Part 22 — the K = 1 annulus mechanism, through the Möbius fold

In the lowest annulus (fold size `K = 1`, heights `2π/q ≤ t < 8π/q`) the wave is
two-term: the unit mode plus its single Möbius image, `1 + c s`, where `c` carries the
functional-equation factor. The kernel already proves the prototype facts for the
canonical Möbius operator: `SpectralSide.w_unit_iff_half` (`‖w s‖ = 1 ↔ Re s = ½` —
the critical line IS the unit circle of the fold) and `SpectralSide.w_FE_reciprocal`
(`w s · w (1−s) = 1` — the FE as circle inversion). The two lemmas below are the K = 1
zero-forcing mechanism stated at that interface:

* a two-term wave whose `c` has the Möbius unit locus can vanish ONLY on the line —
  the balance `‖c‖ = 1` is available nowhere else (`mobius_two_term_zero_on_line`);
* with a remainder of size `η` and a modulus gradient `m` away from the locus, every
  zero is confined to the tube `|Re s − ½| ≤ η/m` (`mobius_two_term_zero_tube`).

Instantiation for `L(s, χ)` in the K = 1 annulus requires two concrete analytic
inputs, named plainly: the FE factor's unit locus (true: `|X(σ+it)| = 1 ⟺ σ = ½`,
from the Γ-modulus and `w_FE_reciprocal`-type reciprocity) and an explicit
approximate-functional-equation remainder bound `η(t) < 1` in the annulus (measured
≈ 0.1–0.2; not yet formalized). Both are situational inputs, not hypotheses
equivalent to the conclusion. -/

section TwoTerm

/-- **K = 1 zero forcing.** If the reflected term `c` is unimodular exactly on the
critical line (the Möbius unit locus, as `SpectralSide.w_unit_iff_half` proves for the
canonical fold), then the two-term wave `1 + c` can vanish only on the line: a zero
forces `‖c s‖ = 1`, and the balance exists nowhere else. -/
theorem mobius_two_term_zero_on_line {c : ℂ → ℂ}
    (hc : ∀ s : ℂ, ‖c s‖ = 1 ↔ s.re = 1 / 2)
    {s : ℂ} (hz : 1 + c s = 0) : s.re = 1 / 2 := by
  have hcs : c s = -1 := by linear_combination hz
  exact (hc s).mp (by rw [hcs, norm_neg, norm_one])

/-- **K = 1 tube.** With a remainder of size `η` and a modulus gradient `m` away from
the Möbius unit locus, every zero of the perturbed two-term wave `1 + c + R` lies in
the tube `|Re s − ½| ≤ η / m`: at a zero, `‖1 + c s‖ = ‖R s‖ ≤ η`, while the reverse
triangle inequality and the gradient force `‖1 + c s‖ ≥ m·|Re s − ½|`. -/
theorem mobius_two_term_zero_tube {c R : ℂ → ℂ} {m η : ℝ}
    (hgrad : ∀ s : ℂ, m * |s.re - 1 / 2| ≤ |‖c s‖ - 1|)
    (hm : 0 < m) {s : ℂ} (hR : ‖R s‖ ≤ η) (hz : 1 + c s + R s = 0) :
    |s.re - 1 / 2| ≤ η / m := by
  have hsum : 1 + c s = -R s := by linear_combination hz
  have h1 : ‖1 + c s‖ ≤ η := by rw [hsum, norm_neg]; exact hR
  have h2 : |‖c s‖ - 1| ≤ ‖1 + c s‖ := by
    have := abs_norm_sub_norm_le (c s) (-1 : ℂ)
    simpa [sub_neg_eq_add, add_comm] using this
  have h3 : m * |s.re - 1 / 2| ≤ η := le_trans (hgrad s) (le_trans h2 h1)
  rw [le_div_iff₀ hm]
  linarith

end TwoTerm

/-! ## Part 23 — the uniformity dichotomy: a zero's line signature touches bottom iff on-line

The central-uniformity criterion (Sam), as kernel mathematics. Every zero `ρ` shows on
the critical line through its FE-pair factor `(s − ρ)(s − (1 − conj ρ))`. The dichotomy:

* **on-line zero** — the factor has a line zero (the dip touches bottom at the zero's
  own height);
* **off-line zero** — the factor's modulus has the strictly positive floor
  `(Re ρ − ½)²` at EVERY line point (the dip never touches; a permanent pothole).

So "the space is uniform — every dip touches bottom" is exactly "every zero is on the
line", per pair, as an iff. Measured (results/central_uniformity.txt): six channels
including conductor 1009, uniform, with the all-on-line tail curvature predicted
parameter-free and confirmed to 2×10⁻⁵. -/

section Dichotomy

/-- **The off-line floor.** An off-line zero's pair factor has modulus at least
`(Re ρ − ½)² > 0` at every point of the line: its dip never touches bottom. -/
theorem offline_pair_positive_floor {s ρ : ℂ} (hs : s.re = 1 / 2) (hρ : ρ.re ≠ 1 / 2) :
    (0 : ℝ) < (ρ.re - 1 / 2) ^ 2 ∧
    ((ρ.re - 1 / 2) ^ 2 : ℝ) ≤ ‖(s - ρ) * (s - (1 - (starRingEnd ℂ) ρ))‖ := by
  have hd : ρ.re - 1 / 2 ≠ 0 := sub_ne_zero.mpr hρ
  refine ⟨by positivity, ?_⟩
  rw [offline_pair_line_factor hs, norm_neg, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  nlinarith [sq_nonneg (s.im - ρ.im)]

/-- **The uniformity dichotomy.** A zero's FE-pair factor has a zero ON the line iff
the zero itself is on the line: dips touch bottom exactly for on-line zeros. This is
the central-uniformity criterion as an iff. -/
theorem pair_signature_touches_iff_online (ρ : ℂ) :
    (∃ s : ℂ, s.re = 1 / 2 ∧ (s - ρ) * (s - (1 - (starRingEnd ℂ) ρ)) = 0) ↔
      ρ.re = 1 / 2 := by
  constructor
  · rintro ⟨s, hs, hz⟩
    rcases mul_eq_zero.mp hz with h | h
    · rw [← sub_eq_zero.mp h]; exact hs
    · have hse : s = 1 - (starRingEnd ℂ) ρ := sub_eq_zero.mp h
      have : s.re = 1 - ρ.re := by
        rw [hse]; simp [Complex.sub_re, Complex.one_re, Complex.conj_re]
      rw [hs] at this
      linarith
  · intro h
    exact ⟨ρ, h, by simp⟩

end Dichotomy

end HelixProduction
