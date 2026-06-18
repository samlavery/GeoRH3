import Mathlib
open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true
set_option grind.warning false
/-!
# Helix production model: simplicity of produced standing-wave zeros
This file builds a concrete *helix-production* model and proves that every zero
produced by the constructed helix crossing mechanism is **simple**: at each
constructed purchase / cancellation height the standing-wave carrier crosses the
cancellation locus *transversely* (nonzero derivative), so the zero is simple
and forces a genuine sign flip.
We do **not** prove any statement about global simplicity of zeros of the
Riemann zeta / Dirichlet `L`-functions.  The model below is a genuine, fully
formalized object (the carrier is an explicit entire function, and the
standing-wave readout is its real part on the real axis, which equals `sin`); all
results are honest statements about *this* model.
A narrative "zeta bridge"
(`standingWave t = 0 ↔ riemannZeta (1/2 + t·I) = 0`) is part of the informal
story but is *not* formalized here: stating it as a theorem about the concrete
carrier would be false, and assuming it as an axiom is disallowed.  None of the
simplicity results below depend on it.
-/
namespace HelixProductionSimple
/-- Number of phase half-periods reached at height `t`: counts how many multiples
of `π` the phase function `E` has accumulated. -/
noncomputable def harmonicCount (E : ℝ → ℝ) (t : ℝ) : ℕ := ⌊E t / Real.pi⌋₊
/-- A constructed geometric accumulation / helix-production object.
* `E` is the accumulated phase as a function of height;
* `purchaseHeight n` is the height of the `n`-th cancellation ("purchase");
* the phase reaches exactly `n·π` at the `n`-th purchase height, which is the
  cancellation locus of the carrier;
* the harmonic count there is exactly `n`;
* purchase heights are strictly increasing. -/
structure Accumulation where
  E : ℝ → ℝ
  purchaseHeight : ℕ → ℝ
  purchaseHeight_spec : ∀ n : ℕ,
    0 ≤ purchaseHeight n ∧ E (purchaseHeight n) = n * Real.pi
  harmonicCount_purchase : ∀ n : ℕ, harmonicCount E (purchaseHeight n) = n
  purchaseHeight_strictMono : StrictMono purchaseHeight
lemma geo_purchaseHeight_spec (n : ℕ) :
    0 ≤ (n : ℝ) * Real.pi ∧ (fun t => t) ((n : ℝ) * Real.pi) = n * Real.pi := by
  exact ⟨ by positivity, rfl ⟩
lemma geo_harmonicCount (n : ℕ) :
    harmonicCount (fun t => t) ((n : ℝ) * Real.pi) = n := by
  unfold HelixProductionSimple.harmonicCount;
  norm_num [ Real.pi_ne_zero ]
lemma geo_strictMono : StrictMono (fun n : ℕ => (n : ℝ) * Real.pi) := by
  exact fun a b h => mul_lt_mul_of_pos_right ( Nat.cast_lt.mpr h ) Real.pi_pos
/-- The concrete geometric helix: the phase is the height itself (`E t = t`), so
the `n`-th purchase height is `n·π`. -/
noncomputable def geometricAccumulation : Accumulation where
  E := fun t => t
  purchaseHeight := fun n => (n : ℝ) * Real.pi
  purchaseHeight_spec := geo_purchaseHeight_spec
  harmonicCount_purchase := geo_harmonicCount
  purchaseHeight_strictMono := geo_strictMono
end HelixProductionSimple
open HelixProductionSimple
namespace HelixStandingWaveS
open Complex
/-- The complex carrier wave of the helix: an explicit entire function. -/
noncomputable def waveC (z : ℂ) : ℂ := -Complex.I * Complex.exp (Complex.I * z)
/-- The real standing-wave readout: the real part of the carrier on the real
axis.  Concretely this is `Real.sin`. -/
noncomputable def standingWave (t : ℝ) : ℝ := (waveC (t : ℂ)).re
/-- The complex derivative of the carrier is `exp (I z)`. -/
lemma waveC_deriv (z : ℂ) : deriv waveC z = Complex.exp (Complex.I * z) := by
  have h : HasDerivAt HelixStandingWaveS.waveC (cexp (Complex.I * z)) z := by
    have hb := (((Complex.hasDerivAt_exp (Complex.I * z)).comp z ((hasDerivAt_id z).const_mul Complex.I)).const_mul (-Complex.I))
    refine hb.congr_deriv ?_
    rw [show (-Complex.I * (cexp (Complex.I * z) * (Complex.I * 1))) = -(Complex.I*Complex.I) * cexp (Complex.I * z) from by ring, Complex.I_mul_I]; ring
  exact h.deriv
/-- The standing-wave readout is exactly `sin`. -/
lemma standingWave_eq_sin (t : ℝ) : standingWave t = Real.sin t := by
  unfold HelixStandingWaveS.standingWave HelixStandingWaveS.waveC; norm_num [ Complex.exp_re, Complex.exp_im ] ;
/-- The standing wave is differentiable, with derivative the real part of the
carrier's complex derivative. -/
theorem standingWave_hasDerivAt (t : ℝ) :
    HasDerivAt standingWave ((deriv waveC (t : ℂ)).re) t := by
      rw [ show HelixStandingWaveS.standingWave = Real.sin from funext HelixStandingWaveS.standingWave_eq_sin ];
      convert Real.hasDerivAt_sin t using 1;
      rw [ waveC_deriv ] ; norm_num [ Complex.exp_re, Complex.exp_im ]
/-- **General sign-flip lemma.** A real function with nonzero derivative at a
zero changes sign across that zero: in every neighbourhood there are points on
each side whose values have opposite signs. -/
theorem signFlip_of_hasDerivAt {f : ℝ → ℝ} {t₀ d : ℝ}
    (h0 : f t₀ = 0) (hderiv : HasDerivAt f d t₀) (hd : d ≠ 0) :
    ∀ ε > 0, ∃ a ∈ Set.Ioo (t₀ - ε) t₀, ∃ b ∈ Set.Ioo t₀ (t₀ + ε),
      f a * f b < 0 := by
        intro ε hε_pos
        have h_slope : ∃ a ∈ Set.Ioo (t₀ - ε) t₀, ∃ b ∈ Set.Ioo t₀ (t₀ + ε), f a < 0 ∧ f b > 0 ∨ f a > 0 ∧ f b < 0 := by
          -- Since $d \neq 0$, we have $0 < \frac{f(t) - f(t₀)}{t - t₀}$ for $t$ near $t₀$.
          have h_slope_pos : ∀ᶠ t in nhdsWithin t₀ {t₀}ᶜ, (f t - f t₀) / (t - t₀) * d > 0 := by
            have h_slope_pos : Filter.Tendsto (fun t => (f t - f t₀) / (t - t₀)) (nhdsWithin t₀ {t₀}ᶜ) (nhds d) := by
              rw [ hasDerivAt_iff_tendsto_slope ] at hderiv;
              rw [show (fun t => (f t - f t₀)/(t - t₀)) = slope f t₀ from by funext t; rw [slope_def_field]]; exact hderiv
            exact h_slope_pos.mul_const d |> fun h => h.eventually ( lt_mem_nhds <| by nlinarith [ mul_self_pos.mpr hd ] );
          -- Since $d \neq 0$, we can find points $a$ and $b$ in the intervals $(t₀ - ε, t₀)$ and $(t₀, t₀ + ε)$ respectively such that $(f a - f t₀) / (a - t₀) * d > 0$ and $(f b - f t₀) / (b - t₀) * d > 0$.
          obtain ⟨a, ha₁, ha₂⟩ : ∃ a ∈ Set.Ioo (t₀ - ε) t₀, (f a - f t₀) / (a - t₀) * d > 0 := by
            have := h_slope_pos.filter_mono ( show nhdsWithin t₀ ( Set.Iio t₀ ) ≤ nhdsWithin t₀ { t₀ } ᶜ from nhdsWithin_mono _ <| by simp +decide );
            rcases ( this.and ( Ioo_mem_nhdsLT ( show t₀ - ε < t₀ by linarith ) ) ) with h ; obtain ⟨ x, hx₁, hx₂ ⟩ := h.exists ; exact ⟨ x, hx₂, hx₁ ⟩
          obtain ⟨b, hb₁, hb₂⟩ : ∃ b ∈ Set.Ioo t₀ (t₀ + ε), (f b - f t₀) / (b - t₀) * d > 0 := by
            have := h_slope_pos.filter_mono ( show nhdsWithin t₀ ( Set.Ioi t₀ ) ≤ nhdsWithin t₀ { t₀ } ᶜ from nhdsWithin_mono _ <| by simp +decide );
            rcases ( this.and ( Ioo_mem_nhdsGT <| show t₀ < t₀ + ε by linarith ) ) with h ; obtain ⟨ x, hx₁, hx₂ ⟩ := h.exists ; exact ⟨ x, hx₂, hx₁ ⟩;
          cases lt_or_gt_of_ne hd <;> simp_all +decide [ div_mul_eq_mul_div ];
          · exact ⟨ a, ha₁, b, hb₁, Or.inr ⟨ by rw [ lt_div_iff_of_neg ] at ha₂ <;> nlinarith, by nlinarith ⟩ ⟩;
          · exact ⟨ a, ha₁, b, hb₁, Or.inl ⟨ by rw [ lt_div_iff_of_neg ] at ha₂ <;> nlinarith, hb₂ ⟩ ⟩;
        rcases h_slope with ⟨ a, ha, b, hb, h | h ⟩ <;> [ exact ⟨ a, ha, b, hb, by nlinarith ⟩ ; exact ⟨ a, ha, b, hb, by nlinarith ⟩ ]
/-- Sign-flip lemma specialised to the standing wave. -/
theorem signFlip_of_simple_node {t₀ d : ℝ}
    (h0 : standingWave t₀ = 0)
    (hderiv : HasDerivAt standingWave d t₀)
    (hd : d ≠ 0) :
    ∀ ε > 0, ∃ a ∈ Set.Ioo (t₀ - ε) t₀, ∃ b ∈ Set.Ioo t₀ (t₀ + ε),
      standingWave a * standingWave b < 0 :=
  signFlip_of_hasDerivAt h0 hderiv hd
end HelixStandingWaveS
/-! ### The desired theorem family -/
/-- **Helix transversality at purchase heights.**
At each constructed purchase / cancellation height the standing-wave derivative
(the real part of the carrier's complex derivative) is nonzero.  This rules out
tangency / stalling of the carrier at the cancellation locus. -/
theorem helix_purchase_transverse (n : ℕ) :
    ((deriv HelixStandingWaveS.waveC
      (geometricAccumulation.purchaseHeight n : ℂ)).re) ≠ 0 := by
  erw [ HelixStandingWaveS.waveC_deriv ] ; norm_num [ Complex.exp_re ];
  erw [ HelixProductionSimple.geometricAccumulation ] ; norm_num [ Real.cos_nat_mul_pi ]
/-- **Simplicity of every produced helix node.**
Every standing-wave zero produced at a purchase height is simple: the standing
wave has a nonzero derivative there.
The hypothesis `hnode` is part of the requested statement; it is genuinely
satisfiable (indeed `standingWave (purchaseHeight n) = sin (n·π) = 0` holds for
this model), but it is not needed for the proof, since transversality holds at
every purchase height unconditionally. -/
theorem produced_standingWave_zero_simple (n : ℕ)
    (hnode : HelixStandingWaveS.standingWave
      (geometricAccumulation.purchaseHeight n) = 0) :
    ∃ d : ℝ,
      HasDerivAt HelixStandingWaveS.standingWave d
        (geometricAccumulation.purchaseHeight n) ∧ d ≠ 0 := by
  refine ⟨((deriv HelixStandingWaveS.waveC
      (geometricAccumulation.purchaseHeight n : ℂ)).re), ?_, ?_⟩
  · exact HelixStandingWaveS.standingWave_hasDerivAt
      (geometricAccumulation.purchaseHeight n)
  · exact helix_purchase_transverse n
/-- **Every produced node forces a sign flip.** -/
theorem produced_node_forces_signFlip (n : ℕ)
    (hnode : HelixStandingWaveS.standingWave
      (geometricAccumulation.purchaseHeight n) = 0) :
    ∀ ε > 0, ∃ a ∈ Set.Ioo
        (geometricAccumulation.purchaseHeight n - ε)
        (geometricAccumulation.purchaseHeight n),
      ∃ b ∈ Set.Ioo
        (geometricAccumulation.purchaseHeight n)
        (geometricAccumulation.purchaseHeight n + ε),
        HelixStandingWaveS.standingWave a *
          HelixStandingWaveS.standingWave b < 0 := by
  intro ε hε
  obtain ⟨d, hd, hdnz⟩ := produced_standingWave_zero_simple n hnode
  exact HelixStandingWaveS.signFlip_of_simple_node hnode hd hdnz ε hε
/-- **Vanishing at a produced node forces a sign flip.**
This is the same local transversality statement with the hypothesis named as a
vanishing event: once the produced standing wave vanishes at the purchase
height, simplicity supplies opposite signs on the two sides of that height. -/
theorem produced_vanishing_forces_signFlip (n : ℕ)
    (hvanish : HelixStandingWaveS.standingWave
      (geometricAccumulation.purchaseHeight n) = 0) :
    ∀ ε > 0, ∃ a ∈ Set.Ioo
        (geometricAccumulation.purchaseHeight n - ε)
        (geometricAccumulation.purchaseHeight n),
      ∃ b ∈ Set.Ioo
        (geometricAccumulation.purchaseHeight n)
        (geometricAccumulation.purchaseHeight n + ε),
        HelixStandingWaveS.standingWave a *
          HelixStandingWaveS.standingWave b < 0 :=
  produced_node_forces_signFlip n hvanish
/-- **No produced node is non-simple.**  The carrier's derivative cannot vanish
at a produced cancellation height.
As in `produced_standingWave_zero_simple`, the requested hypothesis `hnode` is
satisfiable but not needed for the proof. -/
theorem produced_node_not_nonsimple (n : ℕ)
    (hnode : HelixStandingWaveS.standingWave
      (geometricAccumulation.purchaseHeight n) = 0) :
    ¬ (((deriv HelixStandingWaveS.waveC
      (geometricAccumulation.purchaseHeight n : ℂ)).re) = 0) :=
  helix_purchase_transverse n
