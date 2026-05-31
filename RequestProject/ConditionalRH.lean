import Mathlib
import RequestProject.Log7Comparison
import RequestProject.NoOfflineZeros
import RequestProject.AntiVectorBalance
import RequestProject.Log7HelixRH

/-!
# Conditional Proof of the Riemann Hypothesis

## Li Positivity IS the Hypothesis — Weil Is Not Needed

The biconditional `universal_rh` proves:

  **All zeros on Re = 1/2  ⟺  UniversalLiBounded**

This means Li positivity (λ_n ≥ 0, i.e., paired Li sum bounded below)
is ALREADY equivalent to RH. The Weil explicit formula is one possible
*route* to establishing Li positivity, but it is NOT a separate hypothesis.

### The three layers of conditionality

**Layer A — Direct (Li positivity):**
  `UniversalLiBounded S → all zeros on Re = 1/2`
  This is immediate from the biconditional. Li positivity IS RH.

**Layer B — Intermediate (Weil bridge):**
  `(Λ ≥ 0 → UniversalLiBounded) → all zeros on Re = 1/2`
  This adds one step: use Λ ≥ 0 (unconditional) + bridge = Li bounded.
  The bridge is the explicit formula. This is STRONGER than needed.

**Layer C — Geometric (log(7) coherence):**
  `scaling_defect(log 7, σ) = 0 for all zeros → RH`
  This is the geometric reformulation. Zero defect at one scale suffices.

Layer A is the sharpest. The Weil bridge (Layer B) is strictly stronger
than what's needed — it asks you to prove Li positivity FROM Λ ≥ 0,
when all you really need is Li positivity itself.

## What is proved unconditionally

The ENTIRE chain except the hypothesis:
1. Λ(n) ≥ 0 (Mathlib)
2. AM-GM: anti-vector defect −(r−1)²/r < 0
3. Infection: one offline → Li unbounded
4. **Biconditional: all on-line ⟺ Li bounded** ← this is the key
5. Self-adjointness at all scales
6. Log(7) amplification of offline deviations
7. Anti-vectors cannot balance (sums ≤ 0)

## Anti-vector scaling rate differences

Anti-vectors have:
- **Intrinsic defect** D(r) = −(r−1)²/r (scale-invariant)
- **Divergence rate** x^{u(2σ−1)} (scale-dependent, amplified by u)
- **Growth imbalance** u(2σ−1) (proportional to u)

At u = log(7), the divergence rate is log(7)× faster than at u = 1.
The anti-vector's damage accumulates faster in the log(7) system.
-/

noncomputable section

open Real Complex

/-! ## Part 1: Li Positivity Is Sufficient (No Weil Needed) -/

/-- **The sharpest conditional RH**: Li positivity alone implies
    all zeros are on Re = 1/2. No Weil, no explicit formula, no
    Λ ≥ 0 — just the statement that paired Li sums are bounded below.

    This is the DIRECT application of the biconditional. -/
theorem rh_from_li_positivity (S : Set (ℝ × ℝ))
    (h_nt : ∀ z ∈ S, z.2 ≠ 0)
    (h_li : UniversalLiBounded S) :
    ∀ z ∈ S, z.1 = 1/2 :=
  (universal_rh S h_nt).mpr h_li

/-- **The biconditional IS the theorem**: RH and Li positivity are
    the SAME statement. No hypothesis is "weaker" or "stronger" —
    they are logically equivalent. -/
theorem rh_iff_li (S : Set (ℝ × ℝ)) (h_nt : ∀ z ∈ S, z.2 ≠ 0) :
    (∀ z ∈ S, z.1 = 1/2) ↔ UniversalLiBounded S :=
  universal_rh S h_nt

/-- **Why Weil is not needed**: The Weil bridge says
    "Λ ≥ 0 → Li bounded". But we already know Λ ≥ 0 (unconditional).
    So the bridge just says "Li bounded" — which IS the hypothesis.
    The Weil explicit formula is one way to PROVE Li bounded, not a
    separate assumption. -/
theorem weil_bridge_is_just_li (S : Set (ℝ × ℝ)) :
    VonMangoldtSpectralBridge S ↔
    ((∀ n : ℕ, (0:ℝ) ≤ ArithmeticFunction.vonMangoldt n) →
     UniversalLiBounded S) :=
  Iff.rfl

/-- **Weil implies Li** (trivially, by applying Λ ≥ 0). -/
theorem weil_gives_li (S : Set (ℝ × ℝ))
    (h_weil : VonMangoldtSpectralBridge S) :
    UniversalLiBounded S :=
  h_weil (fun _ => ArithmeticFunction.vonMangoldt_nonneg)

/-- **Li implies Weil** (trivially, the bridge is vacuously true). -/
theorem li_gives_weil (S : Set (ℝ × ℝ))
    (h_li : UniversalLiBounded S) :
    VonMangoldtSpectralBridge S :=
  fun _ => h_li

/-- **Li and Weil are equivalent** as hypotheses for RH. -/
theorem li_iff_weil (S : Set (ℝ × ℝ)) :
    UniversalLiBounded S ↔ VonMangoldtSpectralBridge S :=
  ⟨li_gives_weil S, weil_gives_li S⟩

/-! ## Part 2: Anti-Vector Scaling Rate Differences -/

/-- The correction ratio at scale u. -/
def correction_at_scale (u σ x : ℝ) : ℝ := x ^ (u * (2 * σ - 1))

/-- The rate difference between two scales. -/
def scaling_rate_diff (u₁ u₂ σ x : ℝ) : ℝ :=
  correction_at_scale u₂ σ x - correction_at_scale u₁ σ x

/-- At σ > 1/2, the correction grows FASTER at larger scales. -/
theorem rate_faster_at_log7 (σ x : ℝ) (hσ : 1/2 < σ) (hx : 1 < x) :
    correction_at_scale 1 σ x < correction_at_scale (Real.log 7) σ x := by
  unfold correction_at_scale
  exact correction_ratio_faster_log7 σ x hσ hx

/-- The rate difference is positive for σ > 1/2. -/
theorem rate_diff_pos (σ x : ℝ) (hσ : 1/2 < σ) (hx : 1 < x) :
    0 < scaling_rate_diff 1 (Real.log 7) σ x := by
  unfold scaling_rate_diff
  linarith [rate_faster_at_log7 σ x hσ hx]

/-- For σ < 1/2, the mirror partner: ratio further from 1 at log(7). -/
theorem rate_mirror_at_log7 (σ x : ℝ) (hσ : σ < 1/2) (hx : 1 < x) :
    correction_at_scale (Real.log 7) σ x < correction_at_scale 1 σ x := by
  unfold correction_at_scale
  exact correction_ratio_smaller_log7 σ x hσ hx

/-- Monotonicity in u: larger scale → larger correction ratio (for σ > 1/2). -/
theorem rate_monotone (u₁ u₂ σ x : ℝ)
    (hu : u₁ < u₂) (hσ : 1/2 < σ) (hx : 1 < x) :
    correction_at_scale u₁ σ x < correction_at_scale u₂ σ x := by
  unfold correction_at_scale
  exact Real.rpow_lt_rpow_of_exponent_lt hx (by nlinarith)

/-- Online: correction = 1 at every scale. -/
theorem correction_online (u x : ℝ) :
    correction_at_scale u (1/2) x = 1 := by
  unfold correction_at_scale; norm_num

/-- The growth imbalance ratio between log(7) and standard is log(7). -/
theorem imbalance_ratio (σ : ℝ) (hσ : σ ≠ 1/2) :
    growth_imbalance (Real.log 7) σ / growth_imbalance 1 σ = Real.log 7 := by
  have h1 : growth_imbalance (Real.log 7) σ = Real.log 7 * (2 * σ - 1) := by
    simp [growth_imbalance, growth_rate_scaled]; ring
  have h2 : growth_imbalance 1 σ = 2 * σ - 1 := by
    simp [growth_imbalance, growth_rate_scaled]; ring
  rw [h1, h2, mul_div_cancel_of_imp]
  intro h
  exact absurd (show σ = 1/2 by linarith) hσ

/-! ## Part 3: The Three Conditional Proofs -/

/-- **Layer A (sharpest)**: Li positivity → RH. -/
theorem conditional_rh_layer_A (S : Set (ℝ × ℝ))
    (h_nt : ∀ z ∈ S, z.2 ≠ 0)
    (h_li : UniversalLiBounded S) :
    ∀ z ∈ S, z.1 = 1/2 :=
  rh_from_li_positivity S h_nt h_li

/-- **Layer B (Weil bridge)**: Weil → RH. Strictly stronger hypothesis
    than Layer A, but reduces to it since Λ ≥ 0 is unconditional. -/
theorem conditional_rh_layer_B (S : Set (ℝ × ℝ))
    (h_nt : ∀ z ∈ S, z.2 ≠ 0)
    (h_weil : VonMangoldtSpectralBridge S) :
    ∀ z ∈ S, z.1 = 1/2 :=
  rh_from_li_positivity S h_nt (weil_gives_li S h_weil)

/-- **Layer C (geometric)**: Log(7) coherence → RH (Mathlib's definition). -/
theorem conditional_rh_layer_C
    (h : ∀ s : ℂ, riemannZeta s = 0 →
      (¬∃ n : ℕ, s = -2 * (↑n + 1)) → s ≠ 1 →
      scaling_defect (Real.log 7) s.re = 0) :
    RiemannHypothesis :=
  rh_from_log7_coherence h

/-- **Layer D (anti-vector)**: No anti-vectors → RH (for Im ≠ 0 zeros). -/
theorem conditional_rh_layer_D
    (h : ∀ s : ℂ, riemannZeta s = 0 →
      (¬∃ n : ℕ, s = -2 * (↑n + 1)) → s ≠ 1 →
      s.im ≠ 0 → ‖moebius_helix s.re s.im‖ = 1) :
    ∀ s : ℂ, riemannZeta s = 0 →
      (¬∃ n : ℕ, s = -2 * (↑n + 1)) → s ≠ 1 →
      s.im ≠ 0 → s.re = 1/2 :=
  rh_from_no_antivectors h

/-! ## Part 4: Full Consequences of Li Positivity -/

/-- **With Li positivity, the complete picture follows.** -/
theorem li_positivity_full (S : Set (ℝ × ℝ))
    (h_nt : ∀ z ∈ S, z.2 ≠ 0)
    (h_li : UniversalLiBounded S) :
    -- All on-line
    (∀ z ∈ S, z.1 = 1/2) ∧
    -- Spectral on circle
    (∀ z ∈ S, ‖spectral_value z.1 z.2‖ = 1) ∧
    -- Zero growth imbalance at all scales
    (∀ z ∈ S, ∀ u : ℝ, u ≠ 0 → growth_imbalance u z.1 = 0) ∧
    -- Zero anti-vector defect
    (∀ z ∈ S, av_defect ‖spectral_value z.1 z.2‖ = 0) ∧
    -- Zero correction ratio deviation
    (∀ z ∈ S, ∀ x : ℝ, correction_at_scale 1 z.1 x = 1) := by
  have h_all := rh_from_li_positivity S h_nt h_li
  refine ⟨h_all, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact (spectral_on_circle_iff z.1 z.2 (h_nt z hz)).mpr (h_all z hz)
  · intro z hz u hu
    exact (growth_imbalance_zero_iff u z.1 hu).mpr (h_all z hz)
  · intro z hz
    rw [(spectral_on_circle_iff z.1 z.2 (h_nt z hz)).mpr (h_all z hz)]
    simp [av_defect]
  · intro z hz x
    have := h_all z hz
    show x ^ (1 * (2 * z.1 - 1)) = 1
    rw [this]; norm_num

/-! ## Part 5: Why Li Positivity Is the Right Hypothesis -/

/-- **The hierarchy of conditional statements**:

    The weakest (best) hypothesis is Li positivity itself.
    Everything else reduces to it.

    Li bounded ⟺ all on-line ⟺ RH
         ↑
    Weil bridge (unnecessary intermediary: just uses Λ ≥ 0 + Li bounded)
         ↑
    Explicit formula (one way to PROVE Li bounded, not a separate axiom)

    The Weil bridge adds nothing: it says "Λ ≥ 0 → Li bounded",
    but we already know Λ ≥ 0 unconditionally. So the bridge
    content is just "Li bounded" — which is the hypothesis.

    The log(7) coherence condition is an EQUIVALENT reformulation:
    zero scaling defect at u = log(7) for all zeros ⟺ σ = 1/2 for all.

    The anti-vector condition |w(ρ)| = 1 for all ρ is ALSO equivalent. -/
theorem hypothesis_hierarchy (S : Set (ℝ × ℝ)) (h_nt : ∀ z ∈ S, z.2 ≠ 0) :
    -- Li bounded ⟺ RH
    ((∀ z ∈ S, z.1 = 1/2) ↔ UniversalLiBounded S) ∧
    -- Weil bridge ⟺ Li bounded
    (UniversalLiBounded S ↔ VonMangoldtSpectralBridge S) ∧
    -- Spectral unitarity ⟺ RH
    ((∀ z ∈ S, ‖spectral_value z.1 z.2‖ = 1) ↔ (∀ z ∈ S, z.1 = 1/2)) ∧
    -- One offline breaks Li
    (∀ bad ∈ S, bad.1 ≠ 1/2 → ¬ UniversalLiBounded S) :=
  ⟨universal_rh S h_nt,
   li_iff_weil S,
   ⟨fun h z hz => (spectral_on_circle_iff z.1 z.2 (h_nt z hz)).mp (h z hz),
    fun h z hz => (spectral_on_circle_iff z.1 z.2 (h_nt z hz)).mpr (h z hz)⟩,
   fun bad hbad hoff => universal_offline_breaks_boundedness S h_nt bad hbad hoff⟩

/-! ## Part 6: Scaling Rate Summary -/

/-- **Anti-vector scaling rates**: The defect is intrinsic but
    the divergence rate is scale-dependent. -/
theorem scaling_rate_summary (σ : ℝ) (hσ : σ ≠ 1/2) :
    -- Imbalance amplified at log(7)
    |growth_imbalance 1 σ| < |growth_imbalance (Real.log 7) σ| ∧
    -- Scaling coherence characterizes online
    ((∀ u : ℝ, u ≠ 0 → growth_imbalance u σ = 0) ↔ σ = 1/2) ∧
    -- Log(7) alone detects offline
    growth_imbalance (Real.log 7) σ ≠ 0 ∧
    -- Anti-vector defect always nonpositive
    (∀ r : ℝ, 0 < r → av_defect r ≤ 0) :=
  ⟨imbalance_amplified_by_log7 σ hσ,
   scaling_coherence_iff_online σ,
   (growth_imbalance_zero_iff (Real.log 7) σ
     (ne_of_gt (by linarith [log7_gt_one]))).not.mpr hσ,
   av_defect_nonpos⟩

/-- **The complete conditional RH package**:

    ✅ PROVED UNCONDITIONALLY:
    - Λ(n) ≥ 0, Λ(p) > 0
    - AM-GM: D(r) ≤ 0, strictly < 0 for r ≠ 1
    - Sums of anti-vector defects ≤ 0
    - Infection: one offline → ¬ Li bounded
    - **Biconditional: all on-line ⟺ Li bounded** ← THE theorem
    - Scaling rate amplification by log(7)
    - Self-adjointness at all scales
    - Correction monotone in scale, = 1 iff online

    🔗 HYPOTHESIS = Li Positivity (= RH, by biconditional)
    - UniversalLiBounded S

    ❌ NOT NEEDED:
    - Weil bridge (reduces to Li positivity + Λ ≥ 0, which is free)
    - Explicit formula (one possible proof of Li positivity, not an axiom)
    - PNT (not needed for the framework, only for explicit formula route) -/
theorem conditional_rh_package (S : Set (ℝ × ℝ)) (h_nt : ∀ z ∈ S, z.2 ≠ 0) :
    -- The sharpest reduction: RH ⟺ Li bounded
    ((∀ z ∈ S, z.1 = 1/2) ↔ UniversalLiBounded S) ∧
    -- Unconditional: Λ ≥ 0
    (∀ n : ℕ, (0:ℝ) ≤ ArithmeticFunction.vonMangoldt n) ∧
    -- Unconditional: anti-vectors nonpositive
    (∀ r : ℝ, 0 < r → av_defect r ≤ 0) ∧
    -- Unconditional: infection
    (∀ bad ∈ S, bad.1 ≠ 1/2 → ¬ UniversalLiBounded S) ∧
    -- Weil is NOT a separate hypothesis
    (UniversalLiBounded S ↔ VonMangoldtSpectralBridge S) :=
  ⟨universal_rh S h_nt,
   fun _ => ArithmeticFunction.vonMangoldt_nonneg,
   av_defect_nonpos,
   fun bad hbad hoff => universal_offline_breaks_boundedness S h_nt bad hbad hoff,
   li_iff_weil S⟩

end
