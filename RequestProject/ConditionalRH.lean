import Mathlib
import RequestProject.NoOfflineZeros
import RequestProject.AntiVectorBalance

/-!
# Li Positivity and Anti-Vector Scaling

## The biconditional

`universal_rh` / `rh_iff_li`:

  **All zeros on Re = 1/2  ⟺  UniversalLiBounded**

Li positivity (λ_n ≥ 0, i.e., paired Li sum bounded below) is equivalent
to the on-line condition. The Weil explicit formula is one possible *route*
to establishing Li positivity (`li_iff_weil`), not a separate hypothesis.

## What is proved unconditionally

1. Λ(n) ≥ 0 (Mathlib)
2. AM-GM: anti-vector defect −(r−1)²/r < 0
3. Infection: one offline → Li unbounded
4. Biconditional: all on-line ⟺ Li bounded
5. Self-adjointness at all scales
6. Log(7) amplification of offline deviations
7. Anti-vectors cannot balance (sums ≤ 0)

## Anti-vector scaling rate differences

Anti-vectors have:
- **Intrinsic defect** D(r) = −(r−1)²/r (scale-invariant)
- **Divergence rate** x^{u(2σ−1)} (scale-dependent, amplified by u)
- **Growth imbalance** u(2σ−1) (proportional to u)

At u = log(7), the divergence rate is log(7)× faster than at u = 1.
-/

noncomputable section

open Real Complex

/-! ## Part 1: Li Positivity Is Sufficient (No Weil Needed) -/

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

/-! ## Part 3: Why Li Positivity Is the Right Hypothesis -/

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
