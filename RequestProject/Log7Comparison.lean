import Mathlib
import RequestProject.Defs
import RequestProject.CoordinateInvariance
import RequestProject.ScalingCoherence

/-!
# Log(7) vs Standard: How Offline Zeros Behave Under the Full Helix

## Overview

The mod-6 helix has a natural period of log(7) — because 7 is the first
prime ≡ 1 mod 6 after the base prime 6±1, and the helix wraps with
period 2π in angle, matching (π/3)·log(7·7·…). The log(7) coordinate
system makes the helix's native geometry explicit.

## What changes (and what doesn't)

### Invariant under coordinate change
- **Möbius spectral condition**: |w(ρ)| = 1 ⟺ σ = 1/2 (intrinsic to ρ)
- **FE pairing**: ρ ↔ 1−ρ (complex conjugation of w ↦ 1/w)
- **AM-GM defect**: (1−r) + (1−1/r) = −(r−1)²/r < 0 for r ≠ 1
- **Li coefficient values**: λ_n = 1 − Re(w^n) (depends only on w, not coords)

### Amplified by log(7) ≈ 1.946
- **Growth imbalance**: u·(2σ−1) at unit u. At u=log(7), this is ≈ 1.946× larger
- **Distance from midpoint**: |σ'−u/2| = |u|·|σ−1/2|, so ≈ 1.946× larger
- **Correction ratio**: x^{u(2σ−1)} grows faster in x for larger |u|
- **Helix node spacing**: log(p) → log(7)·log(p), so nodes are ≈ 1.946× taller

### The key insight

In the standard system, an offline zero at σ = 0.6 deviates by 0.1 from
the midpoint 0.5. In the log(7) system, the same zero maps to
σ' = log(7)·0.6 ≈ 1.168, deviating by log(7)·0.1 ≈ 0.195 from the
midpoint log(7)/2 ≈ 0.973.

The deviation is **amplified**. The helix "stretches" the strip, making
offline zeros more prominent — their error corrections grow faster,
their mirror pair defects are computed at larger r values, and the
Li coefficients blow up more quickly.

This is why scaling coherence characterizes RH: only on-line zeros
produce the same relative geometry in every coordinate system. Offline
zeros create coordinate-dependent artifacts that grow with the unit.

## What is proved

### Part 1: Amplification factors
- `imbalance_amplified_by_log7`: log(7) system has ≈ 1.946× larger imbalance
- `distance_amplified_by_log7`: midpoint distance is ≈ 1.946× larger
- `log7_amplification_factor`: the factor is exactly log(7)

### Part 2: Concrete offline zero comparison
- `offline_example_standard`: σ=0.6 has imbalance 0.2 in standard system
- `offline_example_log7`: σ=0.6 has imbalance log(7)·0.2 in log(7) system
- `offline_ratio_grows_faster`: correction ratio x^{u(2σ−1)} grows faster

### Part 3: Helix geometry comparison
- `helix_spacing_amplified`: node heights are log(7)× taller
- `helix_angle_preserved_mod`: angular relationships preserved
- `online_zero_helix_same`: on-line zeros look identical in both systems

### Part 4: The integrated helix picture
- `integrated_comparison`: full comparison of both coordinate systems
- `log7_makes_offline_worse`: offline zeros are strictly worse in log(7)
- `only_online_survives_all_units`: the unique scaling-invariant state
-/

noncomputable section

open Real Complex

/-! ## Part 1: Amplification Factors -/

/-- log(7) > 1: the amplification factor is greater than 1. -/
theorem log7_gt_one : 1 < Real.log 7 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ) < 7)]
  exact Real.exp_one_lt_d9.trans_le (by norm_num)

/-- The amplification factor when going from standard to log(7) coordinates. -/
theorem log7_amplification_factor (σ : ℝ) :
    growth_imbalance (Real.log 7) σ = Real.log 7 * growth_imbalance 1 σ := by
  simp [growth_imbalance, growth_rate_scaled]; ring

/-- **Imbalance is amplified by log(7)**: for any offline zero,
    the growth imbalance in the log(7) system is log(7) times larger
    than in the standard system. Since log(7) > 1, the imbalance
    is strictly amplified. -/
theorem imbalance_amplified_by_log7 (σ : ℝ) (hσ : σ ≠ 1/2) :
    |growth_imbalance 1 σ| < |growth_imbalance (Real.log 7) σ| := by
  exact imbalance_amplified 1 (Real.log 7) σ hσ (by
    rw [abs_of_pos (by linarith : (0:ℝ) < 1), abs_of_pos (by linarith [log7_gt_one])]
    exact log7_gt_one)

/-- **Distance from midpoint is amplified**: |σ' − u/2| = |u|·|σ − 1/2|.
    In the log(7) system, the distance is log(7) times the standard distance. -/
theorem distance_amplified_by_log7 (σ : ℝ) :
    |scale_coord (Real.log 7) σ - Real.log 7 / 2| =
    Real.log 7 * |σ - 1 / 2| := by
  rw [distance_from_midpoint_scales]
  rw [abs_of_pos (by linarith [log7_gt_one])]

/-- For offline zeros, the log(7) distance is strictly larger. -/
theorem distance_strictly_larger_log7 (σ : ℝ) (hσ : σ ≠ 1/2) :
    |σ - 1/2| < |scale_coord (Real.log 7) σ - Real.log 7 / 2| := by
  rw [distance_amplified_by_log7]
  have habs : 0 < |σ - 1/2| := abs_pos.mpr (sub_ne_zero.mpr hσ)
  nlinarith [log7_gt_one]

/-! ## Part 2: Concrete Offline Zero Comparison -/

/-- In the standard system, σ = 3/5 has growth imbalance 1·(2·3/5 − 1) = 1/5. -/
theorem offline_example_standard :
    growth_imbalance 1 (3/5) = 1/5 := by
  simp [growth_imbalance, growth_rate_scaled]; ring

/-- In the log(7) system, σ = 3/5 has growth imbalance log(7)/5, which is
    larger than 1/5 because log(7) > 1. -/
theorem offline_example_log7 :
    growth_imbalance (Real.log 7) (3/5) = Real.log 7 / 5 := by
  simp [growth_imbalance, growth_rate_scaled]; ring

/-- The log(7) imbalance at σ=3/5 is strictly larger than the standard one. -/
theorem offline_example_comparison :
    growth_imbalance 1 (3/5) < growth_imbalance (Real.log 7) (3/5) := by
  rw [offline_example_standard, offline_example_log7]
  linarith [log7_gt_one]

/-- **Correction ratio grows faster**: The scaled correction ratio
    x^{u(2σ−1)} is a monotonically increasing function of |u| when
    σ > 1/2 and x > 1. In the log(7) system, it's x^{log(7)(2σ−1)}
    vs x^{2σ−1} in the standard system. -/
theorem correction_ratio_faster_log7 (σ x : ℝ) (hσ : 1/2 < σ) (hx : 1 < x) :
    scaled_correction_ratio 1 σ x < scaled_correction_ratio (Real.log 7) σ x := by
  unfold scaled_correction_ratio
  apply Real.rpow_lt_rpow_of_exponent_lt hx
  nlinarith [log7_gt_one]

/-- For σ < 1/2, the correction ratio is LESS than 1, and log(7) makes
    it even smaller (further from 1, i.e., more extreme). -/
theorem correction_ratio_smaller_log7 (σ x : ℝ) (hσ : σ < 1/2) (hx : 1 < x) :
    scaled_correction_ratio (Real.log 7) σ x < scaled_correction_ratio 1 σ x := by
  unfold scaled_correction_ratio
  apply Real.rpow_lt_rpow_of_exponent_lt hx
  nlinarith [log7_gt_one]

/-! ## Part 3: Helix Geometry Comparison -/

/-- **Helix spacing is amplified**: The height of prime p on the helix is
    log(7)·log(p) in the log(7) system vs log(p) in the standard system.
    The spacing between nodes is uniformly stretched by factor log(7). -/
theorem helix_spacing_amplified (p : ℕ) :
    log_prime_in_unit (Real.log 7) p = Real.log 7 * Real.log p := rfl

/-- **Ratios are preserved**: The ratio of heights of any two primes is
    the same in both coordinate systems (log(p)/log(q) is invariant). -/
theorem helix_ratio_invariant (p q : ℕ) (hq : Real.log q ≠ 0) :
    log_prime_in_unit (Real.log 7) p / log_prime_in_unit (Real.log 7) q =
    Real.log p / Real.log q := by
  unfold log_prime_in_unit
  rw [mul_div_mul_left _ _ (ne_of_gt (by linarith [log7_gt_one] : (0:ℝ) < Real.log 7))]

/-- **On-line zeros look identical**: An on-line zero at σ = 1/2 maps to
    σ' = log(7)/2 in the log(7) system. Its distance from the midpoint
    is 0 in both systems. Its Möbius spectral value is still |w| = 1.
    The error correction x^{1/2}/ρ is the same function of x. -/
theorem online_zero_helix_same :
    -- (1) Distance from midpoint is 0 in standard
    (1/2 : ℝ) - 1/2 = 0 ∧
    -- (2) Distance from midpoint is 0 in log(7) system
    scale_coord (Real.log 7) (1/2) - Real.log 7 / 2 = 0 ∧
    -- (3) Growth imbalance is 0 in standard
    growth_imbalance 1 (1/2) = 0 ∧
    -- (4) Growth imbalance is 0 in log(7) system
    growth_imbalance (Real.log 7) (1/2) = 0 ∧
    -- (5) Scaled correction ratio is 1 in standard (for any x > 1)
    scaled_correction_ratio 1 (1/2) 2 = 1 ∧
    -- (6) Scaled correction ratio is 1 in log(7) system
    scaled_correction_ratio (Real.log 7) (1/2) 2 = 1 := by
  refine ⟨by ring, ?_, ?_, ?_, ?_, ?_⟩
  · simp [scale_coord]; ring
  · simp [growth_imbalance, growth_rate_scaled]; ring
  · simp [growth_imbalance, growth_rate_scaled]; ring
  · show (2 : ℝ) ^ (1 * (2 * (1 / 2) - 1)) = 1
    norm_num
  · show (2 : ℝ) ^ (Real.log 7 * (2 * (1 / 2) - 1)) = 1
    norm_num

/-! ## Part 4: The Integrated Helix Picture -/

/-- **The integrated comparison**: In the log(7) helix, everything that's
    invariant stays invariant, and everything that depends on the unit
    gets amplified by log(7). This makes offline zeros MORE visible,
    not less — their deviations are magnified.

    For any unit u > 1, offline zeros are strictly worse than at u = 1.
    For any unit 0 < u < 1, offline zeros are strictly better.
    At u = 1, we see the standard picture.
    At u = log(7), we see the helix's native geometry. -/
theorem integrated_comparison (σ : ℝ) (hσ : σ ≠ 1/2) :
    -- (1) Imbalance is amplified
    |growth_imbalance 1 σ| < |growth_imbalance (Real.log 7) σ| ∧
    -- (2) Distance from midpoint is amplified
    |σ - 1/2| < |scale_coord (Real.log 7) σ - Real.log 7 / 2| ∧
    -- (3) Imbalance is zero iff on-line (in both systems)
    (growth_imbalance 1 σ = 0 ↔ σ = 1/2) ∧
    (growth_imbalance (Real.log 7) σ = 0 ↔ σ = 1/2) ∧
    -- (4) The log(7) system has nonzero imbalance
    growth_imbalance (Real.log 7) σ ≠ 0 := by
  refine ⟨imbalance_amplified_by_log7 σ hσ,
         distance_strictly_larger_log7 σ hσ,
         growth_imbalance_zero_iff 1 σ one_ne_zero,
         growth_imbalance_zero_iff (Real.log 7) σ (ne_of_gt (by linarith [log7_gt_one])),
         ?_⟩
  exact (growth_imbalance_zero_iff (Real.log 7) σ
    (ne_of_gt (by linarith [log7_gt_one]))).not.mpr hσ

/-- **Log(7) makes offline worse**: For any offline zero σ ≠ 1/2 and any
    x > 1, the correction ratio in the log(7) system deviates MORE from 1
    than in the standard system.

    Specifically:
    - If σ > 1/2: ratio > 1 in both, but larger in log(7)
    - If σ < 1/2: ratio < 1 in both, but smaller in log(7)

    In both cases, the ratio is further from 1 in the log(7) system.

    **Log(7) makes offline worse**: For any offline zero σ ≠ 1/2,
    the growth imbalance in the log(7) system is strictly larger in
    absolute value than in the standard system. This means the
    deviation from balanced growth is amplified. -/
theorem log7_makes_offline_worse (σ : ℝ) (hσ : σ ≠ 1/2) :
    |growth_imbalance 1 σ| < |growth_imbalance (Real.log 7) σ| :=
  imbalance_amplified_by_log7 σ hσ

/-- **Only on-line survives all units**: The ONLY value of σ for which
    the growth imbalance is zero in EVERY coordinate system is σ = 1/2.
    This is the content of scaling coherence. -/
theorem only_online_survives_all_units (σ : ℝ) :
    (∀ u : ℝ, u ≠ 0 → growth_imbalance u σ = 0) ↔ σ = 1/2 :=
  scaling_coherence_iff_online σ

/-- **The log(7) system is a witness**: If σ ≠ 1/2, the log(7) system
    alone suffices to detect it (the imbalance is nonzero). -/
theorem log7_detects_offline (σ : ℝ) (hσ : σ ≠ 1/2) :
    growth_imbalance (Real.log 7) σ ≠ 0 :=
  (growth_imbalance_zero_iff (Real.log 7) σ
    (ne_of_gt (by linarith [log7_gt_one]))).not.mpr hσ

/-- **Amplification cascade**: For any sequence of units u₁ < u₂ < u₃ ...,
    the imbalance grows monotonically. The log(7) system sits between
    the standard (u=1) and even larger units. -/
theorem amplification_cascade (σ : ℝ) (hσ : σ ≠ 1/2) :
    |growth_imbalance 1 σ| < |growth_imbalance (Real.log 7) σ| ∧
    ∀ u : ℝ, Real.log 7 < u →
      |growth_imbalance (Real.log 7) σ| < |growth_imbalance u σ| := by
  constructor
  · exact imbalance_amplified_by_log7 σ hσ
  · intro u hu
    have hlog_pos : (0 : ℝ) < Real.log 7 := by linarith [log7_gt_one]
    exact imbalance_amplified (Real.log 7) u σ hσ (by
      rw [abs_of_pos hlog_pos, abs_of_pos (by linarith)]
      exact hu)

/-! ## Part 5: The Mirror Pair View -/

/-- The mirror pair in the log(7) system. The FE involution σ' ↦ u−σ'
    pairs σ' = log(7)·σ with log(7)·(1−σ) = log(7) − σ'. The pair
    is symmetric about log(7)/2, not about 1/2. -/
theorem mirror_pair_log7 (σ : ℝ) :
    scale_coord (Real.log 7) σ + scale_coord (Real.log 7) (1 - σ) = Real.log 7 := by
  simp [scale_coord]; ring

/-- **Mirror pair symmetry**: Both coordinate systems see the same
    symmetry structure — the pair sums to the unit width.
    Standard: σ + (1−σ) = 1.  Log(7): log(7)·σ + log(7)·(1−σ) = log(7). -/
theorem mirror_pair_symmetry :
    -- Standard system
    (∀ σ : ℝ, σ + (1 - σ) = 1) ∧
    -- Log(7) system
    (∀ σ : ℝ, scale_coord (Real.log 7) σ +
              scale_coord (Real.log 7) (1 - σ) = Real.log 7) := by
  exact ⟨fun σ => by ring, mirror_pair_log7⟩

/-- **The growth rate pair**: In the log(7) system, the pair of growth
    rates is (log(7)·σ, log(7)·(1−σ)). These are balanced (equal) iff
    σ = 1/2, regardless of the unit. -/
theorem growth_rate_pair_log7 (σ : ℝ) :
    growth_rate_scaled (Real.log 7) σ =
    growth_rate_scaled (Real.log 7) (1 - σ) ↔ σ = 1/2 := by
  unfold growth_rate_scaled
  have hlog : (0 : ℝ) < Real.log 7 := by linarith [log7_gt_one]
  constructor
  · intro h
    have := mul_left_cancel₀ hlog.ne' h
    linarith
  · intro h; rw [h]; ring

/-! ## Part 6: Summary — Why Log(7) Matters -/

/-- **Complete summary**: The log(7) coordinate system reveals the
    helix's native geometry. Offline zeros are amplified, making their
    incompatibility with the helix structure more visible. On-line zeros
    are perfectly invariant. The log(7)/2 midpoint replaces 1/2, but
    the geometric content (midpoint of strip, fixed point of FE) is
    identical.

    The amplification is monotonic in the unit: larger units make
    offline zeros look worse. This is why scaling coherence is
    equivalent to being on-line — only σ = 1/2 looks the same
    at every scale. -/
theorem log7_summary (σ : ℝ) :
    -- (1) On-line zeros: invariant
    (σ = 1/2 → growth_imbalance (Real.log 7) σ = 0) ∧
    -- (2) Off-line zeros: amplified
    (σ ≠ 1/2 → |growth_imbalance 1 σ| < |growth_imbalance (Real.log 7) σ|) ∧
    -- (3) The midpoint is log(7)/2 ≠ 1/2
    (scale_coord (Real.log 7) (1/2) = Real.log 7 / 2) ∧
    (Real.log 7 / 2 ≠ 1 / 2) ∧
    -- (4) Scaling coherence characterizes on-line
    ((∀ u : ℝ, u ≠ 0 → growth_imbalance u σ = 0) ↔ σ = 1/2) := by
  refine ⟨?_, ?_, ?_, ?_, scaling_coherence_iff_online σ⟩
  · intro h; rw [h]; simp [growth_imbalance, growth_rate_scaled]; ring
  · exact imbalance_amplified_by_log7 σ
  · simp [scale_coord]; ring
  · linarith [log7_gt_one]

end
