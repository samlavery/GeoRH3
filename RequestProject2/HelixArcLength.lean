import Mathlib
import RequestProject.HelixWindingGrowth

/-!
# Rebasing the helix to reality: `√n` EARNED from even arc-spacing

The construction is rebased onto its frozen-certain inputs — the linear radial law `R(k)=e^{mode}·k`
and the **even arc-length placement** of the integers — from which the `√n` baseline is *derived*, not
assumed.

The planar speed of the spiral `R(t)=e^{mode}·t` at angle `2πt` is `e^{mode}·√(1+(2πt)²)`
(`R'=e^{mode}`, `φ'=2π`), so the slope `e^{mode}` factors out of the arc length. We sandwich the
slope-free integral `arc0 k = ∫₀ᵏ √(1+(2πt)²)` between `πk²` and `k+πk²` (pointwise
`2πt ≤ √(1+(2πt)²) ≤ 1+2πt`, trivial integrals — no `arsinh`, no area measure), scale by `e^{mode}`,
and invert the even placement `arc = n·U` to earn `R(kₙ)² = Θ(n)`, i.e. **`R(kₙ) = Θ(√n)`**.

**The slope `e^{mode}` cancels** in the dimensionless law (`radius_sq_slope_cancels`): dividing `R²`
by `e^{mode}` leaves a slope-free band `U/(1+π)·n ≤ R²/e^{mode} ≤ U/π·n`.

**`pitch = unit` is the single fitted line** — `placed mode U n k := arc mode k = n·U` — and `U` appears
*nowhere* in the `Θ(k²)` geometry (`speed0`/`arc0`/`arc0_lower`/`arc0_upper`), only here. Swap it without
touching the earned `√n`.

Honest caveats: (1) we prove the `Θ(k²)` sandwich, not the exact `arc0 k / k² → π` (the `arsinh`
antiderivative is heavier and not needed for `Θ(√n)`); (2) the lower bound needs `k ≥ 1` (to absorb the
linear term — harmless for large `n`); (3) `placed` *assumes* a `kₙ` with `arc mode kₙ = n·U` exists;
constructing it (IVT on the strictly-monotone continuous `arc`) is a clean follow-up.
-/

open scoped Real
open MeasureTheory intervalIntegral

namespace HelixArcLength

/-- Slope-free planar arc-length integrand `√(1+(2πt)²)`. -/
noncomputable def speed0 (t : ℝ) : ℝ := Real.sqrt (1 + (2 * Real.pi * t) ^ 2)

theorem speed0_cont : Continuous speed0 := by unfold speed0; fun_prop

theorem speed0_lower (t : ℝ) : 2 * Real.pi * t ≤ speed0 t := by
  unfold speed0
  rcases le_or_gt (2 * Real.pi * t) 0 with h | h
  · exact le_trans h (Real.sqrt_nonneg _)
  · calc 2 * Real.pi * t = Real.sqrt ((2 * Real.pi * t) ^ 2) := by rw [Real.sqrt_sq h.le]
      _ ≤ Real.sqrt (1 + (2 * Real.pi * t) ^ 2) := by apply Real.sqrt_le_sqrt; nlinarith

theorem speed0_upper {t : ℝ} (ht : 0 ≤ t) : speed0 t ≤ 1 + 2 * Real.pi * t := by
  unfold speed0
  have hpos : (0 : ℝ) ≤ 1 + 2 * Real.pi * t := by positivity
  rw [show (1 + 2 * Real.pi * t) = Real.sqrt ((1 + 2 * Real.pi * t) ^ 2) by rw [Real.sqrt_sq hpos]]
  apply Real.sqrt_le_sqrt
  nlinarith [mul_nonneg Real.pi_pos.le ht]

/-- Slope-free planar arc length `arc0 k = ∫₀ᵏ √(1+(2πt)²) dt`. -/
noncomputable def arc0 (k : ℝ) : ℝ := ∫ t in (0 : ℝ)..k, speed0 t

/-- **Lower `Θ(k²)` bound** (from `√(1+(2πt)²) ≥ 2πt`): `πk² ≤ arc0 k`. -/
theorem arc0_lower {k : ℝ} (hk : 0 ≤ k) : Real.pi * k ^ 2 ≤ arc0 k := by
  unfold arc0
  have hint : (∫ t in (0 : ℝ)..k, (2 * Real.pi * t)) = Real.pi * k ^ 2 := by
    rw [intervalIntegral.integral_const_mul, integral_id]; ring
  rw [← hint]
  apply intervalIntegral.integral_mono_on hk
  · exact (by fun_prop : Continuous (fun t : ℝ => 2 * Real.pi * t)).intervalIntegrable _ _
  · exact speed0_cont.intervalIntegrable _ _
  · intro x _; exact speed0_lower x

/-- **Upper `Θ(k²)` bound** (from `√(1+(2πt)²) ≤ 1+2πt` on `[0,k]`): `arc0 k ≤ k + πk²`. -/
theorem arc0_upper {k : ℝ} (hk : 0 ≤ k) : arc0 k ≤ k + Real.pi * k ^ 2 := by
  unfold arc0
  have hii1 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 k :=
    (continuous_const).intervalIntegrable _ _
  have hii2 : IntervalIntegrable (fun t : ℝ => 2 * Real.pi * t) volume 0 k :=
    (by fun_prop : Continuous (fun t : ℝ => 2 * Real.pi * t)).intervalIntegrable _ _
  have hint : (∫ t in (0 : ℝ)..k, (1 + 2 * Real.pi * t)) = k + Real.pi * k ^ 2 := by
    rw [intervalIntegral.integral_add hii1 hii2,
        intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const]
    simp; ring
  rw [← hint]
  apply intervalIntegral.integral_mono_on hk
  · exact speed0_cont.intervalIntegrable _ _
  · exact hii1.add hii2
  · intro x hx; exact speed0_upper hx.1

/-- Full planar arc length with the frozen slope: `arc mode k = e^{mode}·arc0 k`. -/
noncomputable def arc (mode k : ℝ) : ℝ := Real.exp mode * arc0 k

theorem arc_lower (mode : ℝ) {k : ℝ} (hk : 0 ≤ k) :
    Real.exp mode * (Real.pi * k ^ 2) ≤ arc mode k :=
  mul_le_mul_of_nonneg_left (arc0_lower hk) (Real.exp_pos mode).le

theorem arc_upper (mode : ℝ) {k : ℝ} (hk : 0 ≤ k) :
    arc mode k ≤ Real.exp mode * (k + Real.pi * k ^ 2) :=
  mul_le_mul_of_nonneg_left (arc0_upper hk) (Real.exp_pos mode).le

/-- The **radius** at loop `k` — agrees with `HelixWinding.norm_plane` (`= ‖plane mode k‖`, `k ≥ 0`). -/
noncomputable def radius (mode k : ℝ) : ℝ := Real.exp mode * k

theorem radius_eq_norm_plane (mode : ℝ) {k : ℝ} (hk : 0 ≤ k) :
    radius mode k = ‖HelixWinding.plane mode k‖ := (HelixWinding.norm_plane mode hk).symm

/-- **[FITTED — single swappable line]** the `n`-th integer sits at arc length `n·U` (even spacing;
    pitch `U` = integer-spacing unit). The ONE less-certain input; `U` is NOT used in the `Θ(k²)`
    bounds, so the earned `√n` is independent of this fit. -/
def placed (mode U n k : ℝ) : Prop := arc mode k = n * U

/-- **Upper bound on `R²`** (from `arc_lower`): `R(kₙ)² ≤ e^{mode}·U/π · n`. -/
theorem radius_sq_le {mode U n k : ℝ} (hk : 0 ≤ k) (hpl : placed mode U n k) :
    (radius mode k) ^ 2 ≤ Real.exp mode * U / Real.pi * n := by
  have hlow : Real.exp mode * (Real.pi * k ^ 2) ≤ n * U := hpl ▸ arc_lower mode hk
  have hpi : 0 < Real.pi := Real.pi_pos
  have hem : 0 < Real.exp mode := Real.exp_pos mode
  unfold radius
  rw [mul_pow, ← Real.exp_nat_mul]
  have hk2 : Real.exp mode * k ^ 2 ≤ n * U / Real.pi := by
    rw [le_div_iff₀ hpi]; nlinarith [hlow]
  calc Real.exp ((2 : ℕ) * mode) * k ^ 2
      = Real.exp mode * (Real.exp mode * k ^ 2) := by
        rw [show ((2 : ℕ) : ℝ) * mode = mode + mode by push_cast; ring, Real.exp_add]; ring
    _ ≤ Real.exp mode * (n * U / Real.pi) := mul_le_mul_of_nonneg_left hk2 hem.le
    _ = Real.exp mode * U / Real.pi * n := by ring

/-- **Lower bound on `R²`** (from `arc_upper`, `k ≥ 1`): `e^{mode}·U/(1+π) · n ≤ R(kₙ)²`. -/
theorem radius_sq_ge {mode U n k : ℝ} (hk : 1 ≤ k) (hpl : placed mode U n k) :
    Real.exp mode * U / (1 + Real.pi) * n ≤ (radius mode k) ^ 2 := by
  have hk0 : (0 : ℝ) ≤ k := le_trans zero_le_one hk
  have hup : n * U ≤ Real.exp mode * (k + Real.pi * k ^ 2) := hpl ▸ arc_upper mode hk0
  have hpi : 0 < Real.pi := Real.pi_pos
  have hem : 0 < Real.exp mode := Real.exp_pos mode
  have hkk : k ≤ k ^ 2 := by nlinarith
  have hup2 : n * U ≤ Real.exp mode * ((1 + Real.pi) * k ^ 2) := by
    refine le_trans hup ?_
    apply mul_le_mul_of_nonneg_left _ hem.le; nlinarith
  unfold radius
  rw [mul_pow, ← Real.exp_nat_mul]
  have h1pi : 0 < 1 + Real.pi := by positivity
  have hk2 : n * U / (1 + Real.pi) ≤ Real.exp mode * k ^ 2 := by
    rw [div_le_iff₀ h1pi]; nlinarith [hup2]
  calc Real.exp mode * U / (1 + Real.pi) * n
      = Real.exp mode * (n * U / (1 + Real.pi)) := by ring
    _ ≤ Real.exp mode * (Real.exp mode * k ^ 2) := mul_le_mul_of_nonneg_left hk2 hem.le
    _ = Real.exp ((2 : ℕ) * mode) * k ^ 2 := by
        rw [show ((2 : ℕ) : ℝ) * mode = mode + mode by push_cast; ring, Real.exp_add]; ring

/-- **The slope `e^{mode}` CANCELS — only `n` (hence `√n`) survives.** Dividing `R(kₙ)²` by `e^{mode}`
    leaves a slope-free two-sided bound `U/(1+π)·n ≤ R²/e^{mode} ≤ U/π·n`. -/
theorem radius_sq_slope_cancels {mode U n k : ℝ} (hk : 1 ≤ k) (hpl : placed mode U n k) :
    U / (1 + Real.pi) * n ≤ (radius mode k) ^ 2 / Real.exp mode
    ∧ (radius mode k) ^ 2 / Real.exp mode ≤ U / Real.pi * n := by
  have hem : 0 < Real.exp mode := Real.exp_pos mode
  have hlo := radius_sq_ge hk hpl
  have hhi := radius_sq_le (le_trans zero_le_one hk) hpl
  have h1pi : 0 < 1 + Real.pi := by positivity
  have e1 : Real.exp mode * U / (1 + Real.pi) * n
      = Real.exp mode * (U / (1 + Real.pi) * n) := by field_simp
  have e2 : Real.exp mode * U / Real.pi * n = Real.exp mode * (U / Real.pi * n) := by field_simp
  rw [e1] at hlo; rw [e2] at hhi
  refine ⟨?_, ?_⟩
  · rw [le_div_iff₀ hem]; nlinarith [hlo]
  · rw [div_le_iff₀ hem]; nlinarith [hhi]

/-- **`R(kₙ) = Θ(√n)`, explicitly**: the radius is squeezed between two constant multiples of `√n`:
    `√(e^{mode}·U/(1+π))·√n ≤ R(kₙ) ≤ √(e^{mode}·U/π)·√n`. The `n`-dependence is exactly `√n`. -/
theorem radius_theta_sqrtn {mode U n k : ℝ} (hk : 1 ≤ k) (hU : 0 ≤ U) (_hn : 0 ≤ n)
    (hpl : placed mode U n k) :
    Real.sqrt (Real.exp mode * U / (1 + Real.pi)) * Real.sqrt n ≤ radius mode k
    ∧ radius mode k ≤ Real.sqrt (Real.exp mode * U / Real.pi) * Real.sqrt n := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hem : 0 < Real.exp mode := Real.exp_pos mode
  have hrad0 : 0 ≤ radius mode k := by unfold radius; positivity
  have hClo : 0 ≤ Real.exp mode * U / (1 + Real.pi) := by positivity
  have hChi : 0 ≤ Real.exp mode * U / Real.pi := by positivity
  have hlo := radius_sq_ge hk hpl
  have hhi := radius_sq_le (le_trans zero_le_one hk) hpl
  refine ⟨?_, ?_⟩
  · rw [← Real.sqrt_mul hClo]
    calc Real.sqrt (Real.exp mode * U / (1 + Real.pi) * n)
        ≤ Real.sqrt ((radius mode k) ^ 2) := Real.sqrt_le_sqrt hlo
      _ = radius mode k := Real.sqrt_sq hrad0
  · rw [← Real.sqrt_mul hChi]
    calc radius mode k = Real.sqrt ((radius mode k) ^ 2) := (Real.sqrt_sq hrad0).symm
      _ ≤ Real.sqrt (Real.exp mode * U / Real.pi * n) := Real.sqrt_le_sqrt hhi

/-! ### The placement EXISTS and is unique — the accumulator is total

The header's noted follow-up, discharged: the arc length is continuous and strictly monotone
(speed ≥ slope, since `√(1+(2πt)²) ≥ 1`), it starts at `0` and is unbounded (`arc0_lower`), so by
the intermediate value theorem EVERY integer `n` has exactly one loop position `kₙ ≥ 0` with
`arc mode kₙ = n·U`. The even-spacing accumulator is total: each consumed integer owns one place
on the spiral, determined by the two constants (slope `e^mode`, pitch `U`) and nothing else. -/

/-- The speed never drops below `1`. -/
theorem one_le_speed0 (t : ℝ) : 1 ≤ speed0 t := by
  unfold speed0
  have h : (1 : ℝ) ≤ 1 + (2 * Real.pi * t) ^ 2 := by nlinarith [sq_nonneg (2 * Real.pi * t)]
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ Real.sqrt (1 + (2 * Real.pi * t) ^ 2) := Real.sqrt_le_sqrt h

/-- The slope-free arc length is continuous. -/
theorem arc0_continuous : Continuous arc0 := by
  rw [continuous_iff_continuousAt]
  intro b
  have h := intervalIntegral.integral_hasDerivAt_right
    (speed0_cont.intervalIntegrable 0 b)
    (speed0_cont.stronglyMeasurableAtFilter _ _)
    speed0_cont.continuousAt
  exact h.continuousAt

/-- The slope-free arc length is strictly monotone. -/
theorem arc0_strictMono : StrictMono arc0 := by
  intro a b hab
  have hsplit : arc0 a + ∫ t in a..b, speed0 t = arc0 b := by
    unfold arc0
    exact intervalIntegral.integral_add_adjacent_intervals
      (speed0_cont.intervalIntegrable 0 a) (speed0_cont.intervalIntegrable a b)
  have hpos : b - a ≤ ∫ t in a..b, speed0 t := by
    have hconst : (∫ t in a..b, (1 : ℝ)) = b - a := by
      rw [intervalIntegral.integral_const]
      simp
    rw [← hconst]
    apply intervalIntegral.integral_mono_on (le_of_lt hab)
      ((continuous_const).intervalIntegrable _ _)
      (speed0_cont.intervalIntegrable _ _)
    intro x _
    exact one_le_speed0 x
  linarith

/-- **The placement exists and is unique**: for every `n ≥ 0` and pitch `U > 0` there is exactly
    one `k ≥ 0` with `arc mode k = n·U`. The accumulator is total — every integer has its one
    place on the spiral, from the constants alone. -/
theorem existsUnique_placed (mode : ℝ) {U : ℝ} (hU : 0 < U) {n : ℝ} (hn : 0 ≤ n) :
    ∃! k : ℝ, 0 ≤ k ∧ placed mode U n k := by
  have hem : (0 : ℝ) < Real.exp mode := Real.exp_pos mode
  set T : ℝ := n * U / Real.exp mode with hT
  have hT0 : 0 ≤ T := by positivity
  set k₀ : ℝ := Real.sqrt (T / Real.pi) + 1 with hk₀
  have hk₀0 : 0 ≤ k₀ := by positivity
  have hceil : T ≤ arc0 k₀ := by
    have hs : Real.sqrt (T / Real.pi) ^ 2 = T / Real.pi :=
      Real.sq_sqrt (by positivity)
    have h2 : T / Real.pi ≤ k₀ ^ 2 := by
      rw [hk₀]
      nlinarith [Real.sqrt_nonneg (T / Real.pi), hs]
    have h1 : T ≤ Real.pi * k₀ ^ 2 := by
      calc T = Real.pi * (T / Real.pi) := by
            field_simp
        _ ≤ Real.pi * k₀ ^ 2 := by
            apply mul_le_mul_of_nonneg_left h2 (le_of_lt Real.pi_pos)
    exact le_trans h1 (arc0_lower hk₀0)
  have harc00 : arc0 0 = 0 := by
    unfold arc0
    simp
  have hivt : ∃ k ∈ Set.Icc 0 k₀, arc0 k = T := by
    have hcont : ContinuousOn arc0 (Set.Icc 0 k₀) := arc0_continuous.continuousOn
    have hmem : T ∈ Set.Icc (arc0 0) (arc0 k₀) := by
      rw [harc00]
      exact ⟨hT0, hceil⟩
    obtain ⟨k, hk, hkeq⟩ := intermediate_value_Icc hk₀0 hcont hmem
    exact ⟨k, hk, hkeq⟩
  obtain ⟨k, hkmem, hkeq⟩ := hivt
  refine ⟨k, ⟨hkmem.1, ?_⟩, ?_⟩
  · unfold placed arc
    rw [hkeq, hT]
    field_simp
  · rintro k' ⟨hk'0, hk'pl⟩
    unfold placed arc at hk'pl
    have hk'eq : arc0 k' = T := by
      rw [hT]
      field_simp at hk'pl ⊢
      linarith [hk'pl]
    exact arc0_strictMono.injective (by rw [hk'eq, hkeq])

end HelixArcLength
