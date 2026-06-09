import Mathlib

/-!
# `‖Γ(z)‖ ≤ Γ(Re z)` — the complex-Gamma modulus bound

Mathlib has `gamma_stirling_bound` (sharp, with the `exp(−π|t|/2)` decay) but not this crude
modulus inequality, which is all an **upper** order-1 log bound needs (dropping the decay only
weakens an upper bound). From the integral representation `Γ(z) = ∫₀^∞ e^{−t} t^{z−1} dt`
(`Re z > 0`): `‖Γ(z)‖ ≤ ∫₀^∞ ‖e^{−t} t^{z−1}‖ = ∫₀^∞ e^{−t} t^{Re z−1} = Γ(Re z)`.
-/

open Complex MeasureTheory Set

namespace GammaBound

/-- **Complex-Gamma modulus bound.** For `Re z > 0`, `‖Γ(z)‖ ≤ Γ(Re z)`. -/
theorem norm_Gamma_le_Gamma_re {z : ℂ} (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Complex.Gamma_eq_integral hz, Complex.GammaIntegral, Real.Gamma_eq_integral hz]
  calc ‖∫ x in Ioi (0:ℝ), (↑(Real.exp (-x)) : ℂ) * (↑x : ℂ) ^ (z - 1)‖
      ≤ ∫ x in Ioi (0:ℝ), ‖(↑(Real.exp (-x)) : ℂ) * (↑x : ℂ) ^ (z - 1)‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ x in Ioi (0:ℝ), Real.exp (-x) * x ^ (z.re - 1) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        have hx0 : 0 < x := hx
        show ‖(↑(Real.exp (-x)) : ℂ) * (↑x : ℂ) ^ (z - 1)‖ = Real.exp (-x) * x ^ (z.re - 1)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
          Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.sub_re, Complex.one_re]

/-- **`Gammaℝ` modulus bound.** For `Re s > 0`, `‖Gammaℝ s‖ ≤ π^{−Re s/2}·Γ(Re s/2)` — combining the
    complex-Γ modulus bound with `Gammaℝ s = π^{−s/2}·Γ(s/2)`. The `gammaFactor` of a Dirichlet
    character is `Gammaℝ s` (even) or `Gammaℝ(s+1)` (odd), so this is its core growth estimate. -/
theorem norm_Gammaℝ_le {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.Gammaℝ s‖ ≤ Real.pi ^ (-s.re / 2) * Real.Gamma (s.re / 2) := by
  have hre2 : (s / 2).re = s.re / 2 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.div_ofReal_re]
  have hreNeg : ((-s) / 2).re = -s.re / 2 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.div_ofReal_re, Complex.neg_re]
  rw [Complex.Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos, hreNeg]
  have h2 : ‖Complex.Gamma (s / 2)‖ ≤ Real.Gamma (s.re / 2) := by
    rw [← hre2]; exact norm_Gamma_le_Gamma_re (by rw [hre2]; linarith)
  exact mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg Real.pi_pos.le _)

/-- **Real-Γ power bound.** `Γ(x) ≤ (x+1)^{x+1}` for `x ≥ 1`. Via `Γ(x) ≤ Γ(⌈x⌉)` (monotone on
    `[2,∞)`; `≤ 1` on `[1,2]` by convexity-below-chord) `= (⌈x⌉−1)! ≤ ⌈x⌉^{⌈x⌉} ≤ (x+1)^{x+1}`. -/
theorem Gamma_le_rpow {x : ℝ} (hx : 1 ≤ x) : Real.Gamma x ≤ (x + 1) ^ (x + 1) := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  set n := ⌈x⌉₊ with hn_def
  have hxn : x ≤ (n : ℝ) := Nat.le_ceil x
  have hnx1 : (n : ℝ) ≤ x + 1 := le_of_lt (Nat.ceil_lt_add_one hx0)
  have hn1 : 1 ≤ n := by exact_mod_cast le_trans hx hxn
  have hΓxn : Real.Gamma x ≤ Real.Gamma (n : ℝ) := by
    by_cases hx2 : x < 2
    · have hn_le2 : n ≤ 2 := Nat.ceil_le.mpr (le_of_lt hx2)
      have hΓ2 : Real.Gamma (2 : ℝ) = 1 := by
        rw [show (2 : ℝ) = ((1 : ℕ) : ℝ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]; simp
      have hΓx1 : Real.Gamma x ≤ 1 := by
        have h1 : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := by norm_num
        have h2 : (2 : ℝ) ∈ Set.Ioi (0 : ℝ) := by norm_num
        have hconv := Real.convexOn_Gamma.2 h1 h2
          (show (0 : ℝ) ≤ 2 - x by linarith) (show (0 : ℝ) ≤ x - 1 by linarith)
          (show (2 - x) + (x - 1) = 1 by ring)
        rw [Real.Gamma_one, hΓ2] at hconv
        simp only [smul_eq_mul] at hconv
        have harg : (2 - x) * 1 + (x - 1) * 2 = x := by ring
        rw [harg] at hconv; linarith
      have hΓn1 : Real.Gamma (n : ℝ) = 1 := by
        have hn12 : n = 1 ∨ n = 2 := by omega
        rcases hn12 with h | h
        · rw [h]; simp [Real.Gamma_one]
        · rw [h]; push_cast; exact hΓ2
      rw [hΓn1]; exact hΓx1
    · have hx2' : 2 ≤ x := not_lt.mp hx2
      have hn2 : (2 : ℝ) ≤ (n : ℝ) := le_trans hx2' hxn
      exact Real.Gamma_strictMonoOn_Ici.monotoneOn (Set.mem_Ici.mpr hx2')
        (Set.mem_Ici.mpr hn2) hxn
  have hΓn_fact : Real.Gamma (n : ℝ) = ((n - 1).factorial : ℝ) := by
    have hcast : (n : ℝ) = ((n - 1 : ℕ) : ℝ) + 1 := by
      rw [Nat.cast_sub hn1, Nat.cast_one]; ring
    rw [hcast, Real.Gamma_nat_eq_factorial]
  have hfact_le : ((n - 1).factorial : ℝ) ≤ ((n ^ n : ℕ) : ℝ) := by
    have h1 : (n - 1).factorial ≤ n.factorial := Nat.factorial_le (Nat.sub_le n 1)
    have h2 : n.factorial ≤ n ^ n := Nat.factorial_le_pow n
    exact_mod_cast le_trans h1 h2
  have hpow : ((n ^ n : ℕ) : ℝ) ≤ (x + 1) ^ (x + 1) := by
    push_cast
    rw [← Real.rpow_natCast (n : ℝ) n]
    calc (n : ℝ) ^ ((n : ℕ) : ℝ)
        ≤ (x + 1) ^ ((n : ℕ) : ℝ) := Real.rpow_le_rpow (by positivity) hnx1 (by positivity)
      _ ≤ (x + 1) ^ (x + 1) := Real.rpow_le_rpow_of_exponent_le (by linarith) hnx1
  calc Real.Gamma x ≤ Real.Gamma (n : ℝ) := hΓxn
    _ = ((n - 1).factorial : ℝ) := hΓn_fact
    _ ≤ ((n ^ n : ℕ) : ℝ) := hfact_le
    _ ≤ (x + 1) ^ (x + 1) := hpow

/-- **Real-Γ log growth (order 1).** `log Γ(x) ≤ (x+1)·log(x+1)` for `x ≥ 1`. -/
theorem log_Gamma_le {x : ℝ} (hx : 1 ≤ x) :
    Real.log (Real.Gamma x) ≤ (x + 1) * Real.log (x + 1) := by
  have hΓpos : 0 < Real.Gamma x := Real.Gamma_pos_of_pos (by linarith)
  calc Real.log (Real.Gamma x)
      ≤ Real.log ((x + 1) ^ (x + 1)) := Real.log_le_log hΓpos (Gamma_le_rpow hx)
    _ = (x + 1) * Real.log (x + 1) := by rw [Real.log_rpow (by linarith : (0 : ℝ) < x + 1)]

/-- **Real-Γ log growth on `[½,∞)`.** `log Γ(x) ≤ (x+1)·log(x+1) + 1` for `x ≥ ½` — extends
    `log_Gamma_le` over the `[½,1)` dip (where `Γ(x) ≤ Γ(½) = √π ≤ 2`, so `log Γ(x) ≤ log 2 ≤ 1`).
    Covers the even-`χ` `gammaFactor` argument `Re s/2 ≥ ½`. -/
theorem log_Gamma_le_half {x : ℝ} (hx : 1 / 2 ≤ x) :
    Real.log (Real.Gamma x) ≤ (x + 1) * Real.log (x + 1) + 1 := by
  have hbase : 0 ≤ (x + 1) * Real.log (x + 1) :=
    mul_nonneg (by linarith) (Real.log_nonneg (by linarith))
  by_cases hx1 : 1 ≤ x
  · linarith [log_Gamma_le hx1]
  · push_neg at hx1
    have hxmem : x ∈ Set.Ioc (0 : ℝ) 1 := ⟨by linarith, le_of_lt hx1⟩
    have hhalfmem : (1 / 2 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
    have hΓle : Real.Gamma x ≤ Real.Gamma (1 / 2) :=
      Real.Gamma_strictAntiOn_Ioc.antitoneOn hhalfmem hxmem hx
    have hΓpos : 0 < Real.Gamma x := Real.Gamma_pos_of_pos (by linarith)
    have hsqrt2 : Real.sqrt Real.pi ≤ 2 := by
      have h4 : Real.pi ≤ 4 := Real.pi_le_four
      calc Real.sqrt Real.pi ≤ Real.sqrt 4 := Real.sqrt_le_sqrt h4
        _ = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have hΓ2 : Real.Gamma x ≤ 2 := le_trans hΓle (by rw [Real.Gamma_one_half_eq]; exact hsqrt2)
    have hlog2 : Real.log 2 ≤ 1 := le_of_lt (lt_trans Real.log_two_lt_d9 (by norm_num))
    have hlGx : Real.log (Real.Gamma x) ≤ Real.log 2 := Real.log_le_log hΓpos hΓ2
    linarith

/-- **`Gammaℝ` log-bound.** For `Re s' ≥ 1`, `log ‖Gammaℝ s'‖ ≤ (Re s'/2 + 1)·log(Re s'/2 + 1) + 1`.
    Combines `norm_Gammaℝ_le` (modulus) with `log_Gamma_le_half` (growth); the `π^{−Re s'/2}` factor
    only helps (its log is `≤ 0`). -/
theorem log_norm_Gammaℝ_le {s' : ℂ} (hs' : 1 ≤ s'.re) :
    Real.log ‖Complex.Gammaℝ s'‖ ≤ (s'.re / 2 + 1) * Real.log (s'.re / 2 + 1) + 1 := by
  have hpos : (0 : ℝ) < s'.re := by linarith
  have hGpos : 0 < ‖Complex.Gammaℝ s'‖ :=
    norm_pos_iff.mpr (Complex.Gammaℝ_ne_zero_of_re_pos hpos)
  have hbound := norm_Gammaℝ_le hpos
  have hΓpos : 0 < Real.Gamma (s'.re / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hπpow_pos : 0 < Real.pi ^ (-s'.re / 2) := Real.rpow_pos_of_pos Real.pi_pos _
  calc Real.log ‖Complex.Gammaℝ s'‖
      ≤ Real.log (Real.pi ^ (-s'.re / 2) * Real.Gamma (s'.re / 2)) := Real.log_le_log hGpos hbound
    _ = (-s'.re / 2) * Real.log Real.pi + Real.log (Real.Gamma (s'.re / 2)) := by
        rw [Real.log_mul (ne_of_gt hπpow_pos) (ne_of_gt hΓpos), Real.log_rpow Real.pi_pos]
    _ ≤ Real.log (Real.Gamma (s'.re / 2)) := by
        have h1 : -s'.re / 2 ≤ 0 := by linarith
        have h2 : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
        nlinarith
    _ ≤ (s'.re / 2 + 1) * Real.log (s'.re / 2 + 1) + 1 := log_Gamma_le_half (by linarith)

/-- `log(ab+1) ≤ log(a+1) + log(b+1)` for `a, b ≥ 0` (since `ab+1 ≤ (a+1)(b+1)`). -/
theorem log_mul_add_one_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.log (a * b + 1) ≤ Real.log (a + 1) + Real.log (b + 1) := by
  have hle : a * b + 1 ≤ (a + 1) * (b + 1) := by nlinarith
  calc Real.log (a * b + 1) ≤ Real.log ((a + 1) * (b + 1)) := Real.log_le_log (by positivity) hle
    _ = Real.log (a + 1) + Real.log (b + 1) := Real.log_mul (by positivity) (by positivity)

/-- `log(a+1) ≤ M+1` when `log a ≤ M` and `M ≥ 0` (so `a+1 ≤ e·exp M = exp(M+1)`). -/
theorem log_add_one_le {a M : ℝ} (ha : 0 ≤ a) (hM : 0 ≤ M) (hMa : Real.log a ≤ M) :
    Real.log (a + 1) ≤ M + 1 := by
  have hexpM : 1 ≤ Real.exp M := Real.one_le_exp hM
  have haexp : a ≤ Real.exp M := by
    rcases eq_or_lt_of_le ha with h | h
    · rw [← h]; linarith
    · exact (Real.log_le_iff_le_exp h).mp hMa
  have ha1 : a + 1 ≤ Real.exp (M + 1) := by
    rw [Real.exp_add]
    nlinarith [haexp, hexpM, Real.exp_one_gt_d9, Real.exp_pos M]
  calc Real.log (a + 1) ≤ Real.log (Real.exp (M + 1)) := Real.log_le_log (by linarith) ha1
    _ = M + 1 := Real.log_exp _

/-- **`Γ(x) ≤ 1/x` on `(0,1]`.** From `Γ(x) = Γ(x+1)/x` and `Γ(x+1) ≤ 1` on `[1,2]` (convexity below
    the chord `y=1`). Controls the `gammaFactor` argument on `[¼,1]` (the `[½,1]` strip half). -/
theorem Gamma_le_inv {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) : Real.Gamma x ≤ 1 / x := by
  have hΓ1 : Real.Gamma (x + 1) ≤ 1 := by
    have h1 : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := by norm_num
    have h2 : (2 : ℝ) ∈ Set.Ioi (0 : ℝ) := by norm_num
    have hconv := Real.convexOn_Gamma.2 h1 h2
      (show (0 : ℝ) ≤ 2 - (x + 1) by linarith) (show (0 : ℝ) ≤ (x + 1) - 1 by linarith)
      (show (2 - (x + 1)) + ((x + 1) - 1) = 1 by ring)
    have hΓ2 : Real.Gamma (2 : ℝ) = 1 := by
      rw [show (2 : ℝ) = ((1 : ℕ) : ℝ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]; simp
    rw [Real.Gamma_one, hΓ2] at hconv
    simp only [smul_eq_mul] at hconv
    have harg : (2 - (x + 1)) * 1 + ((x + 1) - 1) * 2 = x + 1 := by ring
    rw [harg] at hconv; linarith
  rw [Real.Gamma_add_one (ne_of_gt hx0)] at hΓ1
  rw [le_div_iff₀ hx0, mul_comm]; exact hΓ1

end GammaBound

#print axioms GammaBound.Gamma_le_inv
#print axioms GammaBound.log_mul_add_one_le
#print axioms GammaBound.log_add_one_le
#print axioms GammaBound.norm_Gamma_le_Gamma_re
#print axioms GammaBound.norm_Gammaℝ_le
#print axioms GammaBound.log_Gamma_le
#print axioms GammaBound.log_Gamma_le_half
#print axioms GammaBound.log_norm_Gammaℝ_le
