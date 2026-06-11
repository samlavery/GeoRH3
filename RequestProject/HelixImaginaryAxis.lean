import Mathlib
import RequestProject.HelixLogFreeFTA

/-!
# Producing the 2-D imaginary axis from the 3-D winding

Before any `Re ρ` discussion: the imaginary coordinate `iy` (the vertical phase the zeros live on) is
*not* imported analytically — it is **produced** from the log-free 3-D FTA winding.

The winding angle `Θ(n) = Σ_{p^e‖n} e·θ(p)` is completely additive (FTA, `windAngle_mul`), built with
**no logarithm**. The single bridge allowed by Rule Eight is the prime-angle assignment `θ(p) = t·log p`
— and under it, *the geometry becomes the analytic vertical phase*:

* `windAngle_log_bridge` :  `Θ(n) = t·log n`  (the additive winding angle, summed over the
  factorization, equals `t·log n` — `log` enters only through the prime-angle bridge);
* `wind_eq_cpow` :  `wind n = n^{i t}`  — the log-free winding **is** the analytic vertical phase
  `n^{it}`, with the height `t` (the imaginary coordinate) as the winding *rate*;
* `helixPt_eq_cpow` :  `helixPt n = n^{½ + i t}`  — the full helix point is the critical-line value:
  the `it` comes from the winding, the `½` from the `√n` area-law radius (`norm_helixPt`). The
  imaginary axis and the `½` baseline both fall out of the 3-D geometry; neither is assumed.

`log` appears in exactly one place (the bridge `θ(p) = t·log p`), never inside `Θ` or `wind`.
-/

open Complex HelixLogFree

namespace HelixImaginaryAxis

/-- **The winding-angle bridge.** The completely-additive FTA winding angle, evaluated with the
    bridge prime-angle `θ(p) = t·log p`, is `t·log n` — because `Σ_{p^e‖n} e·log p = log n`
    (the factorization identity). The geometry (`Θ`) is log-free; the `log` lives only in the bridge. -/
theorem windAngle_log_bridge (t : ℝ) (n : ℕ) (hn : n ≠ 0) :
    windAngle (fun p => t * Real.log p) n = t * Real.log n := by
  have hcast : (n : ℝ) = ∏ p ∈ n.factorization.support, (p : ℝ) ^ (n.factorization p) := by
    have hh := Nat.factorization_prod_pow_eq_self hn
    rw [Finsupp.prod] at hh
    have hh2 := congrArg (Nat.cast (R := ℝ)) hh
    rw [Nat.cast_prod] at hh2
    simp only [Nat.cast_pow] at hh2
    exact hh2.symm
  have hlog : Real.log n = ∑ p ∈ n.factorization.support, (n.factorization p : ℝ) * Real.log p := by
    rw [hcast, Real.log_prod]
    · exact Finset.sum_congr rfl (fun p _ => Real.log_pow _ _)
    · intro p hp
      have hp2 : 2 ≤ p :=
        (Nat.prime_of_mem_primeFactors (by rwa [Nat.support_factorization] at hp)).two_le
      positivity
  rw [windAngle, Finsupp.sum, hlog, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun p _ => by ring)

/-- **The 2-D imaginary axis, produced from the 3-D winding.** Under the bridge `θ(p) = t·log p`, the
    log-free FTA winding `wind n` *is* the analytic vertical phase `n^{i t}`. The height `t` — the
    imaginary coordinate where the zeros live — is exactly the winding rate. -/
theorem wind_eq_cpow (t : ℝ) (n : ℕ) (hn : n ≠ 0) :
    (wind (fun p => t * Real.log p) n : ℂ) = (n : ℂ) ^ (Complex.I * t) := by
  rw [wind, Circle.coe_exp, windAngle_log_bridge t n hn,
      Complex.cpow_def_of_ne_zero (by exact_mod_cast hn)]
  have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    rw [show (n : ℂ) = ((n : ℝ) : ℂ) from by push_cast; ring, ← Complex.ofReal_log (by positivity)]
  rw [hlog]; congr 1; push_cast; ring

/-- **The full helix point is the critical-line value `n^{½ + i t}`.** The `i t` (imaginary axis) comes
    from the winding (`wind_eq_cpow`); the `½` comes from the `√n` area-law radius. Both fall out of the
    3-D geometry — neither the vertical axis nor the `½` baseline is imported. -/
theorem helixPt_eq_cpow (t : ℝ) (n : ℕ) (hn : n ≠ 0) :
    helixPt (fun p => t * Real.log p) n = (n : ℂ) ^ ((1 / 2 : ℂ) + Complex.I * t) := by
  rw [helixPt, wind_eq_cpow t n hn]
  have hsqrt : (Real.sqrt n : ℂ) = (n : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]; norm_num
  rw [hsqrt, ← Complex.cpow_add _ _ (by exact_mod_cast hn)]

/-! ## Assembling `L` from the helix points -/

variable {N : ℕ} [NeZero N]

/-- **The general helix point** at radius `n^σ` (area law) and winding rate `t`: `helixPtGen σ t n =
    n^{σ + i t}`. The critical-line slice `σ = ½` is `helixPt` (radius `√n`). -/
noncomputable def helixPtGen (σ t : ℝ) (n : ℕ) : ℂ :=
  ((n : ℝ) ^ σ : ℝ) * (wind (fun p => t * Real.log p) n : ℂ)

theorem helixPtGen_eq_cpow (σ t : ℝ) (n : ℕ) (hn : n ≠ 0) :
    helixPtGen σ t n = (n : ℂ) ^ ((σ : ℂ) + Complex.I * t) := by
  rw [helixPtGen, wind_eq_cpow t n hn,
      show (((n : ℝ) ^ σ : ℝ) : ℂ) = (n : ℂ) ^ (σ : ℂ) from by
        rw [Complex.ofReal_cpow (by positivity)]; push_cast; ring,
      ← Complex.cpow_add _ _ (by exact_mod_cast hn)]

/-- The critical-line slice `σ = ½` is exactly the `√n` helix point. -/
theorem helixPtGen_half (t : ℝ) (n : ℕ) :
    helixPtGen (1 / 2) t n = helixPt (fun p => t * Real.log p) n := by
  rw [helixPtGen, helixPt, Real.sqrt_eq_rpow]

/-- **`L` assembled from the helix points.** For `Re s > 1`, the Dirichlet `L`-function is the sum of
    the character over the geometric helix points: `L(s,χ) = Σ_n χ(n) / helixPtGen(σ,t)(n)`, with each
    `helixPtGen(σ,t)(n) = n^{σ+it}` produced from the log-free winding (`helixPtGen_eq_cpow`). The
    vertical structure is the winding; the `L`-zeros are exactly where this helix-point sum (analytically
    continued from `Re s > 1` to the critical line `σ = ½`, where `helixPtGen = helixPt`) **cancels** —
    the winding cancellation events. -/
theorem lfunction_eq_helixSum (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.LFunction χ s = ∑' n : ℕ, χ (n : ZMod N) / helixPtGen s.re s.im n := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs, LSeries]
  refine tsum_congr (fun n => ?_)
  rcases eq_or_ne n 0 with hn | hn
  · subst hn
    have h0 : helixPtGen s.re s.im 0 = 0 := by
      rw [helixPtGen, Nat.cast_zero, Real.zero_rpow (by intro h; rw [h] at hs; norm_num at hs),
        Complex.ofReal_zero, zero_mul]
    rw [h0, div_zero, LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hn, helixPtGen_eq_cpow s.re s.im n hn,
        show (s.re : ℂ) + Complex.I * s.im = s from by
          rw [mul_comm Complex.I (s.im : ℂ)]; exact Complex.re_add_im s]

/-- **The projection 3D→2D, on `iy`.** The 2-D winding (the imaginary-axis phase) is the helix point
    with its `√n` radial divided off: `wind n = helixPt n / √n`. Since `‖helixPt n‖ = √n`
    (`HelixLogFree.norm_helixPt`), this *is* the projection onto the unit circle — it **keeps** the
    winding phase (the `iy` / height) and **drops** the radial (the `x`). -/
theorem wind_eq_helixPt_div_sqrt (t : ℝ) (n : ℕ) (hn : n ≠ 0) :
    (wind (fun p => t * Real.log p) n : ℂ)
      = helixPt (fun p => t * Real.log p) n / (Real.sqrt n : ℂ) := by
  rw [helixPt, mul_comm, mul_div_assoc, div_self (by
    simp only [ne_eq, Complex.ofReal_eq_zero]; positivity), mul_one]

/-- **The phasor form of `L` on the imaginary axis.** Each term is `fibre weight χ(n)` × `radial decay
    1/n^σ` × `winding phasor 1/wind(t)(n)`: `L` along `iy` is the `χ`-weighted sum of winding phasors,
    each of magnitude `1/n^σ` (at `σ=½`, `1/√n`) and rotating at its winding rate. The zeros are the
    heights `t` where these phasors **cancel** — the winding cancellation events. -/
theorem lfunction_eq_phasorSum (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.LFunction χ s
      = ∑' n : ℕ, χ (n : ZMod N) * (((n : ℝ) ^ s.re : ℝ) : ℂ)⁻¹
          * (wind (fun p => s.im * Real.log p) n : ℂ)⁻¹ := by
  rw [lfunction_eq_helixSum χ hs]
  refine tsum_congr (fun n => ?_)
  rw [helixPtGen, div_eq_mul_inv, mul_inv]; ring

end HelixImaginaryAxis
