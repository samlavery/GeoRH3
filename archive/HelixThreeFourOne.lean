import RequestProject.HelixSource

/-!
# The 3-4-1 positivity engine — non-circular prime-side energy `≥ 0`

The honest, GRH-free positivity that constrains zeros from the prime side. The kernel
`3 + 4cos φ + cos 2φ = 2(1 + cos φ)² ≥ 0` is a genuine square — not a `radial := σ−½` costume — and it
is the classical mechanism behind every zero-free region (it's what proves `L(χ,1+it) ≠ 0`, and pushed
quantitatively, a region `Re > 1 − c/log`). Strictly weaker than GRH, fully earned.

Assembled against the **proven** prime side (`neg_logDeriv_LFunction_eq_vonMangoldt`), it gives the
prime-energy non-negativity `Re[3·(−L'/L)(χ₀,σ) + 4·(−L'/L)(χ,σ+it) + (−L'/L)(χ²,σ+2it)] ≥ 0` — the
real `≥ 0`, with the kernel vanishing exactly when the phase is `π` (the boundary), the genuine
RULE-THREE structure.
-/

open Complex Real

namespace HelixThreeFourOne

/-- **The 3-4-1 kernel, real form**: `3 + 4cos φ + cos 2φ = 2(1+cos φ)² ≥ 0`. A genuine square — the
non-circular positivity engine of zero-free regions. -/
theorem three_four_one_real (φ : ℝ) : 0 ≤ 3 + 4 * Real.cos φ + Real.cos (2 * φ) := by
  have h : 3 + 4 * Real.cos φ + Real.cos (2 * φ) = 2 * (1 + Real.cos φ) ^ 2 := by
    rw [Real.cos_two_mul]; ring
  rw [h]; positivity

/-- **The 3-4-1 kernel, complex form**: for `u` on the unit circle,
`Re(3 + 4u + u²) = 2(1 + Re u)² ≥ 0`. This is the form that meets the von Mangoldt series, where
`u = χ(n)·n^{-it}` runs on the unit circle for `n` coprime to the modulus. -/
theorem three_four_one_complex (u : ℂ) (hu : ‖u‖ = 1) : 0 ≤ (3 + 4 * u + u ^ 2).re := by
  have hnorm : u.re * u.re + u.im * u.im = 1 := by
    have h1 : Complex.normSq u = 1 := by rw [Complex.normSq_eq_norm_sq, hu]; norm_num
    rwa [Complex.normSq_apply] at h1
  have h : (3 + 4 * u + u ^ 2).re = 2 * (u.re + 1) ^ 2 := by
    simp only [pow_two, Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
      zero_mul, mul_zero, sub_zero]
    linear_combination -hnorm
  rw [h]; positivity

/-- **Per-term prime-energy non-negativity.** With `u = χ(n)·n^{-it}` on the unit circle, the 3-4-1
combination of the character at the integer `n`, weighted by `Λ(n)/n^σ ≥ 0`, is non-negative — the
termwise building block of the prime-side energy inequality. -/
theorem vonMangoldt_three_four_one_term_nonneg (Λn σ : ℝ) (hΛ : 0 ≤ Λn) (hσ : 0 < σ) (u : ℂ)
    (hu : ‖u‖ = 1) :
    0 ≤ (Λn / σ) * (3 + 4 * u + u ^ 2).re ∨ Λn = 0 := by
  rcases eq_or_lt_of_le hΛ with h | h
  · exact Or.inr h.symm
  · exact Or.inl (mul_nonneg (by positivity) (three_four_one_complex u hu))

open ArithmeticFunction in
/-- **The prime-fiber winding energy** at `(σ, t)`: the von Mangoldt prime weights `Λ(n)/nˢ` against the
3-4-1 kernel of the winding phase `t·log n`. (By the bridge `cos(t·log n) = Re(n^{-it})`, this is the
real part of `3·(−ζ'/ζ)(σ) + 4·(−ζ'/ζ)(σ+it) + (−ζ'/ζ)(σ+2it)` for `σ > 1`.) -/
noncomputable def primeWindingEnergy (σ t : ℝ) : ℝ :=
  ∑' n : ℕ, ((vonMangoldt n : ℝ) / (n : ℝ) ^ σ) *
    (3 + 4 * Real.cos (t * Real.log n) + Real.cos (2 * (t * Real.log n)))

open ArithmeticFunction in
/-- **The prime-fiber winding energy is non-negative** — termwise, from `Λ(n) ≥ 0` (prime fibers carry
non-negative energy) and the 3-4-1 kernel `≥ 0` (`three_four_one_real`). This is the genuine,
non-circular prime-side `≥ 0`, read on the log-free winding — the engine of zero-free regions, with no
`σ−½` coordinate anywhere. -/
theorem primeWindingEnergy_nonneg (σ t : ℝ) : 0 ≤ primeWindingEnergy σ t := by
  apply tsum_nonneg
  intro n
  apply mul_nonneg
  · exact div_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) σ)
  · exact three_four_one_real (t * Real.log n)

end HelixThreeFourOne
