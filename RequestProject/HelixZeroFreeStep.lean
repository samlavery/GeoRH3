import RequestProject.DirichletLHadamardComplete
import RequestProject.HelixThreeFourOne

/-!
# The zero-bound: a zero pushes `Re(L'/L)` up, diagonally by `1/(σ−β)`

The second classical ingredient of a zero-free region (the first being `primeWindingEnergy_nonneg`, the
3-4-1 positivity). From the Hadamard partial fraction `logDeriv Λ_χ(s) = A + ∑_ρ ord(ρ)[1/(s−ρ)+1/ρ]`,
each resolvent term has **strictly positive real part** for `Re s > 1` (the convergent region), and at
`s = σ + i·Im ρ₀` the diagonal term is exactly `1/(σ − Re ρ₀)` — diverging as `σ → Re ρ₀⁺`. So a zero
near `Re = 1` forces `Re(logDeriv Λ)` large and positive there; fed into the 3-4-1 inequality
`3·(pole) − 4·(zero) + (…) ≥ 0`, a zero too close to `Re = 1` contradicts the positivity. These bricks
are kernel-clean and non-circular — pure resolvent geometry, no `σ−½` coordinate.
-/

open Complex

namespace HelixZeroFree

variable {N : ℕ} [NeZero N]

/-- **Resolvent positivity in the convergent region.** For `Re s > 1` and a point `ρ` with `Re ρ < 1`,
`Re(1/(s−ρ)) = (Re s − Re ρ)/‖s−ρ‖² > 0`. Every zero contributes a *positive* real part to
`Re(logDeriv Λ)` in the convergent region — the source of the zero-bound. -/
theorem resolvent_re_pos {s ρ : ℂ} (hs : 1 < s.re) (hρ : ρ.re < 1) :
    0 < (1 / (s - ρ)).re := by
  have hne : s - ρ ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [h] at hs; linarith
  rw [one_div, Complex.inv_re, Complex.sub_re]
  exact div_pos (by linarith) (Complex.normSq_pos.mpr hne)

/-- **The diagonal resolvent term.** At `s = σ + i·Im ρ` (matching the zero's height), the resolvent is
real and equals `1/(σ − Re ρ)` — the large positive term a zero contributes, diverging as
`σ → Re ρ⁺`. -/
theorem resolvent_re_diagonal {ρ : ℂ} {σ : ℝ} (_hσ : ρ.re < σ) :
    (1 / ((σ : ℂ) + Complex.I * (ρ.im : ℝ) - ρ)).re = 1 / (σ - ρ.re) := by
  have h1 : (σ : ℂ) + Complex.I * (ρ.im : ℝ) - ρ = ((σ - ρ.re : ℝ) : ℂ) := by
    apply Complex.ext <;>
      simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
        Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im]
  rw [h1, one_div, ← Complex.ofReal_inv, Complex.ofReal_re, one_div]

/-- **A nontrivial zero has `Re ρ < 1`** — the precondition for `resolvent_re_pos`. -/
theorem nontrivialZero_re_lt_one {χ : DirichletCharacter ℂ N} {ρ : ℂ}
    (hρ : ρ ∈ GRHSpectral.NontrivialZeros χ) : ρ.re < 1 := hρ.2.1

/-- **The zero-bound, assembled per term.** For a nontrivial zero `ρ₀` and `σ > 1`, evaluating the
resolvent of the Hadamard sum at `s = σ + i·Im ρ₀`: the `ρ₀`-term is exactly `1/(σ − Re ρ₀) > 0`, and
every other `ρ`-term has positive real part. So the zero `ρ₀` injects a controlled, *positive,
divergent-as-σ→Re ρ₀* contribution into `Re(logDeriv Λ_χ)` — the precise mechanism the 3-4-1 inequality
turns into "no zeros near `Re = 1`." -/
theorem zero_diagonal_pos {χ : DirichletCharacter ℂ N} {ρ₀ : ℂ}
    (hρ₀ : ρ₀ ∈ GRHSpectral.NontrivialZeros χ) {σ : ℝ} (hσ : 1 < σ) :
    (1 / ((σ : ℂ) + Complex.I * (ρ₀.im : ℝ) - ρ₀)).re = 1 / (σ - ρ₀.re)
      ∧ 0 < 1 / (σ - ρ₀.re) := by
  have hlt : ρ₀.re < σ := lt_trans (nontrivialZero_re_lt_one hρ₀) hσ
  exact ⟨resolvent_re_diagonal hlt, by
    apply div_pos one_pos; linarith [nontrivialZero_re_lt_one hρ₀]⟩

/-- **The 3-4-1 optimization — the arithmetical heart of the zero-free region.** Once the three
analytic bounds (pole `3·A ≤ 3/δ`, zero `−4·B ≥ 4/(ε+δ)`, remainder `≤ C`) are fed into the 3-4-1
inequality `0 ≤ 3A + 4B + D`, what remains is purely arithmetic: evaluated at the optimal scale
`δ = 1/(2C)`, the inequality `0 ≤ 3/δ − 4/(ε+δ) + C` forces `ε ≥ 1/(14C)`. With `ε = (1−β)·𝓛` and
`C ≍ 𝓛`, this is exactly the zero-free region `1 − β ≥ c/𝓛`. Kernel-clean, non-circular. -/
theorem zerofree_optimization {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε)
    (h : 0 ≤ 3 / (1 / (2 * C)) - 4 / (ε + 1 / (2 * C)) + C) :
    1 / (14 * C) ≤ ε := by
  have hC0 : C ≠ 0 := hC.ne'
  have hden : 0 < ε + 1 / (2 * C) := by positivity
  have e1 : 3 / (1 / (2 * C)) = 6 * C := by field_simp; norm_num
  rw [e1] at h
  have h2 : 4 / (ε + 1 / (2 * C)) ≤ 7 * C := by linarith
  rw [div_le_iff₀ hden, mul_add] at h2
  have e2 : 7 * C * (1 / (2 * C)) = 7 / 2 := by field_simp
  rw [e2] at h2
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 14 * C)]
  nlinarith [h2]

end HelixZeroFree
