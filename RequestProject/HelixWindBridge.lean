import RequestProject.HelixLogFreeFTA
import RequestProject.HelixSource

/-!
# The bridge: log-free winding ⟷ `−L'/L`, on the proven prime side

RULE EIGHT's external dictionary, made concrete. The log-free geometric winding `HelixLogFree.wind`
is identified with `n^{it}` **only here**, at the bridge — `log` enters exclusively in this readout,
never in the geometry. With the bridge angle `θ p = γ·log p`, the winding becomes `wind n = n^{iγ}`
(`wind_glog_eq_cpow`), and the **winding-twisted von Mangoldt prime field equals `−L'/L` translated by
the winding parameter**:

  `∑_n χ(n)Λ(n)·wind(n)·n^{−s} = −L'/L(s − iγ)`   (`Re s > 1`).

This is genuinely non-circular: it is an *identity for every real `γ`*, established on the **proven**
prime/Euler side (`neg_logDeriv_LFunction_eq_vonMangoldt`), assuming nothing about where the zeros sit.
It realizes "winding parameter = spectral (imaginary) coordinate of the `L`-trace": a resonance of the
winded field at real `s = β` occurs exactly when `s − iγ = ρ` is a zero, i.e. `γ = −Im ρ` unwinds that
zero's height to the axis. The remaining gap (analytic continuation past `Re s > 1` to *see* the zeros
as resonances) is the explicit-formula wall — across the bridge, off the geometric critical path.
-/

open Complex ArithmeticFunction

namespace HelixWindBridge

variable {N : ℕ} [NeZero N]

/-- **`log` is FTA-additive over the prime factorization** — the fact that makes the bridge angle
`θ p = γ·log p` reproduce `windAngle = γ·log n`: `log n = ∑_{pᵉ ‖ n} e·log p`. -/
theorem real_log_eq_factorization_sum {n : ℕ} (hn : n ≠ 0) :
    Real.log n = n.factorization.sum (fun p e => (e : ℝ) * Real.log p) := by
  conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn]
  rw [Finsupp.prod, Finsupp.sum, Nat.cast_prod, Real.log_prod]
  · apply Finset.sum_congr rfl
    intro p _
    rw [Nat.cast_pow, Real.log_pow]
  · intro p hp
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors
      (by rwa [Nat.support_factorization] at hp)).two_le
    have : (0 : ℝ) < (p : ℕ) ^ (n.factorization p) := by positivity
    positivity

/-- **The bridge angle realizes `γ·log`**: `windAngle (γ·log) n = γ·log n`. Log-free geometry on the
left; `log` only in the bridge assignment on the right. -/
theorem windAngle_glog (γ : ℝ) {n : ℕ} (hn : n ≠ 0) :
    HelixLogFree.windAngle (fun p => γ * Real.log p) n = γ * Real.log n := by
  rw [HelixLogFree.windAngle, real_log_eq_factorization_sum hn, Finsupp.mul_sum]
  apply Finsupp.sum_congr
  intro p _
  ring

/-- **The bridge** `wind (γ·log) n = n^{iγ}` (`n ≥ 1`). The single point where the geometric winding is
identified with the analytic `n^{it}`; `log` appears only here. -/
theorem wind_glog_eq_cpow (γ : ℝ) {n : ℕ} (hn : n ≠ 0) :
    ((HelixLogFree.wind (fun p => γ * Real.log p) n : Circle) : ℂ)
      = (n : ℂ) ^ ((γ : ℂ) * Complex.I) := by
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hnpos : (0 : ℝ) ≤ (n : ℝ) := by positivity
  rw [HelixLogFree.wind, Circle.coe_exp, windAngle_glog γ hn,
    Complex.cpow_def_of_ne_zero hnc]
  congr 1
  have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [show (n : ℂ) = ((n : ℝ) : ℂ) from by push_cast; ring]
    exact (Complex.ofReal_log hnpos).symm
  rw [hlog]
  push_cast
  ring

/-- **The winding-twisted von Mangoldt prime field = `−L'/L` shifted by the winding parameter.** For
`Re s > 1`, the geometric winding twist of the prime field equals `−L'/L(s − iγ)`. Established on the
**proven** prime side; an identity for every real `γ`, with no hypothesis on the zeros. -/
theorem windedVonMangoldt_eq_neg_logDeriv_shift (χ : DirichletCharacter ℂ N) (γ : ℝ) {s : ℂ}
    (hs : 1 < s.re) :
    LSeries (fun n => (χ ↑n * (vonMangoldt n : ℂ)) *
        ((HelixLogFree.wind (fun p => γ * Real.log p) n : Circle) : ℂ)) s
      = -logDeriv (DirichletCharacter.LFunction χ) (s - (γ : ℂ) * Complex.I) := by
  have hshift : (s - (γ : ℂ) * Complex.I).re = s.re := by
    simp [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im]
  rw [HelixSource.neg_logDeriv_LFunction_eq_vonMangoldt χ (by rw [hshift]; exact hs)]
  unfold LSeries
  apply tsum_congr
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term]
  · have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, Pi.mul_apply,
      wind_glog_eq_cpow γ hn, Complex.cpow_sub _ _ hnc]
    field_simp

end HelixWindBridge
