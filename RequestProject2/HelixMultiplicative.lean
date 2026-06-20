import RequestProject.HelixGaugeIdentity
import RequestProject.HelixLogFreeFTA

/-!
# Multiplicativity on the log-free helix — the FTA forcing, step 1

The structural feature that separates genuine `L`-functions (zeros conjecturally on the line) from
functions with a functional equation but no Euler product (Davenport–Heilbronn — zeros off the line,
even off the strip) is **FTA-multiplicativity**: multiplication of integers becomes addition of winding
angles, `Θ(mn) = Θ(m) + Θ(n)` (`HelixLogFree.windAngle_mul`, straight from `Nat.factorization_mul`),
so the winding is a completely multiplicative character (`HelixLogFree.wind_mul`).

**The FTA-multiplicativity is height-free — there is no strip.** `helixChar_mul` and `wind_mul` make
**no reference to `s` or any height**; the winding is a multiplicative character at *every* height, on
the critical line included. FTA on the helix never starts or stops — it always works. The helix is its
own continuation, so this structure is genuinely present where the zeros are.

What *is* height-bounded is only the **product representation** of it:

* `helixChar_mul` — the helix character `Ψ(n) = χ(n)·wind(n)` is completely multiplicative
  (multiplication → multiplication on the helix, from `Θ`'s additivity). **Height-free.**
* `helixSource_eq_eulerProduct` — for `Re s > 1`, the helix source (a sum over **all integers**) equals
  the gauge times a **product over primes** `∏_p (1 − χ(p)p^{-s})⁻¹` — unique factorization made
  analytic. The *identity* is bounded to `Re s > 1` only because the **product converges** there; the
  underlying multiplicativity it expresses is everywhere.
* `helix_no_zero_re_ge_one` — `L ≠ 0` for `Re s ≥ 1`. This is the *convergence-bounded shadow* of the
  multiplicativity: a no-zeros statement you can read off the product **where it converges**. (DH lacks
  even this — no Euler product → zeros in `Re s > 1`.) But it is NOT the helix's FTA power; it stops at
  `Re = 1` only because the *product representation* does, not because the FTA does.

**The open content, stated right:** force the cancellation onto the center using the **everywhere**
multiplicativity acting *on the line itself* — where the product representation diverges but the
multiplicative structure persists (the helix continues itself there). That the product tool breaks on
the line while the structure does not is exactly why this is hard and why it is the genuine GRH step —
log-free FTA on the line, not a bounded Euler-product convergence.
-/

open Complex HelixLogFree

namespace HelixMult

variable {N : ℕ} [NeZero N]

/-- The **helix character** `Ψ(n) = χ(n)·wind(n)` — the Dirichlet character twisted by the log-free
    FTA winding. -/
noncomputable def helixChar (χ : DirichletCharacter ℂ N) (θ : ℕ → ℝ) (n : ℕ) : ℂ :=
  χ (n : ZMod N) * (wind θ n : ℂ)

/-- **Multiplication → multiplication on the helix.** `Ψ(mn) = Ψ(m)·Ψ(n)` for `m,n ≠ 0`: the character
    is multiplicative and the winding angle is *additive* (`Θ(mn) = Θ(m)+Θ(n)`, `windAngle_mul`, FTA),
    so the winding multiplies. The helix character is completely multiplicative — the geometric form of
    unique factorization. -/
theorem helixChar_mul (χ : DirichletCharacter ℂ N) (θ : ℕ → ℝ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    helixChar χ θ (m * n) = helixChar χ θ m * helixChar χ θ n := by
  rw [helixChar, helixChar, helixChar, Nat.cast_mul, map_mul, wind_mul θ hm hn, Circle.coe_mul]
  ring

/-- **The multiplicative identity `1` maps to the additive identity `0`.** The winding is a *monoid
    homomorphism* `(ℕ≥1, ×, 1) → (ℝ, +, 0)`: `windAngle_mul` sends `×` to `+`, and this sends the
    identity `1 ↦ 0` (the empty factorization). On the log-free helix the "do-nothing" element is `0`,
    not `1` — multiplication is genuinely *replaced by* addition, identity and all. -/
theorem windAngle_one (θ : ℕ → ℝ) : windAngle θ 1 = 0 := by
  simp [windAngle, Nat.factorization_one]

/-- The winding of the identity is the unit phasor `wind 1 = 1` (angle `0` on the circle): the `n=1`
    anchor `a(1)=1` sits at the additive identity. -/
theorem wind_one (θ : ℕ → ℝ) : (wind θ 1 : ℂ) = 1 := by
  simp [wind, windAngle, Nat.factorization_one]

/-- The helix character is a monoid homomorphism: with `helixChar_mul` (× → ·) this identity law
    `Ψ(1) = 1` makes `Ψ` completely multiplicative in the strict sense. The identity `1` is the lattice
    origin — the zero exponent vector under FTA `ℕ≥1 ≅ ⊕_p ℕ`. -/
theorem helixChar_one (χ : DirichletCharacter ℂ N) (θ : ℕ → ℝ) : helixChar χ θ 1 = 1 := by
  simp [helixChar]

/-- **The Euler product — sum over integers = product over primes.** The helix source (summed over
    **all** integers, `lfunction_eq_helixSum`) equals the gauge times the **prime** product
    `∏_p (1 − χ(p)p^{-s})⁻¹` for `Re s > 1`. This is the analytic face of `helixChar_mul` /
    `windAngle_mul`: complete multiplicativity factors the integer sum into a prime product — unique
    factorization, the structure Davenport–Heilbronn lacks. -/
theorem helixSource_eq_eulerProduct (χ : DirichletCharacter ℂ N) (C : ℝ) (hC : 0 < C)
    {s : ℂ} (hs : 1 < s.re) :
    HelixGauge.HelixSource χ C s
      = (C : ℂ) ^ (-s) * ∏' p : Nat.Primes, (1 - χ ↑↑p * (↑↑p : ℂ) ^ (-s))⁻¹ := by
  rw [HelixGauge.helixSource_eq_gauge_mul_L χ C hC hs, DirichletCharacter.LFunction_eq_LSeries χ hs,
      ← DirichletCharacter.LSeries_eulerProduct_tprod χ hs]

/-- **The convergence-bounded shadow: no zeros for `Re s ≥ 1`.** Where the Euler product *converges*
    (`Re s > 1`, plus the boundary `Re s = 1` by the prime number theorem) it is a product of nonzero
    factors, so `L` cannot vanish — a no-zeros statement read directly off the product representation.
    **This is the exact step Davenport–Heilbronn fails** (no Euler product → genuine zeros in `Re s > 1`).
    But note what this is NOT: it is not the helix's FTA power. The multiplicativity (`helixChar_mul`)
    holds at every height; this lemma stops at `Re = 1` only because the *product representation* stops
    converging there, not because the FTA does. The genuine forcing — the multiplicativity acting on the
    line, where the product diverges but the structure persists — is the open GRH content, not this. -/
theorem helix_no_zero_re_ge_one (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {s : ℂ} (hs : 1 ≤ s.re) :
    DirichletCharacter.LFunction χ s ≠ 0 :=
  DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hs

end HelixMult
