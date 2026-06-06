import Mathlib
import RequestProject.ChiThreeLogDerivIdentity
import RequestProject.GRHSpectralCriterion

/-!
# The χ₃ functional equation: ½ is the *derived* center (the wiring step)

This file puts the "½ is the archimedean fixed point" claim on solid ground by connecting the
session's completion `completedLChi3` to Mathlib's standard `completedLFunction χ₃` and invoking
Mathlib's functional equation.

* `χ3_odd`, `χ3_isQuadratic`, `χ3_inv` (`χ₃⁻¹ = χ₃`), `χ3_primitive` (conductor `= 3`).
* `chi3_functional_equation` — Mathlib's FE instantiated:
  `completedLFunction χ₃ (1−s) = 3^(s−½) · rootNumber · completedLFunction χ₃ s`.
  Note the `s − ½` exponent: ½ sits *inside* the FE, structurally.
* `fe_center_half` — ½ is the unique fixed point of the reflection `s ↦ 1−s`.
* `completedLChi3_eq` — the wiring: our completion equals the standard one up to the nowhere‑zero
  conductor factor `3^((s+1)/2)`. Hence ½ is an **output** of the Euler‑Γ completion we proved, not
  an assumed input.
-/

open Complex DirichletCharacter

namespace ChiThree

/-- χ₃ is odd: `χ₃(−1) = −1` (it is the quadratic character mod 3, and `−1 ≡ 2`). -/
theorem χ3_odd : χ3.Odd := by
  show χ3 (-1) = -1
  rw [show (-1 : ZMod 3) = 2 from by decide, χ3_two]

/-- χ₃ is quadratic: its values lie in `{0, 1, −1}` (inherited from `quadraticChar`). -/
theorem χ3_isQuadratic : χ3.IsQuadratic := by
  intro a
  rcases quadraticChar_isQuadratic (ZMod 3) a with h | h | h <;>
    · unfold χ3; rw [MulChar.ringHomComp_apply, h]; simp

/-- χ₃ is its own inverse (real / quadratic character). -/
theorem χ3_inv : χ3⁻¹ = χ3 := MulChar.IsQuadratic.inv χ3_isQuadratic

/-- χ₃ is primitive: its conductor is the full modulus `3` (since `3` is prime and `χ₃ ≠ 1`). -/
theorem χ3_primitive : χ3.IsPrimitive := by
  rw [isPrimitive_def]
  have hdvd : χ3.conductor ∣ 3 := conductor_dvd_level χ3
  have hne1 : χ3.conductor ≠ 1 := fun h => χ3_ne_one ((eq_one_iff_conductor_eq_one).mpr h)
  rcases (show Nat.Prime 3 by norm_num).eq_one_or_self_of_dvd _ hdvd with h | h
  · exact absurd h hne1
  · exact h

/-- **The functional equation for χ₃** (Mathlib's `completedLFunction_one_sub`, instantiated). The
reflection is `s ↦ 1 − s` and the conductor balance `3^(s − ½)` vanishes (`= 1`) exactly at the
center. Using `χ₃⁻¹ = χ₃` this is a genuine self‑FE. -/
theorem chi3_functional_equation (s : ℂ) :
    completedLFunction χ3 (1 - s) =
      (3 : ℂ) ^ (s - 1 / 2) * χ3.rootNumber * completedLFunction χ3 s := by
  have h := χ3_primitive.completedLFunction_one_sub s
  rw [χ3_inv] at h
  simpa using h

/-- **½ is the unique fixed point** of the functional‑equation reflection `s ↦ 1 − s`. -/
theorem fe_center_half (s : ℂ) : 1 - s = s ↔ s = 1 / 2 := by
  constructor
  · intro h; linear_combination (-1 / 2 : ℂ) * h
  · intro h; rw [h]; ring

/-- **The wiring.** Our session's completion `completedLChi3` equals Mathlib's standard
`completedLFunction χ₃` up to the nowhere‑zero conductor factor `3^((s+1)/2)` (valid off the
trivial‑zero poles `s = −1, −3, …`). So the FE, entireness, and zero structure of the standard
object transfer to ours. -/
theorem completedLChi3_eq {s : ℂ} (hs : ∀ m : ℕ, (s + 1) / 2 ≠ -(m : ℂ)) :
    completedLChi3 s = (3 : ℂ) ^ ((s + 1) / 2) * completedLFunction χ3 s := by
  have hΓ : Complex.Gamma ((s + 1) / 2) ≠ 0 := Complex.Gamma_ne_zero hs
  have hπz2 : (Real.pi : ℂ) ^ ((s + 1) / 2) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast Real.pi_ne_zero)]; exact Complex.exp_ne_zero _
  have hL : LFunction χ3 s = completedLFunction χ3 s / χ3.gammaFactor s :=
    LFunction_eq_completed_div_gammaFactor χ3 s (Or.inr (by norm_num))
  have hgf : χ3.gammaFactor s = ((Real.pi : ℂ) ^ ((s + 1) / 2))⁻¹ * Complex.Gamma ((s + 1) / 2) := by
    rw [Odd.gammaFactor_def χ3_odd, Complex.Gammaℝ_def,
        show (-(s + 1) / 2 : ℂ) = -((s + 1) / 2) by ring, Complex.cpow_neg]
  have hcpow : (3 : ℂ) ^ ((s + 1) / 2)
      = (3 / Real.pi : ℂ) ^ ((s + 1) / 2) * (Real.pi : ℂ) ^ ((s + 1) / 2) := by
    rw [show (3 / Real.pi : ℂ) = ((3 / Real.pi : ℝ) : ℂ) by push_cast; ring,
        show (Real.pi : ℂ) = ((Real.pi : ℝ) : ℂ) by rfl,
        ← Complex.mul_cpow_ofReal_nonneg (by positivity) (Real.pi_pos.le)]
    norm_num [Real.pi_ne_zero]
  unfold completedLChi3
  rw [hL, hgf, hcpow]
  field_simp

/-- **Capstone: ½ is χ₃'s functional‑equation center, derived — not assumed.** The completed
L‑function satisfies the FE under `s ↦ 1 − s`; ½ is that reflection's unique fixed point; and our
session's completion equals the standard one up to the nowhere‑zero conductor factor. So ½ is the
archimedean signature of χ₃ (an output of the Euler‑Γ completion), and the open question is whether
the *zeros* sit on it — not where the center is. -/
theorem chi3_half_is_fe_center :
    (∀ s : ℂ, completedLFunction χ3 (1 - s)
        = (3 : ℂ) ^ (s - 1 / 2) * χ3.rootNumber * completedLFunction χ3 s) ∧
    (∀ s : ℂ, 1 - s = s ↔ s = 1 / 2) ∧
    (∀ s : ℂ, (∀ m : ℕ, (s + 1) / 2 ≠ -(m : ℂ)) →
        completedLChi3 s = (3 : ℂ) ^ ((s + 1) / 2) * completedLFunction χ3 s) :=
  ⟨chi3_functional_equation, fe_center_half, fun _ hs => completedLChi3_eq hs⟩

/-! ### The loss field maps to the zero values -/

/-- The loss field's singularities map to zero values: `completedLChi3` (whose `−logDeriv` is the
loss field `−Λ′/Λ`) vanishes exactly where `L(s,χ₃)` vanishes, for `Re s > −1` — the conductor power
and `Γ((s+1)/2)` never vanish there. -/
theorem completedLChi3_zero_iff {s : ℂ} (hs : (-1 : ℝ) < s.re) :
    completedLChi3 s = 0 ↔ LFunction χ3 s = 0 := by
  have hgam : 0 < ((s + 1) / 2).re := by
    rw [ArchGamma.div_two_re, Complex.add_re, Complex.one_re]; linarith
  have hc : (3 / Real.pi : ℂ) ^ ((s + 1) / 2) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero
        (div_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))]
    exact Complex.exp_ne_zero _
  have hG : Complex.Gamma ((s + 1) / 2) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m heq; rw [heq] at hgam
    simp only [Complex.neg_re, Complex.natCast_re] at hgam
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m; linarith
  unfold completedLChi3
  rw [mul_eq_zero, mul_eq_zero, or_iff_right hc, or_iff_right hG]

/-- **The loss field maps to the zero values.** The nontrivial zeros of `L(s,χ₃)` — the values the
loss field `−Λ′/Λ = −logDeriv(completedLChi3)` is built from — are *exactly* the strip points where
the completed object vanishes (i.e. where the loss field has its poles). -/
theorem nontrivialZeros_eq_completedLChi3_strip_zeros (ρ : ℂ) :
    ρ ∈ GRHSpectral.NontrivialZeros χ3 ↔
      (0 < ρ.re ∧ ρ.re < 1 ∧ completedLChi3 ρ = 0) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, (completedLChi3_zero_iff (by linarith)).mpr h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, (completedLChi3_zero_iff (by linarith)).mp h3⟩

end ChiThree

#print axioms ChiThree.completedLChi3_zero_iff
#print axioms ChiThree.nontrivialZeros_eq_completedLChi3_strip_zeros
#print axioms ChiThree.chi3_functional_equation
#print axioms ChiThree.completedLChi3_eq
#print axioms ChiThree.chi3_half_is_fe_center
