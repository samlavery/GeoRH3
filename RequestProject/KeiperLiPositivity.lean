import Mathlib
import RequestProject.XiProduct
import RequestProject.KeiperLiNonempty

/-!
# Keiper–Li coefficient λ₁: unconditional positivity from the strip

The Keiper–Li coefficients are `λ_n = Σ_ρ [1 − (1 − 1/ρ)ⁿ]`, summed over the
nontrivial zeros `ρ`. Li's theorem says `λ_n ≥ 0 for all n ⟺ RH`; the
**individual low coefficients are unconditional**.

This file proves the `n = 1` case completely and unconditionally:

  `λ₁ = Σ_ρ [1 − (1 − 1/ρ)] = Σ_ρ 1/ρ`,   and   `Re(1/ρ) = Re ρ / |ρ|² > 0`

because **every nontrivial zero has `Re ρ > 0`** (the critical strip). No RH is
used: the positivity is forced by the strip alone, not by the line.

* `li1Term_pos`    — per zero: `(1/ρ).re > 0` (the mechanism, unconditional).
* `li1_summable`   — `Σ_ρ (1/ρ).re` converges (majorised by `Σ 1/‖ρ‖²`,
                     which is `ZD.summable_inv_norm_sq_nontrivialZeros`).
* `lambda1_nonneg` — `λ₁ ≥ 0` unconditionally.
* `lambda1_pos`    — `λ₁ > 0` once a nontrivial zero exists.

The convergence uses `Re ρ < 1` (the other strip wall) to majorise the summand
by `1/‖ρ‖²`; the positivity uses `Re ρ > 0`. Both walls of the strip, no line.
-/

noncomputable section

open Complex

namespace ZD

/-- The `n = 1` Keiper–Li summand `(1/ρ).re = Re ρ / |ρ|²`. -/
def li1Term (ρ : ℂ) : ℝ := (1 / ρ).re

/-- **Per-zero `n = 1` Li positivity (unconditional).** Every nontrivial zero
    contributes a strictly positive amount `Re ρ / |ρ|² > 0` to `λ₁`, purely
    because `Re ρ > 0` (the critical strip) — no RH. -/
theorem li1Term_pos {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) : 0 < li1Term ρ := by
  have hre : 0 < ρ.re := hρ.1
  have hne : ρ ≠ 0 := by rintro rfl; simp at hre
  unfold li1Term
  rw [one_div, Complex.inv_re]
  exact div_pos hre (Complex.normSq_pos.mpr hne)

/-- The summand is bounded above by the summable majorant `1/‖ρ‖²`, using the
    *other* strip wall `Re ρ < 1`. -/
theorem li1Term_le {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) :
    li1Term ρ ≤ 1 / ‖ρ‖ ^ 2 := by
  have hre : 0 < ρ.re := hρ.1
  have hlt : ρ.re < 1 := hρ.2.1
  have hne : ρ ≠ 0 := by rintro rfl; simp at hre
  have hsq : ‖ρ‖ ^ 2 = Complex.normSq ρ := (Complex.normSq_eq_norm_sq ρ).symm
  unfold li1Term
  rw [one_div, Complex.inv_re, hsq,
    div_le_div_iff_of_pos_right (Complex.normSq_pos.mpr hne)]
  exact hlt.le

/-- **`λ₁` summability.** `Σ_ρ (1/ρ).re` converges, majorised termwise by
    `Σ_ρ 1/‖ρ‖²` (`ZD.summable_inv_norm_sq_nontrivialZeros`). -/
theorem li1_summable :
    Summable (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} => li1Term ρ.val) :=
  Summable.of_nonneg_of_le
    (fun ρ => (li1Term_pos ρ.property).le)
    (fun ρ => li1Term_le ρ.property)
    summable_inv_norm_sq_nontrivialZeros

/-- The first Keiper–Li coefficient `λ₁ = Σ_ρ (1/ρ).re = Σ_ρ Re ρ / |ρ|²`. -/
def lambda1 : ℝ := ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros}, li1Term ρ.val

/-- **`λ₁ ≥ 0`, unconditional.** A tsum of strictly-positive terms. -/
theorem lambda1_nonneg : 0 ≤ lambda1 :=
  tsum_nonneg (fun ρ => (li1Term_pos ρ.property).le)

/-- **`λ₁ > 0`, unconditional given a nontrivial zero exists.** Strict
    positivity of the first Li coefficient: one positive summand bounds the
    nonnegative tail from below. The only non-Mathlib hypothesis is that the
    zero set is nonempty — a classical fact, not RH. -/
theorem lambda1_pos (h : (NontrivialZeros).Nonempty) : 0 < lambda1 := by
  obtain ⟨ρ, hρ⟩ := h
  exact lt_of_lt_of_le (li1Term_pos hρ)
    (li1_summable.le_tsum ⟨ρ, hρ⟩ (fun j _ => (li1Term_pos j.property).le))

/-- **`λ₁ > 0`, fully unconditional.** The strip-forced per-zero positivity
    (`li1Term_pos`) summed over the zeros, with the residual nonemptiness
    hypothesis discharged by `nontrivialZeros_nonempty` (the classical, non-RH
    existence of a nontrivial zero, proved from the Hadamard factorization +
    functional equation). No `∀n`, no RH — the first Li coefficient is positive
    by the strip alone. -/
theorem lambda1_pos_unconditional : 0 < lambda1 :=
  lambda1_pos nontrivialZeros_nonempty

end ZD

end

#print axioms ZD.li1Term_pos
#print axioms ZD.li1_summable
#print axioms ZD.lambda1_nonneg
#print axioms ZD.lambda1_pos
#print axioms ZD.lambda1_pos_unconditional
