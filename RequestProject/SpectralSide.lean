import Mathlib
import RequestProject.HelixEmpiricalCores
import RequestProject.VonMangoldtEFStandalone

/-!
# The spectral side: the Möbius operator whose unitarity is RH

Built on my own axiom-clean cores (`HelixEmpiricalCores`). This is the operator-side
companion to `HelixProjection` (the geometric side).

For a zero `ρ` the **Möbius spectral value** is `w(ρ) = 1 − 1/ρ` (the helix operation).
The diagonal operator `W = diag(w(ρ_k))` on a finite zero-set is:

* **unitary** ⟺ every `‖w(ρ_k)‖ = 1` ⟺ every `Re(ρ_k) = ½`  (`spectral_unitary_iff_RH`)
* its **Li trace** is `λ_n = Σ_ρ (1 − w(ρ)ⁿ) = tr(I − Wⁿ)`
* on the unit circle each mode's energy is a **square** `‖1 − wⁿ‖² = 2(1 − Re wⁿ) ≥ 0`
* the **functional equation** pairs spectral values reciprocally: `w(ρ)·w(1−ρ) = 1`

All unconditional. The remaining (open) input is that the *actual* zeros put `W` on the
circle — equivalently `W` unitary, equivalently RH.
-/

open Complex

noncomputable section

namespace SpectralSide

/-- The Möbius/Li spectral value of a zero `ρ` — the helix operation `w = 1 − 1/ρ`. -/
def w (ρ : ℂ) : ℂ := 1 - 1 / ρ

/-- Spectral value on the unit circle ⟺ the zero on the critical line. -/
theorem w_unit_iff_half (ρ : ℂ) (hρ : ρ ≠ 0) :
    Complex.normSq (w ρ) = 1 ↔ ρ.re = 1 / 2 := by
  unfold w; exact HelixEmpiricalCores.liMap_unit_iff_half ρ hρ

/-- **The Möbius spectral operator is unitary ⟺ RH** for the zero-set: every spectral
    value on the unit circle ⟺ every zero on the line. -/
theorem spectral_unitary_iff_RH (zeros : Finset ℂ) (h0 : ∀ ρ ∈ zeros, ρ ≠ 0) :
    (∀ ρ ∈ zeros, Complex.normSq (w ρ) = 1) ↔ (∀ ρ ∈ zeros, ρ.re = 1 / 2) :=
  ⟨fun h ρ hρ => (w_unit_iff_half ρ (h0 ρ hρ)).mp (h ρ hρ),
   fun h ρ hρ => (w_unit_iff_half ρ (h0 ρ hρ)).mpr (h ρ hρ)⟩

/-- The **Li trace** `λ_n = Σ_ρ (1 − w(ρ)ⁿ) = tr(I − Wⁿ)`. -/
def liTrace (zeros : Finset ℂ) (n : ℕ) : ℂ := ∑ ρ ∈ zeros, (1 - w ρ ^ n)

/-- On the unit circle each spectral mode's energy is a square: `‖1 − wⁿ‖² = 2(1 − Re wⁿ)`. -/
theorem spectral_energy_sq_of_unit (ρ : ℂ) (hρ : Complex.normSq (w ρ) = 1) (n : ℕ) :
    Complex.normSq (1 - w ρ ^ n) = 2 * (1 - (w ρ ^ n).re) :=
  HelixEmpiricalCores.li_energy_eq_sq_of_unit (w ρ) hρ n

/-- On the unit circle the spectral energy is `≥ 0` — no negative projection-loss energy. -/
theorem spectral_energy_nonneg_of_unit (ρ : ℂ) (hρ : Complex.normSq (w ρ) = 1) (n : ℕ) :
    0 ≤ 2 * (1 - (w ρ ^ n).re) :=
  HelixEmpiricalCores.li_energy_nonneg (w ρ) hρ n

/-- **The functional equation pairs spectral values as reciprocals**: `w(ρ)·w(1−ρ) = 1`. -/
theorem w_FE_reciprocal (ρ : ℂ) (hρ : ρ ≠ 0) (hρ1 : (1 : ℂ) - ρ ≠ 0) :
    w ρ * w (1 - ρ) = 1 := by
  unfold w; field_simp; ring

/-- **Spectral criterion for RH (unconditional).** Mathlib's `RiemannHypothesis`
    holds **iff** the Möbius operator is unitary on the nontrivial zeros — every
    `‖w(ρ)‖ = 1`. This replaces the sorried `rh_from_ef` route with a clean
    equivalence: RH is the unitarity of the helix spectral operator. -/
theorem riemannHypothesis_iff_spectral_unitary :
    RiemannHypothesis ↔
      (∀ ρ ∈ VMEFStandalone.NontrivialZeros, Complex.normSq (w ρ) = 1) := by
  rw [VMEFStandalone.RiemannHypothesis_iff_NontrivialZeros]
  refine ⟨fun h ρ hρ => ?_, fun h ρ hρ => ?_⟩
  · have hne : ρ ≠ 0 := by rintro rfl; exact absurd hρ.1 (by simp)
    exact (w_unit_iff_half ρ hne).mpr (h ρ hρ)
  · have hne : ρ ≠ 0 := by rintro rfl; exact absurd hρ.1 (by simp)
    exact (w_unit_iff_half ρ hne).mp (h ρ hρ)

end SpectralSide

#print axioms SpectralSide.spectral_unitary_iff_RH
#print axioms SpectralSide.spectral_energy_nonneg_of_unit
#print axioms SpectralSide.w_FE_reciprocal
