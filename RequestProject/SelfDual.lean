import RequestProject.SpectralSide
import RequestProject.MobiusPath
import RequestProject.GrindF

open Complex

namespace SelfDual

/-! # The self-dual nature of the geometry and the spectral/harmonic side

**One involution governs both sides:** the duality `ρ ↦ 1 − ρ`.
* On the **geometric** (Möbius/winding) side it is circle **inversion** `w ↦ w⁻¹`.
* On the **spectral/harmonic** side it is the **functional-equation pairing** `ρ ↔ 1 − ρ`.

Its **self-dual axis** — the locus fixed by the duality, where the object equals its own dual — is
exactly the critical line `Re ρ = ½`. This is positive structure: proved outright, no zeros assumed,
no GRH. -/

/-- The duality involution on the spectral parameter (the functional-equation pairing). -/
def dual (ρ : ℂ) : ℂ := 1 - ρ

/-- **The duality is an involution.** `(1 − (1 − ρ)) = ρ`. -/
@[simp] theorem dual_dual (ρ : ℂ) : dual (dual ρ) = ρ := by simp [dual]

/-- **Geometric self-duality: the Möbius carries the duality as circle inversion.**
    `w(1 − ρ) = (w ρ)⁻¹` — the parameter duality `ρ ↦ 1−ρ` is winding inversion `w ↦ w⁻¹`. Proved
    from the FE reciprocal `w ρ · w(1−ρ) = 1`. -/
theorem w_dual (ρ : ℂ) (hρ : ρ ≠ 0) (h1 : (1 : ℂ) - ρ ≠ 0) :
    SpectralSide.w (1 - ρ) = (SpectralSide.w ρ)⁻¹ := by
  have hrec := SpectralSide.w_FE_reciprocal ρ hρ h1
  have hwρ : SpectralSide.w ρ ≠ 0 := by
    rintro h; rw [h, zero_mul] at hrec; exact one_ne_zero hrec.symm
  rw [inv_eq_one_div, eq_div_iff hwρ]
  linear_combination hrec

/-- **The self-dual axis is the critical line.** The winding sits on the unit circle — the locus
    fixed by inversion `w ↦ w⁻¹` (there `w⁻¹ = conj w`, so `w` is its own dual) — **exactly** when
    `Re ρ = ½`. The critical line is precisely where geometry equals its dual. -/
theorem selfDual_axis (ρ : ℂ) (hρ : ρ ≠ 0) :
    ‖SpectralSide.w ρ‖ = 1 ↔ ρ.re = 1 / 2 :=
  MobiusPath.w_norm_one_iff hρ

/-- **On the self-dual axis the winding equals its own dual.** At `Re ρ = ½`, `w(1−ρ) = (w ρ)⁻¹` and
    `‖w ρ‖ = 1`, so `(w ρ)⁻¹` is the unit-circle reflection of `w ρ` — the object coincides with its
    inverse-dual on the circle. The critical line is the fixed locus of the whole self-duality. -/
theorem dual_eq_inv_on_axis (ρ : ℂ) (hρ : ρ ≠ 0) (h1 : (1 : ℂ) - ρ ≠ 0) (hax : ρ.re = 1 / 2) :
    SpectralSide.w (1 - ρ) = (SpectralSide.w ρ)⁻¹ ∧ ‖SpectralSide.w ρ‖ = 1 :=
  ⟨w_dual ρ hρ h1, (selfDual_axis ρ hρ).mpr hax⟩

/-- **Self-dual nature, assembled — one theorem.** A single involution `ρ ↦ 1−ρ`:
    * it is an involution (`dual_dual`);
    * the geometry carries it as inversion `w(1−ρ) = (w ρ)⁻¹` (`w_dual`);
    * its self-dual axis — winding on the unit circle, fixed by inversion — is **exactly** the
      critical line `Re ρ = ½` (`selfDual_axis`).

    The geometry (Möbius/winding inversion) and the spectral/harmonic side (the FE pairing `ρ ↔ 1−ρ`)
    are the same self-duality, and the line `Re = ½` is its fixed axis — positive, proved, with no
    reference to any zero. -/
theorem self_dual_nature (ρ : ℂ) (hρ : ρ ≠ 0) (h1 : (1 : ℂ) - ρ ≠ 0) :
    dual (dual ρ) = ρ
      ∧ SpectralSide.w (1 - ρ) = (SpectralSide.w ρ)⁻¹
      ∧ (‖SpectralSide.w ρ‖ = 1 ↔ ρ.re = 1 / 2) :=
  ⟨dual_dual ρ, w_dual ρ hρ h1, selfDual_axis ρ hρ⟩

end SelfDual
