import Mathlib
import RequestProject.SpectralSide

/-!
# The Möbius structure of the spectral side

`SpectralSide.w(ρ) = 1 − 1/ρ` is a Möbius map, and the functional equation
`w(ρ)·w(1−ρ) = 1` is the Möbius **reciprocal** `w ↦ 1/w` — the half-twist of the strip.
This file records the strip geometry on the spectral values:

* the FE is the reciprocal involution (`w_FE_is_reciprocal`);
* a reciprocal pair **straddles** the unit circle — moduli multiply to 1
  (`mobius_modulus_product`);
* the unit circle is the **core** (fixed locus): a value is on it iff its FE-mirror is
  (`mobius_circle_iff_mirror`).
-/

noncomputable section
open Complex

namespace SpectralMobius

/-- **The FE is the Möbius reciprocal (the half-twist).** `w(1−ρ) = w(ρ)⁻¹`. -/
theorem w_FE_is_reciprocal (ρ : ℂ) (hρ : ρ ≠ 0) (hρ1 : 1 - ρ ≠ 0) :
    SpectralSide.w (1 - ρ) = (SpectralSide.w ρ)⁻¹ := by
  have h := SpectralSide.w_FE_reciprocal ρ hρ hρ1
  have hwρ : SpectralSide.w ρ ≠ 0 := by
    intro h0; rw [h0, zero_mul] at h; exact one_ne_zero h.symm
  field_simp
  rw [mul_comm]; exact h

/-- **The reciprocal pair straddles the unit circle**: the moduli multiply to `1`.
    So unless both lie on the core, one is inside (`|w|<1`) and one outside (`|w|>1`). -/
theorem mobius_modulus_product (ρ : ℂ) (hρ : ρ ≠ 0) (hρ1 : 1 - ρ ≠ 0) :
    Complex.normSq (SpectralSide.w ρ) * Complex.normSq (SpectralSide.w (1 - ρ)) = 1 := by
  rw [← map_mul, SpectralSide.w_FE_reciprocal ρ hρ hρ1, map_one]

/-- **The unit circle is the Möbius core (fixed locus).** A spectral value is on the
    circle iff its FE-mirror is — they cross the core together. -/
theorem mobius_circle_iff_mirror (ρ : ℂ) (hρ : ρ ≠ 0) (hρ1 : 1 - ρ ≠ 0) :
    Complex.normSq (SpectralSide.w ρ) = 1 ↔
      Complex.normSq (SpectralSide.w (1 - ρ)) = 1 := by
  have h := mobius_modulus_product ρ hρ hρ1
  constructor <;> intro hc
  · rw [hc, one_mul] at h; exact h
  · rw [hc, mul_one] at h; exact h

/-- **The strip geometry, packaged**: the FE is the reciprocal, the pair straddles the
    circle, and the circle is the shared core. -/
theorem spectral_mobius_strip (ρ : ℂ) (hρ : ρ ≠ 0) (hρ1 : 1 - ρ ≠ 0) :
    (SpectralSide.w (1 - ρ) = (SpectralSide.w ρ)⁻¹) ∧
    (Complex.normSq (SpectralSide.w ρ) * Complex.normSq (SpectralSide.w (1 - ρ)) = 1) ∧
    (Complex.normSq (SpectralSide.w ρ) = 1 ↔
      Complex.normSq (SpectralSide.w (1 - ρ)) = 1) :=
  ⟨w_FE_is_reciprocal ρ hρ hρ1, mobius_modulus_product ρ hρ hρ1,
   mobius_circle_iff_mirror ρ hρ hρ1⟩

end SpectralMobius

#print axioms SpectralMobius.w_FE_is_reciprocal
#print axioms SpectralMobius.mobius_modulus_product
#print axioms SpectralMobius.mobius_circle_iff_mirror
