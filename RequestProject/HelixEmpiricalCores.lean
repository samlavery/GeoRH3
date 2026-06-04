import Mathlib

/-!
# Lean cores of the empirical helix computations

Kernel-verified, axiom-clean (`[propext, Classical.choice, Quot.sound]`) algebraic
cores of three numerical experiments, all pivoting on the derived half-unit
(`HelixHalfUnit.helix_forces_half`):

* **`li_chi3_deep.py`** (`λ_n(χ₃) ≥ 0` to n=40) →
  `li_energy_eq_sq_of_unit`, `li_energy_nonneg`, `liMap_unit_iff_half`.
  The paired Li / projection-loss energy is a **sum of squares on the unit circle**,
  and the circle `|1−1/ρ| = 1` is exactly `Re ρ = ½` — the same half-unit the scaling
  forces. This is "no negative projection-loss energy."

* **`helix_winding.c`** (the χ₃ winding rides √x) →
  `helix_phasor_on_circle`: the winding phasor `e^{i·(π/3)·log p}` has modulus 1,
  i.e. the projection lands ON the circle (no radial leak).

* **`gamma_winding.c`** (the √3, `log L(1,χ₃)`) →
  `eisenstein_principal_channel` (`ω+ω̄ = 1`), `eisenstein_chi3_channel` (`ω−ω̄ = i√3`),
  `eisenstein_chi3_modulus` (`|ω−ω̄| = √3`): the μ₆/Eisenstein two-channel split.
-/

open Complex

noncomputable section

namespace HelixEmpiricalCores

-- ═══ li_chi3_deep.py : projection-loss (Li) energy is a square at the midpoint ═══

/-- `normSq(1 − wⁿ) = 2(1 − Re wⁿ)` on the unit circle — the paired Li / projection-loss
    energy `λ_n` is a sum of squares. -/
theorem li_energy_eq_sq_of_unit (w : ℂ) (hw : Complex.normSq w = 1) (n : ℕ) :
    Complex.normSq (1 - w ^ n) = 2 * (1 - (w ^ n).re) := by
  have h1 : Complex.normSq (w ^ n) = 1 := by rw [map_pow, hw, one_pow]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re, Complex.sub_im,
             Complex.one_im, zero_sub] at h1 ⊢
  nlinarith [h1]

/-- The projection-loss energy is `≥ 0` on the circle (no negative loss). -/
theorem li_energy_nonneg (w : ℂ) (hw : Complex.normSq w = 1) (n : ℕ) :
    0 ≤ 2 * (1 - (w ^ n).re) := by
  rw [← li_energy_eq_sq_of_unit w hw]; exact Complex.normSq_nonneg _

/-- The Li/Möbius map `w = 1 − 1/ρ` (the helix operation) is on the unit circle
    **iff** `Re ρ = ½` — the same half-unit forced by the scaling isometry. -/
theorem liMap_unit_iff_half (ρ : ℂ) (hρ : ρ ≠ 0) :
    Complex.normSq (1 - 1 / ρ) = 1 ↔ ρ.re = 1 / 2 := by
  have hns : Complex.normSq ρ ≠ 0 := by simpa [Complex.normSq_eq_zero] using hρ
  rw [show (1 : ℂ) - 1 / ρ = (ρ - 1) / ρ from by field_simp, map_div₀, div_eq_one_iff_eq hns]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re, Complex.sub_im,
             Complex.one_im, sub_zero]
  constructor <;> intro h <;> nlinarith [h]

-- ═══ helix_winding.c : the angular winding rides the unit circle ═══

/-- The helix winding phasor `exp(i·θ)` (real `θ = (π/3)·log p`) has modulus 1:
    the projection lands ON the circle — no radial leak. -/
theorem helix_phasor_on_circle (θ : ℝ) :
    ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := by
  rw [Complex.norm_exp]; simp

-- ═══ gamma_winding.c : the Eisenstein μ₆ channels (the √3) ═══

/-- The primitive 6th root `ω = exp(iπ/3) = ½ + (√3/2)i` (the Eisenstein unit). -/
noncomputable def eisensteinOmega : ℂ := ⟨1 / 2, Real.sqrt 3 / 2⟩

/-- Principal channel: `ω + ω̄ = 1` (reflection-even — the total count). -/
theorem eisenstein_principal_channel :
    eisensteinOmega + (starRingEnd ℂ) eisensteinOmega = 1 := by
  rw [Complex.ext_iff]
  refine ⟨?_, ?_⟩ <;>
    simp [eisensteinOmega, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im]
  norm_num

/-- χ₃ channel: `ω − ω̄ = i√3` (reflection-odd — the imaginary/χ₃ part). -/
theorem eisenstein_chi3_channel :
    eisensteinOmega - (starRingEnd ℂ) eisensteinOmega = (Real.sqrt 3 : ℂ) * Complex.I := by
  simp [eisensteinOmega, Complex.ext_iff, Complex.sub_re, Complex.sub_im, Complex.conj_re,
        Complex.conj_im, Complex.mul_re, Complex.mul_im]

/-- The χ₃-channel modulus is exactly `√3`. -/
theorem eisenstein_chi3_modulus :
    ‖eisensteinOmega - (starRingEnd ℂ) eisensteinOmega‖ = Real.sqrt 3 := by
  rw [eisenstein_chi3_channel, norm_mul, Complex.norm_I, mul_one]
  simp [abs_of_nonneg (Real.sqrt_nonneg 3)]

end HelixEmpiricalCores

#print axioms HelixEmpiricalCores.li_energy_nonneg
#print axioms HelixEmpiricalCores.liMap_unit_iff_half
#print axioms HelixEmpiricalCores.helix_phasor_on_circle
#print axioms HelixEmpiricalCores.eisenstein_chi3_modulus
