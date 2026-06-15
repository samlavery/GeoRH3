import Mathlib
import RequestProject.SpectralIdentification
import RequestProject.HelixRoundTrip
import RequestProject.HelixEmpiricalCores

/-!
# Wiring: the derived `½` ↔ on-line Li positivity, one chain

`HelixEmpiricalCores.liMap_unit_iff_half` (the derived half-unit: the Li/Möbius map
sits on the unit circle iff `Re ρ = ½`) is wired into the project's
`spectral_identification_complete`, giving a single equivalence:

  `HasSpectralIdentification σ γ  ⟺  σ = ½  ⟺  ‖moebius_helix σ γ‖ = 1`

and on that circle the paired-Li / projection-loss energy is `≥ 0`.
-/

open Complex

noncomputable section

namespace HalfUnitChain

/-- The Li/Möbius unit-circle condition is exactly `σ = ½`, via the derived
    half-unit core `HelixEmpiricalCores.liMap_unit_iff_half`. -/
theorem moebius_normSq_unit_iff_half (sigma gamma : ℝ) (hσ1 : 0 < sigma) :
    Complex.normSq (moebius_helix sigma gamma) = 1 ↔ sigma = 1 / 2 := by
  have hre : (⟨sigma, gamma⟩ : ℂ).re = sigma := rfl
  have hρ : (⟨sigma, gamma⟩ : ℂ) ≠ 0 := by
    intro h; rw [h] at hre; simp only [Complex.zero_re] at hre; linarith
  have key := HelixEmpiricalCores.liMap_unit_iff_half (⟨sigma, gamma⟩ : ℂ) hρ
  rw [hre] at key
  simpa [moebius_helix] using key

/-- **One chain**: spectral identification ⟺ the derived half-unit ⟺ Li-map on
    the unit circle. -/
theorem half_unit_TFAE (sigma gamma : ℝ) (hσ1 : 0 < sigma) (hσ2 : sigma < 1) :
    [HasSpectralIdentification sigma gamma,
     sigma = 1 / 2,
     Complex.normSq (moebius_helix sigma gamma) = 1].TFAE := by
  tfae_have 1 ↔ 2 := spectral_identification_complete sigma gamma hσ1 hσ2
  tfae_have 2 ↔ 3 := (moebius_normSq_unit_iff_half sigma gamma hσ1).symm
  tfae_finish

/-- On the Li circle (= the derived half-unit), the paired-Li / projection-loss
    energy is `≥ 0` for every `n` — the on-line positivity, reached *through* the
    derived `½`. -/
theorem half_unit_li_nonneg (sigma gamma : ℝ) (hσ1 : 0 < sigma) (hσ2 : sigma < 1)
    (h : Complex.normSq (moebius_helix sigma gamma) = 1) (n : ℕ) :
    0 ≤ (li_helix_term sigma gamma n).re + (li_helix_term (1 - sigma) (-gamma) n).re := by
  have hhalf : sigma = 1 / 2 := (moebius_normSq_unit_iff_half sigma gamma hσ1).mp h
  exact spectral_id_forces_nonneg sigma gamma
    ((spectral_identification_complete sigma gamma hσ1 hσ2).mpr hhalf) n

end HalfUnitChain

#print axioms HalfUnitChain.half_unit_TFAE
#print axioms HalfUnitChain.half_unit_li_nonneg
