import RequestProject.DirichletLZeroCount

/-!
# Zero set of the completed Dirichlet `L`: `Λ_χ(z) = 0 ↔ z ∈ NontrivialZeros χ`

For primitive `χ ≠ 1`, the entire completed `L` vanishes **exactly** on the critical-strip zeros:
- **forward** (`completedLFunction_eq_zero_of_mem`, already in `DirichletLHadamard`): a nontrivial
  zero is a zero of `Λ_χ`.
- **reverse** (here): a zero of `Λ_χ` is a nontrivial zero. Three regions:
  * `Re ≥ 1`: `Γ`-factor nonzero + Mathlib's `LFunction_ne_zero_of_one_le_re`.
  * `Re ≤ 0`: functional equation `Λ_χ(1−s) = N^{s−½}·rootNumber·Λ_{χ⁻¹}(s)` reflects onto `Re ≥ 1`
    for `χ⁻¹` (primitive, `≠ 1` by `conductor_inv`/`inv_eq_one`), with `rootNumber ≠ 0`.
  * `0 < Re < 1`: `Γ`-factor nonzero, so `Λ_χ = 0 ⟹ L = 0`, i.e. a nontrivial zero.

This is the `Λ_χ` analogue of `ZD.riemannXi_eq_zero_iff`. It feeds the order-matching-everywhere needed
for the entire zero-free quotient `Λ_χ / LProductMult χ` in the Hadamard factorization.
-/

open Complex

namespace DirichletLHadamard

variable {N : ℕ} [NeZero N]

/-- **`Λ_χ` is nonzero for `Re z ≥ 1`** (`Γ`-factor nonzero, `L` nonzero by Mathlib). -/
theorem completedLFunction_ne_zero_of_one_le_re {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    {z : ℂ} (hz : 1 ≤ z.re) : DirichletCharacter.completedLFunction χ z ≠ 0 := by
  intro hzero
  have hz0 : z ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hz; norm_num at hz
  have hrel := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ z (Or.inl hz0)
  rw [hzero, zero_div] at hrel
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) hz hrel

/-- **`χ⁻¹` is primitive** when `χ` is (`conductor_inv`). -/
theorem isPrimitive_inv {χ : DirichletCharacter ℂ N} (hχp : χ.IsPrimitive) : χ⁻¹.IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
  exact hχp

/-- **`χ⁻¹ ≠ 1`** when `χ ≠ 1`. -/
theorem inv_ne_one_of_ne_one {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) : χ⁻¹ ≠ 1 := by
  intro h; exact hχ (inv_eq_one.mp h)

/-- **The reverse inclusion**: a zero of `Λ_χ` is a nontrivial zero of `L`. -/
theorem completedLFunction_zero_mem_NontrivialZeros {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hχp : χ.IsPrimitive) {z : ℂ} (hz : DirichletCharacter.completedLFunction χ z = 0) :
    z ∈ GRHSpectral.NontrivialZeros χ := by
  -- Re z < 1.
  have hlt1 : z.re < 1 := by
    by_contra h
    push_neg at h
    exact completedLFunction_ne_zero_of_one_le_re hχ h hz
  -- Re z > 0 (via functional equation reflecting onto Re ≥ 1 for χ⁻¹).
  have hgt0 : 0 < z.re := by
    by_contra h
    push_neg at h
    set s : ℂ := 1 - z with hs_def
    have hsre : 1 ≤ s.re := by
      rw [hs_def, Complex.sub_re, Complex.one_re]; linarith
    have hFE := hχp.completedLFunction_one_sub s
    rw [show (1 - s) = z from by rw [hs_def]; ring] at hFE
    rw [hz] at hFE
    -- 0 = N^(s-1/2) * rootNumber χ * Λ_{χ⁻¹}(s); all three factors are nonzero.
    have hN_ne : ((N : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    have hpow_ne : (N : ℂ) ^ (s - 1 / 2) ≠ 0 := by
      rw [Complex.cpow_def_of_ne_zero hN_ne]; exact Complex.exp_ne_zero _
    have hrn_ne : χ.rootNumber ≠ 0 := rootNumber_ne_zero hχ hχp
    have hinv_ne : DirichletCharacter.completedLFunction χ⁻¹ s ≠ 0 :=
      completedLFunction_ne_zero_of_one_le_re (inv_ne_one_of_ne_one hχ) hsre
    exact absurd hFE.symm (mul_ne_zero (mul_ne_zero hpow_ne hrn_ne) hinv_ne)
  -- L χ z = 0.
  have hLzero : DirichletCharacter.LFunction χ z = 0 := by
    have hz0 : z ≠ 0 := by
      intro h; rw [h, Complex.zero_re] at hgt0; exact lt_irrefl 0 hgt0
    have hrel := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ z (Or.inl hz0)
    rw [hz, zero_div] at hrel
    exact hrel
  exact ⟨hgt0, hlt1, hLzero⟩

end DirichletLHadamard
