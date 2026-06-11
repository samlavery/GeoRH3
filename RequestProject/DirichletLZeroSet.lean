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

/-- **Character-agnostic FE zero-pairing.** For primitive `χ ≠ 1`, the functional equation
    `Λ_χ(1−s) = N^{s−½}·rootNumber(χ)·Λ_{χ⁻¹}(s)` reflects each nontrivial zero `ρ` of `L(·,χ)` onto a
    nontrivial zero `1−ρ` of `L(·,χ⁻¹)`. (Put `s = 1−ρ`: the left side is `Λ_χ(ρ) = 0`, the prefactor
    `N^{(1−ρ)−½}·rootNumber(χ)` is nonzero, so `Λ_{χ⁻¹}(1−ρ) = 0`; the reverse inclusion for the
    primitive `χ⁻¹ ≠ 1` then places `1−ρ` in its strip.) For **self-dual** `χ` (`χ⁻¹ = χ`, e.g. the
    real character χ₃) this is the same-character symmetry `ρ ↦ 1−ρ` — the general form of
    `chi3_completedLogDerivPole_one_sub`. Pure analytic input from Mathlib's FE; no GRH-strength. -/
theorem one_sub_mem_NontrivialZeros_inv {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hχp : χ.IsPrimitive) {ρ : ℂ} (hρ : ρ ∈ GRHSpectral.NontrivialZeros χ) :
    (1 - ρ) ∈ GRHSpectral.NontrivialZeros χ⁻¹ := by
  have hz : DirichletCharacter.completedLFunction χ ρ = 0 := completedLFunction_eq_zero_of_mem hρ
  have hFE := hχp.completedLFunction_one_sub (1 - ρ)
  rw [show (1 - (1 - ρ)) = ρ from by ring, hz] at hFE
  have hN_ne : ((N : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hpow_ne : (N : ℂ) ^ ((1 - ρ) - 1 / 2) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hN_ne]; exact Complex.exp_ne_zero _
  have hrn_ne : χ.rootNumber ≠ 0 := rootNumber_ne_zero hχ hχp
  have hLinv0 : DirichletCharacter.completedLFunction χ⁻¹ (1 - ρ) = 0 := by
    rcases mul_eq_zero.mp hFE.symm with h | h
    · exact absurd h (mul_ne_zero hpow_ne hrn_ne)
    · exact h
  exact completedLFunction_zero_mem_NontrivialZeros (inv_ne_one_of_ne_one hχ)
    (isPrimitive_inv hχp) hLinv0

/-- **Same-character FE pairing for self-dual `χ`.** When `χ⁻¹ = χ` (the real/quadratic characters),
    the agnostic pairing `one_sub_mem_NontrivialZeros_inv` collapses to `ρ ↦ 1−ρ` within `χ` itself —
    exactly the hypothesis `fe_tends_towards_closure`/`fe_nonexpansion_closure` consume, now available
    for every self-dual primitive `χ ≠ 1`, not just χ₃. -/
theorem one_sub_mem_NontrivialZeros_of_selfDual {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hχp : χ.IsPrimitive) (hsd : χ⁻¹ = χ) {ρ : ℂ}
    (hρ : ρ ∈ GRHSpectral.NontrivialZeros χ) :
    (1 - ρ) ∈ GRHSpectral.NontrivialZeros χ := by
  have h := one_sub_mem_NontrivialZeros_inv hχ hχp hρ
  rwa [hsd] at h

end DirichletLHadamard
