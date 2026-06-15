import RequestProject.DirichletLHadamardComplete

/-!
# Sharp growth of `LOverP χ` and the explicit Hadamard product factorization

Once the constancy `logDeriv (LOverP χ) ≡ A` is established (from the `log²` Nevanlinna growth), the
entire zero-free quotient is *explicitly* exponential:

  `LOverP χ z = LOverP χ 0 · exp(A·z)`.

This is strictly sharper than the `log²` mean-type bound used to prove it (not circular: the `log²`
bound stands on its own Nevanlinna proof; this is a downstream structural consequence). It yields:
- **linear** growth `‖LOverP χ z‖ ≤ exp(C‖z‖+D)`,
- hence the **single-`log`** (mean-type-1) growth, discharging
  `HadamardPartialFraction_of_LOverP_growth`,
- and the **explicit multiplicative Hadamard factorization**
  `completedLFunction χ z = exp(A·z+B) · LProductMult χ z`.
-/

open Complex

noncomputable section

namespace DirichletLHadamard

variable {N : ℕ} [NeZero N]

/-- **`LOverP χ` is explicitly exponential**: `LOverP χ z = LOverP χ 0 · exp(A·z)`. -/
theorem LOverP_eq_const_mul_exp {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) :
    ∃ A : ℂ, ∀ z : ℂ, LOverP χ z = LOverP χ 0 * Complex.exp (A * z) := by
  obtain ⟨A, hA⟩ := HadamardConst.logDeriv_const_of_logSqGrowth (LOverP_differentiable hχ hχp)
    (LOverP_ne_zero hχ hχp) (LOverP_growth_meanType hχ hχp)
  exact ⟨A, HadamardConst.eq_const_mul_exp_of_logDeriv_const (LOverP_differentiable hχ hχp)
    (LOverP_ne_zero hχ hχp) hA⟩

/-- **Linear growth bound** on `LOverP χ` — the sharpest form. -/
theorem LOverP_growth_linear {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) :
    ∃ C D : ℝ, ∀ z : ℂ, ‖LOverP χ z‖ ≤ Real.exp (C * ‖z‖ + D) := by
  obtain ⟨A, hAeq⟩ := LOverP_eq_const_mul_exp hχ hχp
  have h0_pos : 0 < ‖LOverP χ 0‖ := norm_pos_iff.mpr (LOverP_ne_zero hχ hχp 0)
  refine ⟨‖A‖, Real.log ‖LOverP χ 0‖, fun z => ?_⟩
  rw [hAeq z, norm_mul, Complex.norm_exp, Real.exp_add, Real.exp_log h0_pos,
    mul_comm (Real.exp (‖A‖ * ‖z‖)) ‖LOverP χ 0‖]
  apply mul_le_mul_of_nonneg_left _ h0_pos.le
  apply Real.exp_le_exp.mpr
  calc (A * z).re ≤ ‖A * z‖ := Complex.re_le_norm _
    _ = ‖A‖ * ‖z‖ := norm_mul _ _

/-- **Sharp (single-`log`, mean-type-1) growth bound** on `LOverP χ`, from the linear bound. -/
theorem LOverP_growth_meanType_sharp {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hχp : χ.IsPrimitive) :
    ∃ C D : ℝ, ∀ z : ℂ,
      ‖LOverP χ z‖ ≤ Real.exp (C * ‖z‖ * Real.log (‖z‖ + 2) + D) := by
  obtain ⟨C, D, hLin⟩ := LOverP_growth_linear hχ hχp
  refine ⟨max C 0, max C 0 + D, fun z => ?_⟩
  refine le_trans (hLin z) (Real.exp_le_exp.mpr ?_)
  set t := ‖z‖ with ht
  have ht_nn : 0 ≤ t := norm_nonneg _
  have hC' : 0 ≤ max C 0 := le_max_right _ _
  have hCle : C ≤ max C 0 := le_max_left _ _
  have key : t ≤ t * Real.log (t + 2) + 1 := by
    rcases le_or_gt 1 (Real.log (t + 2)) with h | h
    · have : t * 1 ≤ t * Real.log (t + 2) := mul_le_mul_of_nonneg_left h ht_nn
      linarith
    · have h_lt : t + 2 < Real.exp 1 := by
        have hmono := Real.exp_lt_exp.mpr h
        rwa [Real.exp_log (by linarith)] at hmono
      have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
      have hlogpos : 0 ≤ t * Real.log (t + 2) :=
        mul_nonneg ht_nn (Real.log_nonneg (by linarith))
      linarith
  have h1 : C * t ≤ max C 0 * t := mul_le_mul_of_nonneg_right hCle ht_nn
  have h2 : max C 0 * t ≤ max C 0 * (t * Real.log (t + 2) + 1) :=
    mul_le_mul_of_nonneg_left key hC'
  have hassoc : max C 0 * t * Real.log (t + 2) = max C 0 * (t * Real.log (t + 2)) := by ring
  nlinarith [h1, h2, hassoc]

/-- **Hadamard partial fraction via the sharp single-`log` bound** — discharges the mean-type-1
conditional `HadamardPartialFraction_of_LOverP_growth`. (Same identity as `hadamardPartialFraction`,
now obtained through the sharper growth.) -/
theorem hadamardPartialFraction_sharp {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hχp : χ.IsPrimitive) : HadamardPartialFraction χ :=
  HadamardPartialFraction_of_LOverP_growth hχ hχp (LOverP_growth_meanType_sharp hχ hχp)

/-- **Explicit multiplicative Hadamard factorization** of the completed Dirichlet `L`:
`completedLFunction χ z = exp(A·z + B) · LProductMult χ z` for all `z`. -/
theorem completedLFunction_eq_exp_mul_LProductMult {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hχp : χ.IsPrimitive) :
    ∃ A B : ℂ, ∀ z : ℂ,
      DirichletCharacter.completedLFunction χ z = Complex.exp (A * z + B) * LProductMult χ z := by
  obtain ⟨A, hA⟩ := LOverP_eq_const_mul_exp hχ hχp
  have hc_ne : LOverP χ 0 ≠ 0 := LOverP_ne_zero hχ hχp 0
  refine ⟨A, Complex.log (LOverP χ 0), fun z => ?_⟩
  have hfact : DirichletCharacter.completedLFunction χ z = LOverP χ z * LProductMult χ z := by
    by_cases hz : z ∈ GRHSpectral.NontrivialZeros χ
    · have hΛ0 : DirichletCharacter.completedLFunction χ z = 0 :=
        completedLFunction_eq_zero_of_mem hz
      have hP0 : LProductMult χ z = 0 := LProductMult_zero_of_mem_NontrivialZeros hχ hz
      rw [hΛ0, hP0, mul_zero]
    · have hP_ne : LProductMult χ z ≠ 0 :=
        LProductMult_ne_zero_of_notMem_NontrivialZeros hχ hχp hz
      have hratio : DirichletCharacter.completedLFunction χ z / LProductMult χ z = LOverP χ z :=
        (ratio_eventuallyEq_LOverP_of_notMem hχ hχp hz).eq_of_nhds
      rw [← hratio]; field_simp
  have hexp : Complex.exp (A * z + Complex.log (LOverP χ 0)) = LOverP χ 0 * Complex.exp (A * z) := by
    rw [Complex.exp_add, Complex.exp_log hc_ne, mul_comm]
  rw [hfact, hA z, hexp]

end DirichletLHadamard

#print axioms DirichletLHadamard.LOverP_eq_const_mul_exp
#print axioms DirichletLHadamard.LOverP_growth_linear
#print axioms DirichletLHadamard.LOverP_growth_meanType_sharp
#print axioms DirichletLHadamard.hadamardPartialFraction_sharp
#print axioms DirichletLHadamard.completedLFunction_eq_exp_mul_LProductMult
