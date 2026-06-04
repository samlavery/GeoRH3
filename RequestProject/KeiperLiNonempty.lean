import Mathlib
import RequestProject.XiHadamardFactorization
import RequestProject.ZeroCountJensen
import RequestProject.ThetaTransport

/-!
# Existence of a nontrivial zeta zero (classical, pre-RH)

This file proves **unconditionally** that the Riemann zeta function has at least
one nontrivial zero, i.e. `ZD.NontrivialZeros` is nonempty.  This is strictly
weaker than the Riemann Hypothesis: RH says *all* nontrivial zeros lie on the
critical line, whereas this statement only asserts that *at least one* nontrivial
zero exists.

## Proof outline (by contradiction)

Assume `NontrivialZeros = ∅`.

1. **Empty product collapses.**  `ZD.xiProductMult` is a `tprod` over
   `MultiZeroIdx := Σ (ρ : {ρ // ρ ∈ NontrivialZeros}), Fin (xiOrderNat ρ.val)`.
   If `NontrivialZeros = ∅`, the base subtype is empty, hence the sigma index
   type is empty, hence the product is `1`.

2. **ξ becomes `exp(A·z + B)`.**  `ZD.riemannXi_hadamard_factorization` gives
   `riemannXi z = exp(A·z + B) · xiProductMult z`; with step 1, `riemannXi z =
   exp(A·z + B)` for all `z`.

3. **Functional equation forces `exp A = 1`.**  `ZD.ZeroCount.riemannXi_one_sub`
   gives `riemannXi (1 - s) = riemannXi s`.  At `s = 0` this reads
   `riemannXi 1 = riemannXi 0`, i.e. `exp(A + B) = exp B`, so `exp A = 1`.

4. **Two explicit values contradict.**  Then
   `riemannXi 2 = exp(2A + B) = (exp A)² · exp B = exp B = riemannXi 0 = 1/2`.
   But the classical form gives `riemannXi 2 = completedRiemannZeta 2 = π/6`
   (via `riemannZeta_two : ζ(2) = π²/6` and `Gammaℝ 2 = π⁻¹`).  So `π/6 = 1/2`,
   i.e. `π = 3`, contradicting `Real.pi_gt_three`.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

open Complex

noncomputable section

namespace ZD

/-- **Step 4 value.** `completedRiemannZeta 2 = π / 6`, from
`riemannZeta_two : ζ(2) = π²/6` and `Gammaℝ 2 = π⁻¹`. -/
theorem completedRiemannZeta_two_eq : completedRiemannZeta 2 = (Real.pi : ℂ) / 6 := by
  have hz := riemannZeta_def_of_ne_zero (s := (2 : ℂ)) (by norm_num)
  rw [riemannZeta_two] at hz
  -- hz : (π : ℂ)^2 / 6 = completedRiemannZeta 2 / Gammaℝ 2
  have hGval : Complex.Gammaℝ (2 : ℂ) = (Real.pi : ℂ) ^ (-1 : ℂ) := by
    rw [Complex.Gammaℝ_def]; norm_num
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hG : Complex.Gammaℝ (2 : ℂ) ≠ 0 := by
    rw [hGval, Complex.cpow_neg_one]; exact inv_ne_zero hpi
  have hC : completedRiemannZeta 2 = ((Real.pi : ℂ) ^ 2 / 6) * Complex.Gammaℝ 2 := by
    rw [hz]; field_simp
  rw [hC, hGval, Complex.cpow_neg_one]
  field_simp

/-- **Step 4 value.** `riemannXi 2 = π / 6`, since `2 ≠ 0, 1` so the classical
form applies with prefactor `2·(2-1)/2 = 1`. -/
theorem riemannXi_two_eq : ZD.riemannXi 2 = (Real.pi : ℂ) / 6 := by
  rw [ZD.riemannXi_eq_classical_of_ne_zero_of_ne_one 2 (by norm_num) (by norm_num),
    completedRiemannZeta_two_eq]
  ring

/-- **Step 1.** If `NontrivialZeros = ∅`, the multiplicity-indexed Weierstrass
product is identically `1`, because its index type is empty. -/
theorem xiProductMult_eq_one_of_empty (h : NontrivialZeros = (∅ : Set ℂ)) :
    ∀ z : ℂ, ZD.xiProductMult z = 1 := by
  have hBase : IsEmpty {ρ : ℂ // ρ ∈ NontrivialZeros} := by
    rw [h]; exact Set.isEmpty_coe_sort.mpr rfl
  haveI hIdx : IsEmpty ZD.MultiZeroIdx := Sigma.isEmpty_left
  intro z
  unfold ZD.xiProductMult
  exact tprod_empty

/-- **Existence of a nontrivial zeta zero (classical, pre-RH).**
`ZD.NontrivialZeros` is nonempty.  Strictly weaker than RH. -/
theorem nontrivialZeros_nonempty : (NontrivialZeros).Nonempty := by
  by_contra h
  -- h : ¬ NontrivialZeros.Nonempty, i.e. NontrivialZeros = ∅
  rw [Set.not_nonempty_iff_eq_empty] at h
  -- Step 2: Hadamard factorization with the empty product collapsing to 1.
  obtain ⟨A, B, hAB⟩ := ZD.riemannXi_hadamard_factorization
  have hProd := xiProductMult_eq_one_of_empty h
  have hExp : ∀ z : ℂ, ZD.riemannXi z = Complex.exp (A * z + B) := by
    intro z; rw [hAB z, hProd z, mul_one]
  -- Step 3: functional equation at s = 0 gives exp A = 1.
  have hFE : ZD.riemannXi 1 = ZD.riemannXi 0 := by
    have := ZD.ZeroCount.riemannXi_one_sub 0
    simpa using this
  have hExpA : Complex.exp A = 1 := by
    have h1 : Complex.exp (A * 1 + B) = Complex.exp (A * 0 + B) := by
      rw [← hExp 1, ← hExp 0]; exact hFE
    have hB : Complex.exp B ≠ 0 := Complex.exp_ne_zero B
    rw [mul_one, mul_zero, zero_add] at h1
    -- h1 : exp (A + B) = exp B
    rw [Complex.exp_add] at h1
    -- h1 : exp A * exp B = exp B
    have h2 : Complex.exp A * Complex.exp B = 1 * Complex.exp B := by rw [one_mul]; exact h1
    exact mul_right_cancel₀ hB h2
  -- Step 4: riemannXi 2 = exp B = riemannXi 0 = 1/2, but also = π/6.
  have hXi0 : ZD.riemannXi 0 = 1 / 2 := ZD.ZeroCount.riemannXi_zero
  have hXi2_exp : ZD.riemannXi 2 = Complex.exp B := by
    rw [hExp 2]
    rw [show A * 2 + B = (A + A) + B by ring, Complex.exp_add, Complex.exp_add, hExpA]
    ring
  have hExpB : Complex.exp B = 1 / 2 := by
    have : ZD.riemannXi 0 = Complex.exp B := by rw [hExp 0]; ring_nf
    rw [← this, hXi0]
  have hXi2_half : ZD.riemannXi 2 = 1 / 2 := by rw [hXi2_exp, hExpB]
  have hXi2_pi : ZD.riemannXi 2 = (Real.pi : ℂ) / 6 := riemannXi_two_eq
  -- π/6 = 1/2 → π = 3, contradiction.
  have hpi_eq : (Real.pi : ℂ) / 6 = 1 / 2 := by rw [← hXi2_pi, hXi2_half]
  have hr : (Real.pi : ℝ) / 6 = 1 / 2 := by
    have hcast : ((Real.pi / 6 : ℝ) : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; exact hpi_eq
    exact_mod_cast hcast
  have hpi3 : Real.pi = 3 := by linarith
  have := Real.pi_gt_three
  linarith

end ZD

#print axioms ZD.nontrivialZeros_nonempty
