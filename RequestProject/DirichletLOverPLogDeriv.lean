import RequestProject.DirichletLOverP
import RequestProject.DirichletLHadamardAssembly
import RequestProject.LogDerivConstOfGrowth

/-!
# `logDeriv (LOverP χ)` off zeros, and the growth-conditional Hadamard partial fraction

Connects the entire zero-free quotient `LOverP χ = Λ_χ/Prod` to the log-derivative difference, then
assembles the **growth-conditional** target:

  `(∃ C D, ∀ z, ‖LOverP χ z‖ ≤ exp(C‖z‖log(‖z‖+2)+D))  ⟹  HadamardPartialFraction χ`.

The generic Hadamard constancy `HadamardConst.logDeriv_const_of_growth` turns the growth into
`logDeriv (LOverP χ) ≡ A`; off the zeros `logDeriv (LOverP χ) = logDeriv Λ_χ − logDeriv Prod`, so the
difference is constant; `HadamardPartialFraction_of_diff_const` finishes. **Everything except the growth
bound is now unconditional and kernel-clean** — the single remaining ingredient is the order-1 mean-type
growth of `Λ_χ/Prod` (numerator bound `completedL_order_one_log_bound` over the product's Nevanlinna
lower bound).
-/

open Complex Filter Topology

noncomputable section

namespace DirichletLHadamard

variable {N : ℕ} [NeZero N]

/-- Off the nontrivial zeros, the literal ratio agrees with `LOverP χ` on a full neighborhood. -/
theorem ratio_eventuallyEq_LOverP_of_notMem {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hχp : χ.IsPrimitive) {z : ℂ} (hz : z ∉ GRHSpectral.NontrivialZeros χ) :
    (fun w => DirichletCharacter.completedLFunction χ w / LProductMult χ w) =ᶠ[𝓝 z] LOverP χ := by
  have h_anal_L : AnalyticAt ℂ (DirichletCharacter.completedLFunction χ) z :=
    completedLFunction_analyticAt hχ z
  have h_anal_P : AnalyticAt ℂ (LProductMult χ) z :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr (LProductMult_differentiable hχ hχp)) z
      (Set.mem_univ z)
  have h_P_ne : LProductMult χ z ≠ 0 :=
    LProductMult_ne_zero_of_notMem_NontrivialZeros hχ hχp hz
  have h_ratio_nf :
      MeromorphicNFAt (fun w => DirichletCharacter.completedLFunction χ w / LProductMult χ w) z :=
    (h_anal_L.div h_anal_P h_P_ne).meromorphicNFAt
  have h_punct :
      (fun w => DirichletCharacter.completedLFunction χ w / LProductMult χ w)
        =ᶠ[nhdsWithin z {z}ᶜ] LOverP χ := by
    have h_mem :
        {w | (fun w => DirichletCharacter.completedLFunction χ w / LProductMult χ w) w
              = LOverP χ w} ∈ codiscreteWithin (Set.univ : Set ℂ) :=
      LOverP_eq_ratio_codiscretely hχ hχp
    rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE] at h_mem
    have h := h_mem z (Set.mem_univ z)
    simp only [Set.compl_univ, Set.union_empty] at h
    exact h
  exact (h_ratio_nf.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
    (LOverP_analyticAt hχ hχp z).meromorphicNFAt).1 h_punct

/-- Off the nontrivial zeros, `logDeriv (LOverP χ) = logDeriv Λ_χ − logDeriv Prod`. -/
theorem logDeriv_LOverP_eq_diff_of_notMem {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hχp : χ.IsPrimitive) {z : ℂ} (hz : z ∉ GRHSpectral.NontrivialZeros χ) :
    logDeriv (LOverP χ) z
      = logDeriv (DirichletCharacter.completedLFunction χ) z - logDeriv (LProductMult χ) z := by
  have h_ratio := ratio_eventuallyEq_LOverP_of_notMem hχ hχp hz
  have h_ratio_deriv :
      deriv (fun w => DirichletCharacter.completedLFunction χ w / LProductMult χ w) z
        = deriv (LOverP χ) z := h_ratio.deriv_eq
  have h_ratio_val :
      (fun w => DirichletCharacter.completedLFunction χ w / LProductMult χ w) z = LOverP χ z :=
    h_ratio.eq_of_nhds
  have h_L_ne : DirichletCharacter.completedLFunction χ z ≠ 0 :=
    fun h => hz (completedLFunction_zero_mem_NontrivialZeros hχ hχp h)
  have h_P_ne : LProductMult χ z ≠ 0 :=
    LProductMult_ne_zero_of_notMem_NontrivialZeros hχ hχp hz
  have h_log_ratio :
      logDeriv (fun w => DirichletCharacter.completedLFunction χ w / LProductMult χ w) z =
        logDeriv (DirichletCharacter.completedLFunction χ) z - logDeriv (LProductMult χ) z := by
    simpa using logDeriv_div (f := DirichletCharacter.completedLFunction χ) (g := LProductMult χ) z
      h_L_ne h_P_ne (completedLFunction_differentiable hχ z) (LProductMult_differentiable hχ hχp z)
  calc logDeriv (LOverP χ) z
      = logDeriv (fun w => DirichletCharacter.completedLFunction χ w / LProductMult χ w) z := by
        rw [logDeriv_apply, logDeriv_apply, ← h_ratio_deriv, ← h_ratio_val]
    _ = logDeriv (DirichletCharacter.completedLFunction χ) z - logDeriv (LProductMult χ) z :=
        h_log_ratio

/-- **Growth-conditional Hadamard partial fraction.** If the entire zero-free quotient
`LOverP χ = Λ_χ / LProductMult χ` has order-1 mean-type growth, then `HadamardPartialFraction χ`
holds. The single remaining input to the full unconditional identity is this growth bound. -/
theorem HadamardPartialFraction_of_LOverP_growth {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hχp : χ.IsPrimitive)
    (hG : ∃ C D : ℝ, ∀ z : ℂ,
      ‖LOverP χ z‖ ≤ Real.exp (C * ‖z‖ * Real.log (‖z‖ + 2) + D)) :
    HadamardPartialFraction χ := by
  obtain ⟨A, hA⟩ := HadamardConst.logDeriv_const_of_growth (LOverP_differentiable hχ hχp)
    (LOverP_ne_zero hχ hχp) hG
  apply HadamardPartialFraction_of_diff_const hχ hχp
  refine ⟨A, ?_⟩
  intro s hs
  rw [← logDeriv_LOverP_eq_diff_of_notMem hχ hχp hs]
  exact hA s

/-- **Growth-conditional Hadamard partial fraction, `log²` (mean-type-2) form.** Matches the growth the
Nevanlinna/Poisson chain naturally produces (`‖LOverP χ z‖ ≤ exp(C‖z‖log²(‖z‖+2)+D)`). -/
theorem HadamardPartialFraction_of_LOverP_logSqGrowth {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hχp : χ.IsPrimitive)
    (hG : ∃ C D : ℝ, ∀ z : ℂ,
      ‖LOverP χ z‖ ≤ Real.exp (C * ‖z‖ * (Real.log (‖z‖ + 2)) ^ 2 + D)) :
    HadamardPartialFraction χ := by
  obtain ⟨A, hA⟩ := HadamardConst.logDeriv_const_of_logSqGrowth (LOverP_differentiable hχ hχp)
    (LOverP_ne_zero hχ hχp) hG
  apply HadamardPartialFraction_of_diff_const hχ hχp
  refine ⟨A, ?_⟩
  intro s hs
  rw [← logDeriv_LOverP_eq_diff_of_notMem hχ hχp hs]
  exact hA s

end DirichletLHadamard

#print axioms DirichletLHadamard.HadamardPartialFraction_of_LOverP_growth
#print axioms DirichletLHadamard.HadamardPartialFraction_of_LOverP_logSqGrowth
