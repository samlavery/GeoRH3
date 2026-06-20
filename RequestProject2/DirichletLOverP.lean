import RequestProject.DirichletLProductMultOrder
import RequestProject.DirichletLZeroSet

/-!
# Entire zero-free quotient `LOverP χ = Λ_χ / LProductMult χ`

Character-`χ` port of `ZD.xiOverP`. The literal ratio `Λ_χ / Prod` is meromorphic (entire/entire); by
order-matching everywhere — at the zeros via `analyticOrderAt_LProductMult_eq_lOrderNat`, off the zeros
via the zero-set characterization (`completedLFunction_zero_mem_NontrivialZeros`, both nonzero) — its
meromorphic order is `0` at every point, so the normal-form representative `LOverP χ` is **entire and
zero-free**. This is the object the generic Hadamard constancy (`HadamardConst.logDeriv_const_of_growth`)
consumes: `logDeriv (LOverP χ)` is constant once the quotient growth is bounded.
-/

open Complex Set Filter Topology

noncomputable section

namespace DirichletLHadamard

variable {N : ℕ} [NeZero N]

/-- `analyticOrderAt Λ_χ z ≠ ⊤` everywhere (`Λ_χ` not locally zero). -/
theorem completedLFunction_analyticOrderAt_ne_top {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (z : ℂ) :
    analyticOrderAt (DirichletCharacter.completedLFunction χ) z ≠ ⊤ :=
  fun h => completedLFunction_not_eventuallyEq_zero hχ (analyticOrderAt_eq_top.mp h)

/-- **Entire zero-free continuation** of `Λ_χ / LProductMult χ` via the normal-form representative. -/
def LOverP (χ : DirichletCharacter ℂ N) : ℂ → ℂ :=
  toMeromorphicNFOn (fun z => DirichletCharacter.completedLFunction χ z / LProductMult χ z) Set.univ

/-- The literal ratio is meromorphic (entire / entire). -/
theorem ratio_meromorphicOn {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) :
    MeromorphicOn (fun z => DirichletCharacter.completedLFunction χ z / LProductMult χ z) Set.univ := by
  apply MeromorphicOn.fun_div
  · exact ((completedLFunction_differentiable hχ).differentiableOn.analyticOnNhd
      isOpen_univ).meromorphicOn
  · exact ((LProductMult_differentiable hχ hχp).differentiableOn.analyticOnNhd
      isOpen_univ).meromorphicOn

/-- `LOverP χ` is in meromorphic normal form on `ℂ`. -/
theorem LOverP_meromorphicNFOn {χ : DirichletCharacter ℂ N} : MeromorphicNFOn (LOverP χ) Set.univ :=
  meromorphicNFOn_toMeromorphicNFOn _ _

/-- `LOverP χ` equals the literal ratio on a codiscrete set. -/
theorem LOverP_eq_ratio_codiscretely {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hχp : χ.IsPrimitive) :
    (fun z => DirichletCharacter.completedLFunction χ z / LProductMult χ z)
      =ᶠ[codiscreteWithin Set.univ] LOverP χ :=
  toMeromorphicNFOn_eqOn_codiscrete (ratio_meromorphicOn hχ hχp)

/-- The order of the literal ratio at any `z` is `0` (orders of `Λ_χ` and `Prod` coincide everywhere). -/
theorem ratio_meromorphicOrderAt_eq_zero {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hχp : χ.IsPrimitive) (z : ℂ) :
    meromorphicOrderAt (fun w => DirichletCharacter.completedLFunction χ w / LProductMult χ w) z = 0 := by
  have h_anal_L : AnalyticAt ℂ (DirichletCharacter.completedLFunction χ) z :=
    completedLFunction_analyticAt hχ z
  have h_anal_P : AnalyticAt ℂ (LProductMult χ) z :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr (LProductMult_differentiable hχ hχp)) z
      (Set.mem_univ _)
  have h_orders : analyticOrderAt (DirichletCharacter.completedLFunction χ) z =
      analyticOrderAt (LProductMult χ) z := by
    by_cases hz : z ∈ GRHSpectral.NontrivialZeros χ
    · have hL_def : analyticOrderAt (DirichletCharacter.completedLFunction χ) z =
          (lOrderNat χ z : ℕ∞) := by
        unfold lOrderNat analyticOrderNatAt
        exact (ENat.coe_toNat (completedLFunction_analyticOrderAt_ne_top hχ z)).symm
      have hP_def := analyticOrderAt_LProductMult_eq_lOrderNat hχ hχp hz
      rw [hL_def, hP_def]
    · have h_L_ne : DirichletCharacter.completedLFunction χ z ≠ 0 :=
        fun h => hz (completedLFunction_zero_mem_NontrivialZeros hχ hχp h)
      have h_P_ne : LProductMult χ z ≠ 0 :=
        LProductMult_ne_zero_of_notMem_NontrivialZeros hχ hχp hz
      rw [h_anal_L.analyticOrderAt_eq_zero.mpr h_L_ne,
          h_anal_P.analyticOrderAt_eq_zero.mpr h_P_ne]
  have h_L_ne_top : analyticOrderAt (DirichletCharacter.completedLFunction χ) z ≠ ⊤ :=
    completedLFunction_analyticOrderAt_ne_top hχ z
  have h_P_ne_top : analyticOrderAt (LProductMult χ) z ≠ ⊤ := h_orders ▸ h_L_ne_top
  rw [fun_meromorphicOrderAt_div h_anal_L.meromorphicAt h_anal_P.meromorphicAt,
      h_anal_L.meromorphicOrderAt_eq, h_anal_P.meromorphicOrderAt_eq, h_orders]
  have ha : analyticOrderAt (LProductMult χ) z =
      ((analyticOrderAt (LProductMult χ) z).toNat : ℕ∞) :=
    (ENat.coe_toNat h_P_ne_top).symm
  rw [ha]
  simp

/-- `LOverP χ` is analytic at every `z`. -/
theorem LOverP_analyticAt {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) (z : ℂ) :
    AnalyticAt ℂ (LOverP χ) z := by
  have h_nf : MeromorphicNFAt (LOverP χ) z := LOverP_meromorphicNFOn (Set.mem_univ z)
  rcases meromorphicNFAt_iff_analyticAt_or.mp h_nf with h | ⟨_, h_lt, _⟩
  · exact h
  · exfalso
    have h_codisc := LOverP_eq_ratio_codiscretely hχ hχp
    have h_punct : (fun w => DirichletCharacter.completedLFunction χ w / LProductMult χ w)
        =ᶠ[nhdsWithin z {z}ᶜ] LOverP χ := by
      have h_mem : {w | (fun w => DirichletCharacter.completedLFunction χ w / LProductMult χ w) w
          = LOverP χ w} ∈ codiscreteWithin (Set.univ : Set ℂ) := h_codisc
      rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE] at h_mem
      have := h_mem z (Set.mem_univ z)
      simp only [Set.compl_univ, Set.union_empty] at this
      exact this
    have h_order_eq : meromorphicOrderAt (LOverP χ) z =
        meromorphicOrderAt (fun w => DirichletCharacter.completedLFunction χ w / LProductMult χ w) z :=
      meromorphicOrderAt_congr h_punct.symm
    rw [h_order_eq, ratio_meromorphicOrderAt_eq_zero hχ hχp] at h_lt
    exact absurd h_lt (by norm_num)

/-- `LOverP χ` is differentiable everywhere. -/
theorem LOverP_differentiable {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) :
    Differentiable ℂ (LOverP χ) :=
  fun z => (LOverP_analyticAt hχ hχp z).differentiableAt

/-- **`LOverP χ` is zero-free.** -/
theorem LOverP_ne_zero {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) (z : ℂ) :
    LOverP χ z ≠ 0 := by
  have h_nf : MeromorphicNFAt (LOverP χ) z := LOverP_meromorphicNFOn (Set.mem_univ z)
  have h_codisc := LOverP_eq_ratio_codiscretely hχ hχp
  have h_punct : (fun w => DirichletCharacter.completedLFunction χ w / LProductMult χ w)
      =ᶠ[nhdsWithin z {z}ᶜ] LOverP χ := by
    have h_mem : {w | (fun w => DirichletCharacter.completedLFunction χ w / LProductMult χ w) w
        = LOverP χ w} ∈ codiscreteWithin (Set.univ : Set ℂ) := h_codisc
    rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE] at h_mem
    have := h_mem z (Set.mem_univ z)
    simp only [Set.compl_univ, Set.union_empty] at this
    exact this
  have h_order_eq : meromorphicOrderAt (LOverP χ) z =
      meromorphicOrderAt (fun w => DirichletCharacter.completedLFunction χ w / LProductMult χ w) z :=
    meromorphicOrderAt_congr h_punct.symm
  rw [ratio_meromorphicOrderAt_eq_zero hχ hχp z] at h_order_eq
  exact h_nf.meromorphicOrderAt_eq_zero_iff.mp h_order_eq

end DirichletLHadamard

#print axioms DirichletLHadamard.LOverP_differentiable
#print axioms DirichletLHadamard.LOverP_ne_zero
