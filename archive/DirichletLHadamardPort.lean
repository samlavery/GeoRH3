import RequestProject.HadamardEngine
import RequestProject.DirichletLHadamard

/-!
# Dirichlet-`L` Hadamard port — residue cancellation ⟹ entire difference

The ξ chain's `ZD.logDeriv_difference_meromorphicOrderAt_nonneg` + `xiHadamardD_analyticAt`, ported to
`completedLFunction χ` via the character-agnostic `HadamardEngine.logDeriv_sub_orderNonneg`. For **any**
entire product `P` (the zero-matched Weierstrass product, to be constructed from the summability brick)
whose analytic order matches `completedLFunction χ` at every point, the difference `logDeriv Λ −
logDeriv P` has no poles and its normal-form representative `LHadamardD χ P` is **entire**.

This discharges the "every residue cancels globally ⟹ entire difference" stage for Dirichlet `L`,
parameterized by `P`. What remains to instantiate `P` concretely: the summability `Σ ord(ρ)/‖ρ‖² < ∞`
(order-1 growth ⇒ Jensen) and then the constancy kill. The engine and this entire-difference brick are
already in place and `χ`-general.
-/

open Complex Filter Topology

namespace DirichletLHadamard

variable {N : ℕ} [NeZero N]

/-- The literal log-derivative difference is meromorphic on `ℂ` (both `Λ` and `P` entire). -/
theorem logDeriv_diff_meromorphicOn {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    {P : ℂ → ℂ} (hP : Differentiable ℂ P) :
    MeromorphicOn (fun z => logDeriv (DirichletCharacter.completedLFunction χ) z - logDeriv P z)
      Set.univ := by
  have h_mero_L : MeromorphicOn (DirichletCharacter.completedLFunction χ) Set.univ :=
    ((completedLFunction_differentiable hχ).differentiableOn.analyticOnNhd isOpen_univ).meromorphicOn
  have h_mero_P : MeromorphicOn P Set.univ :=
    (hP.differentiableOn.analyticOnNhd isOpen_univ).meromorphicOn
  exact h_mero_L.logDeriv.fun_sub h_mero_P.logDeriv

/-- **Residue cancellation for Dirichlet `L`** (engine instantiation). Entire `P` whose analytic order
    matches `completedLFunction χ` everywhere ⟹ `logDeriv Λ − logDeriv P` has order ≥ 0 everywhere. -/
theorem logDeriv_diff_orderNonneg {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    {P : ℂ → ℂ} (hP : Differentiable ℂ P)
    (hord : ∀ z, analyticOrderAt (DirichletCharacter.completedLFunction χ) z = analyticOrderAt P z)
    (z : ℂ) :
    0 ≤ meromorphicOrderAt
          (fun w => logDeriv (DirichletCharacter.completedLFunction χ) w - logDeriv P w) z :=
  HadamardEngine.logDeriv_sub_orderNonneg
    (fun w => completedLFunction_analyticAt hχ w)
    (fun w => (Complex.analyticOnNhd_univ_iff_differentiable.mpr hP) w (Set.mem_univ w))
    (fun _ => completedLFunction_not_eventuallyEq_zero hχ)
    hord z

/-- The normal-form representative of `logDeriv Λ − logDeriv P` on `ℂ`. -/
noncomputable def LHadamardD (χ : DirichletCharacter ℂ N) (P : ℂ → ℂ) : ℂ → ℂ :=
  toMeromorphicNFOn
    (fun z => logDeriv (DirichletCharacter.completedLFunction χ) z - logDeriv P z) Set.univ

/-- `LHadamardD` agrees with the literal difference on a codiscrete set. -/
theorem LHadamardD_eq_diff_codiscretely {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    {P : ℂ → ℂ} (hP : Differentiable ℂ P) :
    (fun z => logDeriv (DirichletCharacter.completedLFunction χ) z - logDeriv P z)
      =ᶠ[codiscreteWithin Set.univ] LHadamardD χ P :=
  toMeromorphicNFOn_eqOn_codiscrete (logDeriv_diff_meromorphicOn hχ hP)

/-- The order of `LHadamardD` equals that of the literal difference at every point. -/
theorem LHadamardD_meromorphicOrderAt {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    {P : ℂ → ℂ} (hP : Differentiable ℂ P) (z : ℂ) :
    meromorphicOrderAt (LHadamardD χ P) z =
      meromorphicOrderAt
        (fun w => logDeriv (DirichletCharacter.completedLFunction χ) w - logDeriv P w) z := by
  have h_codisc := LHadamardD_eq_diff_codiscretely hχ hP
  have h_punct :
      (fun w => logDeriv (DirichletCharacter.completedLFunction χ) w - logDeriv P w)
        =ᶠ[nhdsWithin z {z}ᶜ] LHadamardD χ P := by
    have h_mem :
        {w | (fun w => logDeriv (DirichletCharacter.completedLFunction χ) w - logDeriv P w) w
              = LHadamardD χ P w} ∈ codiscreteWithin (Set.univ : Set ℂ) := h_codisc
    rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE] at h_mem
    have := h_mem z (Set.mem_univ z)
    simp only [Set.compl_univ, Set.union_empty] at this
    exact this
  exact (meromorphicOrderAt_congr h_punct).symm

/-- **The Dirichlet entire-difference brick.** For entire `P` with order matching `completedLFunction χ`
    everywhere, the normal-form difference `LHadamardD χ P` is **analytic at every point** — the
    residues cancel globally and the singularities are removable. The `χ`-general analogue of
    `xiHadamardD_analyticAt`. -/
theorem LHadamardD_analyticAt {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    {P : ℂ → ℂ} (hP : Differentiable ℂ P)
    (hord : ∀ z, analyticOrderAt (DirichletCharacter.completedLFunction χ) z = analyticOrderAt P z)
    (z : ℂ) : AnalyticAt ℂ (LHadamardD χ P) z := by
  have h_nf : MeromorphicNFAt (LHadamardD χ P) z :=
    meromorphicNFOn_toMeromorphicNFOn _ _ (Set.mem_univ z)
  rcases meromorphicNFAt_iff_analyticAt_or.mp h_nf with h | ⟨_, h_lt, _⟩
  · exact h
  · exfalso
    rw [LHadamardD_meromorphicOrderAt hχ hP z] at h_lt
    exact absurd h_lt (not_lt.mpr (logDeriv_diff_orderNonneg hχ hP hord z))

/-- Hence `LHadamardD χ P` is **entire** (differentiable everywhere). -/
theorem LHadamardD_differentiable {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    {P : ℂ → ℂ} (hP : Differentiable ℂ P)
    (hord : ∀ z, analyticOrderAt (DirichletCharacter.completedLFunction χ) z = analyticOrderAt P z) :
    Differentiable ℂ (LHadamardD χ P) :=
  fun z => (LHadamardD_analyticAt hχ hP hord z).differentiableAt

end DirichletLHadamard

#print axioms DirichletLHadamard.logDeriv_diff_orderNonneg
#print axioms DirichletLHadamard.LHadamardD_analyticAt
