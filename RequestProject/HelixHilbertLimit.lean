import Mathlib
import RequestProject.HelixFormLimit

/-!
# The limiting Hilbert space `H∞` as the closed analysis image in `ℓ²`

The finite-energy form `q∞(f) = ∑ₙ |c n f|²` is the pullback of the `ℓ²` norm under the analysis
map `f ↦ (c n f)ₙ`. So instead of hand-building an inner product from a limit and completing, we
realize `H∞` as the **closure of the analysis image inside `ℓ²`** — a closed subspace of a Hilbert
space, hence itself a Hilbert space, with the inner product inherited from `ℓ²`:

* `analysisMap : finiteEnergy ⟶ ℓ²`,  `f ↦ (c n f)ₙ`     (well-defined: finite energy ⇒ `ℓ²`),
* `H∞ = closure (range analysisMap)`                       (a closed `ℂ`-submodule of `ℓ²`),
* `CompleteSpace H∞` + the `ℓ²` inner product            ⇒ `H∞` is a Hilbert space.

`nullSpace` is exactly `ker analysisMap`, so this is `completion (finiteEnergy ⧸ nullSpace)` —
Sam's step 4 — realized concretely.
-/

open scoped ENNReal BigOperators

namespace HelixForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] (c : ℕ → (V →L[ℂ] ℂ))

/-- The limiting form is the `ℝ≥0∞`-valued infinite sum of `|c n f|²`. -/
theorem qInf_eq_tsum (f : V) : qInf c f = ∑' n, ENNReal.ofReal (‖c n f‖ ^ 2) := by
  rw [qInf, ENNReal.tsum_eq_iSup_nat]
  refine iSup_congr fun N => ?_
  rw [qN, ENNReal.ofReal_sum_of_nonneg (fun n _ => sq_nonneg _)]

/-- Finite energy ⇒ the coefficient sequence is square-summable. -/
theorem summable_sq_of_mem {f : V} (hf : f ∈ finiteEnergy c) :
    Summable (fun n => ‖c n f‖ ^ 2) := by
  have hlt : qInf c f < ⊤ := hf
  rw [qInf_eq_tsum] at hlt
  have hs := ENNReal.summable_toNNReal_of_tsum_ne_top hlt.ne
  have hrw : (ENNReal.toNNReal ∘ fun n => ENNReal.ofReal (‖c n f‖ ^ 2))
      = fun n => (‖c n f‖ ^ 2).toNNReal := by
    funext n; simp only [Function.comp_apply, ENNReal.ofReal, ENNReal.toNNReal_coe]
  rw [hrw] at hs
  have hcoe := NNReal.summable_coe.mpr hs
  have hid : (fun n => ((‖c n f‖ ^ 2).toNNReal : ℝ)) = fun n => ‖c n f‖ ^ 2 := by
    funext n; exact Real.coe_toNNReal _ (sq_nonneg _)
  rwa [hid] at hcoe

/-- Finite energy ⇒ the coefficient sequence lies in `ℓ²`. -/
theorem memℓp_of_mem {f : V} (hf : f ∈ finiteEnergy c) : Memℓp (fun n => c n f) 2 := by
  apply memℓp_gen
  have hs := summable_sq_of_mem c hf
  have hpow : (fun i => ‖c i f‖ ^ (2 : ℝ≥0∞).toReal) = fun i => ‖c i f‖ ^ (2 : ℕ) := by
    funext i
    rw [show (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hpow]; exact hs

/-- **The analysis map** `f ↦ (c n f)ₙ` from finite-energy vectors into `ℓ²`. -/
noncomputable def analysisMap : finiteEnergy c →ₗ[ℂ] lp (fun _ : ℕ => ℂ) 2 where
  toFun f := ⟨fun n => c n (f : V), memℓp_of_mem c f.2⟩
  map_add' f g := by
    ext n
    simp only [lp.coeFn_add, Pi.add_apply, Submodule.coe_add, map_add]
  map_smul' a f := by
    ext n
    simp only [lp.coeFn_smul, Pi.smul_apply, SetLike.val_smul, map_smul, RingHom.id_apply]

/-- **The limiting Hilbert space** `H∞`: the closure of the analysis image in `ℓ²`. -/
noncomputable def Hinf : Submodule ℂ (lp (fun _ : ℕ => ℂ) 2) :=
  (LinearMap.range (analysisMap c)).topologicalClosure

/-- `H∞` is closed in `ℓ²`. -/
theorem Hinf_isClosed : IsClosed (Hinf c : Set (lp (fun _ : ℕ => ℂ) 2)) :=
  (LinearMap.range (analysisMap c)).isClosed_topologicalClosure

/-- `H∞` is complete — a Hilbert space (closed subspace of the complete `ℓ²`), with the inherited
    `ℓ²` inner product. -/
instance : CompleteSpace (Hinf c) :=
  (Hinf_isClosed c).completeSpace_coe

/-- `H∞` is a Hilbert space: it carries an inner product (inherited from `ℓ²`) and is complete. -/
noncomputable example : InnerProductSpace ℂ (Hinf c) := inferInstance
example : CompleteSpace (Hinf c) := inferInstance

end HelixForm
