import Mathlib

/-!
# The limit as a monotone-form completion of finite Gram spaces

The infinite object is built from the finite Gram quadratic forms, **not** as an entrywise matrix
limit. For an analysis operator with sampled components `c n : V →L[ℂ] ℂ` (the rows of `B_N`):

* `qN N f = ‖B_N f‖² = ∑_{n<N} |c n f|²`              — the finite Gram form,
* `qN N f ≤ qN (N+1) f`                               — **monotone exhaustion** (`qN_le_succ`),
* `qInf f = ⨆ N, qN N f`  in `ℝ≥0∞`                   — the extended limiting form (may be `∞`),
* `finiteEnergy = { f | qInf f < ∞ }`                — the finite-energy domain (a submodule),
* `nullSpace   = { f | qInf f = 0 }`                 — the null vectors (a submodule).

The limiting Hilbert space is then `completion (finiteEnergy ⧸ nullSpace)`; this file builds the
form machinery (steps 1–4) on which that completion and the self-adjoint `G∞` rest. The point of
`ℝ≥0∞`: "the limit is infinite" means an extended form that is `∞` off the finite-energy domain —
not a value forced on every vector.
-/

open scoped ENNReal BigOperators

namespace HelixForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] (c : ℕ → (V →L[ℂ] ℂ))

/-- The finite Gram quadratic form `q_N(f) = ‖B_N f‖² = ∑_{n<N} |c n f|²`. -/
noncomputable def qN (N : ℕ) (f : V) : ℝ := ∑ n ∈ Finset.range N, ‖c n f‖ ^ 2

theorem qN_nonneg (N : ℕ) (f : V) : 0 ≤ qN c N f :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **Monotone exhaustion:** `q_N(f) ≤ q_{N+1}(f)` — each step adds a non-negative term. -/
theorem qN_le_succ (N : ℕ) (f : V) : qN c N f ≤ qN c (N + 1) f := by
  simp only [qN, Finset.sum_range_succ]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem qN_mono (f : V) : Monotone fun N => qN c N f :=
  monotone_nat_of_le_succ fun N => qN_le_succ c N f

@[simp] theorem qN_zero (N : ℕ) : qN c N 0 = 0 := by simp [qN]

/-- The form is homogeneous of degree two: `q_N(a • f) = ‖a‖² · q_N(f)`. -/
theorem qN_smul (N : ℕ) (a : ℂ) (f : V) : qN c N (a • f) = ‖a‖ ^ 2 * qN c N f := by
  unfold qN
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_smul, smul_eq_mul, norm_mul, mul_pow]

/-- Sub-additivity (parallelogram bound): `q_N(f+g) ≤ 2 q_N(f) + 2 q_N(g)`. -/
theorem qN_add_le (N : ℕ) (f g : V) : qN c N (f + g) ≤ 2 * qN c N f + 2 * qN c N g := by
  have h : ∀ n ∈ Finset.range N,
      ‖c n (f + g)‖ ^ 2 ≤ 2 * ‖c n f‖ ^ 2 + 2 * ‖c n g‖ ^ 2 := by
    intro n _
    rw [map_add]
    have htri := norm_add_le (c n f) (c n g)
    nlinarith [htri, norm_nonneg (c n f), norm_nonneg (c n g),
      norm_nonneg (c n f + c n g), sq_nonneg (‖c n f‖ - ‖c n g‖)]
  calc qN c N (f + g) = ∑ n ∈ Finset.range N, ‖c n (f + g)‖ ^ 2 := rfl
    _ ≤ ∑ n ∈ Finset.range N, (2 * ‖c n f‖ ^ 2 + 2 * ‖c n g‖ ^ 2) := Finset.sum_le_sum h
    _ = 2 * qN c N f + 2 * qN c N g := by
        simp only [qN, Finset.sum_add_distrib, Finset.mul_sum]

/-- **The limiting form** `q∞(f) = sup_N q_N(f)`, valued in `ℝ≥0∞` (possibly `∞`). -/
noncomputable def qInf (f : V) : ℝ≥0∞ := ⨆ N, ENNReal.ofReal (qN c N f)

theorem qN_le_qInf (N : ℕ) (f : V) : ENNReal.ofReal (qN c N f) ≤ qInf c f := by
  rw [qInf]; exact le_iSup (fun n => ENNReal.ofReal (qN c n f)) N

@[simp] theorem qInf_zero : qInf c 0 = 0 := by simp [qInf]

/-- `q∞(a • f) = ‖a‖² · q∞(f)`. -/
theorem qInf_smul (a : ℂ) (f : V) : qInf c (a • f) = ENNReal.ofReal (‖a‖ ^ 2) * qInf c f := by
  simp only [qInf, qN_smul]
  simp_rw [ENNReal.ofReal_mul (sq_nonneg ‖a‖)]
  rw [ENNReal.mul_iSup]

/-- `q∞(f+g) ≤ 2 q∞(f) + 2 q∞(g)`. -/
theorem qInf_add_le (f g : V) : qInf c (f + g) ≤ 2 * qInf c f + 2 * qInf c g := by
  refine iSup_le fun N => ?_
  have h2f : (0:ℝ) ≤ 2 * qN c N f := by have := qN_nonneg c N f; linarith
  have h2g : (0:ℝ) ≤ 2 * qN c N g := by have := qN_nonneg c N g; linarith
  calc ENNReal.ofReal (qN c N (f + g))
      ≤ ENNReal.ofReal (2 * qN c N f + 2 * qN c N g) :=
        ENNReal.ofReal_le_ofReal (qN_add_le c N f g)
    _ = 2 * ENNReal.ofReal (qN c N f) + 2 * ENNReal.ofReal (qN c N g) := by
        rw [ENNReal.ofReal_add h2f h2g]
        congr 1 <;>
          rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat]
    _ ≤ 2 * qInf c f + 2 * qInf c g := by
        gcongr <;> exact qN_le_qInf c N _

/-- **The finite-energy domain** `{ f | q∞(f) < ∞ }`, a `ℂ`-submodule of `V`. -/
noncomputable def finiteEnergy : Submodule ℂ V where
  carrier := { f | qInf c f < ⊤ }
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    simp only [Set.mem_setOf_eq] at hf hg ⊢
    calc qInf c (f + g) ≤ 2 * qInf c f + 2 * qInf c g := qInf_add_le c f g
      _ < ⊤ := by
          refine ENNReal.add_lt_top.mpr ⟨?_, ?_⟩
          · exact ENNReal.mul_lt_top (by simp) hf
          · exact ENNReal.mul_lt_top (by simp) hg
  smul_mem' := by
    intro a f hf
    simp only [Set.mem_setOf_eq, SetLike.mem_coe] at hf ⊢
    rw [qInf_smul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf

/-- **The null space** `{ f | q∞(f) = 0 }`, a `ℂ`-submodule of `V` (quotiented out before
    completion). -/
noncomputable def nullSpace : Submodule ℂ V where
  carrier := { f | qInf c f = 0 }
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    simp only [Set.mem_setOf_eq] at hf hg ⊢
    have h := qInf_add_le c f g
    simp only [hf, hg, mul_zero, add_zero, nonpos_iff_eq_zero] at h
    exact h
  smul_mem' := by
    intro a f hf
    simp only [Set.mem_setOf_eq, SetLike.mem_coe] at hf ⊢
    rw [qInf_smul, hf, mul_zero]

end HelixForm
