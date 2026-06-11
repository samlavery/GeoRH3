import RequestProject.HelixUnitaryFlow

/-!
# Step 2, operator form: the phasor dynamics ARE a one-parameter unitary group

`HelixUnitaryFlow.phasorFlow` gives the per-mode phasor `U(t)(n) = n^{it} ∈ Circle` with the pointwise
group law for `n ≠ 0`. Here it is assembled into the object step 2 actually asks for — a
**strongly-continuous one-parameter group of diagonal unitaries**: a monoid homomorphism
`ℝ → (ℕ → Circle)` into the diagonal-unitary group, modulus `1` by construction.

This is the **unitarity** that carries the on-line forcing — the spectral values land on the unit
circle (`SpectralSide.w_unit_iff_half`: `‖w‖ = 1 ⟺ Re = ½`) — and it is unconditional: **no Weil/Li
positivity, no `≥ 0`, no self-adjoint generator, no Stone.** Each `U(t)` is a unit-modulus diagonal
(hence unitary); `U(s+t) = U(s)·U(t)`, `U(0) = 1`; and `t ↦ U(t)(n)` is continuous.

* `flowHom` — `U : Multiplicative ℝ →* (ℕ → Circle)`, the one-parameter subgroup.
* `phasorFlow_norm` — each entry is on the unit circle (`‖U(t)(n)‖ = 1`).
* `phasorFlow_continuous` — strong continuity of the flow.
-/

open HelixLogFree HelixFlow Complex

namespace HelixFlow

/-- The flow is trivial on the index `0`: `U(t)(0) = 1` (the empty factorization has winding angle 0). -/
@[simp] theorem phasorFlow_index_zero (t : ℝ) : phasorFlow t 0 = 1 := by
  simp [phasorFlow, wind, windAngle, Finsupp.sum]

/-- **One-parameter group law, all indices.** `U(s+t) = U(s)·U(t)` for every `n` — the `n = 0` case is
    `1 = 1·1`, so the `n ≠ 0` hypothesis of `phasorFlow_add` drops. -/
theorem phasorFlow_add_all (s t : ℝ) (n : ℕ) :
    phasorFlow (s + t) n = phasorFlow s n * phasorFlow t n := by
  rcases eq_or_ne n 0 with hn | hn
  · subst hn; simp
  · exact phasorFlow_add s t n hn

/-- **The unitary flow as a one-parameter subgroup of the diagonal-unitary group `ℕ → Circle`.**
    Writing the additive line `ℝ` multiplicatively, `U : Multiplicative ℝ →* (ℕ → Circle)` is a monoid
    homomorphism: `U(0) = 1`, `U(s+t) = U(s)·U(t)`. Each `U(t)` is a diagonal of unit-modulus entries —
    a unitary. The FTA welding across modes is the *separate* multiplicativity `phasorFlow_mul`. -/
noncomputable def flowHom : Multiplicative ℝ →* (ℕ → Circle) where
  toFun t := fun n => phasorFlow (Multiplicative.toAdd t) n
  map_one' := by funext n; exact phasorFlow_zero n
  map_mul' s t := by funext n; exact phasorFlow_add_all _ _ n

@[simp] theorem flowHom_apply (t : ℝ) (n : ℕ) :
    flowHom (Multiplicative.ofAdd t) n = phasorFlow t n := rfl

/-- **Each flow value is unitary** (on the unit circle): `‖U(t)(n)‖ = 1`. -/
theorem phasorFlow_norm (t : ℝ) (n : ℕ) : ‖(phasorFlow t n : ℂ)‖ = 1 := by
  simp [phasorFlow]

/-- **Strong continuity of the flow.** For each mode `n`, `t ↦ U(t)(n)` is continuous — so the group
    `flowHom` is a *strongly-continuous* one-parameter unitary group (`U(t)(n) = n^{it}`). -/
theorem phasorFlow_continuous (n : ℕ) :
    Continuous (fun t : ℝ => (phasorFlow t n : ℂ)) := by
  rcases eq_or_ne n 0 with hn | hn
  · subst hn
    have : (fun t : ℝ => (phasorFlow t 0 : ℂ)) = fun _ => (1 : ℂ) := by
      funext t; rw [phasorFlow_index_zero]; simp
    rw [this]; exact continuous_const
  · have hc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have heq : (fun t : ℝ => (phasorFlow t n : ℂ))
        = fun t : ℝ => (n : ℂ) ^ (Complex.I * (t : ℂ)) := by
      funext t; exact phasorFlow_eq_cpow t n hn
    rw [heq]
    exact (continuous_const.mul Complex.continuous_ofReal).const_cpow (Or.inl hc)

/-- **Step 2, assembled.** The phasor dynamics form a strongly-continuous one-parameter group of
    diagonal unitaries — unconditional, modulus 1, no positivity: `U(0) = 1`, `U(s+t) = U(s)·U(t)`,
    `‖U(t)(n)‖ = 1`, and `t ↦ U(t)(n)` continuous. -/
theorem isUnitaryOneParameterFlow :
    (flowHom (Multiplicative.ofAdd 0) = 1) ∧
    (∀ s t : ℝ, flowHom (Multiplicative.ofAdd (s + t))
        = flowHom (Multiplicative.ofAdd s) * flowHom (Multiplicative.ofAdd t)) ∧
    (∀ t : ℝ, ∀ n : ℕ, ‖(phasorFlow t n : ℂ)‖ = 1) ∧
    (∀ n : ℕ, Continuous (fun t : ℝ => (phasorFlow t n : ℂ))) := by
  refine ⟨?_, ?_, phasorFlow_norm, phasorFlow_continuous⟩
  · rw [ofAdd_zero, map_one]
  · intro s t; rw [ofAdd_add, map_mul]

end HelixFlow

#print axioms HelixFlow.flowHom
#print axioms HelixFlow.isUnitaryOneParameterFlow
#print axioms HelixFlow.phasorFlow_continuous
