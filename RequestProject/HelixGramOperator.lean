import Mathlib
import RequestProject.HelixHilbertLimit

/-!
# The Gram form and the operator `B∞` toward `G∞ = B∞* B∞`

Step 6 of the form route: the limiting Gram is the closed non-negative Hermitian form

    s(f,g) = ⟪B∞ f, B∞ g⟫   (on the finite-energy domain),   Re s(f,f) = ‖B∞ f‖² = q∞(f) ≥ 0,

whose associated self-adjoint operator is `G∞`. Here:

* `gramForm` — the form `s`, proven **non-negative** and **Hermitian**, with diagonal `‖B∞ f‖²`
  (the closed non-negative form representing `G∞`);
* `Bpmap` — `B∞` as a densely-defined (partial) linear operator `V →ₗ.[ℂ] ℓ²`, domain the
  finite-energy submodule.

The next step uses mathlib's unbounded-operator adjoint (`LinearPMap.adjoint`, available when `V`
is a Hilbert space) to form `B∞*` and then `G∞ = B∞* B∞`; its self-adjointness is von Neumann's
`T*T` theorem / the Friedrichs representation of this closed form — flagged, not asserted.
-/

open scoped ENNReal BigOperators ComplexConjugate

namespace HelixForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] (c : ℕ → (V →L[ℂ] ℂ))

/-- **The Gram sesquilinear form** `s(f,g) = ⟪B∞ f, B∞ g⟫` representing `G∞`. -/
noncomputable def gramForm (f g : finiteEnergy c) : ℂ :=
  inner ℂ (analysisMap c f) (analysisMap c g)

/-- **The form is non-negative:** `Re s(f,f) ≥ 0`. -/
theorem gramForm_nonneg (f : finiteEnergy c) : 0 ≤ RCLike.re (gramForm c f f) := by
  rw [gramForm]; exact inner_self_nonneg

/-- **The diagonal is `‖B∞ f‖²`** (`= q∞(f)`). -/
theorem gramForm_self_re (f : finiteEnergy c) :
    RCLike.re (gramForm c f f) = ‖analysisMap c f‖ ^ 2 := by
  rw [gramForm]; exact inner_self_eq_norm_sq _

/-- **The form is Hermitian:** `s(f,g) = conj (s(g,f))`. -/
theorem gramForm_hermitian (f g : finiteEnergy c) :
    gramForm c f g = conj (gramForm c g f) := by
  rw [gramForm, gramForm, inner_conj_symm]

/-- The form is additive in its second argument (one slot of sesquilinearity). -/
theorem gramForm_add_right (f g h : finiteEnergy c) :
    gramForm c f (g + h) = gramForm c f g + gramForm c f h := by
  rw [gramForm, gramForm, gramForm, map_add, inner_add_right]

/-- **`B∞` as a densely-defined (partial) operator** `V →ₗ.[ℂ] ℓ²`, with domain the finite-energy
    vectors. (Its adjoint `B∞*` and `G∞ = B∞* B∞` follow via `LinearPMap.adjoint` when `V` is a
    Hilbert space.) -/
noncomputable def Bpmap : V →ₗ.[ℂ] lp (fun _ : ℕ => ℂ) 2 where
  domain := finiteEnergy c
  toFun := analysisMap c

@[simp] theorem Bpmap_domain : (Bpmap c).domain = finiteEnergy c := rfl

@[simp] theorem Bpmap_apply (f : finiteEnergy c) : (Bpmap c) f = analysisMap c f := rfl

end HelixForm
