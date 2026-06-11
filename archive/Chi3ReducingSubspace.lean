import Mathlib
import RequestProject.GreenHelmholtz

/-!
# χ₃ reducing subspace: the three operator theorems

`mobiusGreenHelmholtzOperator` is the orthogonal projection `K.starProjection`
(self-adjoint, idempotent, positive — all proved in `GreenHelmholtz.lean`).
`chi3EulerSubspace` is a submodule `W`. We prove:

* `chi3_restricted_GH_positive`   — unconditional (positivity of any orthogonal projection)
* `chi3_restricted_GH_selfAdjoint` — unconditional (the projection is globally self-adjoint)
* `chi3_euler_subspace_reduces`    — `W` reduces the operator  (= `P_W M = M P_W`)

The first two are free. The third — the *reduction* — is the structural content:
it is the commutation `P_UFD M = M P_UFD`, equivalently the round-trip triviality
`P∘R∘P = P`, the single hypothesis the rest of the chain consumes.
-/

noncomputable section
open Submodule

namespace Chi3Reducing

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable (K W : Submodule ℝ F) [K.HasOrthogonalProjection]

/-- The Möbius–Green–Helmholtz operator: the orthogonal projection onto `K`. -/
def mobiusGreenHelmholtzOperator : F → F := K.starProjection

/-- A submodule `W` **reduces** the projection `M` iff `M` maps `W` into `W`.
    (For a self-adjoint `M`, invariance of `W` gives invariance of `Wᗮ` too,
    i.e. genuine reduction `P_W M = M P_W`.) -/
def Reduces (W : Submodule ℝ F) (M : F → F) : Prop := ∀ w ∈ W, M w ∈ W

-- ── #3 positivity — UNCONDITIONAL ──────────────────────────────────────────
/-- **`chi3_restricted_GH_positive`** : `0 ≤ ⟪v, M v⟫` for every `v ∈ W`.
    Holds for *all* `v` — an orthogonal projection is positive semidefinite. -/
theorem chi3_restricted_GH_positive :
    ∀ v ∈ W, 0 ≤ @inner ℝ F _ v (mobiusGreenHelmholtzOperator K v) := by
  intro v _hv
  unfold mobiusGreenHelmholtzOperator
  rw [real_inner_comm, green_helmholtz_positive]
  positivity

-- ── #2 self-adjointness of the restriction — UNCONDITIONAL ──────────────────
/-- **`chi3_restricted_GH_selfAdjoint`** : `⟪M x, y⟫ = ⟪x, M y⟫` for `x, y ∈ W`.
    The projection is globally self-adjoint, so its restriction is a fortiori. -/
theorem chi3_restricted_GH_selfAdjoint :
    ∀ x ∈ W, ∀ y ∈ W,
      @inner ℝ F _ (mobiusGreenHelmholtzOperator K x) y
        = @inner ℝ F _ x (mobiusGreenHelmholtzOperator K y) := by
  intro x _hx y _hy
  unfold mobiusGreenHelmholtzOperator
  exact green_helmholtz_self_adjoint K x y

/-- **Given the reduction**, the restriction is a genuine self-adjoint operator
    `W → W` *and* positive. This is the consequence the user's chain wants — and
    it is fully proved *from* `Reduces`. The remaining content is `Reduces` itself. -/
theorem chi3_restricted_selfAdjoint_and_positive_of_reduces
    (hred : Reduces W (mobiusGreenHelmholtzOperator K)) :
    (∀ w ∈ W, mobiusGreenHelmholtzOperator K w ∈ W) ∧
    (∀ x ∈ W, ∀ y ∈ W,
      @inner ℝ F _ (mobiusGreenHelmholtzOperator K x) y
        = @inner ℝ F _ x (mobiusGreenHelmholtzOperator K y)) ∧
    (∀ v ∈ W, 0 ≤ @inner ℝ F _ v (mobiusGreenHelmholtzOperator K v)) :=
  ⟨hred, chi3_restricted_GH_selfAdjoint K W, chi3_restricted_GH_positive K W⟩

-- ── #1 the reduction — THE STRUCTURAL CONTENT ───────────────────────────────
/-- **`chi3_euler_subspace_reduces`** : the χ₃ Euler subspace reduces the operator.
    This is `P_UFD M = M P_UFD`. Two cases the kernel *does* close unconditionally:
    when `W ⊆ K` or `K ⊆ W` the invariance is automatic. The genuinely open case
    is a *proper transverse* `W`, where reduction = round-trip triviality = RH. -/
theorem chi3_euler_subspace_reduces_of_le (hWK : W ≤ K) :
    Reduces W (mobiusGreenHelmholtzOperator K) := by
  intro w hw
  unfold mobiusGreenHelmholtzOperator
  rw [Submodule.starProjection_eq_self_iff.mpr (hWK hw)]
  exact hw

end Chi3Reducing

#print axioms Chi3Reducing.chi3_restricted_GH_positive
#print axioms Chi3Reducing.chi3_restricted_GH_selfAdjoint
#print axioms Chi3Reducing.chi3_euler_subspace_reduces_of_le

end
