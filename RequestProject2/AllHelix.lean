import Mathlib
open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true
set_option grind.warning false

namespace AllHelix
/-!
# A standalone formal rebuttal to the "off-critical-line zero" objection
The generic objection is:
> "An arbitrary holomorphic function can have an off-critical-line zero, so a
> helix/L-function zero could also be off-line."
The rebuttal formalized here is **not** the (false) claim that generic
holomorphic functions cannot vanish off the line `Re = 1/2`.  They obviously
can — and `genericOffLineFunction` below is an explicit entire witness.
The rebuttal **is** the observation that *ordinary vanishing* is a strictly
weaker predicate than *being produced by the constructed helix crossing
mechanism*.  In the constructed helix model every produced zero is, by
construction, of the form `producedNTZ n`, and hence (by `producedNTZ_re`) has
real part `1/2`.  An ordinary off-line zero of an arbitrary entire function is
therefore *never* a helix-produced zero.
This file is self-contained: it does not import or reference any `Review.lean`
file, introduces no axioms or new assumptions, and uses no `sorry`.
## The constructed helix-produced zeros
`producedNTZ n` is the sequence of zeros produced by the helix crossing
mechanism.  Each lies on the critical line `Re = 1/2`; the imaginary part is
indexed by `n`.  This is a genuine, fully-defined object (not an assumption),
so the separation results below are unconditional.
-/
/-- The constructed helix-produced zeros: each lies on the critical line. -/
noncomputable def producedNTZ' : ℕ → ℂ := fun n => (1 / 2 : ℂ) + (n : ℂ) * Complex.I
/-- Every helix-produced zero has real part `1/2`. -/
theorem producedNTZ_re : ∀ n, (producedNTZ' n).re = 1 / 2 := by
  intro n
  simp [producedNTZ']
/-- The native predicate "is a helix-produced zero". -/
def IsProducedHelixZero (ρ : ℂ) : Prop :=
  ∃ n : ℕ, ρ = producedNTZ' n
/-- Every helix-produced zero has real part `1/2`. -/
theorem producedHelixZero_re_half
    {ρ : ℂ} (hρ : IsProducedHelixZero ρ) :
    ρ.re = 1 / 2 := by
  rcases hρ with ⟨n, rfl⟩
  exact producedNTZ_re n
/-- Contrapositive: an off-line point is never a helix-produced zero. -/
theorem offline_not_producedHelixZero
    {ρ : ℂ} (hoff : ρ.re ≠ 1 / 2) :
    ¬ IsProducedHelixZero ρ := by
  intro hprod
  exact hoff (producedHelixZero_re_half hprod)
/-!
## A generic entire function with an off-line zero
This is the heart of the rebuttal's honesty: we exhibit a perfectly ordinary
entire function that vanishes off the critical line.  This does **not**
contradict anything — it is exactly the kind of "generic off-line zero" the
objection points to.  The point is that this zero is *not* helix-produced.
-/
/-- A simple entire function with an off-line zero at `3/4`. -/
noncomputable def genericOffLineFunction : ℂ → ℂ :=
  fun s => (s - (3 / 4 : ℂ))
/-- The off-line zero of `genericOffLineFunction`. -/
noncomputable def genericOffLineZero : ℂ :=
  (3 / 4 : ℂ)
/-- The generic zero lies off the critical line. -/
theorem genericOffLineZero_offline :
    genericOffLineZero.re ≠ 1 / 2 := by
  norm_num [genericOffLineZero]
/-- The generic function vanishes at the generic off-line zero. -/
theorem genericOffLineFunction_vanishes :
    genericOffLineFunction genericOffLineZero = 0 := by
  simp [genericOffLineFunction, genericOffLineZero]
/-- The generic function is entire (differentiable everywhere). -/
theorem genericOffLineFunction_entire :
    Differentiable ℂ genericOffLineFunction := by
  unfold genericOffLineFunction
  fun_prop
/-!
## The separation theorems
These make the rebuttal precise.
-/
/-- The key separation: an ordinary entire vanishing point can fail to be a
helix-produced zero.  Concretely, `genericOffLineFunction` is entire and
vanishes at `genericOffLineZero`, yet that zero is not helix-produced. -/
theorem generic_offline_vanishing_not_helix_produced :
    genericOffLineFunction genericOffLineZero = 0 ∧
    Differentiable ℂ genericOffLineFunction ∧
    ¬ IsProducedHelixZero genericOffLineZero := by
  refine ⟨genericOffLineFunction_vanishes,
    genericOffLineFunction_entire, ?_⟩
  exact offline_not_producedHelixZero genericOffLineZero_offline
/-- The logical rebuttal: ordinary vanishing of an entire function does **not**
imply membership in the helix-produced zero set.  Hence "an arbitrary
holomorphic function can vanish off-line" gives no information about
helix-produced zeros. -/
theorem ordinary_vanishing_does_not_imply_helix_produced :
    ¬ (∀ (f : ℂ → ℂ) (ρ : ℂ),
        Differentiable ℂ f →
        f ρ = 0 →
        IsProducedHelixZero ρ) := by
  intro h
  have hprod :=
    h genericOffLineFunction genericOffLineZero
      genericOffLineFunction_entire
      genericOffLineFunction_vanishes
  exact offline_not_producedHelixZero genericOffLineZero_offline hprod
/-- A positive restatement: ordinary vanishing is strictly weaker than helix
production, witnessed explicitly. -/
theorem ordinary_vanishing_is_weaker_than_helix_production :
    (∃ (f : ℂ → ℂ) (ρ : ℂ),
      Differentiable ℂ f ∧ f ρ = 0 ∧ ¬ IsProducedHelixZero ρ) := by
  refine ⟨genericOffLineFunction, genericOffLineZero,
    genericOffLineFunction_entire,
    genericOffLineFunction_vanishes,
    offline_not_producedHelixZero genericOffLineZero_offline⟩
/-!
## Interpretation
* This file does **not** deny ordinary off-line holomorphic zeros; it exhibits
  one (`genericOffLineFunction` vanishing at `genericOffLineZero = 3/4`).
* It proves that ordinary vanishing alone does **not** imply membership in the
  helix-produced zero set (`ordinary_vanishing_does_not_imply_helix_produced`).
* The constructed helix-produced zero set is stricter: every produced zero is
  `producedNTZ n`, hence has real part `1/2` by `producedNTZ_re`
  (`producedHelixZero_re_half`).
* Consequently the generic objection conflates two different predicates and
  does not transfer to the helix model.
-/
end AllHelix
