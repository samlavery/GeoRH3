import Mathlib
import RequestProject.GRHSpectralCriterion
import RequestProject.HelixProjectionEigenvalue
import RequestProject.NoOfflineZeros

/-!
# GRH ⟺ Li positivity (zero side)

Li's criterion for `L(s,χ)`, stated on the zero side and kept clean of the prime side:
the paired Li coefficient `(1 − w(ρ)ⁿ) + (1 − w(1−ρ)ⁿ)` is a quantity built from the
**peaks** (the zeros), and

* on the line it is `≥ 0` (`on_line_pair_nonneg`);
* off the line it is unbounded below (`eigenvalue_projection_forces_line`'s engine),

so `GRH χ ⟺ every paired Li coefficient is nonnegative`.
-/

noncomputable section
open Complex DirichletCharacter

namespace GRHLi

variable {N : ℕ} [NeZero N]

/-- **GRH(χ) ⟺ Li positivity on the χ-zeros.** For nontrivial zeros with nonzero
    imaginary part, GRH holds ⟺ every paired Li coefficient is nonnegative — Li's
    criterion, entirely on the zero side (the peaks). -/
theorem GRH_iff_li_positivity (χ : DirichletCharacter ℂ N)
    (hγ : ∀ ρ ∈ GRHSpectral.NontrivialZeros χ, ρ.im ≠ 0) :
    GRHSpectral.GRH χ ↔
      (∀ ρ ∈ GRHSpectral.NontrivialZeros χ, ∀ n : ℕ,
        0 ≤ (li_helix_term ρ.re ρ.im n).re +
            (li_helix_term (1 - ρ.re) (-ρ.im) n).re) := by
  constructor
  · intro h ρ hρ n
    have hσ : ρ.re = 1 / 2 := h ρ hρ
    rw [hσ]
    exact on_line_pair_nonneg ρ.im n
  · intro h ρ hρ
    exact eigenvalue_projection_forces_line ρ.re ρ.im (hγ ρ hρ) (h ρ hρ)

end GRHLi

#print axioms GRHLi.GRH_iff_li_positivity
