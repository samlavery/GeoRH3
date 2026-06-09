import Mathlib
import RequestProject.SpectralSide
import RequestProject.FENonExpansionClosure
import RequestProject.GrindF

open Complex

/-! # The Möbius closure: on-line from the non-expansion bound

**The Möbius is the lens, not the engine.** It supplies the coordinate change and the closure —
`‖w ρ‖ = 1 ⟺ Re ρ = ½`, and the reciprocal that turns a bound into membership of the circle — but it
does **not** supply the bound. The GRH content is `‖w ρ‖ ≤ 1`, and that is *exactly* `Re ρ ≥ ½` — every
zero on or to the right of the line (Möbius image in the closed disk). (Not radial non-expansion: that is
`exp((Re ρ − ½)M)` bounded, the opposite sign, `Re ρ ≤ ½`.) With the FE reciprocal pairing `ρ ↔ 1−ρ`, the
`≥ ½` half folds to on-line. So this file proves only the last mile:

* `w(ρ)·w(1−ρ) = 1` — the FE reciprocal (`SpectralSide.w_FE_reciprocal`, proven).
* non-expansion `‖w ρ‖ ≤ 1` `+` the reciprocal ⟹ `‖w ρ‖ = 1`
  (`FEClosure.fe_nonexpansion_closure`, proven: `a·b=1, a≤1, b≤1, a,b≥0 ⟹ a=1`).
* `‖w ρ‖ = 1 ⟺ Re ρ = ½` (`equidistant_iff`, proven: `‖w ρ‖ = ‖ρ−1‖/‖ρ‖`).

The single GRH-strength input is the bound `‖w ρ‖ ≤ 1`; the Möbius does the rest. Naming reflects that:
the theorem is `grh_of_nonExpansion`, not "grh via Möbius". -/

namespace MobiusPath

open HelixReadsGRH GRHSpectral

variable {N : ℕ} [NeZero N]

/-- **Möbius unit circle ⟺ critical line.** `‖w ρ‖ = 1 ↔ Re ρ = ½`, via `‖w ρ‖ = ‖ρ−1‖/‖ρ‖` and
    `equidistant_iff`. -/
theorem w_norm_one_iff {ρ : ℂ} (hρ : ρ ≠ 0) :
    ‖SpectralSide.w ρ‖ = 1 ↔ ρ.re = 1 / 2 := by
  have hw : SpectralSide.w ρ = (ρ - 1) / ρ := by
    rw [SpectralSide.w]; field_simp
  rw [hw, norm_div, div_eq_one_iff_eq (norm_ne_zero_iff.mpr hρ)]
  exact equidistant_iff ρ

/-- **GRH from the non-expansion bound** (the Möbius does the closure, not the work). The GRH-strength
    input is `hNonExpand` (`‖w ρ‖ ≤ 1`); `hFE`/`hne` are standard analytic facts. The Möbius supplies only
    the last mile: reciprocal closure to the unit circle, then unit circle ⟺ on-line. The bound itself is
    exactly `Re ρ ≥ ½` (zero on/right of the line); the FE reciprocal folds it to on-line. That `≥ ½` is
    the conservation/spectral content, and is *not* a Möbius fact. -/
theorem grh_of_nonExpansion (χ : DirichletCharacter ℂ N)
    (hFE : ∀ ρ : ℂ, CompletedLogDerivPole χ ρ → CompletedLogDerivPole χ (1 - ρ))
    (hne : ∀ ρ : ℂ, CompletedLogDerivPole χ ρ → ρ ≠ 0 ∧ (1 - ρ) ≠ 0)
    (hNonExpand : ∀ ρ : ℂ, CompletedLogDerivPole χ ρ → ‖SpectralSide.w ρ‖ ≤ 1) :
    GRH χ := by
  intro ρ hρ
  have hpole : CompletedLogDerivPole χ ρ := hρ
  have h1 : ‖SpectralSide.w ρ‖ = 1 :=
    FEClosure.fe_nonexpansion_closure χ hFE hne hNonExpand ρ hpole
  exact (w_norm_one_iff (hne ρ hpole).1).mp h1

end MobiusPath
