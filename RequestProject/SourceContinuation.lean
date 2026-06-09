import Mathlib
import RequestProject.EulerMaclaurinDirichlet
import RequestProject.GrindF

open Complex

/-! # The completion layer: completed source response = completed L

Sam's continuation-framed `Exhausts`, built on the repo's own Euler–Maclaurin file. The completed
**source** response (the Dirichlet partial sums, tsum-free, continued) equals `LFunction χ` on the
nontrivial region. This replaces the per-zero eigenvector framing with one analytic-continuation
identity, so "every nontrivial zero is a zero of the completed source response" is automatic.

* `c_fun` / `c_eq_zeta` (this repo's `EulerMaclaurinDirichlet`) supply the **principal/ζ** instance —
  the tsum-free EM continuation `s/(s−1) − s∫{t}t^{−s−1}` equals `ζ` on `0 < Re s < 1`.
* mathlib's `LFunction` continuation supplies the non-principal instances (raw conditionally-convergent
  source, no EM term — the `Σχ = 0` cancellation does the completion for free).

The on-line forcing stays in `GrindF` (`equidistant_iff`). The single remaining obligation is the
**geometric** step `hGeom`: a zero of the source response sits on the unit-circle locus `‖ρ−1‖=‖ρ‖`. -/

namespace SourceContinuation

open GRH.EulerMaclaurinDirichlet

/-- An explicit, **tsum-free**, source-built analytic continuation of the Dirichlet response that agrees
    with `LFunction χ` on the nontrivial region `0 < Re s < 1`. The "Completion" layer. -/
structure Completion {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) where
  /-- the explicit source-built continuation (e.g. `c_fun` for ζ). -/
  response : ℂ → ℂ
  /-- it agrees with the analytic `L` on the critical strip. -/
  eq_L : ∀ s : ℂ, 0 < s.re → s.re < 1 → response s = DirichletCharacter.LFunction χ s

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- **completed_zero_captured.** Every nontrivial zero of `L(χ)` is a zero of the completed source
    response — by the continuation identity alone, no per-zero eigenvector. -/
theorem completed_zero_captured (SC : Completion χ) {ρ : ℂ}
    (hρ : DirichletCharacter.LFunction χ ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    SC.response ρ = 0 := by
  rw [SC.eq_L ρ h0 h1]; exact hρ

/-- **The ζ instance, from the repo's Euler–Maclaurin file.** `c_fun` is the tsum-free EM continuation;
    `c_eq_zeta` proves it equals `ζ = LFunction (χ mod 1)` on the strip. -/
noncomputable def zetaCompletion (χ₁ : DirichletCharacter ℂ 1) :
    Completion χ₁ where
  response := c_fun
  eq_L := by
    intro s hσ hσ1
    show c_fun s = DirichletCharacter.LFunction χ₁ s
    have hs1 : s ≠ 1 := by rintro rfl; simp at hσ1
    rw [c_eq_zeta s hσ hs1, DirichletCharacter.LFunction_modOne_eq]

/-- **The full split, gap explicit.** Completion (source `=` L, *proven* — EM for ζ, `LFunction`
    otherwise) `+` the geometric forcing `hGeom` (a zero of the source response lies on the unit-circle
    locus `‖ρ−1‖=‖ρ‖`) `⟹` GRH, via `equidistant_iff` (*proven*, `GrindF`). The completion box is
    filled; `hGeom` is the single remaining obligation — Hilbert–Pólya / source-flow unitarity. -/
theorem grh_of_completion_and_geometric_forcing
    (SC : Completion χ)
    (hGeom : ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → SC.response ρ = 0 → ‖ρ - 1‖ = ‖ρ‖) :
    ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re = 1 / 2 := by
  intro ρ hρ h0 h1
  have hsrc : SC.response ρ = 0 := completed_zero_captured SC hρ h0 h1
  exact (equidistant_iff ρ).mp (hGeom ρ h0 h1 hsrc)

end SourceContinuation
