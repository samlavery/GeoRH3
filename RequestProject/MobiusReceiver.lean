import RequestProject.HelixSource
import RequestProject.MobiusPath
import RequestProject.SelfDual

open Complex

namespace MobiusReceiver

open HelixSource GRHSpectral

variable {N : ℕ} [NeZero N]

/-! # Self-dual by Möbius — the self-dual axis, never GRH

Framing correction: **the Möbius supplies self-duality, not GRH.** Its entire content is that the
**self-dual unit circle `‖w‖ = 1` is the critical line `Re = ½`** (`w_norm_one_iff`) — an
*identification of loci*, a self-dual fact. It places no zero. GRH — the zeros actually *sitting* on
that locus — is the **coincidence of singularities** (`SourceComplete`), discharged by
`grh_of_sourceComplete`. The Möbius is the self-dual lens; there is no "GRH by Möbius." -/

/-- A nontrivial zero is **on the self-dual circle** when its Möbius image lies on the unit circle. -/
def OnSelfDualCircle (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ ρ ∈ NontrivialZeros χ, ‖SpectralSide.w ρ‖ = 1

/-- **Self-dual by Möbius: the self-dual circle is the critical line.** For a nontrivial zero,
    `‖w ρ‖ = 1 ⟺ Re ρ = ½`. The Möbius identifies the self-dual locus with the line — that is all it
    does. It names the locus; it does not put the zero on it. -/
theorem selfDualCircle_eq_critical (χ : DirichletCharacter ℂ N) {ρ : ℂ}
    (hρ : ρ ∈ NontrivialZeros χ) :
    ‖SpectralSide.w ρ‖ = 1 ↔ ρ.re = 1 / 2 :=
  MobiusPath.w_norm_one_iff (nontrivial_ne_zero hρ)

/-- **The coincidence places the zeros on the self-dual circle** — and this, not the Möbius, is the
    GRH-bearing step. If every spectral singularity is a geometric one (`SourceComplete`), each zero's
    Möbius image lands on the unit circle, because its source mode is on `Re = ½` (`poleCoord_re`).
    The Möbius only supplies the self-dual circle it lands on; the *placement* is the coincidence. -/
theorem onSelfDualCircle_of_sourceComplete (χ : DirichletCharacter ℂ N) (h : SourceComplete χ) :
    OnSelfDualCircle χ := by
  intro ρ hρ
  obtain ⟨ψ, hψ⟩ := h ρ hρ
  rw [MobiusPath.w_norm_one_iff (nontrivial_ne_zero hρ), hψ]
  exact ψ.poleCoord_re

end MobiusReceiver
