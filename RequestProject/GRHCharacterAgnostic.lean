import RequestProject.FENonExpansionClosure
import RequestProject.DirichletLZeroSet

/-!
# Character-agnostic GRH reduction

The χ₃ reduction `HelixStrictCompletion.GRH_chi3_of_radial_modes_converge`, made general. For every
self-dual primitive `χ ≠ 1`, GRH(χ) reduces to a single atom: the actual zeros' radial loss modes
`exp((Re ρ − ½)·θ)` converge as the helix winds (`θ → ∞`). The functional-equation pairing
`ρ ↦ 1 − ρ` is supplied generally by `DirichletLHadamard.one_sub_mem_NontrivialZeros_of_selfDual`
(Mathlib's FE), so the **only** remaining obligation — identical for every character — is the
non-divergence `hconv`. χ₃ is one instance; nothing in the reduction is χ₃-specific.
-/

open Complex

namespace GRHCharacterAgnostic

variable {N : ℕ} [NeZero N]

/-- **GRH for any self-dual primitive `χ ≠ 1`, reduced to radial-mode convergence.** The functional
    equation pairs `ρ ↦ 1−ρ` within `χ` (self-dual `χ⁻¹ = χ`, i.e. the real/quadratic characters),
    and FE-symmetrized non-divergence of the radial loss modes forces `Re ρ = ½`. This is the
    character-agnostic form of `GRH_chi3_of_radial_modes_converge`: the lone hypothesis `hconv` — that
    each nontrivial zero's radial mode `exp((Re ρ − ½)·θ)` tends to a finite limit — is the same atom
    for every character. -/
theorem GRH_of_radial_modes_converge_selfDual (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) (hsd : χ⁻¹ = χ)
    (hconv : ∀ ρ : ℂ, HelixReadsGRH.CompletedLogDerivPole χ ρ →
        ∃ L : ℝ, Filter.Tendsto (fun θ : ℝ => Real.exp ((ρ.re - 1 / 2) * θ))
          Filter.atTop (nhds L)) :
    GRHSpectral.GRH χ :=
  fun ρ hρ =>
    FEClosure.fe_tends_towards_closure χ
      (fun _ hρ' => DirichletLHadamard.one_sub_mem_NontrivialZeros_of_selfDual hχ hχp hsd hρ')
      hconv ρ hρ

end GRHCharacterAgnostic
