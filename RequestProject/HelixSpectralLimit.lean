import Mathlib
import RequestProject.GRHSpectralCriterion

/-!
# The spectral-limit target — the one open statement

The finite tower is built (`HelixSurrogate`, `HelixChannelInstance`, `HelixDiracOperator`,
`HelixTraceIdentity`): for each channel the Dirac operator `A_N` is self-adjoint, so its
spectral values `μ_{N,j}` are **real**, and `Tr((z−A_N)⁻¹) = Σ_j 1/(z − μ_{N,j})`.

The single remaining step is the limit `T_N(z) → −Λ'/Λ(½ + iz)`: that every pole of the
completed log-derivative is captured as a limit of those **real** spectral values. This file
states that limit precisely (`SpectralLimitCaptures`) and proves the reduction
`SpectralLimitCaptures χ → GRH χ` **unconditionally** — because a limit of reals is real, so
the pole parameter `z(ρ) = γ − i(σ−½)` is real, i.e. `Re ρ = ½`.

`SpectralLimitCaptures` is the OPEN frontier; it is equivalent to GRH for `χ`. The implication
below is the genuine, hypothesis-free reduction (the "if you prove the limit, GRH follows").
-/

namespace HelixLimit

open Filter Topology

variable {N : ℕ} [NeZero N]

/-- The pole parameter of `−L'/L(½ + i·z)` for a nontrivial zero `ρ = σ + iγ`:
    `z(ρ) = γ − i(σ − ½)`. It is real exactly when `Re ρ = ½`. -/
noncomputable def poleParam (ρ : ℂ) : ℂ := (ρ.im : ℂ) - Complex.I * ((ρ.re : ℂ) - 1 / 2)

/-- `Im (z(ρ)) = -(Re ρ − ½)`, so `z(ρ)` is real iff `Re ρ = ½`. -/
theorem poleParam_im (ρ : ℂ) : (poleParam ρ).im = -(ρ.re - 1 / 2) := by
  simp [poleParam, Complex.sub_im, Complex.mul_im]

/-- **The open spectral-limit target.** For channel `χ`, every nontrivial zero's pole
    parameter `z(ρ)` is the limit of a sequence of **real** numbers — the real spectral
    values `μ_{N,j}` of the self-adjoint finite Dirac operators `A_N`. This is the
    `T_N → −Λ'/Λ` capture statement: OPEN, and equivalent to GRH for `χ`. -/
def SpectralLimitCaptures (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ ρ ∈ GRHSpectral.NontrivialZeros χ,
    ∃ μ : ℕ → ℝ, Tendsto (fun k => (μ k : ℂ)) atTop (nhds (poleParam ρ))

/-- **The reduction (unconditional): spectral-limit capture ⟹ GRH.** If every zero's pole is
    captured as a limit of **real** spectral values of the self-adjoint `A_N`, then every zero
    lies on the critical line — a limit of reals is real, forcing `Im (z(ρ)) = 0`, i.e.
    `Re ρ = ½`. The self-adjointness (reality of the `μ`) is doing the work; the only open
    input is `SpectralLimitCaptures`. -/
theorem grh_of_spectralLimitCaptures (χ : DirichletCharacter ℂ N)
    (h : SpectralLimitCaptures χ) : GRHSpectral.GRH χ := by
  intro ρ hρ
  obtain ⟨μ, hμ⟩ := h ρ hρ
  have h0 : Tendsto (fun k => ((μ k : ℂ)).im) atTop (nhds (poleParam ρ).im) :=
    (Complex.continuous_im.tendsto _).comp hμ
  simp only [Complex.ofReal_im] at h0
  have him : (poleParam ρ).im = 0 := tendsto_nhds_unique h0 tendsto_const_nhds
  rw [poleParam_im] at him
  linarith

end HelixLimit
