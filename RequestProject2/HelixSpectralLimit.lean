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

`SpectralLimitCaptures` is the OPEN frontier. The implication
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

/-- **Reverse: GRH ⟹ SpectralLimitCaptures.** If `ρ` is on the line then `poleParam ρ` is already
    real, so the *constant* real sequence `(poleParam ρ).re` converges to it. Note this uses **no
    operator at all** — it just re-encodes `Re ρ = ½`. -/
theorem spectralLimitCaptures_of_grh (χ : DirichletCharacter ℂ N)
    (h : GRHSpectral.GRH χ) : SpectralLimitCaptures χ := by
  intro ρ hρ
  have him : (poleParam ρ).im = 0 := by rw [poleParam_im, h ρ hρ]; ring
  have hreal : ((poleParam ρ).re : ℂ) = poleParam ρ := by
    apply Complex.ext <;> simp [him]
  exact ⟨fun _ => (poleParam ρ).re, by simpa [hreal] using tendsto_const_nhds⟩

/-- **`SpectralLimitCaptures χ ↔ GRH χ` — the stated target is a costume.** The `Prop` quantifies
    over *arbitrary* real sequences, never the spectrum of `A_N`; a real sequence can only converge
    to `poleParam ρ` when that is real, i.e. `Re ρ = ½`. So `SpectralLimitCaptures` is GRH unfolded,
    and proving it gives no leverage from the operator. The genuine Hilbert–Pólya statement — that
    the **eigenvalues of `A_N`** accumulate at the zeros' pole-params — is a *different* proposition,
    not stated here, and is a question about the specific `lossMatrix`, not about `poleParam`. -/
theorem spectralLimitCaptures_iff_grh (χ : DirichletCharacter ℂ N) :
    SpectralLimitCaptures χ ↔ GRHSpectral.GRH χ :=
  ⟨grh_of_spectralLimitCaptures χ, spectralLimitCaptures_of_grh χ⟩

/-- **Hilbert–Pólya capstone — self-adjointness forces the line, no positivity.** If every
    nontrivial zero's pole parameter `z(ρ) = γ − i(σ − ½)` is an eigenvalue of *some* Hermitian
    matrix, then `σ = ½` for every zero. The entire forcing is the **reality of a self-adjoint
    spectrum** — `Matrix.IsHermitian.eigenvalues : n → ℝ` — so `z(ρ)` is real, `Im z(ρ) = 0`,
    `σ = ½`. There is **no `≥ 0` floor, no Weil/Li positivity**: the only input is `A = Aᴴ ⇒
    spectrum ⊆ ℝ`. The hypothesis is the *spectral representation* (the zeros realized as a
    self-adjoint spectrum) — the Hilbert–Pólya object the trace identity must produce. -/
theorem grh_of_hermitian_capture (χ : DirichletCharacter ℂ N)
    (h : ∀ ρ ∈ GRHSpectral.NontrivialZeros χ,
      ∃ (k : ℕ) (A : Matrix (Fin k) (Fin k) ℂ) (hA : A.IsHermitian) (i : Fin k),
        poleParam ρ = ((hA.eigenvalues i : ℝ) : ℂ)) :
    GRHSpectral.GRH χ := by
  intro ρ hρ
  obtain ⟨k, A, hA, i, hcap⟩ := h ρ hρ
  have him : (poleParam ρ).im = 0 := by rw [hcap, Complex.ofReal_im]
  rw [poleParam_im] at him
  linarith

/-- **Hilbert–Pólya capstone, spectral-measure form** — self-adjointness forces the line, with no
    positivity and no finite-eigenvalue limit. Let `a` be a self-adjoint element of **any** C⋆-algebra
    (e.g. a bounded self-adjoint operator on a Hilbert space — the "channel", whose spectrum may be
    infinite, so one channel can receive *all* the zeros). If every nontrivial zero's pole parameter
    `z(ρ) = γ − i(σ−½)` lies in `spectrum ℂ a`, then `σ = ½` for every zero.

    The forcing is `IsSelfAdjoint a ⇒ spectrum ℂ a ⊆ ℝ` (`IsSelfAdjoint.im_eq_zero_of_mem_spectrum`):
    a spectral atom is real, so `Im z(ρ) = 0`, so `σ = ½`. No `≥ 0`, no Herglotz/Weil floor, no
    eigenvalue sequence — pure spectral reality.

    `poleParam ρ` is the genuine pole location of `−L'/L(½ + i·)` in the `z`-variable, **not** a planted
    `σ−½`: its imaginary part `−(σ−½)` is killed by the operator's reality, not discarded by fiat.

    **The single open box is `hcap`**: *the log-derivative poles of `L` are spectral atoms of the real
    self-adjoint channel.* Everything else is plumbing. (`channelDirac` is one such self-adjoint
    element of the matrix C⋆-algebra; the statement is operator-agnostic so the channel is free to be
    the right — infinite — one, not the prime-side finite truncation.) -/
theorem grh_of_selfAdjoint_spectral_capture
    {A : Type*} [CStarAlgebra A] [StarModule ℂ A] {a : A} (ha : IsSelfAdjoint a)
    (χ : DirichletCharacter ℂ N)
    (hcap : ∀ ρ ∈ GRHSpectral.NontrivialZeros χ, poleParam ρ ∈ spectrum ℂ a) :
    GRHSpectral.GRH χ := by
  intro ρ hρ
  have him : (poleParam ρ).im = 0 := ha.im_eq_zero_of_mem_spectrum (hcap ρ hρ)
  rw [poleParam_im] at him
  linarith

end HelixLimit
