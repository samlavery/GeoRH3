import RequestProject.SpectralEquivalence
/-!
# The unconditional Frobenius eigenstate: the Hilbert–Pólya self-adjoint design is real & self-adjoint
The previous file `SpectralEquivalence.lean` proved that *producing* a Hilbert–Pólya spectral
realisation of the nontrivial zeros is **logically equivalent to GRH** — a true statement, but
not a new theorem (it is a restatement of the open problem).
This file isolates the part of the Hilbert–Pólya picture that is **genuinely unconditional** and
requires neither GRH nor the infinitude of zeros: the self-adjoint *design* itself — the
real-diagonal "Gram / von Neumann" multiplication operator — together with an explicit
**Frobenius eigenstate**.  Concretely we prove, with no number-theoretic hypothesis whatsoever:
* **Self-adjoint.**  The real-diagonal operator `diagOp d` on the ℓ²-space `ι →₀ ℂ` is symmetric
  (`DiagModel.diagOp_symmetric`), as is the one-dimensional fiber operator
  `vonNeumannOp γ` (`vonNeumannOp_isSymmetric`).
* **Real.**  Von Neumann reality: *every* eigenvalue of these self-adjoint operators has zero
  imaginary part (`diagOp_spectrum_real`, `vonNeumannOp_spectrum_real`).  This is the "the design
  is real" deliverable — the spectrum lives on the real axis unconditionally.
* **An explicit unconditional Frobenius eigenstate.**  For each index `i`, the basis vector
  `single i 1` is a genuine *nonzero* eigenvector of `diagOp d` with the *real* eigenvalue `d i`
  (`diagOp_eigenvector`); and for each real height `γ`, the unit-energy spectral wave
  `t ↦ exp(i γ t)` is a Frobenius eigenstate of the self-adjoint generator `D = -i d/dt` with the
  real eigenvalue `γ` (`frobenius_spectralWave_eigenstate`).
The capstone `hilbertPolya_design_real_selfAdjoint` packages "real and self-adjoint, with an
explicit Frobenius eigenstate" into a single unconditional statement, and
`unconditional_frobenius_eigenstate` records the spectral-wave incarnation.  No `axiom`, no
`sorry`, no GRH.
-/
open Complex
open CriticalLinePhasor
open CriticalLinePhasor.Faithfulness.DiagModel
namespace CriticalLinePhasor.UnconditionalFrobenius
/-! ## 1. The real-diagonal "Gram / von Neumann" design on `ι →₀ ℂ` -/
section DiagDesign
variable {ι : Type*}
/-- **Explicit Frobenius eigenstate of the real-diagonal design.**  For each index `i`, the basis
vector `single i 1` is a *nonzero* eigenvector of the real-diagonal operator `diagOp d`, and the
operator acts on it by multiplication by the *real* scalar `d i`.  No hypotheses. -/
theorem diagOp_eigenvector (d : ι → ℝ) (i : ι) :
    Finsupp.single i (1 : ℂ) ≠ 0 ∧
      diagOp d (Finsupp.single i (1 : ℂ)) = (d i : ℂ) • Finsupp.single i (1 : ℂ) := by
  refine ⟨Finsupp.single_ne_zero.mpr one_ne_zero, ?_⟩
  rw [diagOp_single]
  simp [Finsupp.smul_single]
/-- **The real-diagonal design has real spectrum (Von Neumann reality).**  Every eigenvalue of the
self-adjoint operator `diagOp d` has zero imaginary part, i.e. the spectrum lies on the real axis.
Unconditional. -/
theorem diagOp_spectrum_real (d : ι → ℝ) {μ : ℂ}
    (hμ : Module.End.HasEigenvalue (diagOp d) μ) : μ.im = 0 :=
  CriticalLinePhasor.Faithfulness.HilbertPolya.symmetric_eigenvalue_real
    (diagOp_symmetric d) hμ
/-- **The Hilbert–Pólya self-adjoint "Gram / von Neumann" design is real and self-adjoint, with an
explicit unconditional Frobenius eigenstate.**
For the universal real-diagonal multiplication operator `diagOp d` on the ℓ²-space `ι →₀ ℂ`,
*without any number-theoretic hypothesis* (no GRH, no infinitude of zeros):
1. it is **self-adjoint** (symmetric);
2. it is **real**: every eigenvalue has zero imaginary part (Von Neumann reality); and
3. it carries, for every index `i`, an explicit **Frobenius eigenstate** — the nonzero
   eigenvector `single i 1` with the *real* eigenvalue `d i`, which is genuinely in the
   spectrum and has zero imaginary part. -/
theorem hilbertPolya_design_real_selfAdjoint (d : ι → ℝ) :
    (diagOp d).IsSymmetric
      ∧ (∀ μ : ℂ, Module.End.HasEigenvalue (diagOp d) μ → μ.im = 0)
      ∧ (∀ i : ι,
          Finsupp.single i (1 : ℂ) ≠ 0
            ∧ diagOp d (Finsupp.single i (1 : ℂ)) = (d i : ℂ) • Finsupp.single i (1 : ℂ)
            ∧ Module.End.HasEigenvalue (diagOp d) (d i : ℂ)
            ∧ ((d i : ℂ)).im = 0) := by
  refine ⟨diagOp_symmetric d, fun μ hμ => diagOp_spectrum_real d hμ, fun i => ?_⟩
  obtain ⟨hne, hact⟩ := diagOp_eigenvector d i
  exact ⟨hne, hact, diagOp_hasEigenvalue d i, by simp⟩
end DiagDesign
/-! ## 2. The spectral-wave Frobenius eigenstate on the fiber `ℂ` -/
/-- **Unconditional Frobenius eigenstate (spectral-wave incarnation).**  For *every* real height
`γ` — with no GRH and no infinitude-of-zeros hypothesis — the unit-energy spectral wave
`t ↦ exp(i γ t)` is a genuine eigenstate of the self-adjoint generator `D = -i d/dt` with the
*real* eigenvalue `γ` and matched (constant unit) energy; and the one-dimensional fiber operator
`vonNeumannOp γ` is self-adjoint with `γ` as its real eigenvalue. -/
theorem frobenius_spectralWave_eigenstate (γ : ℝ) :
    (∀ t : ℝ, ‖FrobeniusEigenstate.spectralWave γ t‖ = 1)
      ∧ (∀ t : ℝ, -Complex.I * deriv (FrobeniusEigenstate.spectralWave γ) t
            = (γ : ℂ) * FrobeniusEigenstate.spectralWave γ t)
      ∧ (HilbertPolya.vonNeumannOp γ).IsSymmetric
      ∧ Module.End.HasEigenvalue (HilbertPolya.vonNeumannOp γ) (γ : ℂ) :=
  FrobeniusEigenstate.frobeniusEigenstate_realization γ
/-- **The fiber von Neumann operator has real spectrum.**  Every eigenvalue of the self-adjoint
operator `vonNeumannOp γ` has zero imaginary part. Unconditional. -/
theorem vonNeumannOp_spectrum_real (γ : ℝ) {μ : ℂ}
    (hμ : Module.End.HasEigenvalue (HilbertPolya.vonNeumannOp γ) μ) : μ.im = 0 :=
  CriticalLinePhasor.Faithfulness.HilbertPolya.symmetric_eigenvalue_real
    (HilbertPolya.vonNeumannOp_isSymmetric γ) hμ
/-- **The unconditional Frobenius eigenstate, assembled.**  For every real height `γ`, with no
GRH and no infinitude-of-zeros input, there is a self-adjoint fiber operator `vonNeumannOp γ`
that is **real** (its spectrum has zero imaginary part) and a genuine **Frobenius eigenstate**:
the matched-energy spectral wave `t ↦ exp(i γ t)` realising the real eigenvalue `γ` of the
generator `D = -i d/dt`. -/
theorem unconditional_frobenius_eigenstate (γ : ℝ) :
    (HilbertPolya.vonNeumannOp γ).IsSymmetric
      ∧ (∀ μ : ℂ, Module.End.HasEigenvalue (HilbertPolya.vonNeumannOp γ) μ → μ.im = 0)
      ∧ Module.End.HasEigenvalue (HilbertPolya.vonNeumannOp γ) (γ : ℂ)
      ∧ (∀ t : ℝ, ‖FrobeniusEigenstate.spectralWave γ t‖ = 1)
      ∧ (∀ t : ℝ, -Complex.I * deriv (FrobeniusEigenstate.spectralWave γ) t
            = (γ : ℂ) * FrobeniusEigenstate.spectralWave γ t) := by
  obtain ⟨hnorm, heig, hsym, hev⟩ := frobenius_spectralWave_eigenstate γ
  exact ⟨hsym, fun μ hμ => vonNeumannOp_spectrum_real γ hμ, hev, hnorm, heig⟩
end CriticalLinePhasor.UnconditionalFrobenius
