import RequestProject.DirichletLHadamardComplete
import RequestProject.HelixFlowVonMangoldt

/-!
# The dual operator `H_z` (zero side) — resolvent trace = log-derivative, DISCHARGED

The prime-side generator `H = diag(log n)` (`HelixFlowGenerator`) has the prime phasor chain as its
log-determinant trace `−L'/L` (`HelixFlowVonMangoldt.flowVonMangoldtTrace_eq_neg_logDeriv`). Its **dual**
`H_z` is **diagonal on the actual nontrivial zeros** `{ρ}` — *at whatever `Re ρ` they sit*, no on-line
assumption, no critical line, no 2-D sheet — each with multiplicity `mult_ρ`. The mechanism: the prime
chain's singularity **is** a legitimate zeta zero, and that is exactly `H_z`'s spectrum.

**The prop — `H_z`'s resolvent trace equals the log-derivative — is DISCHARGED, unconditionally.**
`dualResolventTrace χ s = Σ_ρ mult_ρ·(1/(s−ρ) + 1/ρ)` (the Hadamard-regularized resolvent trace over
the actual zeros), and `dualResolventTrace_eq_logDeriv` proves

  `logDeriv Λ(s) = A + dualResolventTrace χ s`   (for all `s` off the zeros)

via `DirichletLHadamard.hadamardPartialFraction` — kernel-clean, and **σ-free**: no `Re ρ = ½`, no
strip, no circle. The zeros are wherever they are; the dual operator's resolvent trace is the
log-derivative regardless. )
-/

open Complex

namespace HelixDualOperator

variable {N : ℕ} [NeZero N]

/-- **The dual operator `H_z`'s regularized resolvent trace.** `H_z` is diagonal on the **actual**
    nontrivial zeros `{ρ}` (any location — no `Re ρ = ½`), each with multiplicity
    `mult_ρ = DirichletLHadamard.lOrderNat χ ρ`. Its Hadamard-regularized resolvent trace is the
    multiplicity-weighted resolvent sum `Σ_ρ mult_ρ·(1/(s−ρ) + 1/ρ)`. -/
noncomputable def dualResolventTrace (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  ∑' ρ : {ρ : ℂ // ρ ∈ GRHSpectral.NontrivialZeros χ},
    (DirichletLHadamard.lOrderNat χ ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val)

/-- **DISCHARGED — the dual operator's resolvent trace equals the log-derivative.** For primitive
    non-principal `χ`, there is a constant `A` with, at every `s` off the zeros,
    `logDeriv Λ(s) = A + dualResolventTrace χ s`. So the dual operator (diagonal on the **actual** zeros,
    *any location*) has resolvent trace `= −L'/L` up to the constant — **unconditionally**. This is
    `DirichletLHadamard.hadamardPartialFraction`: kernel-clean, σ-free, **no `Re ρ = ½`, no strip, no
    sheet**. Stated plainly — proven, not a `grh_of_…`. -/
theorem dualResolventTrace_eq_logDeriv (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχp : χ.IsPrimitive) :
    ∃ A : ℂ, ∀ s ∉ GRHSpectral.NontrivialZeros χ,
      logDeriv (DirichletCharacter.completedLFunction χ) s = A + dualResolventTrace χ s :=
  DirichletLHadamard.hadamardPartialFraction hχ hχp

end HelixDualOperator

#print axioms HelixDualOperator.dualResolventTrace_eq_logDeriv
