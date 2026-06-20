import RequestProject.DirichletLOverPGrowthMain
import RequestProject.DirichletLOverPLogDeriv

/-!
# The Dirichlet-`L` Hadamard partial fraction — UNCONDITIONAL

Capstone: combine the unconditional growth bound `LOverP_growth_meanType` with the growth-conditional
`HadamardPartialFraction_of_LOverP_logSqGrowth` to discharge the last hypothesis. For every primitive
non-principal Dirichlet character `χ`,

  `HadamardPartialFraction χ` :
    `∃ A, ∀ s ∉ NontrivialZeros χ,
       logDeriv (completedLFunction χ) s = A + ∑'_ρ (ord ρ)·(1/(s−ρ) + 1/ρ)`

holds with **no** hypotheses beyond `χ ≠ 1` and `χ.IsPrimitive` — the general-`χ` GRH identification,
classical-analysis–unconditional. Kernel footprint `[propext, Classical.choice, Quot.sound]`.

This is the global Hadamard partial fraction (the "global energy balance" between the geometric
prime-counting/sign-neutralizing canonical product and the spectral log-derivative), assembled from:
order-1 growth ⇒ Jensen ⇒ zero-count ⇒ summability ⇒ Weierstrass product (order-matched, with
partial-fraction log-derivative) ⇒ entire zero-free quotient ⇒ Nevanlinna/Poisson growth ⇒
Borel–Carathéodory constancy.
-/

noncomputable section

namespace DirichletLHadamard

variable {N : ℕ} [NeZero N]

/-- **The Dirichlet-`L` Hadamard partial fraction, unconditional** (primitive `χ ≠ 1`). -/
theorem hadamardPartialFraction {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) :
    HadamardPartialFraction χ :=
  HadamardPartialFraction_of_LOverP_logSqGrowth hχ hχp (LOverP_growth_meanType hχ hχp)

end DirichletLHadamard

#print axioms DirichletLHadamard.hadamardPartialFraction
