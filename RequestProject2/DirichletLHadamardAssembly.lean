import RequestProject.DirichletLProductMultPartialFraction

/-!
# Final assembly: `HadamardPartialFraction χ` from the constancy of the log-derivative difference

This wires the unconditional bricks built in this port — the multiplicity-weighted Weierstrass product
`LProductMult χ`, its order-matching `analyticOrderAt (LProductMult χ) ρ = lOrderNat χ ρ`, and its
log-derivative partial fraction `logDeriv (LProductMult χ) s = ∑'_ρ ord(ρ)·(1/(s−ρ)+1/ρ)` — into the
**target** `HadamardPartialFraction χ` (the general-`χ` GRH identification, Step 7).

The reduction is exact: `HadamardPartialFraction χ` holds **iff** the log-derivative difference
`logDeriv Λ_χ − logDeriv (LProductMult χ)` is constant off the nontrivial zeros. The forward direction
here is unconditional; the constancy hypothesis is the *one* remaining classical input — the Hadamard
constancy for the entire zero-free quotient `Λ_χ / LProductMult χ` of order ≤ 1, whose remaining
ingredient is the Nevanlinna growth bound on that quotient (`XiOverPGrowth`-style proximity argument,
character-agnostic in structure; the `Λ_χ` upper bound is `completedL_order_one_log_bound`).

Mirror of `WeilHadamardOpenPatch.xi_logDeriv_partial_fraction_of_diff_const_on_open`, but stated
globally on the whole zero-free complement (matching the global `HadamardPartialFraction` target).
-/

open Complex

noncomputable section

namespace DirichletLHadamard

variable {N : ℕ} [NeZero N]

/-- **Final assembly (constancy ⇒ partial fraction).** If the log-derivative difference
`logDeriv Λ_χ − logDeriv (LProductMult χ)` is constant `= A` off the nontrivial zeros, then the
Hadamard partial fraction holds with that same constant `A`. Unconditional given the product-side
partial fraction `logDeriv_LProductMult_partial_fraction`. -/
theorem HadamardPartialFraction_of_diff_const {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hχp : χ.IsPrimitive)
    (hconst : ∃ A : ℂ, ∀ s : ℂ, s ∉ GRHSpectral.NontrivialZeros χ →
      logDeriv (DirichletCharacter.completedLFunction χ) s - logDeriv (LProductMult χ) s = A) :
    HadamardPartialFraction χ := by
  obtain ⟨A, hA⟩ := hconst
  refine ⟨A, ?_⟩
  intro s hs
  have h_pf := logDeriv_LProductMult_partial_fraction hχ hχp hs
  have h_diff := hA s hs
  calc logDeriv (DirichletCharacter.completedLFunction χ) s
      = (logDeriv (DirichletCharacter.completedLFunction χ) s - logDeriv (LProductMult χ) s)
          + logDeriv (LProductMult χ) s := by ring
    _ = A + logDeriv (LProductMult χ) s := by rw [h_diff]
    _ = A + ∑' ρ : {ρ : ℂ // ρ ∈ GRHSpectral.NontrivialZeros χ},
          (lOrderNat χ ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val) := by rw [h_pf]

end DirichletLHadamard

#print axioms DirichletLHadamard.HadamardPartialFraction_of_diff_const
