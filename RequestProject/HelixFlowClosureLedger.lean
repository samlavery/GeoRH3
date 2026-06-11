import RequestProject.HelixFlowUnitaryGroup
import RequestProject.DirichletClosureLedger

/-!
# Splicing the flow fibre phasor chain through the closure ledger

The flow fibre phasor chain `Σ_{n≤M} χ(n)·n^{-σ}·U(t)(n)⁻¹` (the unitary flow `HelixFlow.phasorFlow`
weighted by the character fibre) **is** the closure-ledger partial sum `LM χ s M` — the phasor
`U(t)(n)⁻¹ = n^{-it}` rebuilds `n^{-s}` from the radial `n^{-σ}`. So the chain inherits, verbatim, the
closure ledger of `DirichletClosureLedger`:

* `flow_rate_bound` — the chain **continues itself into the strip** `0 < Re s`, converging to `L(χ,s)`
  at rate `M^{-σ}` (the helix's own continuation, no external analytic input).
* `flow_chain_vanishes_at_zero` — at a zero the chain **tends to 0**: the fibre phasors cancel, and
  that cancellation event is the zero.
* `flow_closure_error_at_zero` — the **height-free ledger**: the rescaled chain `·M^s` differs from the
  running fibre imbalance `A(M) = Σ_{n≤M}χ(n)` by `O(1)`, and `A(M)` is **free of `Im s`** — every zero,
  at every height `t`, carries the same ledger. (The striking t-invariant fact.)

For non-principal `χ` (`χ ≠ 1`) — the clean case, where the running imbalance is bounded.
-/

open Complex HelixFlow DirichletClosureLedger

namespace HelixFlowClosureLedger

variable {N : ℕ} [NeZero N]

/-- The flow fibre phasor chain's partial sum: `Σ_{n≤M} χ(n)·n^{-σ}·U(t)(n)⁻¹`. -/
noncomputable def flowPartialSum (χ : DirichletCharacter ℂ N) (s : ℂ) (M : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 0 M,
    χ (n : ZMod N) * (((n : ℝ) ^ s.re : ℝ) : ℂ)⁻¹ * (phasorFlow s.im n : ℂ)⁻¹

/-- **The flow chain IS the closure-ledger chain**: `flowPartialSum χ s M = LM χ s M`. The phasor
    `U(t)(n)⁻¹ = n^{-it}` rebuilds `n^{-s}` from the radial weight `n^{-σ}` (the `n = 0` term vanishes,
    `χ 0 = 0`). -/
theorem flowPartialSum_eq_LM (χ : DirichletCharacter ℂ N) (hN : N ≠ 1) (s : ℂ) (M : ℕ) :
    flowPartialSum χ s M = LM χ s M := by
  rw [flowPartialSum, LM]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rcases eq_or_ne n 0 with hn | hn
  · subst hn
    simp [DirichletCharacter.map_zero' χ hN]
  · rw [phasorFlow_eq_cpow s.im n hn]
    have hsplit : (((n : ℝ) ^ s.re : ℝ) : ℂ) * (n : ℂ) ^ (Complex.I * (s.im : ℂ)) = (n : ℂ) ^ s := by
      rw [show (((n : ℝ) ^ s.re : ℝ) : ℂ) = (n : ℂ) ^ (s.re : ℂ) from by
            rw [Complex.ofReal_cpow (by positivity)]; push_cast; ring,
          ← Complex.cpow_add _ _ (by exact_mod_cast hn)]
      congr 1
      rw [mul_comm Complex.I (s.im : ℂ)]; exact Complex.re_add_im s
    rw [mul_assoc, ← mul_inv, hsplit, ← Complex.cpow_neg]

/-- **The chain reaches `L` in the strip.** For `Re s > 0` (non-principal `χ`) the flow fibre phasor
    chain converges to `L(χ,s)` at rate `M^{-σ}`: `‖flowPartialSum − L‖ ≤ C·M^{-σ}`. The chain winds up
    the lattice into the strip — the helix's own continuation (`DirichletClosureLedger.rate_bound`). -/
theorem flow_rate_bound (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (s : ℂ)
    (hσ : 0 < s.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 1 ≤ M →
      ‖flowPartialSum χ s M - DirichletCharacter.LFunction χ s‖ ≤ C * (M : ℝ) ^ (-s.re) := by
  obtain ⟨C, hC, hbound⟩ := rate_bound χ hχ s hσ
  refine ⟨C, hC, fun M hM => ?_⟩
  rw [flowPartialSum_eq_LM χ (modulus_ne_one χ hχ) s M]
  exact hbound M hM

/-- **The chain vanishes at a zero — the cancellation event.** At a zero `L(χ,s) = 0` (`Re s > 0`) the
    flow fibre phasor chain tends to `0`: `‖flowPartialSum‖ ≤ C·M^{-σ} → 0`. The fibre phasors cancel,
    and that vanishing **is** the zero. -/
theorem flow_chain_vanishes_at_zero (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (s : ℂ)
    (hσ : 0 < s.re) (hzero : DirichletCharacter.LFunction χ s = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 1 ≤ M → ‖flowPartialSum χ s M‖ ≤ C * (M : ℝ) ^ (-s.re) := by
  obtain ⟨C, hC, hbound⟩ := flow_rate_bound χ hχ s hσ
  refine ⟨C, hC, fun M hM => ?_⟩
  have h := hbound M hM
  rwa [hzero, sub_zero] at h

/-- **The height-free ledger at a zero — the striking t-invariant fact.** At a zero (`Re s > 0`), the
    rescaled flow chain `flowPartialSum·M^s` differs from the running fibre imbalance
    `A(M) = Σ_{n≤M}χ(n)` by a uniformly bounded amount: `‖flowPartialSum·M^s − A(M)‖ ≤ C`. The leading
    object `A(M)` is **free of the height `Im s`** — the height lives only in the unit phase `M^{-it}`.
    So every zero, at every height `t`, carries the **same** ledger
    (`DirichletClosureLedger.closure_error_bounded_at_zero`). -/
theorem flow_closure_error_at_zero (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (s : ℂ)
    (hσ : 0 < s.re) (hzero : DirichletCharacter.LFunction χ s = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 1 ≤ M →
      ‖flowPartialSum χ s M * (M : ℂ) ^ s - Asum χ M‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := closure_error_bounded_at_zero χ hχ s hσ hzero
  refine ⟨C, hC, fun M hM => ?_⟩
  rw [flowPartialSum_eq_LM χ (modulus_ne_one χ hχ) s M]
  exact hbound M hM

/-- **The EXACT t-invariant ledger on the flow chain** (the finished universalization). At a zero
    (`Re s > 0`) the rescaled flow fibre phasor chain converges to the fibre imbalance against the
    channel constant `L(0,χ)`, at rate `O(M^{-1})`:
    `‖flowPartialSum·M^s − (A(M) − L(0,χ))‖ ≤ C·M^{-1}`. The invariant `A(M) − L(0,χ)` is a property of
    the **fibre / L-function**, NOT of the zero: `A(M) = Σ_{n≤M} χ(n)` is the running character-sum
    imbalance and `L(0,χ) = −(1/N)·Σ_a a·χ(a)` the channel constant, both intrinsic to `χ` with no zero
    in them. The zero is only the **locus where the rescaled chain exposes it** — at a zero the
    smooth/principal part cancels, leaving the bare fibre fluctuation. So every zero reveals the **same**
    fibre invariant (t-invariant) precisely because the invariant belongs to the fibre, not the zero; the
    height `t = Im ρ` lives in the divided-out phase `M^{it}`, not in the invariant
    (`DirichletClosureLedger.closure_ledger_exact`, `cmean_closed_form`). -/
theorem flow_closure_exact (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (s : ℂ)
    (hσ : 0 < s.re) (hzero : DirichletCharacter.LFunction χ s = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 1 ≤ M →
      ‖flowPartialSum χ s M * (M : ℂ) ^ s
          - (Asum χ M - DirichletCharacter.LFunction χ 0)‖ ≤ C * (M : ℝ) ^ (-(1 : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := closure_ledger_exact χ hχ s hσ hzero
  refine ⟨C, hC, fun M hM => ?_⟩
  rw [flowPartialSum_eq_LM χ (modulus_ne_one χ hχ) s M]
  exact hbound M hM

end HelixFlowClosureLedger

#print axioms HelixFlowClosureLedger.flowPartialSum_eq_LM
#print axioms HelixFlowClosureLedger.flow_chain_vanishes_at_zero
#print axioms HelixFlowClosureLedger.flow_closure_error_at_zero
#print axioms HelixFlowClosureLedger.flow_closure_exact
