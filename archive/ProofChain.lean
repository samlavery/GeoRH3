import RequestProject.HelixResolventCapture

open Filter Topology Complex

namespace ProofChain

variable {N : ℕ} [NeZero N]

/-- The spectral target `T_L(z) = −L'/L(½ + i z)` — the completed log-derivative readout. -/
noncomputable def TL (χ : DirichletCharacter ℂ N) : ℂ → ℂ :=
  fun z => -logDeriv (DirichletCharacter.LFunction χ) (1 / 2 + Complex.I * z)

/-- # The full proof chain, assembled — one kernel theorem.

```
  primitive χ
   → Euler-unitary prime fibers        -- the candidate source trace `T` (wind:ℕ→Circle, |χ(p)|=1)
   → sourceTrace = −L'/L               -- `hCont` (local principal-part cancellation) + `hdecay`
   → harmonic boundary receiver        -- SingularSupport / IsSelfAdjointReceiver
   → self-adjoint / no-drift           -- `hsa`
   → resolvent-trace capture           -- zeros_subset_singularSupport_of_traceIdentity (PROVEN)
   → local-to-global                   -- global_traceIdentity_of_local (PROVEN)
   → GRH
```

**Proven spine** (composed here): `global_traceIdentity_of_local` ∘ `grh_of_harmonicTraceReceiver_traceIdentity`.
**The two GRH-bearing inputs, left explicit and honest:**
* `hCont`/`hdecay` — the trace identity `T = −L'/L` (`sourceTrace = −L'/L`), the local→global step;
* `hsa` — the receiver is self-adjoint (regular off ℝ), the earned no-drift reality.
`hspec`/`hL` are standard meromorphicity, not GRH content. This composes the chain; it does not
discharge the two open links (`sourceComplete_iff_grh` certifies they are GRH-equivalent). -/
theorem grh_of_chain (χ : DirichletCharacter ℂ N) (T : ℂ → ℂ)
    (hspec : ∀ z, MeromorphicAt T z)
    (hL : ∀ z, MeromorphicAt (TL χ) z)
    (hCont : Continuous (T - TL χ))
    (hdecay : Tendsto (T - TL χ) (Filter.cocompact ℂ) (𝓝 0))
    (hsa : HelixLimit.IsSelfAdjointReceiver T) :
    GRHSpectral.GRH χ := by
  -- local principal parts cancel + decay  ⟹  global trace identity  `T = −L'/L`
  have hid : T = TL χ := HelixLimit.global_traceIdentity_of_local hspec hL hCont hdecay
  -- self-adjoint receiver + trace identity  ⟹  capture  ⟹  GRH
  exact HelixLimit.grh_of_harmonicTraceReceiver_traceIdentity hsa (fun z => congrFun hid z)

end ProofChain
