import RequestProject.HelixDualOperator
import RequestProject.HelixFlowGenerator
import RequestProject.HelixFlowResolvent

/-!
# The Hilbert–Pólya chain — six steps, one bundle, all proven

Everything below is about the **same two objects**: the log-derivative `−L'/L` and the nontrivial
zeros. The prime phasor flow's trace and the dual operator's resolvent trace are *the same* `−L'/L`;
the zeros are *the same* set, read as that function's singularities / the dual operator's spectrum.

```
1. helix Hilbert space            ℓ²(ℕ) = lp (ℕ → ℂ) 2                       — CompleteSpace
2. FTA/Euler phasor dynamics      U(t)(n) = n^{it} ∈ Circle, U(s+t)=U(s)U(t) — unitary flow
   = a unitary flow
3. its self-adjoint generator     U(t) = e^{itH},  H(n) = log n ∈ ℝ          — phasorFlow_eq_exp, gen_real
4. the trace readout / spectral   −L'/L  =  the flow's von Mangoldt trace     — flowVonMangoldtTrace_eq…
   determinant is −L'/L                  =  Σ_ρ mult_ρ·(1/(s−ρ)+1/ρ)         — dualResolventTrace_eq…
5. zeros are spectral events      every nontrivial zero is a pole of −L'/L    — resonates_at_zeros
6. a self-adjoint spectrum        IsSelfAdjoint a ⟹ spectrum ⊆ ℝ             — im_eq_zero_of_mem_spectrum
   is real
```

`hilbertPolyaChain` bundles all six, **unconditionally** (primitive non-principal `χ`), kernel-clean.

**Honest endpoint (the chain ENDS at 6).** Step 6 is the *principle* — a self-adjoint spectrum is real.
Steps 4–5 put the zeros into the dual operator as its spectrum. The chain does **not** assert that
*this* operator is self-adjoint — that step (its spectrum being real ⟹ `Re ρ = ½`) is the one thing not
discharged, and is deliberately left outside the bundle. Everything up to and including the reality
principle is here and proven; the application to force the line is the separate, undischarged appendage.
-/

open Complex Filter Topology HelixFlow HelixFlowGenerator HelixFlowVonMangoldt HelixDualOperator

/-- **The Hilbert–Pólya chain, bundled and proven (unconditional).** For a primitive non-principal `χ`,
    the six steps hold together — and they all speak about the same `−L'/L` and the same zeros. -/
theorem hilbertPolyaChain {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) :
    -- 1. the helix Hilbert space ℓ²(ℕ)
    CompleteSpace (lp (fun _ : ℕ => ℂ) 2) ∧
    -- 2. the FTA/Euler-welded phasor dynamics define a unitary flow (modulus 1, one-parameter group)
    ((∀ (t : ℝ) (n : ℕ), ‖(phasorFlow t n : ℂ)‖ = 1) ∧
     (∀ (s t : ℝ) (n : ℕ), phasorFlow (s + t) n = phasorFlow s n * phasorFlow t n)) ∧
    -- 3. its self-adjoint generator `H(n) = log n`: `U(t) = e^{itH}`, `H` real
    (∀ (t : ℝ) (n : ℕ),
      (phasorFlow t n : ℂ) = Complex.exp (Complex.I * ((t : ℂ) * (gen n : ℂ))) ∧
        (gen n : ℂ).im = 0) ∧
    -- 4. the trace readout / spectral determinant IS `−L'/L`: prime side = zero side
    ((∀ s : ℂ, 1 < s.re →
        flowVonMangoldtTrace χ s = -logDeriv (DirichletCharacter.LFunction χ) s) ∧
     (∃ A : ℂ, ∀ s ∉ GRHSpectral.NontrivialZeros χ,
        logDeriv (DirichletCharacter.completedLFunction χ) s = A + dualResolventTrace χ s)) ∧
    -- 5. the zeros are spectral events: every nontrivial zero is a resonance (pole) of `−L'/L`
    (∀ ρ ∈ GRHSpectral.NontrivialZeros χ,
      ¬ ∃ L, Tendsto (fun s => -logDeriv (DirichletCharacter.LFunction χ) s) (𝓝[≠] ρ) (𝓝 L)) ∧
    -- 6. a self-adjoint spectrum is real (the principle the chain ends at)
    (∀ a : lp (fun _ : ℕ => ℂ) ⊤, IsSelfAdjoint a → ∀ z ∈ spectrum ℂ a, z.im = 0) :=
  ⟨inferInstance,
   ⟨phasorFlow_norm, phasorFlow_add_all⟩,
   fun t n => ⟨phasorFlow_eq_exp t n, gen_real n⟩,
   ⟨fun _ hs => flowVonMangoldtTrace_eq_neg_logDeriv χ hs, dualResolventTrace_eq_logDeriv χ hχ hχp⟩,
   fun _ hρ => EnergyBalance.resonates_at_zeros χ hρ,
   fun _ ha _ hz => ha.im_eq_zero_of_mem_spectrum hz⟩

#print axioms hilbertPolyaChain
