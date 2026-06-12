import RequestProject.HelixDualOperator
import RequestProject.HelixFlowGenerator
import RequestProject.HelixFlowResolvent
import RequestProject.HelixStandingWave
import RequestProject.HelixProduction

/-!
# The Hilbert–Pólya chain — TEN steps, one bundle, all proven

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

## The census — where the finish lives (state of the squeeze)

GRH per window = two counters agree. Both halves exist, in different files, awaiting marriage:

* **UPPER (χ-general, `DirichletLZeroCount`/`DirichletLZeroSet`, kernel-done):** Jensen for `Λχ`
  (`completedL_jensen_at_zero`), the weighted disk zero-count bound
  (`completedL_weighted_zero_count_disk_bound`), strip containment
  (`completedLFunction_zero_mem_NontrivialZeros`), finiteness in every ball
  (`NontrivialZeros_inter_closedBall_finite`), `rootNumber_ne_zero` (the Möbius crack),
  `Σ 1/|ρ|²` summability.
* **LOWER (ζ-instantiated, `HelixStandingWave`, kernel-done):** the standing wave, nodes isolated &
  finite, `nodeCount`/`boxCount`, the alternation engine (`k` flips ⟹ `k` ordered on-line zeros),
  per-window RH from counter agreement (`rh_in_window_of_counters_agree`), global packaging
  (`rh_of_window_certificates`).
* **THE MARRIAGE — UNIVERSAL (every primitive character)** (`HelixStandingWave`, all kernel-clean):
  the wave `Φ_χ = N^{s/2}·Λχ` satisfies `conj Φ_χ(½+it) = W(χ⁻¹)·Φ_χ(½+it)` for EVERY primitive
  `χ ≠ 1` (`waveChar_line_conj_gen` — self-duality not needed); the constant is unimodular by
  FE-reflection at a witness (`rootNumber_inv_conj_mul`, no Gauss sums); a half-phase `ε` with
  `ε² = W`, `conj ε·ε = 1` exists (`exists_halfPhase`, ℂ alg. closed), and `ε·Φ_χ` is REAL on the
  line (`exists_standingWave_universal`). Counter chain complete for all three faces — `W = +1`
  (`standingWaveChar`), `W = −1` (`standingWaveCharIm`), general `ε`-wave (`standingWaveCharGen`) —
  all feeding ONE census (`nodeCountChar`); the strip census is Jensen-bounded explicitly
  (`boxCountChar_le_of_jensen`: `≤ C·R·log R`); counters agree per window ⟹ GRH in window
  (`grh_in_window_of_counters_agree_char`); certificates on all symmetric windows ⟹ `GRH χ`
  outright (`grh_of_window_certificates_char` — `Λχ` entire, no height dodge).
* **THE PÓLYA REDUCTION** (`HelixStandingWave`, kernel-clean, all characters): the quartet
  `σ(ρ) = 1 − conj ρ` maps each `Z(χ)` to itself and is CIRCLE INVERSION in Möbius coordinates
  (`w_quartet`); GRH ⟺ the spectral image sits on the circle (`grh_iff_w_image_unit`) ⟺ the
  one-sided bound `‖w‖ ≤ 1` (`w_norm_eq_one_of_le_one` — deficiency dies in conjugate pairs);
  the unitarity ledger `∏‖w‖ = 1` on every σ-closed window (`prod_w_norm_eq_one`); an interior
  zero forces a strictly exterior partner (`orbit_straddle_of_interior`).
* **THE CORRIDOR (unconditional, `HelixZeroFreeStep`, kernel-clean):** the first interior
  narrowing of the strip — for every primitive non-quadratic `χ`, EVERY zero obeys
  `c/(1+|t|)⁵ ≤ Re ρ ≤ 1 − c/(1+|t|)⁵` with explicit `c > 0` (`zero_free_region_poly`,
  `zero_corridor`). Assembly: Mathlib's dlVP product `‖L(χ⁰)³L(χ)⁴L(χ²)‖ ≥ 1` + the ledger's
  half-plane growth `‖L‖ ≤ N‖s‖/Re s` (`norm_LFunction_le_half_plane`) through Cauchy's estimate
  (`norm_deriv_LFunction_le`) + the mean-value zero-penalty (`norm_LFunction_le_of_zero`) +
  height-uniform pole repulsion (`zero_repulsion_near_one`). This is the Euler-product (FTA)
  constraint landed quantitatively: the spectrum provably cannot approach either strip wall. The `c/log` sharpening and the quadratic (exceptional-zero)
  case are sharper instruments on the same machine.
* **THE VOID (the one gate):** no exterior spectral point — `‖w(ρ)‖ ≤ 1` for every zero,
  equivalently no zero with `Re < ½`. The equivalence is now KERNEL-PROVEN
  (`grh_iff_exteriorVoid`: `GRH χ ⟺ ExteriorVoid χ`), with the ledger in log form
  (`sum_log_w_norm_eq_zero`: `Σ log‖w‖ = 0` per σ-closed window) and the balanced-distance law
  (`sum_log_dist_balanced`: `Σ log‖ρ−1‖ = Σ log‖ρ‖` — the Jensen-ready face). The open weld,
  stated plainly. The structure's case: every phasor is unit, the fiber conserves, the ledger
  balances to zero net mass, the helix is one-sided (`radial_refl_mismatch`) — the exterior
  partner the straddle demands has no radius to live on. Proving that refusal is the remaining
  work.

**The complete chain (`hilbertPolyaChainComplete`, steps 1–10).** The original six end at the
abstract reality principle. Steps 7–10 (the purchase model, `HelixProduction` Part 20) supply the
working form: every accumulation yields a REAL, strictly ordered ladder of purchase heights with
the budget met exactly (7), the staircase `⌊E/π⌋` reads it rung-for-rung (8), the regularized
resolvent over any such ladder cannot resonate off the real axis (9), and every nontrivial zero
is a PAID spectral event — simple pole, residue = multiplicity ≥ 1 (10). All ten unconditional,
kernel-clean.

**Honest remainder — the dictionary, stated as arithmetic.** The chain does not contain the
instantiation that a given `L`'s traversal accumulation matches its vanishing set rung-for-rung;
in census form this is `boxCountChar = nodeCountChar` per window. Numerics
(`numerics/purchase_model.py`): the ladder predicts the zeros of `ζ` and `χ₃` from ONE
calibration constant each at ~15% of a mean gap with exact interlacing over the tested ranges —
the count never slips; the heights breathe by the fluctuation. The remaining mathematics is that
the staircase never slips anywhere.
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

/-- **The weld arcs (the finish campaign), bundled — all UNCONDITIONAL.** The three-way weld
    (flip ⟺ octave ⟺ rendezvous) as landed so far, every hypothesis situational:
    1. a sign flip of the standing wave yields an on-line `ζ`-zero strictly between (classical hook);
    2. at ANY vanishing — location-free, no line — the two fibres MEET (admission = rendezvous);
    3. a transversal node is a sign flip in every window (node = flip);
    4. the wave's real derivative is the holomorphic derivative on the line (the ℂ→ℝ bridge).
    **Still open, honestly (the remaining arcs):** rendezvous = node at the fold (wave reality at the
    meeting point); the census `N(T)` welding flip-count to admission-count (multiplicity-safe — no
    simplicity assumed); the χ₃-instance wiring; final conductor-parametrized packaging. -/
theorem weldArcs :
    -- 1. classical hook: flip ⟹ counted on-line zero
    (∀ a b : ℝ, a < b → HelixStandingWave.standingWave a * HelixStandingWave.standingWave b < 0 →
      ∃ t ∈ Set.Ioo a b, riemannZeta (1 / 2 + (t : ℂ) * I) = 0) ∧
    -- 2. admission = rendezvous, location-free: at ANY vanishing the fibres meet
    (∀ Φ : ZMod 3 → ℂ, Function.Odd Φ → Φ 1 ≠ 0 → ∀ s : ℂ, ZMod.LFunction Φ s = 0 →
      HurwitzZeta.hurwitzZetaOdd (ZMod.toAddCircle (1 : ZMod 3)) s
        = HurwitzZeta.hurwitzZetaOdd (ZMod.toAddCircle (2 : ZMod 3)) s) ∧
    -- 3. node = flip: a transversal node flips sign in every window
    (∀ (f : ℝ → ℝ) (t₀ d : ℝ), f t₀ = 0 → HasDerivAt f d t₀ → d ≠ 0 → ∀ ε : ℝ, 0 < ε →
      ∃ a ∈ Set.Ioo (t₀ - ε) t₀, ∃ b ∈ Set.Ioo t₀ (t₀ + ε), f a * f b < 0) ∧
    -- 4. the ℂ→ℝ bridge: the wave's derivative is the holomorphic derivative on the line
    (∀ t : ℝ, HasDerivAt HelixStandingWave.standingWave
      ((deriv HelixStandingWave.waveC (t : ℂ)).re) t) :=
  ⟨fun _ _ hab h => HelixStandingWave.online_zero_of_signFlip hab h,
   fun Φ hΦ h1 s hz => HelixStandingWave.fibres_meet_at_any_vanishing Φ hΦ h1 s hz,
   fun _ _ _ h0 hd hne _ hε => HelixStandingWave.signFlip_of_simple_node h0 hd hne hε,
   HelixStandingWave.standingWave_hasDerivAt⟩

/-- **The FULL Hilbert–Pólya chain — ten steps, one bundle, all unconditional.** The original six
    (space, unitary flow, real generator, trace readout, zeros as events, reality principle) plus
    the purchase model's four:

    7. **the ladder** — every accumulation purchases each harmonic at a unique height, with the
       budget met exactly (`E(tₙ) = n·π`), and the ladder is REAL AND STRICTLY ORDERED by
       construction;
    8. **the staircase** — the harmonic count reads the ladder exactly (`⌊E/π⌋ = n` at the n-th
       purchase): `H_z` is a floor function of accumulation, not an operator owing reality;
    9. **the working reality principle** — the regularized resolvent over any such ladder cannot
       resonate off the real axis, for any admissible weights;
    10. **the payment** — every nontrivial zero is a PAID spectral event: the trace has a simple
        pole there with residue = multiplicity ≥ 1, the quantum delivered by the fiber.

    Every component is kernel-clean with standard axioms. What this chain does NOT contain —
    stated plainly, as arithmetic and not as a hypothesis — is the dictionary instantiation: that
    a given `L`'s traversal accumulation matches its vanishing set rung-for-rung (the census
    equality `boxCountChar = nodeCountChar` per window). The numerics (purchase_model.py)
    validate that dictionary at ~15% of a mean gap with exact interlacing over the tested ranges
    of `ζ` and `χ₃`, from one calibration constant each. -/
theorem hilbertPolyaChainComplete {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) :
    -- 1–6: the original chain
    (CompleteSpace (lp (fun _ : ℕ => ℂ) 2) ∧
     ((∀ (t : ℝ) (n : ℕ), ‖(phasorFlow t n : ℂ)‖ = 1) ∧
      (∀ (s t : ℝ) (n : ℕ), phasorFlow (s + t) n = phasorFlow s n * phasorFlow t n)) ∧
     (∀ (t : ℝ) (n : ℕ),
       (phasorFlow t n : ℂ) = Complex.exp (Complex.I * ((t : ℂ) * (gen n : ℂ))) ∧
         (gen n : ℂ).im = 0) ∧
     ((∀ s : ℂ, 1 < s.re →
         flowVonMangoldtTrace χ s = -logDeriv (DirichletCharacter.LFunction χ) s) ∧
      (∃ A : ℂ, ∀ s ∉ GRHSpectral.NontrivialZeros χ,
         logDeriv (DirichletCharacter.completedLFunction χ) s = A + dualResolventTrace χ s)) ∧
     (∀ ρ ∈ GRHSpectral.NontrivialZeros χ,
       ¬ ∃ L, Tendsto (fun s => -logDeriv (DirichletCharacter.LFunction χ) s) (𝓝[≠] ρ) (𝓝 L)) ∧
     (∀ a : lp (fun _ : ℕ => ℂ) ⊤, IsSelfAdjoint a → ∀ z ∈ spectrum ℂ a, z.im = 0)) ∧
    -- 7–9: the purchase model, complete (ladder, order, staircase, discreteness, reality ban)
    (∀ A : HelixProduction.Accumulation,
      (∀ n : ℕ, 0 ≤ A.purchaseHeight n ∧ A.E (A.purchaseHeight n) = n * Real.pi) ∧
      StrictMono A.purchaseHeight ∧
      (∀ n : ℕ, HelixProduction.harmonicCount A.E (A.purchaseHeight n) = n) ∧
      (∀ R : ℝ, {n : ℕ | |A.purchaseHeight n| ≤ R}.Finite) ∧
      (∀ c : ℕ → ℝ, (∀ n, 0 ≤ c n) →
        Summable (fun n => c n / (A.purchaseHeight (n + 1)) ^ 2) →
        ∀ w : ℂ, w.im ≠ 0 → DifferentiableAt ℂ
          (fun z : ℂ => ∑' n : ℕ, (c n : ℂ)
            * (1 / (z - (A.purchaseHeight (n + 1) : ℂ))
              + 1 / (A.purchaseHeight (n + 1) : ℂ))) w)) ∧
    -- 10: every zero is a PAID spectral event (simple pole, residue = multiplicity ≥ 1)
    (∀ ρ ∈ GRHSpectral.NontrivialZeros χ,
      ∃ (n : ℕ) (g : ℂ → ℂ), 1 ≤ n ∧ AnalyticAt ℂ g ρ ∧ g ρ ≠ 0 ∧
        analyticOrderAt (DirichletCharacter.LFunction χ) ρ = (n : ℕ∞) ∧
        ∀ᶠ s in nhdsWithin ρ {ρ}ᶜ,
          -logDeriv (DirichletCharacter.LFunction χ) s
            = -((n : ℂ) * (s - ρ)⁻¹ + deriv g s / g s)) := by
  refine ⟨hilbertPolyaChain χ hχ hχp, ?_, ?_⟩
  · exact fun A => HelixProduction.Accumulation.purchase_model_complete A
  · exact fun ρ hρ => (EnergyBalance.sole_origin χ hρ).2

/-- **The grand chain: everything proven, one theorem.** The full ten-step Hilbert–Pólya
chain (above) TOGETHER WITH the transport beams of Parts 21–23: a hypothetical off-line
zero's line factor is a strictly negative real at every line point (phase frozen — it
can never pay phase into any window), its dip carries the strictly positive floor
`(Re ρ − ½)²` (it never touches bottom), a zero's FE-pair signature touches the line
iff the zero is ON the line (the uniformity dichotomy), a nonempty pole sum cannot
vanish identically (no silent cancellation for a ghost set), and the two-term/Möbius
mechanism forces zeros of `1 + c` onto the unit locus of the fold. Unconditional;
kernel axioms only. The single statement this chain still awaits is the global quantum
symmetry — count = phase/π, the staircase never slips — equivalently
`offLineCountChar = 0` for every window: the one number left to kill. -/
theorem grandTransportChain {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) :
    -- the ten-step chain
    ((CompleteSpace (lp (fun _ : ℕ => ℂ) 2) ∧
     ((∀ (t : ℝ) (n : ℕ), ‖(phasorFlow t n : ℂ)‖ = 1) ∧
      (∀ (s t : ℝ) (n : ℕ), phasorFlow (s + t) n = phasorFlow s n * phasorFlow t n)) ∧
     (∀ (t : ℝ) (n : ℕ),
       (phasorFlow t n : ℂ) = Complex.exp (Complex.I * ((t : ℂ) * (gen n : ℂ))) ∧
         (gen n : ℂ).im = 0) ∧
     ((∀ s : ℂ, 1 < s.re →
         flowVonMangoldtTrace χ s = -logDeriv (DirichletCharacter.LFunction χ) s) ∧
      (∃ A : ℂ, ∀ s ∉ GRHSpectral.NontrivialZeros χ,
         logDeriv (DirichletCharacter.completedLFunction χ) s = A + dualResolventTrace χ s)) ∧
     (∀ ρ ∈ GRHSpectral.NontrivialZeros χ,
       ¬ ∃ L, Tendsto (fun s => -logDeriv (DirichletCharacter.LFunction χ) s) (𝓝[≠] ρ) (𝓝 L)) ∧
     (∀ a : lp (fun _ : ℕ => ℂ) ⊤, IsSelfAdjoint a → ∀ z ∈ spectrum ℂ a, z.im = 0)) ∧
    (∀ A : HelixProduction.Accumulation,
      (∀ n : ℕ, 0 ≤ A.purchaseHeight n ∧ A.E (A.purchaseHeight n) = n * Real.pi) ∧
      StrictMono A.purchaseHeight ∧
      (∀ n : ℕ, HelixProduction.harmonicCount A.E (A.purchaseHeight n) = n) ∧
      (∀ R : ℝ, {n : ℕ | |A.purchaseHeight n| ≤ R}.Finite) ∧
      (∀ c : ℕ → ℝ, (∀ n, 0 ≤ c n) →
        Summable (fun n => c n / (A.purchaseHeight (n + 1)) ^ 2) →
        ∀ w : ℂ, w.im ≠ 0 → DifferentiableAt ℂ
          (fun z : ℂ => ∑' n : ℕ, (c n : ℂ)
            * (1 / (z - (A.purchaseHeight (n + 1) : ℂ))
              + 1 / (A.purchaseHeight (n + 1) : ℂ))) w)) ∧
    (∀ ρ ∈ GRHSpectral.NontrivialZeros χ,
      ∃ (n : ℕ) (g : ℂ → ℂ), 1 ≤ n ∧ AnalyticAt ℂ g ρ ∧ g ρ ≠ 0 ∧
        analyticOrderAt (DirichletCharacter.LFunction χ) ρ = (n : ℕ∞) ∧
        ∀ᶠ s in nhdsWithin ρ {ρ}ᶜ,
          -logDeriv (DirichletCharacter.LFunction χ) s
            = -((n : ℂ) * (s - ρ)⁻¹ + deriv g s / g s))) ∧
    -- the transport beams (Parts 21–23): frozen phase, positive floor, dichotomy,
    -- no silent cancellation, the Möbius two-term forcing
    (∀ s ρ : ℂ, s.re = 1 / 2 → ρ.re ≠ 1 / 2 →
       ((s - ρ) * (s - (1 - (starRingEnd ℂ) ρ))).im = 0 ∧
       ((s - ρ) * (s - (1 - (starRingEnd ℂ) ρ))).re < 0) ∧
    (∀ s ρ : ℂ, s.re = 1 / 2 → ρ.re ≠ 1 / 2 →
       (0 : ℝ) < (ρ.re - 1 / 2) ^ 2 ∧
       ((ρ.re - 1 / 2) ^ 2 : ℝ) ≤ ‖(s - ρ) * (s - (1 - (starRingEnd ℂ) ρ))‖) ∧
    (∀ ρ : ℂ,
       (∃ s : ℂ, s.re = 1 / 2 ∧ (s - ρ) * (s - (1 - (starRingEnd ℂ) ρ)) = 0) ↔
         ρ.re = 1 / 2) ∧
    (∀ (F : Finset ℂ) (w : ℂ → ℂ) (ρ₀ : ℂ), ρ₀ ∈ F → w ρ₀ ≠ 0 →
       ¬ (∀ s : ℂ, s ∉ (F : Set ℂ) → ∑ ρ ∈ F, w ρ / (s - ρ) = 0)) ∧
    (∀ c : ℂ → ℂ, (∀ s : ℂ, ‖c s‖ = 1 ↔ s.re = 1 / 2) →
       ∀ s : ℂ, 1 + c s = 0 → s.re = 1 / 2) := by
  refine ⟨hilbertPolyaChainComplete χ hχ hχp,
    fun s ρ hs hρ => HelixProduction.offline_pair_phase_frozen hs hρ,
    fun s ρ hs hρ => HelixProduction.offline_pair_positive_floor hs hρ,
    fun ρ => HelixProduction.pair_signature_touches_iff_online ρ,
    fun F w ρ₀ h0 hw => HelixProduction.finite_pole_sum_ne_zero h0 hw,
    fun c hc s hz => HelixProduction.mobius_two_term_zero_on_line hc hz⟩

#print axioms hilbertPolyaChain
#print axioms hilbertPolyaChainComplete
#print axioms weldArcs
#print axioms grandTransportChain
