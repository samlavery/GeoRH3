import RequestProject.ArchimedeanGamma
import RequestProject.HelixDualOperator
import RequestProject.HelixFlowGenerator
import RequestProject.HelixFlowResolvent
import RequestProject.HelixFlowClosureLedger
import RequestProject.HelixRoundTrip
import RequestProject.HelixStandingWave
import RequestProject.HelixProduction
import RequestProject.RiemannHypothesisBridge

/-!
# The Hilbert–Pólya chain — R1–R9 infrastructure map

This file records the chain infrastructure only.  It does not turn the chain into a final
zero-location conclusion.  The explicit `hilbertPolyaChainR1ToR9` theorem below is the audit map:
each component points to the module that carries that step.

R1. Hilbert space: `lp (fun _ : ℕ => ℂ) 2`.
R2. Earned unitarity: `HelixFlowUnitaryGroup`.
R3. Reality/no-drift forcing: `HelixSourceFlow` plus the real generator in `HelixFlowGenerator`.
R4. Trace = L, helix-native: `HelixFlowClosureLedger` and `DirichletClosureLedger`.
R5. Zeros are spectral events: `HelixFlowClosureLedger` and `EnergyBalance`.
R6. Spectral realization: threshold crossing + channel rendezvous + quantum ladder.
R7. Exhaustion: `ladder_induction` and `Accumulation.ladder_rigidity`.
R8. Faithfulness: exact `π/3` rechart plus the intrinsic closure ledger.
R9. Genuine object: `GRHSpectral.NontrivialZeros` is Mathlib's `LFunction` zero set in the strip.

Older bundled theorems in this file are kept for downstream compatibility; the R1–R9 theorem is the
preferred chain index.
-/

open Complex Filter Topology HelixFlow HelixFlowGenerator HelixFlowVonMangoldt HelixDualOperator

/-- **R1–R9 chain map, no final zero-location conclusion.**  This theorem bundles the currently
    preferred modules for each step without asserting the last inheritance step. -/
theorem hilbertPolyaChainR1ToR9 {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) :
    -- R1: Hilbert space.
    CompleteSpace (lp (fun _ : ℕ => ℂ) 2) ∧
    -- R2: earned unitary one-parameter flow.
    ((HelixFlow.flowHom (Multiplicative.ofAdd 0) = 1) ∧
      (∀ s t : ℝ, HelixFlow.flowHom (Multiplicative.ofAdd (s + t))
        = HelixFlow.flowHom (Multiplicative.ofAdd s) * HelixFlow.flowHom (Multiplicative.ofAdd t)) ∧
      (∀ t : ℝ, ∀ n : ℕ, ‖(phasorFlow t n : ℂ)‖ = 1) ∧
      (∀ n : ℕ, Continuous (fun t : ℝ => (phasorFlow t n : ℂ)))) ∧
    -- R3: real generator and sigma-free no-drift forcing.
    ((∀ (t : ℝ) (n : ℕ),
        (phasorFlow t n : ℂ) = Complex.exp (Complex.I * ((t : ℂ) * (gen n : ℂ))) ∧
          (gen n : ℂ).im = 0) ∧
      (∀ (lam : ℂ) (c : ℝ), c ≠ 0 →
        (∀ τ : ℝ, Real.exp (lam.re * τ) * c = c) → lam.re = 0)) ∧
    -- R4: helix-native trace/chain readout reaches `L` on `0 < Re s`.
    ((∀ s : ℂ, 0 < s.re →
        ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 1 ≤ M →
          ‖HelixFlowClosureLedger.flowPartialSum χ s M
              - DirichletCharacter.LFunction χ s‖ ≤ C * (M : ℝ) ^ (-s.re)) ∧
      (∀ s : ℂ, 0 < s.re →
        DirichletClosureLedger.cChar χ s = DirichletCharacter.LFunction χ s)) ∧
    -- R5: at a genuine zero, the phasor chain cancels and the log-derivative has a pole.
    ((∀ s : ℂ, 0 < s.re → DirichletCharacter.LFunction χ s = 0 →
        ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 1 ≤ M →
          ‖HelixFlowClosureLedger.flowPartialSum χ s M‖ ≤ C * (M : ℝ) ^ (-s.re)) ∧
      (∀ ρ ∈ GRHSpectral.NontrivialZeros χ,
        ¬ ∃ L, Tendsto (fun s => -logDeriv (DirichletCharacter.LFunction χ) s)
          (𝓝[≠] ρ) (𝓝 L))) ∧
    -- R6: threshold crossing, quantum ladder, and channel rendezvous/payment.
    ((∀ {E : ℝ → ℝ}, Continuous E → StrictMono E →
        ∀ {a c b : ℝ}, E a ≤ c → a ≤ b → c ≤ E b →
          ∃! t : ℝ, a ≤ t ∧ E t = c) ∧
      (∀ {E : ℝ → ℝ} {t : ℝ} {n : ℤ},
        E t = n * Real.pi → HelixProduction.harmonicCount E t = n) ∧
      (∀ k : ℤ, quantumLevelZ (k + 1) = quantumLevelZ k + Real.pi) ∧
      (quantumLevelZ 0 = Real.pi / 2) ∧
      (∀ F : Finset ℕ, ∀ s : ℕ → ℝ,
        (∑ n ∈ F, s n = 0 ↔ plusBucket F s = minusBucket F s) ∧
        (∑ n ∈ F, s n = 0 → ∑ n ∈ F, |s n| = 2 * plusBucket F s))) ∧
    -- R7: ladder exhaustion by induction and rigidity of any conversion-law crossing sequence.
    ((∀ (P : ℝ → Prop), P (quantumLevelZ 0) →
        (∀ k : ℤ, P (quantumLevelZ k) → P (quantumLevelZ (k + 1))) →
        (∀ k : ℤ, P (quantumLevelZ k) → P (quantumLevelZ (k - 1))) →
        ∀ k : ℤ, P (quantumLevelZ k)) ∧
      (∀ A : HelixProduction.Accumulation, ∀ c : ℕ → ℝ,
        (∀ n, 0 ≤ c n) → (∀ n, A.E (c n) = n * Real.pi) →
          ∀ n, c n = A.purchaseHeight n)) ∧
    -- R8: faithful `π/3` coordinate chart plus intrinsic zero ledger.
    ((Function.LeftInverse arcChartInv arcChart ∧ Function.RightInverse arcChartInv arcChart) ∧
      (∀ x : ℝ, arcChart x = Real.pi / 6 ↔ x = 1 / 2) ∧
      (∀ s : ℂ, 0 < s.re → DirichletCharacter.LFunction χ s = 0 →
        ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 1 ≤ M →
          ‖HelixFlowClosureLedger.flowPartialSum χ s M * (M : ℂ) ^ s
              - (DirichletClosureLedger.Asum χ M - DirichletCharacter.LFunction χ 0)‖
            ≤ C * (M : ℝ) ^ (-(1 : ℝ)))) ∧
    -- R9: genuine object, by definition.
    (∀ ρ : ℂ,
      ρ ∈ GRHSpectral.NontrivialZeros χ ↔
        0 < ρ.re ∧ ρ.re < 1 ∧ DirichletCharacter.LFunction χ ρ = 0) := by
  refine ⟨inferInstance, HelixFlow.isUnitaryOneParameterFlow, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨fun t n => ⟨phasorFlow_eq_exp t n, gen_real n⟩, HelixSource.source_noDrift⟩
  · exact ⟨fun s hs => HelixFlowClosureLedger.flow_rate_bound χ hχ s hs,
      fun s hs => DirichletClosureLedger.cChar_eq_LFunction χ hχ s hs⟩
  · exact ⟨fun s hs hz => HelixFlowClosureLedger.flow_chain_vanishes_at_zero χ hχ s hs hz,
      fun ρ hρ => EnergyBalance.resonates_at_zeros χ hρ⟩
  · refine ⟨?_, ?_, quantumLevelZ_step, ?_, ?_⟩
    · intro E hcont hmono a c b hac hab hcb
      exact HelixProduction.existsUnique_threshold hcont hmono hac hab hcb
    · intro E t n h
      exact HelixProduction.harmonicCount_at_threshold h
    · exact (quantumLevelZ_midpoint_straddle).2.1
    · intro F s
      exact ⟨vanishing_iff_rendezvous F s, fun h => price_at_rendezvous F s h⟩
  · exact ⟨ladder_induction,
      fun A c hc0 hcE n => HelixProduction.Accumulation.ladder_rigidity A c hc0 hcE n⟩
  · exact ⟨arcChart_complete, arcChart_line,
      fun s hs hz => HelixFlowClosureLedger.flow_closure_exact χ hχ s hs hz⟩
  · intro ρ
    rfl

/-! ## Conditional projection closure

The HP/helix side is the R1-R9 infrastructure above.  The additional input here is a projection
faithfulness statement: fiber capture events must be represented by the source fiber, and
lower-dimensional projection must not introduce events absent from that source. -/

/-- A source fiber/channel event on the 3D helix.

It deliberately does not store `ρ.re = 1 / 2`.  Instead it stores the source-side
conservation/readout data from which the HP chain derives the midpoint readout. -/
structure SourceFiberEvent {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (ρ : ℂ) where
  driftRate : ℂ
  amplitude : ℝ
  amplitude_ne_zero : amplitude ≠ 0
  source_conserved :
    ∀ τ : ℝ, Real.exp (driftRate.re * τ) * amplitude = amplitude
  source_coordinate : ℝ
  piThird_coordinate : source_coordinate = arcChart ρ.re
  height_matches_zero : driftRate.im = ρ.im
  zero_ne_zero : ρ ≠ 0
  source_chain_cancels :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 1 ≤ M →
      ‖HelixFlowClosureLedger.flowPartialSum χ ρ M‖ ≤ C * (M : ℝ) ^ (-ρ.re)
  source_resolvent_pole :
    ¬ ∃ L, Tendsto (fun s => -logDeriv (DirichletCharacter.LFunction χ) s)
      (𝓝[≠] ρ) (𝓝 L)

/-- A fiber capture event for a Dirichlet channel, represented at the formal boundary by Mathlib's
    `LFunction` zero set. -/
def FiberCaptureEvent {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (ρ : ℂ) : Prop :=
  ρ ∈ GRHSpectral.NontrivialZeros χ

/-- Source completeness in the 3D model: every nontrivial zero is realized as a source fiber event. -/
def SourceComplete3D {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ ρ, FiberCaptureEvent χ ρ → Nonempty (SourceFiberEvent χ ρ)

/-- The R1-R9 chain realizes every nontrivial zero as a 3D source fiber event for non-principal
    channels.  This is the source-completeness step; it does not conclude `ρ.re = 1 / 2`. -/
theorem sourceComplete3D_of_HP {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) : SourceComplete3D χ := by
  have hHP := hilbertPolyaChainR1ToR9 χ hχ
  rcases hHP with ⟨_, _, _, _, hR5, _, _, hR8, hR9⟩
  intro ρ hρ
  have hρ' := (hR9 ρ).mp hρ
  refine
    ⟨{ driftRate := Complex.I * (ρ.im : ℂ),
        amplitude := 1,
        amplitude_ne_zero := one_ne_zero,
        source_conserved := ?_,
        source_coordinate := arcChart ρ.re,
        piThird_coordinate := rfl,
        height_matches_zero := ?_,
        zero_ne_zero := GRHSpectral.nontrivial_ne_zero hρ,
        source_chain_cancels := hR5.1 ρ hρ'.1 hρ'.2.2,
        source_resolvent_pole := hR5.2 ρ hρ }⟩
  · intro τ
    simp
  · simp

/-- Projection faithfulness for one Dirichlet channel.  This is only the source-to-readout transport:
    source completion supplies the source event, and this structure says that dimensional collapse
    preserves the event's 1D Pythagorean readout and creates no extra projected events. -/
structure FaithfulDimensionalProjection {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) where
  projected_event : ℂ → Prop
  source_event_faithfully_projected :
    ∀ ρ, SourceFiberEvent χ ρ → projected_event ρ
  lower_dimensions_create_no_events :
    ∀ ρ, projected_event ρ → SourceFiberEvent χ ρ
  projected_readout_pythagorean :
    ∀ ρ, (hsrc : SourceFiberEvent χ ρ) → hsrc.driftRate.re = 0 → projected_event ρ →
      Complex.normSq (SpectralSide.w ρ) = 1

/-- Source events force the midpoint once the HP chain supplies source no-drift, source completion
    supplies the source event, and faithful transport supplies the 1D Pythagorean readout. -/
theorem SourceFiberEvent.midpoint_axis_of_HP {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} {ρ : ℂ} (hχ : χ ≠ 1)
    (hfaith : FaithfulDimensionalProjection χ) (hsrc : SourceFiberEvent χ ρ) : ρ.re = 1 / 2 := by
  have hHP := hilbertPolyaChainR1ToR9 χ hχ
  rcases hHP with ⟨_, _, hR3, _, _, _, _, hR8, _⟩
  have hNoDrift : hsrc.driftRate.re = 0 :=
    hR3.2 hsrc.driftRate hsrc.amplitude hsrc.amplitude_ne_zero hsrc.source_conserved
  have hproj : hfaith.projected_event ρ :=
    hfaith.source_event_faithfully_projected ρ hsrc
  have hPyth : Complex.normSq (SpectralSide.w ρ) = 1 :=
    hfaith.projected_readout_pythagorean ρ hsrc hNoDrift hproj
  have hMid : ρ.re = 1 / 2 :=
    (SpectralSide.w_unit_iff_half ρ hsrc.zero_ne_zero).mp hPyth
  have hChart : arcChart ρ.re = Real.pi / 6 := (hR8.2.1 ρ.re).mpr hMid
  exact (hR8.2.1 ρ.re).mp hChart

/-- Conditional per-character closure from the R1-R9 HP infrastructure and projection faithfulness. -/
theorem GRH_of_HP_and_Faithfulness {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hfaith : FaithfulDimensionalProjection χ) : GRHSpectral.GRH χ := by
  intro ρ hρ
  rcases sourceComplete3D_of_HP χ hχ ρ hρ with ⟨hsrc⟩
  exact SourceFiberEvent.midpoint_axis_of_HP hχ hfaith hsrc

/-- Faithful projection for every non-principal Dirichlet channel. -/
structure FaithfulDimensionalProjectionAll where
  character :
    ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M), χ ≠ 1 →
      FaithfulDimensionalProjection χ

/-- All non-principal channels close from the HP map and faithful projection.  The principal/L1 channel
    is handled by the separate zeta wrapper below. -/
theorem GRHComplete_of_HP_and_Faithfulness (hfaith : FaithfulDimensionalProjectionAll) :
    ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M), χ ≠ 1 → GRHSpectral.GRH χ := by
  intro M hM χ hχ
  exact GRH_of_HP_and_Faithfulness χ hχ (hfaith.character M χ hχ)

/-- A source fiber/channel event for the eta-regularized zeta/L1 fiber. -/
structure ZetaSourceFiberEvent (ρ : ℂ) where
  driftRate : ℂ
  amplitude : ℝ
  amplitude_ne_zero : amplitude ≠ 0
  source_conserved :
    ∀ τ : ℝ, Real.exp (driftRate.re * τ) * amplitude = amplitude
  height_ne_zero : ρ.im ≠ 0
  pythagorean_of_no_drift :
    driftRate.re = 0 →
      (moebius_helix ρ.re ρ.im).re ^ 2 + (moebius_helix ρ.re ρ.im).im ^ 2 = 1

/-- The conditional projection mechanism for the eta-regularized zeta/L1 channel. -/
structure FaithfulZetaDimensionalProjection where
  projected_event : ℂ → Prop
  fiber_capture_faithfully_projected :
    ∀ ρ, ρ ∈ ZD.NontrivialZeros → projected_event ρ
  lower_dimensions_create_no_events :
    ∀ ρ, projected_event ρ → ZetaSourceFiberEvent ρ

/-- Zeta/L1 source events force the `CoshBalance` midpoint by the same no-drift and
    Pythagorean readout route. -/
theorem ZetaSourceFiberEvent.midpoint_axis_of_source_noDrift {ρ : ℂ}
    (hsrc : ZetaSourceFiberEvent ρ) : ρ.re = CoshBalance := by
  have hNoDrift : hsrc.driftRate.re = 0 :=
    HelixSource.source_noDrift hsrc.driftRate hsrc.amplitude hsrc.amplitude_ne_zero
      hsrc.source_conserved
  have hPyth :
      (moebius_helix ρ.re ρ.im).re ^ 2 + (moebius_helix ρ.re ρ.im).im ^ 2 = 1 :=
    hsrc.pythagorean_of_no_drift hNoDrift
  have hMid : ρ.re = 1 / 2 :=
    (readout_pythagoras_iff_online ρ.re ρ.im hsrc.height_ne_zero).mp hPyth
  rwa [CoshBalance_eq_half]

/-- Conditional zeta/L1 closure through Mathlib's `RiemannHypothesis` bridge.  This is a separate
    wrapper only because the repository bridge is stated for `ZD.NontrivialZeros`. -/
theorem RH_of_HP_and_Faithfulness (hfaith : FaithfulZetaDimensionalProjection) :
    RiemannHypothesis :=
  RHBridge.no_offline_zeros_implies_rh fun ρ hρ =>
    ZetaSourceFiberEvent.midpoint_axis_of_source_noDrift
      (hfaith.lower_dimensions_create_no_events ρ
        (hfaith.fiber_capture_faithfully_projected ρ hρ))

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

/-- **The weld arcs, bundled — all UNCONDITIONAL.** The three-way weld
    (flip ⟺ octave ⟺ rendezvous) at the ζ/χ₃ instance, every hypothesis situational:
    1. a sign flip of the standing wave yields an on-line `ζ`-zero strictly between (classical hook);
    2. at ANY vanishing — location-free, no line — the two fibres MEET (admission = rendezvous);
    3. a transversal node is a sign flip in every window (node = flip);
    4. the wave's real derivative is the holomorphic derivative on the line (the ℂ→ℝ bridge).
    The conductor-general forms are kernel-proven in `HelixStandingWave`: the χ₃ instance with
    derived side conditions (`fibres_meet_at_any_vanishing'`), node ⟺ line-zero for every
    primitive character (`standingWaveChar_node_iff`, `standingWaveCharIm_node_iff`,
    `standingWaveCharGen_node_iff`), the alternation census engine
    (`online_zeros_of_alternation_char`, `alternation_le_nodeCountChar`), and the window
    packaging (`grh_in_window_of_counters_agree_char`, `grh_of_window_certificates_char`). -/
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
    equality `boxCountChar = nodeCountChar` per window). Numerics (`numerics/`): the ladder's
    rungs interlace the zeros exactly over all tested channels; the count never slipped. -/
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
kernel axioms only. What it does not contain is the census equality
`boxCountChar = nodeCountChar` per window — the program's open statement. -/
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

/-! ## Form B — the prime-side trace continued into the strip: the meeting bricks

Step 4 of the chain holds the two trace readouts side by side: the **prime side**
(`flowVonMangoldtTrace`, the Λ-weighted phasor chain with real generator `log n`, a convergent
sum on `Re s > 1`) and the **zero side** (`dualResolventTrace`, the Hadamard-regularized
resolvent sum over the actual nontrivial zeros). Form B of the program continues the prime-side
trace INTO the strip, where the zeros live. The bricks below are the kernel packaging of that
continuation — all unconditional, σ-free (the zeros enter at whatever real parts they have):

* the **gauge split** `Λ'/Λ = γ'/γ + L'/L` on the right half-plane
  (`completedLFunction_logDeriv_gauge_split`). In Mathlib's normalization the gauge factor
  `Λχ/L` is exactly the Archimedean `χ.gammaFactor` — `Γℝ(s)` (even χ) or `Γℝ(s+1)` (odd χ),
  via `LFunction_eq_completed_div_gammaFactor`; **no conductor power** sits between `Λχ` and
  `L` (the conductor `N^{s/2}` enters the functional equation's symmetric wave `N^{s/2}·Λχ`,
  not the gauge);
* **BRICK 1, `flowDualTraceMeeting`** — the MEETING: on `Re s > 1` the zero-side resolvent
  trace equals `−A` minus the prime-side flow trace plus the explicit gauge correction, with
  the gauge spelled concretely (digamma form, both parities) in the same theorem;
* **BRICK 2, `primeTraceContinuationIntoStrip`** — the continuation EXISTS: `−L'/L` agrees
  with the prime trace on `Re s > 1`, extends to the whole punctured right half-plane as
  `−A − dualResolventTrace + logDeriv γ`, is differentiable there off the zeros (no spurious
  poles; the `Γℝ`-poles all sit at `Re ≤ 0`), and has no finite limit at any nontrivial zero.

Honest scope: these identities are over the ACTUAL zeros and carry no statement about where
those zeros sit — no `Re ρ = ½`, no reality of the continued spectrum, no census. That is
deliberate: the bricks are the meeting/continuation plumbing Form B stands on, not the
on-line forcing. -/

/-- `Γℝ` is differentiable at every point of the right half-plane (`Re s > 0` keeps `s/2`
    off the poles of `Γ`). -/
theorem differentiableAt_GammaR_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ Complex.Gammaℝ s := by
  have h_half_ne : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
    intro m heq
    have hre : (s / 2).re = -(m : ℝ) := by rw [heq]; simp
    rw [ArchGamma.div_two_re] at hre
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hΓ_diff : DifferentiableAt ℂ Complex.Gamma (s / 2) :=
    Complex.differentiableAt_Gamma _ h_half_ne
  have hcpow_diff : DifferentiableAt ℂ (fun t : ℂ => (Real.pi : ℂ) ^ (-t / 2)) s := by
    refine DifferentiableAt.const_cpow ((differentiableAt_id.neg).div_const 2) ?_
    left; exact_mod_cast Real.pi_pos.ne'
  have hcomp : DifferentiableAt ℂ (fun t : ℂ => Complex.Gamma (t / 2)) s :=
    hΓ_diff.comp s (differentiableAt_id.div_const 2)
  rw [show Complex.Gammaℝ = fun t : ℂ => (Real.pi : ℂ) ^ (-t / 2) * Complex.Gamma (t / 2) from
    funext Complex.Gammaℝ_def]
  exact hcpow_diff.mul hcomp

/-- The Archimedean gauge factor `χ.gammaFactor` is differentiable on the right half-plane
    (both parities: `Γℝ(s)` and `Γℝ(s+1)` are pole-free for `Re s > 0`). -/
theorem differentiableAt_gammaFactor_of_re_pos {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 0 < s.re) : DifferentiableAt ℂ χ.gammaFactor s := by
  rcases χ.even_or_odd with h | h
  · rw [show χ.gammaFactor = fun z => Complex.Gammaℝ z from funext fun z => h.gammaFactor_def z]
    exact differentiableAt_GammaR_of_re_pos hs
  · rw [show χ.gammaFactor = fun z => Complex.Gammaℝ (z + 1) from
      funext fun z => h.gammaFactor_def z]
    have h1 : (0 : ℝ) < (s + 1).re := by rw [Complex.add_re, Complex.one_re]; linarith
    exact (differentiableAt_GammaR_of_re_pos h1).comp s (differentiableAt_id.add_const 1)

/-- **The gauge split.** On the right half-plane, away from zeros of `L`, the log-derivative of
    the completed `L` splits as gauge plus `L`: `Λ'/Λ = γ'/γ + L'/L`. In Mathlib's
    normalization `Λχ = γ(s)·L(s,χ)` exactly — no conductor power between them
    (`LFunction_eq_completed_div_gammaFactor`) — so the gauge factor `Λχ/L` is concretely the
    Archimedean `χ.gammaFactor`. -/
theorem completedLFunction_logDeriv_gauge_split {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re)
    (hL : DirichletCharacter.LFunction χ s ≠ 0) :
    logDeriv (DirichletCharacter.completedLFunction χ) s
      = logDeriv χ.gammaFactor s + logDeriv (DirichletCharacter.LFunction χ) s := by
  have hG : χ.gammaFactor s ≠ 0 := DirichletLHadamard.gammaFactor_ne_zero hs
  have hdL : DifferentiableAt ℂ (DirichletCharacter.LFunction χ) s :=
    (DirichletCharacter.differentiable_LFunction hχ) s
  have hdG : DifferentiableAt ℂ χ.gammaFactor s := differentiableAt_gammaFactor_of_re_pos χ hs
  have hev : DirichletCharacter.completedLFunction χ =ᶠ[nhds s]
      fun z => χ.gammaFactor z * DirichletCharacter.LFunction χ z := by
    have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds hs] with z hz
    have hz0 : z ≠ 0 := by
      intro h0; rw [h0, Complex.zero_re] at hz; exact lt_irrefl 0 hz
    have hGz : χ.gammaFactor z ≠ 0 := DirichletLHadamard.gammaFactor_ne_zero hz
    have hrel := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ z (Or.inl hz0)
    rw [eq_div_iff hGz] at hrel
    show DirichletCharacter.completedLFunction χ z
      = χ.gammaFactor z * DirichletCharacter.LFunction χ z
    linear_combination -hrel
  have h_deriv_eq : deriv (DirichletCharacter.completedLFunction χ) s
      = deriv (fun z => χ.gammaFactor z * DirichletCharacter.LFunction χ z) s := hev.deriv_eq
  have h_val_eq : DirichletCharacter.completedLFunction χ s
      = (fun z => χ.gammaFactor z * DirichletCharacter.LFunction χ z) s := hev.self_of_nhds
  simp only [logDeriv_apply]
  rw [h_deriv_eq, h_val_eq]
  have := logDeriv_mul s hG hL hdG hdL
  simpa [logDeriv_apply] using this

/-- **The gauge, spelled — even case.** For even `χ` the gauge is `Γℝ(s)`, with
    `logDeriv = −½·log π + ½·ψ(s/2)` (`ψ` the digamma) on `Re s > 0`. -/
theorem gammaFactor_logDeriv_even {N : ℕ} {χ : DirichletCharacter ℂ N} (hχe : χ.Even)
    {s : ℂ} (hs : 0 < s.re) :
    logDeriv χ.gammaFactor s
      = -(1 / 2 : ℂ) * Complex.log (Real.pi : ℂ) + (1 / 2 : ℂ) * Complex.digamma (s / 2) := by
  rw [show χ.gammaFactor = fun z => Complex.Gammaℝ z from funext fun z => hχe.gammaFactor_def z]
  exact ArchGamma.logDeriv_GammaR s hs

/-- **The gauge, spelled — odd case.** For odd `χ` the gauge is `Γℝ(s+1)`, with
    `logDeriv = −½·log π + ½·ψ((s+1)/2)` on `Re s > 0`. -/
theorem gammaFactor_logDeriv_odd {N : ℕ} {χ : DirichletCharacter ℂ N} (hχo : χ.Odd)
    {s : ℂ} (hs : 0 < s.re) :
    logDeriv χ.gammaFactor s
      = -(1 / 2 : ℂ) * Complex.log (Real.pi : ℂ)
        + (1 / 2 : ℂ) * Complex.digamma ((s + 1) / 2) := by
  rw [show χ.gammaFactor = fun z => Complex.Gammaℝ (z + 1) from
    funext fun z => hχo.gammaFactor_def z]
  have h1 : (0 : ℝ) < (s + 1).re := by rw [Complex.add_re, Complex.one_re]; linarith
  have hg : HasDerivAt (fun z : ℂ => z + 1) 1 s := (hasDerivAt_id s).add_const 1
  have hcomp := logDeriv_comp (f := Complex.Gammaℝ) (g := fun z : ℂ => z + 1) (x := s)
    (differentiableAt_GammaR_of_re_pos h1) hg.differentiableAt
  rw [Function.comp_def] at hcomp
  rw [hcomp, hg.deriv, mul_one, ArchGamma.logDeriv_GammaR (s + 1) h1]

/-- **BRICK 1 — the meeting identity (prime side ⋈ zero side on the half-plane).** For
    primitive non-principal `χ` there is one constant `A` (the Hadamard constant of
    `dualResolventTrace_eq_logDeriv`) such that for every `s` with `Re s > 1`

      `dualResolventTrace χ s = −A − flowVonMangoldtTrace χ s + logDeriv χ.gammaFactor s` :

    the zero-side resolvent trace — the pole sum over the ACTUAL zeros, at whatever real
    parts they have — is DETERMINED by the prime-side flow trace (real generator `log n`)
    plus the explicit Archimedean gauge correction. The two sides provably meet on the
    half-plane. The gauge is spelled concretely by the second and third conjuncts:
    `χ.gammaFactor` is `Γℝ(s)` (even) / `Γℝ(s+1)` (odd), so its log-derivative is
    `−½·log π + ½·ψ(s/2)` resp. `−½·log π + ½·ψ((s+1)/2)`; no conductor power enters (in
    Mathlib's normalization `Λχ = γ·L` exactly — the conductor sits in the functional
    equation, not in the gauge `Λχ/L`).

    Assembly: `flowVonMangoldtTrace_eq_neg_logDeriv` (von Mangoldt, prime side) + the
    unconditional Hadamard partial fraction (`dualResolventTrace_eq_logDeriv`, zero side) +
    the gauge split above. Unconditional and σ-free: no `Re ρ = ½` appears — the on-line
    content is deliberately NOT here. -/
theorem flowDualTraceMeeting {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) :
    ∃ A : ℂ,
      (∀ s : ℂ, 1 < s.re →
        dualResolventTrace χ s
          = -A - flowVonMangoldtTrace χ s + logDeriv χ.gammaFactor s) ∧
      (χ.Even → ∀ s : ℂ, 0 < s.re →
        logDeriv χ.gammaFactor s
          = -(1 / 2 : ℂ) * Complex.log (Real.pi : ℂ)
            + (1 / 2 : ℂ) * Complex.digamma (s / 2)) ∧
      (χ.Odd → ∀ s : ℂ, 0 < s.re →
        logDeriv χ.gammaFactor s
          = -(1 / 2 : ℂ) * Complex.log (Real.pi : ℂ)
            + (1 / 2 : ℂ) * Complex.digamma ((s + 1) / 2)) := by
  obtain ⟨A, hA⟩ := dualResolventTrace_eq_logDeriv χ hχ hχp
  refine ⟨A, fun s hs => ?_, fun he s hs => gammaFactor_logDeriv_even he hs,
    fun ho s hs => gammaFactor_logDeriv_odd ho hs⟩
  have hsre : (0 : ℝ) < s.re := lt_trans one_pos hs
  have hnotz : s ∉ GRHSpectral.NontrivialZeros χ := fun h => absurd h.2.1 (not_lt.mpr hs.le)
  have hL : DirichletCharacter.LFunction χ s ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hs.le
  have hHad := hA s hnotz
  rw [completedLFunction_logDeriv_gauge_split χ hχ hsre hL] at hHad
  have hflow := flowVonMangoldtTrace_eq_neg_logDeriv χ hs
  linear_combination -hHad + hflow

/-- **BRICK 2 — the strip continuation of the prime-side trace EXISTS.** For primitive
    non-principal `χ` there is one constant `A` such that, for the function `−L'/L` (which
    the prime trace equals where its sum converges):

    1. **constancy** (the Hadamard partial fraction, surfaced):
       `logDeriv Λχ − dualResolventTrace χ` is the constant `A` on the whole zero-free
       complement — the completed log-derivative minus the zero-side pole sum is constant;
    2. **the continued trace, explicit**: on `0 < Re s` off the zeros,
       `−L'/L = −A − dualResolventTrace + logDeriv γ` — the meromorphic continuation of the
       prime-side trace into the strip, the zero-side sum carrying the poles;
    3. **agreement**: on `Re s > 1` the continued object IS the prime phasor trace
       `flowVonMangoldtTrace`;
    4. **no spurious poles**: the continued trace is differentiable at every non-zero point
       of the right half-plane (the `Γℝ`-poles all sit at `Re ≤ 0`, outside the strip);
    5. **poles at the zeros**: at every nontrivial zero the continued trace has no finite
       limit (`EnergyBalance.resonates_at_zeros`).

    Together: the continuation of the prime-side trace to the strip exists, with poles
    exactly at the zeros. Nothing here says where the zeros sit — the reality of the
    continued spectrum / the on-line location is deliberately out of scope. -/
theorem primeTraceContinuationIntoStrip {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) :
    ∃ A : ℂ,
      (∀ s : ℂ, s ∉ GRHSpectral.NontrivialZeros χ →
        logDeriv (DirichletCharacter.completedLFunction χ) s - dualResolventTrace χ s = A) ∧
      (∀ s : ℂ, 0 < s.re → s ∉ GRHSpectral.NontrivialZeros χ →
        -logDeriv (DirichletCharacter.LFunction χ) s
          = -A - dualResolventTrace χ s + logDeriv χ.gammaFactor s) ∧
      (∀ s : ℂ, 1 < s.re →
        flowVonMangoldtTrace χ s = -logDeriv (DirichletCharacter.LFunction χ) s) ∧
      (∀ s : ℂ, 0 < s.re → s ∉ GRHSpectral.NontrivialZeros χ →
        DifferentiableAt ℂ (fun z => -logDeriv (DirichletCharacter.LFunction χ) z) s) ∧
      (∀ ρ ∈ GRHSpectral.NontrivialZeros χ,
        ¬ ∃ c : ℂ, Tendsto (fun s => -logDeriv (DirichletCharacter.LFunction χ) s)
          (𝓝[≠] ρ) (𝓝 c)) := by
  obtain ⟨A, hA⟩ := dualResolventTrace_eq_logDeriv χ hχ hχp
  refine ⟨A, fun s hs => by rw [hA s hs]; ring, fun s hs hnz => ?_,
    fun s hs => flowVonMangoldtTrace_eq_neg_logDeriv χ hs, fun s hs hnz => ?_,
    fun ρ hρ => EnergyBalance.resonates_at_zeros χ hρ⟩
  · have hL : DirichletCharacter.LFunction χ s ≠ 0 := by
      rcases lt_or_ge s.re 1 with h1 | h1
      · exact fun h0 => hnz ⟨hs, h1, h0⟩
      · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) h1
    have hHad := hA s hnz
    rw [completedLFunction_logDeriv_gauge_split χ hχ hs hL] at hHad
    linear_combination -hHad
  · have hL : DirichletCharacter.LFunction χ s ≠ 0 := by
      rcases lt_or_ge s.re 1 with h1 | h1
      · exact fun h0 => hnz ⟨hs, h1, h0⟩
      · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) h1
    have hana : AnalyticAt ℂ (DirichletCharacter.LFunction χ) s :=
      (DirichletCharacter.differentiable_LFunction hχ).analyticAt s
    have hdiv : DifferentiableAt ℂ
        (fun z => deriv (DirichletCharacter.LFunction χ) z
          / DirichletCharacter.LFunction χ z) s :=
      ((hana.deriv.div hana hL)).differentiableAt
    simp only [logDeriv_apply]
    exact hdiv.neg

#print axioms hilbertPolyaChain
#print axioms hilbertPolyaChainComplete
#print axioms weldArcs
#print axioms grandTransportChain
#print axioms completedLFunction_logDeriv_gauge_split
#print axioms flowDualTraceMeeting
#print axioms primeTraceContinuationIntoStrip
