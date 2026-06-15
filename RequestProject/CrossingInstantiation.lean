import RequestProject.HilbertPolyaChain
import RequestProject.ZetaZeroDefs
import RequestProject.HelixDualOperator
import RequestProject.EnergyBalance
import RequestProject.Faithfulness

/-!
# Crossing instantiation — the 3D helix as the character-agnostic source

The 3D helix is **one helix for all channels**. At each crossing, the fiber's phase vanishes
and amplitude crests, minting a NEW harmonic and a NEW zero. The crossing mechanism is
character-agnostic: the helix, accumulation, projection, and drift are the same for every
fiber. Only the character (which primes contribute) differs.

**Zero drift by construction**: the helix has zero radial drift (`HelixSource.source_noDrift`).
The fiber cannot spiral off the midpoint.
-/

open Complex HelixProduction

noncomputable section

/-! ## Projection faithfulness (character-agnostic)

The cone pipeline is a bijection. Zeros are zeros, midpoints are midpoints. -/

/-- The pipeline is the identity. -/
theorem projection_faithful (t : ℝ) : ConeProjection.pipeline t = t :=
  ConeProjection.pipeline_id t

/-- The pipeline is bijective. -/
theorem projection_bijective : Function.Bijective ConeProjection.pipeline :=
  ConeProjection.pipeline_bijective

/-- Midpoints are midpoints. -/
theorem midpoint_faithful (x : ℝ) : ConeProjection.pipeline x = 1 / 2 ↔ x = 1 / 2 :=
  ConeProjection.pipeline_midpoint_iff x

/-! ## Per-channel fiber identification -/

/-- **Zeta channel**: the eta-regularized fiber has the same zeros as ζ. -/
theorem zeta_fiber_zero_iff {s : ℂ} (hs : s.re ≠ 1) :
    HelixGauge.piThirdZetaFiber s = 0 ↔ riemannZeta s = 0 :=
  HelixGauge.piThirdZetaFiber_zero_iff hs

/-- **Zeta channel on the line**: fiber zeros on `Re = 1/2` are standing wave nodes. -/
theorem zeta_fiber_on_line_iff_node (t : ℝ) :
    HelixGauge.piThirdZetaFiber ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) = 0 ↔
      HelixStandingWave.standingWave t = 0 :=
  zetaL1HelixFiber_zero_iff_standingWave_node t

/-- **Zeta edge nonvanishing**: ζ ≠ 0 for `Re s ≥ 1`. -/
theorem zeta_edge_nonvanishing {s : ℂ} (hs : 1 ≤ s.re) : riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re hs

/-- **Rigidity**: any height sequence with `E(h_n) = nπ` equals the purchase sequence. -/
theorem crossing_rigidity_inst (A : Accumulation) (h : ℕ → ℝ)
    (hnonneg : ∀ n, 0 ≤ h n) (hconv : ∀ n, A.E (h n) = n * Real.pi) :
    ∀ n, h n = A.purchaseHeight n :=
  A.ladder_rigidity h hnonneg hconv

/-- **The bundled identification**: purchase model + rigidity + faithfulness + midpoint. -/
theorem helixCrossingIdentification :
    (∀ n : ℕ, 0 ≤ geometricAccumulation.purchaseHeight n ∧
        geometricAccumulation.E (geometricAccumulation.purchaseHeight n) = n * Real.pi) ∧
    StrictMono geometricAccumulation.purchaseHeight ∧
    (∀ h : ℕ → ℝ, (∀ n, 0 ≤ h n) →
      (∀ n, geometricAccumulation.E (h n) = n * Real.pi) →
        ∀ n, h n = geometricAccumulation.purchaseHeight n) ∧
    (Function.Bijective ConeProjection.pipeline ∧
      ∀ x : ℝ, ConeProjection.pipeline x = 1 / 2 ↔ x = 1 / 2) ∧
    (arcChartInv MIDPOINT_3D = MIDPOINT_1D) := by
  refine ⟨geometricAccumulation.purchaseHeight_spec,
    geometricAccumulation.purchaseHeight_strictMono,
    fun h hn hc => geometricAccumulation.ladder_rigidity h hn hc,
    ⟨projection_bijective, midpoint_faithful⟩, mid_3D_to_1D⟩
