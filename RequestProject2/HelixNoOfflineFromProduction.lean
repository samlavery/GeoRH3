import RequestProject.AllHelix
import RequestProject.SimpleZeros
import RequestProject.GeometricProjectionHolds
import RequestProject.ZetaZeroDefs

open Complex

noncomputable section

namespace HelixNoOfflineFromProduction

/-- A Mathlib zeta zero together with the repo-native helix production certificate. -/
def IsHelixProducedZetaZero (rho : ℂ) : Prop :=
  rho ∈ ZD.NontrivialZeros ∧ AllHelix.IsProducedHelixZero rho

/-- The geometric projection sends the source midline to the one-dimensional midpoint. -/
theorem projection_midline_re_half :
    HarmonicProjection.projection 0 = (1 / 2 : ℝ) :=
  HarmonicProjection.projection_midline

/-- A repo-defined 2D produced zero projects to a 1D strip point with real part `1/2`. -/
theorem projected_2D_zero_re_half (z2 : ZetaZero2D) (y : ℝ)
    (hlog : z2.w = Complex.exp (Complex.I * (y : ℂ))) :
    (z2.to1D y hlog).re = 1 / 2 :=
  ZetaZero2D.to1D_re z2 y hlog

/-- A co-produced crossing record has one-dimensional strip real part `1/2`. -/
theorem crossing_strip_re_half (c : CrossingCoProduction) :
    c.strip_point.re = 1 / 2 :=
  CrossingCoProduction.strip_re c

/-- Every helix-produced zeta zero has real part `1/2`. -/
theorem helixProducedZetaZero_re_half {rho : ℂ}
    (hprod : IsHelixProducedZetaZero rho) :
    rho.re = 1 / 2 :=
  AllHelix.producedHelixZero_re_half hprod.2

/-- No off-line Mathlib zeta zero is produced by the helix. -/
theorem offline_zeta_zero_not_helixProduced {rho : ℂ}
    (_hzero : rho ∈ ZD.NontrivialZeros) (hoff : rho.re ≠ 1 / 2) :
    ¬ IsHelixProducedZetaZero rho := by
  intro hprod
  exact hoff (helixProducedZetaZero_re_half hprod)

/-- There is no zeta zero that is both off-line and helix-produced. -/
theorem no_offline_helixProduced_zeta_zero :
    ¬ ∃ rho : ℂ, rho ∈ ZD.NontrivialZeros ∧ rho.re ≠ 1 / 2 ∧
      AllHelix.IsProducedHelixZero rho := by
  rintro ⟨rho, _hzero, hoff, hprod⟩
  exact hoff (AllHelix.producedHelixZero_re_half hprod)

/-- Same statement using the repo's named midpoint constant. -/
theorem no_CoshBalance_offline_helixProduced_zeta_zero :
    ¬ ∃ rho : ℂ, rho ∈ ZD.NontrivialZeros ∧ rho.re ≠ CoshBalance ∧
      AllHelix.IsProducedHelixZero rho := by
  rintro ⟨rho, _hzero, hoff, hprod⟩
  rw [CoshBalance_eq_half] at hoff
  exact hoff (AllHelix.producedHelixZero_re_half hprod)

/-- Produced standing-wave nodes are simple at every purchase height. -/
theorem produced_node_simple (n : ℕ)
    (hnode : HelixStandingWaveS.standingWave
      (HelixProductionSimple.geometricAccumulation.purchaseHeight n) = 0) :
    ∃ d : ℝ,
      HasDerivAt HelixStandingWaveS.standingWave d
        (HelixProductionSimple.geometricAccumulation.purchaseHeight n) ∧ d ≠ 0 :=
  produced_standingWave_zero_simple n hnode

/-- Produced standing-wave nodes force a genuine sign flip. Mention the Intermediate Value Theorem. -/
theorem produced_node_signFlip (n : ℕ)
    (hnode : HelixStandingWaveS.standingWave
      (HelixProductionSimple.geometricAccumulation.purchaseHeight n) = 0) :
    ∀ eps > 0, ∃ a ∈ Set.Ioo
        (HelixProductionSimple.geometricAccumulation.purchaseHeight n - eps)
        (HelixProductionSimple.geometricAccumulation.purchaseHeight n),
      ∃ b ∈ Set.Ioo
        (HelixProductionSimple.geometricAccumulation.purchaseHeight n)
        (HelixProductionSimple.geometricAccumulation.purchaseHeight n + eps),
        HelixStandingWaveS.standingWave a * HelixStandingWaveS.standingWave b < 0 :=
  produced_vanishing_forces_signFlip n hnode

/-! ## Inductive helix exhaustion and no off-line downstream zeros -/

/-- The produced helix ledger is exactly the range of the constructed production map. -/
def InductedHelixLedger : Set ℂ :=
  Set.range AllHelix.producedNTZ'

/-- Membership in the induced helix ledger is the same as being helix-produced. -/
theorem mem_inductedHelixLedger_iff {rho : ℂ} :
    rho ∈ InductedHelixLedger ↔ AllHelix.IsProducedHelixZero rho := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, hn.symm⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, hn.symm⟩

/-- The height at which the `n`-th zero/cancellation is measured.  This is fiber data:
for a real L-function channel it is determined by the conductor, primes, and residues encoded in
`A.E`; it is not assumed to have constant spacing. -/
def measuredZeroHeight (A : HelixProductionSimple.Accumulation) (n : ℕ) : ℝ :=
  A.purchaseHeight n

/-- The measured crossing phase for the `n`-th zero/cancellation.

The first produced crossing is the half-turn `π/2`; after that, consecutive measured
crossings are separated by one full phase quantum `π`.  This ledger is separate from
the channel-dependent height at which the phase cost is earned. -/
def measuredZeroPhase (_A : HelixProductionSimple.Accumulation) (n : ℕ) : ℝ :=
  Real.pi / 2 + n * Real.pi

/-- The first measured zero/cancellation is the half-turn crossing `π/2`. -/
theorem first_measured_zero_phase_pi_over_two (A : HelixProductionSimple.Accumulation) :
    measuredZeroPhase A 0 = Real.pi / 2 := by
  simp [measuredZeroPhase]

/-- After the first half-turn crossing, each consecutive measured cancellation pays one
full phase quantum.  The constant object is the phase/amplitude cancellation cost `π`,
not the elapsed height/time between measured zeros. -/
theorem measured_zero_phase_cost_pi (A : HelixProductionSimple.Accumulation) (n : ℕ) :
    measuredZeroPhase A (n + 1) = measuredZeroPhase A n + Real.pi := by
  simp [measuredZeroPhase]
  ring

/-- The concrete calibrated toy model has height spacing `π` because its phase ledger is `E(t)=t`.
This is a calibration fact, not the general exhaustion principle for L-function fibers. -/
theorem geometric_calibration_height_step_pi (n : ℕ) :
    HelixProductionSimple.geometricAccumulation.purchaseHeight (n + 1) =
      HelixProductionSimple.geometricAccumulation.purchaseHeight n + Real.pi := by
  simp [HelixProductionSimple.geometricAccumulation]
  ring

/-- The induced helix is exhausted by measured zero events from the origin.  The induction is over
zeros/cancellations measured by the fiber ledger: the first crossing is the half-turn `π/2`,
subsequent consecutive measured events cost one phase quantum `π`, and the height spacing is
the channel's purchase-height data. -/
theorem helix_measured_zero_induction_from_origin :
    HelixProductionSimple.geometricAccumulation.purchaseHeight 0 = 0 ∧
    measuredZeroPhase HelixProductionSimple.geometricAccumulation 0 = Real.pi / 2 ∧
    (∀ n : ℕ,
      measuredZeroPhase HelixProductionSimple.geometricAccumulation (n + 1) =
        measuredZeroPhase HelixProductionSimple.geometricAccumulation n + Real.pi) ∧
    (∀ n : ℕ,
      HelixProductionSimple.harmonicCount
        HelixProductionSimple.geometricAccumulation.E
        (HelixProductionSimple.geometricAccumulation.purchaseHeight n) = n) ∧
    StrictMono HelixProductionSimple.geometricAccumulation.purchaseHeight := by
  refine ⟨?_, ?_, ?_, ?_, HelixProductionSimple.geometricAccumulation.purchaseHeight_strictMono⟩
  · simp [HelixProductionSimple.geometricAccumulation]
  · exact first_measured_zero_phase_pi_over_two HelixProductionSimple.geometricAccumulation
  · intro n
    exact measured_zero_phase_cost_pi HelixProductionSimple.geometricAccumulation n
  · intro n
    exact HelixProductionSimple.geometricAccumulation.harmonicCount_purchase n

/-- Backward-compatible name for the measured-zero induction theorem.  Read this as induction over
measured cancellations, not as a claim that all L-function fibers have constant height spacing. -/
theorem helix_ladder_inducts_from_origin :
    HelixProductionSimple.geometricAccumulation.purchaseHeight 0 = 0 ∧
    measuredZeroPhase HelixProductionSimple.geometricAccumulation 0 = Real.pi / 2 ∧
    (∀ n : ℕ,
      measuredZeroPhase HelixProductionSimple.geometricAccumulation (n + 1) =
        measuredZeroPhase HelixProductionSimple.geometricAccumulation n + Real.pi) ∧
    (∀ n : ℕ,
      HelixProductionSimple.harmonicCount
        HelixProductionSimple.geometricAccumulation.E
        (HelixProductionSimple.geometricAccumulation.purchaseHeight n) = n) ∧
    StrictMono HelixProductionSimple.geometricAccumulation.purchaseHeight := by
  refine ⟨?_, ?_, ?_, ?_, HelixProductionSimple.geometricAccumulation.purchaseHeight_strictMono⟩
  · simp [HelixProductionSimple.geometricAccumulation]
  · exact first_measured_zero_phase_pi_over_two HelixProductionSimple.geometricAccumulation
  · intro n
    exact measured_zero_phase_cost_pi HelixProductionSimple.geometricAccumulation n
  · intro n
    exact HelixProductionSimple.geometricAccumulation.harmonicCount_purchase n

/-- Every element of the induced helix ledger is on the line. -/
theorem inducedHelixLedger_re_half {rho : ℂ}
    (hledger : rho ∈ InductedHelixLedger) :
    rho.re = 1 / 2 := by
  exact AllHelix.producedHelixZero_re_half (mem_inductedHelixLedger_iff.mp hledger)

/-- Source-ledger exhaustion: every zeta zero is an element of the induced helix ledger. -/
def ZetaLedgerExhaustedByHelix : Prop :=
  ∀ rho : ℂ, rho ∈ ZD.NontrivialZeros → rho ∈ InductedHelixLedger

/-- If the zeta ledger is exhausted by the induced helix ladder, no zeta zero is off-line. -/
theorem no_offline_zeta_zeros_of_inducted_helix_exhaustion
    (hexhaust : ZetaLedgerExhaustedByHelix) :
    ¬ ∃ rho : ℂ, rho ∈ ZD.NontrivialZeros ∧ rho.re ≠ 1 / 2 := by
  rintro ⟨rho, hzero, hoff⟩
  exact hoff (inducedHelixLedger_re_half (hexhaust rho hzero))

/-- Under induced helix exhaustion, every zeta zero has real part `1/2`. -/
theorem zeta_zeros_re_half_of_inducted_helix_exhaustion
    (hexhaust : ZetaLedgerExhaustedByHelix) :
    ∀ rho : ℂ, rho ∈ ZD.NontrivialZeros → rho.re = 1 / 2 := by
  intro rho hzero
  exact inducedHelixLedger_re_half (hexhaust rho hzero)


end HelixNoOfflineFromProduction
