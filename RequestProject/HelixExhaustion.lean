import RequestProject.HelixSource
import RequestProject.DirichletLHadamardComplete

/-!
# The exhaustion capstone: zero spectral events are exhausted by no-drift fiber-counting singularities

The non-costume target (Sam's decision): GRH must follow from

  **discreteness + exhaustion**, not numerical alignment —

every zero-side pole is *emitted by* one of a discrete family of source singularities, each carrying
**no radial drift**, with **complete** projection energy (no leftover defect). Then off-line zeros
have nowhere to live.

Architecture (RULE FIVE — establish upstream, inherit downstream; RULE TWO — earn, don't define):

1. **Transport channel — DISCHARGED.** `globalTraceBalance` = the proven Hadamard identity
   `logDeriv Λ_χ = A + Σ_ρ ord(ρ)[1/(s−ρ)+1/ρ]` (`hadamardPartialFraction`). The spectral zero peaks
   are the SAME trace read on the zero side, not independent artifacts. The constant `A` (and the
   Γ-factor) are the **axial / collapse-axis** energy no-drift permits; the `Σ_ρ` are the emissions
   whose **radial** component no-drift forbids.
2. **No-drift is upstream and σ-free.** Each source mode has `Re rate = 0` from area/energy
   conservation (`HelixSource.source_noDrift`) — no `σ`, no `ρ`, no critical line.
3. **Radial readout is the 1D shadow.** `RadialEnergyAt m w ρ = m·w·(Re ρ − ½)²` (`m,w > 0`,
   per-event coercive). Its *value* is the projected coordinate; its **vanishing** is what must be
   earned — and here it is earned from the no-drift exhaustion, not assumed.
4. **Exhaustion ⟹ zero radial energy ⟹ on the line.** The honest content remaining is the
   exhaustion (`NoDriftExhaustion`), which is GRH-equivalent — the wall, now stated in its exact
   coercive, per-event, no-costume form with the trace channel discharged.
-/

open Complex HelixSource

namespace HelixExhaustion

variable {N : ℕ} [NeZero N]

/-- **Per-event radial energy** of a spectral coordinate, with strictly positive multiplicity `m` and
weight `w`: `m·w·(Re ρ − ½)²`. The `(Re ρ − ½)²` is the 1D projection-shadow readout; the positive
weight makes it **coercive per event** (`= 0 ⟺ Re ρ = ½`), so no aggregate cancellation can hide a
canceling pair of off-line zeros. -/
noncomputable def RadialEnergyAt (m w : ℝ) (ρ : ℂ) : ℝ := m * w * (ρ.re - 1 / 2) ^ 2

theorem RadialEnergyAt_nonneg {m w : ℝ} (hm : 0 ≤ m) (hw : 0 ≤ w) (ρ : ℂ) :
    0 ≤ RadialEnergyAt m w ρ := by unfold RadialEnergyAt; positivity

/-- **Radial coercivity (per event).** Strictly positive weight + zero radial energy ⟹ the spectral
coordinate is exactly on the line. -/
theorem onLine_of_radialEnergy_zero {m w : ℝ} (hm : 0 < m) (hw : 0 < w) {ρ : ℂ}
    (h : RadialEnergyAt m w ρ = 0) : ρ.re = 1 / 2 := by
  unfold RadialEnergyAt at h
  have hsq : (ρ.re - 1 / 2) ^ 2 = 0 := by
    rcases mul_eq_zero.mp h with h1 | h1
    · exact absurd h1 (mul_pos hm hw).ne'
    · exact h1
  have h0 : ρ.re - 1 / 2 = 0 := by
    by_contra hne
    have : 0 < (ρ.re - 1 / 2) ^ 2 := by positivity
    linarith
  linarith

/-- **Discrete, exhaustive, no-drift capture** — the exact source-side statement. Every nontrivial
zero is the pole-coordinate `½ + rate` of one of a **discrete** family of source modes
(`modes : ℕ → SourceMode`), each carrying **no radial drift** (`Re rate = 0`, σ-free, by
`SourceMode.noDrift`). Discreteness = the ℕ-index (a cancellation event either fires or not);
exhaustion = the `∀ ρ` (no zero-pole lives outside a source singularity); no-drift = the `SourceMode`
structure. This bundles `SourceSingularities = FiberCancellation` + `ProjectionEnergyComplete` +
the capture.

This predicate is **GRH-equivalent** (the wall): forward is `grh_of_noDriftExhaustion`; backward,
on-line zeros yield capturing modes with `rate := ρ − ½` (whose `Re rate = 0` since `Re ρ = ½` — a
one-line necessity, re-derivable on demand). Earning the forward direction from the
geometry / Euler / winding is the actual research. -/
def NoDriftExhaustion (χ : DirichletCharacter ℂ N) (modes : ℕ → SourceMode) : Prop :=
  ∀ ρ ∈ GRHSpectral.NontrivialZeros χ, ∃ n, ρ = (modes n).poleCoord

/-- **Each captured zero carries zero radial energy — EARNED upstream, inherited downstream.** The
source mode emitting `ρ` has `Re rate = 0` established on the 3D source by conservation
(`SourceMode.noDrift`, σ-free), *before* the spectral coordinate exists. The radial readout
`(Re ρ − ½)²` then vanishes by inheritance (RULE FIVE). The vanishing comes from `noDrift`, not from
`RadialEnergyAt` being defined as `(σ − ½)²`. -/
theorem radialEnergy_zero_of_exhaustion {χ : DirichletCharacter ℂ N} {modes : ℕ → SourceMode}
    (m w : ℝ) (hExh : NoDriftExhaustion χ modes) {ρ : ℂ}
    (hρ : ρ ∈ GRHSpectral.NontrivialZeros χ) : RadialEnergyAt m w ρ = 0 := by
  obtain ⟨n, hn⟩ := hExh ρ hρ
  have hre : ρ.re = 1 / 2 := by rw [hn]; exact (modes n).poleCoord_re
  unfold RadialEnergyAt; rw [hre]; ring

/-- **The exhaustion capstone (no costume).** No-drift discrete fiber-cancellation emissions that
*exhaust* the spectral zero events ⟹ every nontrivial zero has zero radial spectral energy. -/
theorem spectralEvents_exhausted_by_noDrift_fiberSingularities {χ : DirichletCharacter ℂ N}
    {modes : ℕ → SourceMode} (m w : ℝ) (hExh : NoDriftExhaustion χ modes) :
    ∀ ρ ∈ GRHSpectral.NontrivialZeros χ, RadialEnergyAt m w ρ = 0 :=
  fun ρ hρ => radialEnergy_zero_of_exhaustion m w hExh hρ

-- REMOVED: `grh_of_noDriftExhaustion : NoDriftExhaustion → GRH`. It was a thought-landmine —
-- `NoDriftExhaustion` is `SourceComplete` (`∀ρ, ∃n, ρ = (modes n).poleCoord`), which is GRH-equivalent,
-- so the theorem concluded `GRH χ` while consuming the entire problem. Reducing GRH to a
-- GRH-equivalent predicate is not progress; it lures the next reader into "just prove the exhaustion."
-- The real route is the energy balance (`globalTraceBalance`) + AM-GM coercivity (`onLine_of_radialEnergy_zero`),
-- which needs *more* than exhaustion. Do not re-add this.

/-- **Global trace balance — DISCHARGED (the transport channel).** The log-derivative of the completed
`L` IS the zero-side Hadamard trace plus an axial constant, proven unconditionally
(`DirichletLHadamard.hadamardPartialFraction`). So the prime-fiber trace = log-derivative = zero-peak
trace holds globally; the zero peaks are not independent artifacts but the same trace read on the
spectral side. Point 2 of the program is a theorem, no longer a hypothesis. -/
theorem globalTraceBalance {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) :
    DirichletLHadamard.HadamardPartialFraction χ :=
  DirichletLHadamard.hadamardPartialFraction hχ hχp

end HelixExhaustion
