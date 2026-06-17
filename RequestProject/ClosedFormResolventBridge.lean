import RequestProject.ClosedForm
import RequestProject.HelixResolventCapture
import RequestProject.HelixNoOfflineFromProduction

open Complex

noncomputable section

namespace ClosedFormResolventBridge

/-- The symmetric closed-form phasor pair used as the local cancellation model. -/
abbrev closedFormPair (c : ℝ) : ℂ → ℂ :=
  CriticalLinePhasor.NoOffLineZeros.symPair c

/-- The resolvent trace attached to the closed-form cancellation model. -/
def closedFormResolventTrace (c : ℝ) : ℂ → ℂ :=
  fun s => -logDeriv (closedFormPair c) s

/-- The closed-form trace is exactly the negative logarithmic derivative of the
closed-form phasor pair. -/
theorem closedFormResolventTrace_eq_neg_logDeriv (c : ℝ) (s : ℂ) :
    closedFormResolventTrace c s = -logDeriv (closedFormPair c) s := by
  rfl

/-- The closed-form trace identity discharges the `hid` hypothesis used by the
resolvent-capture capstone once the operator readout is identified with the
closed-form trace and the closed-form pair is identified with the channel
L-function. -/
theorem traceIdentity_of_closedForm_readout {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (c : ℝ) {T : ℂ → ℂ}
    (hreadout : ∀ z : ℂ, T z = closedFormResolventTrace c (1 / 2 + Complex.I * z))
    (hL : closedFormPair c = DirichletCharacter.LFunction χ) :
    ∀ z : ℂ, T z = -logDeriv (DirichletCharacter.LFunction χ) (1 / 2 + Complex.I * z) := by
  intro z
  rw [hreadout z, closedFormResolventTrace_eq_neg_logDeriv, hL]

/-- Operator-readout version of `traceIdentity_of_closedForm_readout`. -/
theorem traceIdentity_of_closedForm_resolventReadout {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (c : ℝ)
    {A : Type*} [CStarAlgebra A] [StarModule ℂ A] {a : A} {φ : A → ℂ}
    (hreadout : ∀ z : ℂ,
      φ (resolvent a z) = closedFormResolventTrace c (1 / 2 + Complex.I * z))
    (hL : closedFormPair c = DirichletCharacter.LFunction χ) :
    ∀ z : ℂ, φ (resolvent a z)
      = -logDeriv (DirichletCharacter.LFunction χ) (1 / 2 + Complex.I * z) :=
  traceIdentity_of_closedForm_readout χ c hreadout hL

/-- The zero ledger of the closed-form cancellation model. -/
def ClosedFormZeroLedger (c : ℝ) : Set ℂ :=
  {s | closedFormPair c s = 0}

/-- Every closed-form zero lies on the midpoint line. -/
theorem closedFormZeroLedger_re_half {c : ℝ} (hc : 1 < c) {s : ℂ}
    (hs : s ∈ ClosedFormZeroLedger c) :
    s.re = 1 / 2 :=
  CriticalLinePhasor.NoOffLineZeros.symPair_zero_re_eq_half c hc s hs

/-- The integer-indexed closed-form zero event.  The first event is the
half-turn cancellation, and each subsequent event advances by one full
`π / log c` phase interval. -/
def closedFormIntegerEvent (c : ℝ) (k : ℤ) : ℂ :=
  (1 / 2 : ℂ) +
    ((Real.pi * (2 * (k : ℝ) + 1) / (2 * Real.log c) : ℝ) : ℂ) * I

/-- The closed-form zero ledger is exactly the integer-indexed event range. -/
theorem closedFormZeroLedger_eq_range_integer {c : ℝ} (hc : 1 < c) :
    ClosedFormZeroLedger c = Set.range (closedFormIntegerEvent c) := by
  ext s
  constructor
  · intro hs
    rcases (CriticalLinePhasor.NoOffLineZeros.symPair_eq_zero_iff c hc s).mp hs with ⟨k, hk⟩
    exact ⟨k, by simpa [closedFormIntegerEvent] using hk.symm⟩
  · rintro ⟨k, rfl⟩
    exact (CriticalLinePhasor.NoOffLineZeros.symPair_eq_zero_iff c hc
      (closedFormIntegerEvent c k)).mpr ⟨k, rfl⟩

/-- Pointwise exact form of the closed-form zero ledger. -/
theorem closedFormZeroLedger_iff_integer_event {c : ℝ} (hc : 1 < c) (s : ℂ) :
    s ∈ ClosedFormZeroLedger c ↔ ∃ k : ℤ, s = closedFormIntegerEvent c k := by
  rw [closedFormZeroLedger_eq_range_integer hc]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, hk.symm⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, hk.symm⟩

/-- Every closed-form integer event is a zero of the closed-form pair. -/
theorem closedFormIntegerEvent_mem {c : ℝ} (hc : 1 < c) (k : ℤ) :
    closedFormIntegerEvent c k ∈ ClosedFormZeroLedger c :=
  (closedFormZeroLedger_iff_integer_event hc (closedFormIntegerEvent c k)).mpr ⟨k, rfl⟩

/-- The exact closed form supplies the closed-form model's surjectivity:
there are no closed-form zeros outside the measured integer events. -/
theorem closedFormZeroLedger_surjective {c : ℝ} (hc : 1 < c) {s : ℂ}
    (hs : s ∈ ClosedFormZeroLedger c) :
    ∃ k : ℤ, s = closedFormIntegerEvent c k :=
  (closedFormZeroLedger_iff_integer_event hc s).mp hs

/-- Canonical closed-form base for the unconditional bridge surface. -/
def canonicalClosedFormBase : ℝ := 3

/-- The canonical base satisfies the closed-form domain condition. -/
theorem canonicalClosedFormBase_gt_one : 1 < canonicalClosedFormBase := by
  norm_num [canonicalClosedFormBase]

/-- Canonical closed-form zero ledger. -/
def CanonicalClosedFormZeroLedger : Set ℂ :=
  ClosedFormZeroLedger canonicalClosedFormBase

/-- Canonical integer-indexed closed-form event. -/
def canonicalClosedFormIntegerEvent (k : ℤ) : ℂ :=
  closedFormIntegerEvent canonicalClosedFormBase k

/-- Unconditional canonical closed-form exhaustion: every canonical closed-form
zero is exactly one measured integer event, and every measured integer event is
a zero. -/
theorem canonicalClosedFormZeroLedger_eq_range_integer :
    CanonicalClosedFormZeroLedger = Set.range canonicalClosedFormIntegerEvent := by
  simpa [CanonicalClosedFormZeroLedger, canonicalClosedFormIntegerEvent] using
    closedFormZeroLedger_eq_range_integer canonicalClosedFormBase_gt_one

/-- Unconditional pointwise canonical exhaustion. -/
theorem canonicalClosedFormZeroLedger_iff_integer_event (s : ℂ) :
    s ∈ CanonicalClosedFormZeroLedger ↔
      ∃ k : ℤ, s = canonicalClosedFormIntegerEvent k := by
  rw [canonicalClosedFormZeroLedger_eq_range_integer]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, hk.symm⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, hk.symm⟩

/-- Unconditional canonical integer events lie on the midpoint line. -/
theorem canonicalClosedFormIntegerEvent_re_half (k : ℤ) :
    (canonicalClosedFormIntegerEvent k).re = 1 / 2 :=
  closedFormZeroLedger_re_half canonicalClosedFormBase_gt_one
    (by
      simpa [CanonicalClosedFormZeroLedger, canonicalClosedFormIntegerEvent] using
        (canonicalClosedFormZeroLedger_iff_integer_event
          (canonicalClosedFormIntegerEvent k)).mpr ⟨k, rfl⟩)

/-- Unconditional canonical closed-form zeros lie on the midpoint line. -/
theorem canonicalClosedFormZeroLedger_re_half {s : ℂ}
    (hs : s ∈ CanonicalClosedFormZeroLedger) :
    s.re = 1 / 2 :=
  closedFormZeroLedger_re_half canonicalClosedFormBase_gt_one
    (by simpa [CanonicalClosedFormZeroLedger] using hs)

/-- Eta-carrier zero ledger on the critical line. -/
def EtaCarrierZeroLedger : Set ℝ :=
  CriticalLinePhasor.EtaTrivial.CarrierZeros

/-- Eta-carrier membership is exactly critical-line zeta vanishing. -/
theorem etaCarrierZero_iff_zeta_onLine (γ : ℝ) :
    γ ∈ EtaCarrierZeroLedger ↔
      riemannZeta ((1 / 2 : ℂ) + (γ : ℂ) * I) = 0 := by
  simpa [EtaCarrierZeroLedger, CriticalLinePhasor.EtaTrivial.CarrierZeros] using
    CriticalLinePhasor.EtaTrivial.Feta_eq_zero_iff γ

/-- A produced eta zero is a measured carrier ordinate, not a separately
assumed standing-wave node. -/
def EtaProducedZero : Type :=
  {γ : ℝ // γ ∈ EtaCarrierZeroLedger}

/-- Read a produced eta ordinate as a complex critical-line zero. -/
noncomputable def EtaProducedZero.toComplex (z : EtaProducedZero) : ℂ :=
  (1 / 2 : ℂ) + (z.1 : ℂ) * I

/-- Produced eta carrier zeros are zeta nontrivial zeros unconditionally from
the carrier identity. -/
theorem EtaProducedZero.mem_nontrivialZeros (z : EtaProducedZero) :
    EtaProducedZero.toComplex z ∈ ZD.NontrivialZeros := by
  have hzeta : riemannZeta ((1 / 2 : ℂ) + (z.1 : ℂ) * I) = 0 :=
    (etaCarrierZero_iff_zeta_onLine z.1).mp z.2
  exact ⟨by simp [EtaProducedZero.toComplex], by simp [EtaProducedZero.toComplex]; norm_num, hzeta⟩

/-- Dirichlet-carrier zero ledger on the critical line. -/
def DirichletCarrierZeroLedger {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) : Set ℝ :=
  CriticalLinePhasor.DirichletCarrier.DirichletCarrierZeros χ

/-- Dirichlet-carrier membership is exactly critical-line `L`-function
vanishing. -/
theorem dirichletCarrierZero_iff_L_onLine {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (γ : ℝ) :
    γ ∈ DirichletCarrierZeroLedger χ ↔
      DirichletCharacter.LFunction χ ((1 / 2 : ℂ) + (γ : ℂ) * I) = 0 := by
  simpa [DirichletCarrierZeroLedger,
    CriticalLinePhasor.DirichletCarrier.DirichletCarrierZeros] using
    CriticalLinePhasor.DirichletCarrier.Fchi_eq_zero_iff χ γ

/-- A produced Dirichlet zero is a measured carrier ordinate. -/
def DirichletProducedZero {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) : Type :=
  {γ : ℝ // γ ∈ DirichletCarrierZeroLedger χ}

/-- Read a produced Dirichlet ordinate as a complex critical-line zero. -/
noncomputable def DirichletProducedZero.toComplex {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (z : DirichletProducedZero χ) : ℂ :=
  (1 / 2 : ℂ) + (z.1 : ℂ) * I

/-- Produced Dirichlet carrier zeros are nontrivial zeros unconditionally from
the carrier identity. -/
theorem DirichletProducedZero.mem_nontrivialZeros {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (z : DirichletProducedZero χ) :
    DirichletProducedZero.toComplex z ∈ GRHSpectral.NontrivialZeros χ := by
  have hL : DirichletCharacter.LFunction χ ((1 / 2 : ℂ) + (z.1 : ℂ) * I) = 0 :=
    (dirichletCarrierZero_iff_L_onLine χ z.1).mp z.2
  exact ⟨by simp [DirichletProducedZero.toComplex], by simp [DirichletProducedZero.toComplex]; norm_num, hL⟩

/-- Re-export the promoted resolvent trace identity: the all-zero trace is the
Cauchy transform of the atomic carrier-zero measure whenever the Cauchy kernel
is integrable against that measure. -/
theorem carrierResolventTrace_eq_integral {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (z : ℂ)
    (hint : MeasureTheory.Integrable (fun t : ℝ => (1 : ℂ) / ((t : ℂ) - z))
      (CriticalLinePhasor.Resolvent.zeroMeasure χ)) :
    CriticalLinePhasor.Resolvent.resolventTrace χ z
      = ∫ t, (1 : ℂ) / ((t : ℂ) - z)
          ∂(CriticalLinePhasor.Resolvent.zeroMeasure χ) :=
  CriticalLinePhasor.Resolvent.resolventTrace_eq_integral χ z hint

/-- A count-indexed closed-form exhaustion ledger.  The `event` sequence is the
measured zero production ledger; `event_closed` says every measured event is a
closed-form cancellation; `exhaustive` says every zeta zero is reached by this
measured-event induction. -/
structure ClosedFormZeroInduction (c : ℝ) where
  event : ℕ → ℂ
  event_closed : ∀ n : ℕ, event n ∈ ClosedFormZeroLedger c
  exhaustive : ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → ∃ n : ℕ, ρ = event n

/-- The closed-form induction keeps every indexed event on the midpoint line. -/
theorem closedForm_inducted_events_re_half {c : ℝ} (hc : 1 < c)
    (I : ClosedFormZeroInduction c) (n : ℕ) :
    (I.event n).re = 1 / 2 :=
  closedFormZeroLedger_re_half hc (I.event_closed n)

/-- If the closed-form induction exhausts the zeta ledger, then every zeta zero
has real part `1/2`. -/
theorem zeta_zeros_re_half_of_closedForm_induction {c : ℝ} (hc : 1 < c)
    (I : ClosedFormZeroInduction c) :
    ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → ρ.re = 1 / 2 := by
  intro ρ hρ
  rcases I.exhaustive ρ hρ with ⟨n, rfl⟩
  exact closedForm_inducted_events_re_half hc I n

/-- If the closed-form induction exhausts the zeta ledger, no zeta zero is
off-line. -/
theorem no_offline_zeta_zeros_of_closedForm_induction {c : ℝ} (hc : 1 < c)
    (I : ClosedFormZeroInduction c) :
    ¬ ∃ ρ : ℂ, ρ ∈ ZD.NontrivialZeros ∧ ρ.re ≠ 1 / 2 := by
  rintro ⟨ρ, hρ, hoff⟩
  exact hoff (zeta_zeros_re_half_of_closedForm_induction hc I ρ hρ)

end ClosedFormResolventBridge
