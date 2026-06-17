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
