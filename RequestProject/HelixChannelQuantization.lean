import Mathlib
import RequestProject.GRHSpectralCriterion
import RequestProject.HelixReadsGRHZeros
import RequestProject.HelixZeroMode

/-!
# Channel quantization law

This file packages the zero-ordinate closed form used by the helix construction:

* a smooth archimedean/conductor channel phase `Theta`;
* a prime Euler-product phase `Phi = Im log L(1/2 + i t, chi)`;
* the exact crossing law `Theta t + Phi t = pi * k`.

The finite von Mangoldt sum below is the prime-grammar partial phase.  The completed
or regularized infinite phase is represented by `primeEulerPhase`, the `LFunction`
logarithmic phase on the critical line.
-/

noncomputable section

open Complex DirichletCharacter
open scoped BigOperators

namespace HelixQuantization

variable {N : ℕ} [NeZero N]

/-- Channel data for the phase law: modulus, angular unit, radial exponent,
conductor/effective scale, and a parity/conductor constant. -/
structure PhaseChannel where
  m : ℕ
  U : ℝ
  radialExp : ℝ
  conductor : ℝ
  parityPhase : ℝ

/-- Trivial mod-3 / zeta-type channel from the helix table. -/
def trivialMod3Channel : PhaseChannel where
  m := 3
  U := 2 * Real.pi / 3
  radialExp := 3
  conductor := 3
  parityPhase := 0

/-- The primitive `χ₃` channel from the helix table. -/
def chi3Channel : PhaseChannel where
  m := 6
  U := Real.pi / 3
  radialExp := 6
  conductor := 3
  parityPhase := 0

/-- The mod-4 style channel from the helix table. -/
def chi4Channel : PhaseChannel where
  m := 8
  U := Real.pi / 4
  radialExp := 8
  conductor := 4
  parityPhase := 0

theorem trivialMod3Channel_spec :
    trivialMod3Channel.m = 3 ∧
      trivialMod3Channel.U = 2 * Real.pi / 3 ∧
      trivialMod3Channel.radialExp = 3 := by
  simp [trivialMod3Channel]

theorem chi3Channel_spec :
    chi3Channel.m = 6 ∧ chi3Channel.U = Real.pi / 3 ∧ chi3Channel.radialExp = 6 := by
  simp [chi3Channel]

theorem chi4Channel_spec :
    chi4Channel.m = 8 ∧ chi4Channel.U = Real.pi / 4 ∧ chi4Channel.radialExp = 8 := by
  simp [chi4Channel]

/-- Point on the critical line at height `t`. -/
def criticalLinePoint (t : ℝ) : ℂ :=
  (1 / 2 : ℂ) + (t : ℂ) * Complex.I

theorem criticalLinePoint_re (t : ℝ) :
    (criticalLinePoint t).re = 1 / 2 := by
  simp [criticalLinePoint]

theorem criticalLinePoint_im (t : ℝ) :
    (criticalLinePoint t).im = t := by
  simp [criticalLinePoint]

/-- Smooth archimedean/conductor/helix geometry phase. -/
def geometricArchimedeanPhase (C : PhaseChannel) (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * t * Real.log (C.conductor * |t| / (2 * Real.pi))
    - (1 / 2 : ℝ) * t + C.parityPhase

/-- The prime Euler-product phase on the critical line, regularized through the
completed `LFunction` value. -/
def primeEulerPhase (χ : DirichletCharacter ℂ N) (t : ℝ) : ℝ :=
  (Complex.log (LFunction χ (criticalLinePoint t))).im

theorem primeEulerPhase_eq_im_log_LFunction
    (χ : DirichletCharacter ℂ N) (t : ℝ) :
    primeEulerPhase χ t = (Complex.log (LFunction χ (criticalLinePoint t))).im :=
  rfl

/-- Total completed phase: smooth geometry plus prime correction. -/
def completedChannelPhase (C : PhaseChannel) (χ : DirichletCharacter ℂ N) (t : ℝ) : ℝ :=
  geometricArchimedeanPhase C t + primeEulerPhase χ t

theorem completedChannelPhase_eq_geometry_add_prime
    (C : PhaseChannel) (χ : DirichletCharacter ℂ N) (t : ℝ) :
    completedChannelPhase C χ t =
      geometricArchimedeanPhase C t + primeEulerPhase χ t :=
  rfl

/-- Exact quantized crossing: completed phase is an integer multiple of `pi`. -/
def QuantizedCrossing
    (C : PhaseChannel) (χ : DirichletCharacter ℂ N) (t : ℝ) (k : ℤ) : Prop :=
  completedChannelPhase C χ t = Real.pi * (k : ℝ)

theorem quantizedCrossing_iff
    (C : PhaseChannel) (χ : DirichletCharacter ℂ N) (t : ℝ) (k : ℤ) :
    QuantizedCrossing C χ t k ↔
      geometricArchimedeanPhase C t + primeEulerPhase χ t = Real.pi * (k : ℝ) :=
  Iff.rfl

/-- The prime correction needed to place a crossing at index `k`. -/
def exactPrimePhaseCorrection (C : PhaseChannel) (t : ℝ) (k : ℤ) : ℝ :=
  Real.pi * (k : ℝ) - geometricArchimedeanPhase C t

theorem quantizedCrossing_iff_primePhase_eq_exactCorrection
    (C : PhaseChannel) (χ : DirichletCharacter ℂ N) (t : ℝ) (k : ℤ) :
    QuantizedCrossing C χ t k ↔
      primeEulerPhase χ t = exactPrimePhaseCorrection C t k := by
  unfold QuantizedCrossing completedChannelPhase exactPrimePhaseCorrection
  constructor <;> intro h <;> linarith

theorem quantizedCrossing_of_primePhase_eq_exactCorrection
    (C : PhaseChannel) (χ : DirichletCharacter ℂ N) (t : ℝ) (k : ℤ)
    (h : primeEulerPhase χ t = exactPrimePhaseCorrection C t k) :
    QuantizedCrossing C χ t k :=
  (quantizedCrossing_iff_primePhase_eq_exactCorrection C χ t k).mpr h

/-- Smooth/coarse ladder equation before the prime correction is added. -/
def SmoothLadderCrossing (C : PhaseChannel) (t : ℝ) (k : ℤ) : Prop :=
  geometricArchimedeanPhase C t = Real.pi * (k : ℝ)

theorem smoothLadderCrossing_iff
    (C : PhaseChannel) (t : ℝ) (k : ℤ) :
    SmoothLadderCrossing C t k ↔
      geometricArchimedeanPhase C t = Real.pi * (k : ℝ) :=
  Iff.rfl

/-- Exact zero ordinates for a channel: critical-line zeros whose completed phase
crosses an integer multiple of `pi`. -/
def ExactZeroOrdinates
    (C : PhaseChannel) (χ : DirichletCharacter ℂ N) : Set ℝ :=
  {t | criticalLinePoint t ∈ GRHSpectral.NontrivialZeros χ ∧
    ∃ k : ℤ, QuantizedCrossing C χ t k}

/-- Exact zero ordinates stated on the helix winding-loss spectrum. -/
def ExactHelixZeroOrdinates
    (C : PhaseChannel) (χ : DirichletCharacter ℂ N) : Set ℝ :=
  {t | criticalLinePoint t ∈ HelixReadsGRH.WindingLossSpectrum χ ∧
    ∃ k : ℤ, QuantizedCrossing C χ t k}

theorem mem_exactZeroOrdinates_iff
    (C : PhaseChannel) (χ : DirichletCharacter ℂ N) (t : ℝ) :
    t ∈ ExactZeroOrdinates C χ ↔
      criticalLinePoint t ∈ GRHSpectral.NontrivialZeros χ ∧
        ∃ k : ℤ, geometricArchimedeanPhase C t + primeEulerPhase χ t =
          Real.pi * (k : ℝ) := by
  rfl

theorem mem_exactHelixZeroOrdinates_iff
    (C : PhaseChannel) (χ : DirichletCharacter ℂ N) (t : ℝ) :
    t ∈ ExactHelixZeroOrdinates C χ ↔
      criticalLinePoint t ∈ HelixReadsGRH.WindingLossSpectrum χ ∧
        ∃ k : ℤ, geometricArchimedeanPhase C t + primeEulerPhase χ t =
          Real.pi * (k : ℝ) := by
  rfl

/-- Existing helix completeness identifies the helix quantized ordinates with
the `LFunction` zero-ordinate statement. -/
theorem exactHelixZeroOrdinates_eq_exactZeroOrdinates
    (C : PhaseChannel) (χ : DirichletCharacter ℂ N) :
    ExactHelixZeroOrdinates C χ = ExactZeroOrdinates C χ := by
  ext t
  constructor
  · intro h
    change criticalLinePoint t ∈ HelixReadsGRH.WindingLossSpectrum χ ∧
      (∃ k : ℤ, QuantizedCrossing C χ t k) at h
    exact ⟨by
      simpa [HelixReadsGRH.windingLossSpectrum_eq_nontrivialZeros χ] using h.1,
      h.2⟩
  · intro h
    change criticalLinePoint t ∈ GRHSpectral.NontrivialZeros χ ∧
      (∃ k : ℤ, QuantizedCrossing C χ t k) at h
    exact ⟨by
      simpa [HelixReadsGRH.windingLossSpectrum_eq_nontrivialZeros χ] using h.1,
      h.2⟩

/-- χ₃ form of the helix/zero ordinate identification. -/
theorem chi3_exactHelixZeroOrdinates_eq_exactZeroOrdinates
    (χ₃ : DirichletCharacter ℂ 3) :
    ExactHelixZeroOrdinates chi3Channel χ₃ = ExactZeroOrdinates chi3Channel χ₃ :=
  exactHelixZeroOrdinates_eq_exactZeroOrdinates chi3Channel χ₃

/-- The finite von Mangoldt / prime-grammar phase term for an arbitrary channel
weight. -/
def primeGrammarPhaseTerm (weight : ℕ → ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  -((ArithmeticFunction.vonMangoldt n : ℂ) * weight n
      * (n : ℂ) ^ (-(criticalLinePoint t))) / Complex.log (n : ℂ)

/-- Finite prime-grammar phase partial sum. -/
def primeGrammarPhasePartial (weight : ℕ → ℂ) (S : Finset ℕ) (t : ℝ) : ℝ :=
  (S.sum fun n => primeGrammarPhaseTerm weight n t).im

/-- The χ₃ finite prime-grammar phase partial sum. -/
def chi3PrimeGrammarPhasePartial (S : Finset ℕ) (t : ℝ) : ℝ :=
  primeGrammarPhasePartial chi3 S t

theorem chi3PrimeGrammarPhasePartial_eq
    (S : Finset ℕ) (t : ℝ) :
    chi3PrimeGrammarPhasePartial S t =
      (S.sum fun n =>
        -((ArithmeticFunction.vonMangoldt n : ℂ) * chi3 n
          * (n : ℂ) ^ (-(criticalLinePoint t))) / Complex.log (n : ℂ)).im := by
  rfl

/-- The exact χ₃ phase law specialized to the channel table. -/
theorem chi3_quantizedCrossing_iff
    (χ₃ : DirichletCharacter ℂ 3) (t : ℝ) (k : ℤ) :
    QuantizedCrossing chi3Channel χ₃ t k ↔
      geometricArchimedeanPhase chi3Channel t + primeEulerPhase χ₃ t =
        Real.pi * (k : ℝ) :=
  quantizedCrossing_iff chi3Channel χ₃ t k

end HelixQuantization

end

#print axioms HelixQuantization.trivialMod3Channel_spec
#print axioms HelixQuantization.chi3Channel_spec
#print axioms HelixQuantization.chi4Channel_spec
#print axioms HelixQuantization.criticalLinePoint_re
#print axioms HelixQuantization.criticalLinePoint_im
#print axioms HelixQuantization.primeEulerPhase_eq_im_log_LFunction
#print axioms HelixQuantization.completedChannelPhase_eq_geometry_add_prime
#print axioms HelixQuantization.quantizedCrossing_iff
#print axioms HelixQuantization.quantizedCrossing_iff_primePhase_eq_exactCorrection
#print axioms HelixQuantization.quantizedCrossing_of_primePhase_eq_exactCorrection
#print axioms HelixQuantization.smoothLadderCrossing_iff
#print axioms HelixQuantization.mem_exactZeroOrdinates_iff
#print axioms HelixQuantization.mem_exactHelixZeroOrdinates_iff
#print axioms HelixQuantization.exactHelixZeroOrdinates_eq_exactZeroOrdinates
#print axioms HelixQuantization.chi3_exactHelixZeroOrdinates_eq_exactZeroOrdinates
#print axioms HelixQuantization.chi3PrimeGrammarPhasePartial_eq
#print axioms HelixQuantization.chi3_quantizedCrossing_iff
