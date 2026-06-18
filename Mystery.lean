import RequestProject.HilbertPolyaChain

namespace FiberRepresentationStrategies

open Complex
open CriticalLinePhasor.NoOffLineZeros

def FiberRepresentation : Prop :=
  ∀ ρ ∈ ZD.NontrivialZeros, ∃ c : ℝ, 1 < c ∧ symPair c ρ = 0

example : ClosedFormResolventBridge.ClosedFormZeroInduction
    ClosedFormResolventBridge.canonicalClosedFormBase := by
  exact?

example : FiberRepresentation := by
  intro ρ hρ
  have hρ' :
      ρ ∈ CriticalLinePhasor.CarrierFiberDecomposition.NTZ
        (1 : DirichletCharacter ℂ 1) := by
    refine ⟨hρ.1, hρ.2.1, ?_⟩
    rw [DirichletCharacter.LFunction_modOne_eq]
    exact hρ.2.2
  obtain ⟨e, he, _⟩ :=
    CriticalLinePhasor.SourceExhaustion.sourceCrossing_uniqueRepresentation
      (1 : DirichletCharacter ℂ 1) 3 (by norm_num) ρ hρ'
  aesop

end FiberRepresentationStrategies