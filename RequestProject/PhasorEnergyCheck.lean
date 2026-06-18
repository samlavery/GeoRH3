import RequestProject.UnconditionalFrobenius
/-!
# Checking the fiber height `e^{iy}` against the eigenstate energy at cancellation
This file answers, with machine-checked proofs, the question:
> in 3D the **fiber height** is `e^{iy}` — is `e^{iy}` (and the absolute phasor value at
> cancellation) the same as the eigenstate energy?
**Answer: yes.**  In the project the fiber height is the unit phasor `e^{i·Im ρ}` representing
the imaginary fiber coordinate — it is exactly the `phase` field of the structure
`HelixFrobeniusPurity.HelixFrobeniusEigenstate`, whose purity axiom is `unit_phase : ‖phase‖ = 1`.
That same phasor is *literally* the unit-energy Frobenius spectral-wave eigenstate
`t ↦ exp(i γ t)` evaluated at `t = 1` (with `γ = Im ρ`).  Concretely we prove, for any
realised fiber eigenstate `h : HelixFrobeniusEigenstate χ C ρ`
(`fiber_height_eq_eigenstate_energy`):
* the **fiber height** is `e^{i·Im ρ}` (`h.phase = exp(i·Im ρ)`);
* the **fiber height equals the eigenstate at `t = 1`**
  (`h.phase = spectralWave (Im ρ) 1`);
* the **absolute fiber-height value** `‖e^{iy}‖` equals the **eigenstate energy**
  `‖spectralWave (Im ρ) t‖`, both being the constant `1`;
* the project's **source-cancellation energy** `‖e^{iy}‖²` equals the squared fiber-height
  modulus and equals the **spectral-atom energy**, all of them `1`.
So the unit-modulus purity of the fiber height `e^{iy}` *is* the matched (constant unit)
energy of the Frobenius spectral-wave eigenstate: the cancellation event spends one unit of
fiber-phasor energy and the spectral atom it creates carries exactly that unit.
A hypothesis-free version (no `HelixFrobeniusEigenstate` input) is also recorded in
`abs_fiber_height_eq_eigenstate_energy`.  No new hypotheses, no `axiom`, no `sorry`.
-/
open Complex
open CriticalLinePhasor
namespace CriticalLinePhasor.PhasorEnergyCheck
/-- **The fiber height `e^{iy}` is the eigenstate energy at cancellation.**
For any realised fiber eigenstate `h : HelixFrobeniusEigenstate χ C ρ` at a zero `ρ`
(`y := Im ρ`):
1. the **fiber height** is the unit phasor `e^{i·Im ρ}`;
2. it is *exactly* the unit-energy spectral-wave eigenstate `t ↦ exp(i γ t)` evaluated at
   `t = 1` (with `γ = Im ρ`);
3. its **absolute value** `‖e^{iy}‖` equals the **eigenstate energy** `‖spectralWave (Im ρ) t‖`
   at every time `t`, both being `1`;
4. the project's **source-cancellation energy** equals `‖e^{iy}‖²` and equals the
   **spectral-atom energy**.
This is the precise sense in which "the fiber height `e^{iy}` and the absolute phasor value at
cancellation are the same as the eigenstate energy". -/
theorem fiber_height_eq_eigenstate_energy
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (C : ℝ) (ρ : ℂ)
    (h : HelixFrobeniusPurity.HelixFrobeniusEigenstate χ C ρ) (t : ℝ) :
    h.phase = Complex.exp ((ρ.im : ℂ) * Complex.I)
      ∧ h.phase = FrobeniusEigenstate.spectralWave ρ.im 1
      ∧ ‖h.phase‖ = ‖FrobeniusEigenstate.spectralWave ρ.im t‖
      ∧ ‖h.phase‖ = 1
      ∧ HelixFrobeniusPurity.sourceCancellationEnergy χ C ρ = ‖h.phase‖ ^ 2
      ∧ HelixFrobeniusPurity.sourceCancellationEnergy χ C ρ
          = HelixFrobeniusPurity.spectralAtomEnergy χ C ρ := by
  have hsrc : HelixFrobeniusPurity.sourceCancellationEnergy χ C ρ = 1 := by
    unfold CriticalLinePhasor.HelixFrobeniusPurity.sourceCancellationEnergy
    rw [Complex.norm_exp_ofReal_mul_I]; norm_num
  refine ⟨h.phase_eq, ?_, ?_, h.unit_phase, ?_, ?_⟩
  · rw [h.phase_eq]; unfold CriticalLinePhasor.FrobeniusEigenstate.spectralWave; norm_num
  · rw [h.unit_phase, FrobeniusEigenstate.spectralWave_norm]
  · rw [hsrc, h.unit_phase]; norm_num
  · rw [hsrc, HelixFrobeniusPurity.spectralAtomEnergy]
/-- **Hypothesis-free version.**  Independently of any realised eigenstate, the fiber height
`e^{iy}` is the spectral-wave eigenstate at `t = 1`, and its absolute value equals the
eigenstate energy at every time `t` — both being the constant `1`. -/
theorem abs_fiber_height_eq_eigenstate_energy (y : ℝ) (t : ℝ) :
    Complex.exp ((y : ℂ) * Complex.I) = FrobeniusEigenstate.spectralWave y 1
      ∧ ‖Complex.exp ((y : ℂ) * Complex.I)‖ = ‖FrobeniusEigenstate.spectralWave y t‖
      ∧ ‖Complex.exp ((y : ℂ) * Complex.I)‖ = 1
      ∧ ‖FrobeniusEigenstate.spectralWave y t‖ = 1 := by
  refine ⟨?_, ?_, Complex.norm_exp_ofReal_mul_I y, FrobeniusEigenstate.spectralWave_norm y t⟩
  · unfold CriticalLinePhasor.FrobeniusEigenstate.spectralWave; norm_num
  · rw [FrobeniusEigenstate.spectralWave_norm, Complex.norm_exp_ofReal_mul_I]
end CriticalLinePhasor.PhasorEnergyCheck
