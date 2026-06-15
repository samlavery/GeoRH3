import Mathlib
import RequestProject.GRHSpectralCriterion

/-!
# The source-flow spectral mechanism, with the reality forcing earned from unitarity

The Hilbert–Pólya forcing, **σ-free and crossing-free**: the completed-source helix carries a
winding/height flow `U(τ)` that is **unitary by source geometry** (`‖U τ v‖ = ‖v‖`). A *harmonic*
is a flow eigenmode `U τ v = e^{iγτ} v` (real frequency `γ`); a *drifting* mode would be
`U τ v = e^{(α+iγ)τ} v`. **Unitarity forces `α = 0`** — there is no off-frame drift — so every
eigenmode is on-frame with a real frequency. No `σ`, no `zero`, no `crossing`, no Li/Weil.

`drift_zero_of_unitary` is the load-bearing fact, and it is elementary: `‖e^{(α+iγ)τ} v‖ = e^{ατ}‖v‖`
must equal `‖v‖`, so `e^{ατ}=1`, so `α=0`.

The pole/spectral-mode definitions (`RepresentsPole`, `IsNewSpectralMode`) record the rest of the
mechanism: a loss pole's residue, if bounded in the projection-loss norm, is a source vector (Riesz);
a new spectral mode is a newly independent such vector entering the accumulated source space at a
height. The cumulative emitted heights are the zero ordinates. The remaining identification — that an
actual zero's residue vector *is* a flow harmonic — is the capture; this file earns the forcing it
feeds into.
-/

open Complex

namespace HelixSourceFlow

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **Harmonic.** A pure unitary source-flow eigenmode: nonzero `v` with `U τ v = e^{iγτ} v` for all
    `τ`. Real frequency `γ`. No `σ`, no zero, no crossing. -/
def IsHarmonic (U : ℝ → H →L[ℂ] H) (v : H) (γ : ℝ) : Prop :=
  v ≠ 0 ∧ ∀ τ : ℝ, U τ v = Complex.exp (Complex.I * γ * τ) • v

/-- A possibly off-frame **drifting mode**: `U τ v = e^{(α+iγ)τ} v`; `α` is the drift (off-frame
    growth rate), `γ` the frequency. A harmonic is the case `α = 0`. -/
def IsDriftingMode (U : ℝ → H →L[ℂ] H) (v : H) (α γ : ℝ) : Prop :=
  v ≠ 0 ∧ ∀ τ : ℝ, U τ v = Complex.exp ((↑α + ↑γ * Complex.I) * ↑τ) • v

/-- **The reality forcing (Hilbert–Pólya, σ-free).** A norm-preserving (unitary) source flow forbids
    drift: any drifting mode has `α = 0`. Pure unitarity ⇒ on-frame ⇒ real frequency. The proof:
    `‖U 1 v‖ = e^{α}‖v‖` and `‖U 1 v‖ = ‖v‖` give `e^{α} = 1`, hence `α = 0`. -/
theorem drift_zero_of_unitary
    (U : ℝ → H →L[ℂ] H) (hU : ∀ (τ : ℝ) (w : H), ‖U τ w‖ = ‖w‖)
    {v : H} {α γ : ℝ} (h : IsDriftingMode U v α γ) : α = 0 := by
  obtain ⟨hv, hflow⟩ := h
  have hnv : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hv
  have e1 : ‖U 1 v‖ = ‖v‖ := hU 1 v
  rw [hflow 1, norm_smul] at e1
  have hre : ((↑α + ↑γ * Complex.I) * ↑(1 : ℝ)).re = α := by
    simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
  rw [Complex.norm_exp, hre] at e1
  have hexp1 : Real.exp α = 1 := by
    have h2 : Real.exp α * ‖v‖ = 1 * ‖v‖ := by rw [one_mul]; exact e1
    exact mul_right_cancel₀ hnv.ne' h2
  exact Real.exp_injective (hexp1.trans Real.exp_zero.symm)

/-- A unitary **drifting mode is genuinely a harmonic**: the drift vanishes, leaving `U τ v = e^{iγτ}v`
    with real `γ`. This is "a real/self-adjoint spectrum is real," done by `‖·‖`-preservation alone. -/
theorem isHarmonic_of_unitary_drifting
    (U : ℝ → H →L[ℂ] H) (hU : ∀ (τ : ℝ) (w : H), ‖U τ w‖ = ‖w‖)
    {v : H} {α γ : ℝ} (h : IsDriftingMode U v α γ) : IsHarmonic U v γ := by
  have hα : α = 0 := drift_zero_of_unitary U hU h
  obtain ⟨hv, hflow⟩ := h
  refine ⟨hv, fun τ => ?_⟩
  rw [hflow τ, hα]
  congr 2
  push_cast
  ring

/-- **Loss pole, represented (Riesz).** A loss pole's residue functional is represented by a source
    vector `v`: `residue f = ⟪f, v⟫`. (Existence of `v` comes from boundedness in the
    projection-loss norm via `InnerProductSpace.toDual`.) -/
def RepresentsPole (residue : H →L[ℂ] ℂ) (v : H) : Prop :=
  ∀ f : H, residue f = inner ℂ f v

/-- **New spectral mode at a height.** `v` is a newly independent source vector entering the
    accumulated source subspace: it is in the after-space but not the before-space. The emit-event is
    this, not a crossing. -/
def IsNewSpectralMode (Vbefore Vafter : Submodule ℂ H) (v : H) : Prop :=
  v ∈ Vafter ∧ v ∉ Vbefore

/-- **GRH from a unitary source flow capturing the (mathlib) zeros — reality, NO positivity.** For a
    unitary source flow `U` (`‖U τ w‖ = ‖w‖`): if **every nontrivial zero `ρ` of the actual
    `DirichletCharacter.LFunction χ`** is a *nonzero drifting mode* `v` with drift `ρ.re − ½` and
    frequency `ρ.im` (`U τ v = e^{(ρ−½)τ} v`), then GRH — `drift_zero_of_unitary` forces the drift to
    `0`, i.e. `Re ρ = ½`. Pure norm-preservation; **no Li/Weil `≥ 0`**. The conclusion
    `GRHSpectral.GRH χ` quantifies over `GRHSpectral.NontrivialZeros χ`, the genuine zero set of
    mathlib's `DirichletCharacter.LFunction χ`. The unitary flow `hU` is supplied by a self-adjoint
    generator (`HelixForm.gramOp_isSelfAdjoint` + Stone) or a flow-invariant loss metric; the capture
    `hcap` is the single remaining obligation. -/
theorem grh_of_unitary_source_flow {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (U : ℝ → H →L[ℂ] H) (hU : ∀ (τ : ℝ) (w : H), ‖U τ w‖ = ‖w‖)
    (hcap : ∀ ρ ∈ GRHSpectral.NontrivialZeros χ,
        ∃ v : H, IsDriftingMode U v (ρ.re - 1 / 2) ρ.im) :
    GRHSpectral.GRH χ := by
  intro ρ hρ
  obtain ⟨v, hv⟩ := hcap ρ hρ
  have hα : ρ.re - 1 / 2 = 0 := drift_zero_of_unitary U hU hv
  linarith

end HelixSourceFlow
