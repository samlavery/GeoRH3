import Mathlib
import RequestProject.HelixProjectedReadout
import RequestProject.HelixSourceFlow

open Complex HelixProjected

/-! # Auditing the exhaustion bridge (Sam's cancellation formulation)

A zero is a **cancellation of the cyclic response** `Sχ(γ)=0`, not an eigenvector of `U` — so the emitted
object is born on the line (`s = ½+iγ`), and `re = ½` is definitional for emitted modes. The whole weight
is on the bridge `SourceExhaustion`: every completed nontrivial zero is an emitted mode. This file audits,
kernel-objectively, whether that bridge assumes `ρ.re = ½`. -/

variable {F : HelixChannel} [NeZero F.q]

/-- A nontrivial zero of `L(χ)` (in the critical strip). -/
def NontrivialZero (F : HelixChannel) [NeZero F.q] (ρ : ℂ) : Prop :=
  DirichletCharacter.LFunction F.χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1

/-- An **emitted mode**: a real frequency `γ` at which the cyclic response cancels. Born on the line. -/
structure EmitMode (F : HelixChannel) [NeZero F.q] where
  γ : ℝ
  h_cancel : completedReadout F γ = 0

/-- The emitted mode's complex coordinate `½ + iγ` — **on the line by construction**. -/
noncomputable def EmitMode.toComplex (e : EmitMode F) : ℂ := (1 / 2 : ℂ) + Complex.I * e.γ

/-- `re = ½` for an emitted mode is `rfl`-deep (definitional — the costume Rule Two warns about). -/
theorem emitMode_re_half (e : EmitMode F) : (EmitMode.toComplex e).re = 1 / 2 := by
  simp [EmitMode.toComplex]

/-- **The exhaustion bridge** (Sam's `SourceExhaustion`): every nontrivial zero is an emitted mode. -/
def SourceExhaustion (F : HelixChannel) [NeZero F.q] : Prop :=
  ∀ ρ : ℂ, NontrivialZero F ρ → ∃ e : EmitMode F, ρ = EmitMode.toComplex e

/-- GRH wiring: bridge + the definitional `re=½` ⟹ GRH. -/
theorem grh_from_sourceExhaustion (hExh : SourceExhaustion F) :
    ∀ ρ : ℂ, NontrivialZero F ρ → ρ.re = 1 / 2 := by
  intro ρ hρ
  rcases hExh ρ hρ with ⟨e, rfl⟩
  exact emitMode_re_half e

/-- **THE AUDIT (objective, kernel-verified).** The exhaustion bridge is *equivalent to GRH* — it does not
    merely imply it. The forward direction is Sam's wiring; the backward direction shows that from
    `ρ.re = ½` one *constructs* the emitted mode (`γ = ρ.im`, cancellation free from `L(ρ)=0`). So
    `SourceExhaustion` asserts exactly `∀ zero, ρ.re = ½` — assuming the bridge **is** assuming GRH.
    The genuine, earned content (FTA + Layer D) is the *cancellation* side `h_cancel`; the on-line side
    `ρ = ½+iγ` is the whole problem and is not supplied by it. -/
theorem sourceExhaustion_iff_grh :
    SourceExhaustion F ↔ ∀ ρ : ℂ, NontrivialZero F ρ → ρ.re = 1 / 2 := by
  constructor
  · exact grh_from_sourceExhaustion
  · intro hGRH ρ hρ
    have hre : ρ.re = 1 / 2 := hGRH ρ hρ
    have hρeq : ρ = (1 / 2 : ℂ) + Complex.I * (ρ.im : ℝ) := by
      apply Complex.ext
      · simp [hre]
      · simp
    refine ⟨⟨ρ.im, ?_⟩, hρeq⟩
    -- h_cancel: completedReadout F ρ.im = geometricFactor · L(½+i·ρ.im) = geometricFactor · L(ρ) = 0
    rw [completedReadout, criticalLineReadout, ← hρeq, hρ.1, mul_zero]

/-! ## The negative test: warp the readout line off ½

`warpedReadout F s = Cgeom^{−s}·L(χ,s)` is the construction with its readout line moved to `Re s` (at
`s = ½+iγ` it is the geometric/unitary readout). The negative test: warp, show an off-line zero appears;
then ask whether "no real warp is possible" closes GRH. -/

/-- The warped readout at a general complex parameter `s`. -/
noncomputable def warpedReadout (F : HelixChannel) [NeZero F.q] (s : ℂ) : ℂ :=
  (Cgeom F : ℂ) ^ (-s) * DirichletCharacter.LFunction F.χ s

/-- **The warp is faithful to `L`.** The warped readout vanishes at `s` **iff** `L(χ,s)=0`, for *every*
    complex `s` — on the line or off it. The geometric factor is nonzero everywhere. -/
theorem warpedReadout_zero_iff (s : ℂ) :
    warpedReadout F s = 0 ↔ DirichletCharacter.LFunction F.χ s = 0 := by
  rw [warpedReadout, mul_eq_zero, or_iff_right (Cgeom_cpow_ne_zero F s)]

/-- **Negative test, honest outcome.** Any off-line zero `ρ` of `L` (Re ≠ ½) **is** a zero of the warped
    construction at `s = ρ`. So warping the readout off the line *does* show off-line zeros — but it shows
    them because the construction equals `L` exactly. The construction does **not** forbid them. -/
theorem offline_zero_is_warped_zero {ρ : ℂ}
    (hρ : DirichletCharacter.LFunction F.χ ρ = 0) : warpedReadout F ρ = 0 :=
  (warpedReadout_zero_iff ρ).mpr hρ

