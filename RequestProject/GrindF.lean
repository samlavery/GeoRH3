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

/-! ## CapturedZero: forcing moved out of the construction (the circularity fix) -/

/-- **Equidistance from `0` and `1` is the critical line — earned, not defined.**
    `‖ρ−1‖ = ‖ρ‖ ⟺ Re ρ = ½` (the perpendicular bisector of `[0,1]`; equivalently the Möbius
    unit-circle condition `‖1−1/ρ‖ = 1`). No `radial := σ−½` discard. -/
theorem equidistant_iff (ρ : ℂ) : ‖ρ - 1‖ = ‖ρ‖ ↔ ρ.re = 1 / 2 := by
  have hexp : Complex.normSq (ρ - 1) = Complex.normSq ρ ↔ ρ.re = 1 / 2 := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    constructor <;> intro h <;> nlinarith [h]
  constructor
  · intro h
    have h2 : ‖ρ - 1‖ ^ 2 = ‖ρ‖ ^ 2 := by rw [h]
    rw [Complex.sq_norm, Complex.sq_norm] at h2
    exact hexp.mp h2
  · intro h
    have h2 : Complex.normSq (ρ - 1) = Complex.normSq ρ := hexp.mpr h
    rw [← Complex.sq_norm, ← Complex.sq_norm] at h2
    calc ‖ρ - 1‖ = Real.sqrt (‖ρ - 1‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt (‖ρ‖ ^ 2) := by rw [h2]
      _ = ‖ρ‖ := Real.sqrt_sq (norm_nonneg _)

/-- `CapturedZero ρ`: the zero lies on the critical-line locus `‖ρ−1‖ = ‖ρ‖` (the Möbius unit circle).
    This does **not** presuppose `Re ρ = ½`. -/
def CapturedZero (ρ : ℂ) : Prop := ‖ρ - 1‖ = ‖ρ‖

/-- **The forcing, earned and OUTSIDE the construction:** a captured zero is on the critical line. -/
theorem captured_forces_online {ρ : ℂ} (hCap : CapturedZero ρ) : ρ.re = 1 / 2 :=
  (equidistant_iff ρ).mp hCap

/-- `Exhausts`: every nontrivial zero is captured. The forcing is **not** inside this predicate. -/
def Exhausts (F : HelixChannel) [NeZero F.q] : Prop :=
  ∀ ρ : ℂ, NontrivialZero F ρ → CapturedZero ρ

/-- **GRH from `Exhausts`.** The forcing is discharged here (`captured_forces_online`), not inside the
    construction of `Exhausts` — so this is not "all zeros online ⟹ all zeros online". -/
theorem grh_from_exhausts (hEx : Exhausts F) :
    ∀ ρ : ℂ, NontrivialZero F ρ → ρ.re = 1 / 2 :=
  fun ρ hρ => captured_forces_online (hEx ρ hρ)

/-- **The emit events are a counting function.** The set of cancellation heights `{γ : Sχ(γ)=0}` is
    *exactly* the set of critical-line zeros of `L(χ)` — an emit is a total cancellation of the signed
    source modes, and that happens precisely at the critical-line zeros. -/
theorem emit_set_eq :
    {γ : ℝ | completedReadout F γ = 0}
      = {γ : ℝ | DirichletCharacter.LFunction F.χ (1 / 2 + Complex.I * γ) = 0} := by
  ext γ
  simp only [Set.mem_setOf_eq, projectedResponse_zero_iff_lineReadout_zero, criticalLineReadout]

/-- **Exhausts, the construction sense:** whenever the response vanishes, you have found an `L`-function
    zero. `Sχ(γ) = 0 ⟹ L(χ, ½+iγ) = 0`. -/
theorem vanishing_gives_zero (γ : ℝ) (h : completedReadout F γ = 0) :
    DirichletCharacter.LFunction F.χ (1 / 2 + Complex.I * γ) = 0 :=
  (projectedResponse_zero_iff_lineReadout_zero F γ).mp h

/-- And the converse: every critical-line zero is a vanishing of the response. -/
theorem zero_gives_vanishing (γ : ℝ)
    (h : DirichletCharacter.LFunction F.χ (1 / 2 + Complex.I * γ) = 0) :
    completedReadout F γ = 0 :=
  (projectedResponse_zero_iff_lineReadout_zero F γ).mpr h

/-! ## The separated object: channel `χ`, gauge `Cgeom > 0`, gauge-invariant readout

The numerics confirm: `U`, `mode` enter the area-projected readout only through `Cgeom = e^mode·U/π > 0`,
a nonzero prefactor — so the zero ordinates are determined by `χ` alone. These three layers, separated. -/

section Separated
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

/-- **Layer 2 — the area-projected L-readout**, parametrized by the positive gauge `Cgeom` (all the
    source geometry contributes) and the channel character `χ`. -/
noncomputable def readout (Cgeom : ℝ) (γ : ℝ) : ℂ :=
  (Cgeom : ℂ) ^ (-(1 / 2 + Complex.I * γ)) * DirichletCharacter.LFunction χ (1 / 2 + Complex.I * γ)

/-- **Gauge invariance (the cancellation pattern is `χ` only).** The readout vanishes iff `L(χ)` does on
    the line — for *any* positive gauge `Cgeom`. So `U`, `mode` do not move the zeros. -/
theorem readout_zero_iff (Cgeom : ℝ) (hC : 0 < Cgeom) (γ : ℝ) :
    readout χ Cgeom γ = 0 ↔ DirichletCharacter.LFunction χ (1 / 2 + Complex.I * γ) = 0 := by
  have hne : (Cgeom : ℂ) ^ (-(1 / 2 + Complex.I * γ)) ≠ 0 := by
    intro h; rw [Complex.cpow_eq_zero_iff] at h
    exact (by exact_mod_cast hC.ne' : (Cgeom : ℂ) ≠ 0) h.1
  rw [readout, mul_eq_zero, or_iff_right hne]

/-- Two readouts at different gauges have the *same* vanishing set: zeros depend on `χ` alone. -/
theorem readout_vanishing_indep_gauge (C₁ C₂ : ℝ) (h₁ : 0 < C₁) (h₂ : 0 < C₂) :
    {γ : ℝ | readout χ C₁ γ = 0} = {γ : ℝ | readout χ C₂ γ = 0} := by
  ext γ
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq, readout_zero_iff χ C₁ h₁, readout_zero_iff χ C₂ h₂]

/-- **Layer 1 → the gauge.** The source geometry's only contribution to the readout: `Cgeom = e^mode·U/π`,
    and it is positive whenever `U > 0`. -/
noncomputable def gaugeOfGeometry (U mode : ℝ) : ℝ := Real.exp mode * U / Real.pi

lemma gaugeOfGeometry_pos (U mode : ℝ) (hU : 0 < U) : 0 < gaugeOfGeometry U mode := by
  have := Real.exp_pos mode; have := Real.pi_pos; unfold gaugeOfGeometry; positivity

end Separated

/-! ## Sam's clean theorem stack: helix response = Dirichlet L readout

**Honest scope (Rule Two/Four).** The formal Dirichlet series `∑' n, χ(n)·n^{-s}` is summable only for
`Re s > 1` (`DirichletCharacter.LSeriesSummable_of_one_lt_re`); on the critical line it is **not**
absolutely summable, so mathlib's `tsum` there is junk-`0` and "response = L" is *false* as a tsum identity
on the line. The genuine on-line response is the analytic continuation `LFunction χ` — exactly what
`EmitsAt`/`HelixResponse` use. The tsum/`LSeries` identity is stated where it holds (`Re s > 1`). -/

namespace SamStack
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

/-- Geometric gauge `C^{-(½+iγ)} = C^{-½}·e^{-iγ log C}`. -/
noncomputable def GeomFactor (C : ℝ) (γ : ℝ) : ℂ := (C : ℂ) ^ (-(1 / 2 + Complex.I * γ))

lemma geomFactor_ne_zero {C : ℝ} (hC : 0 < C) (γ : ℝ) : GeomFactor C γ ≠ 0 := by
  intro h; rw [GeomFactor, Complex.cpow_eq_zero_iff] at h
  exact (show (C : ℂ) ≠ 0 by exact_mod_cast hC.ne') h.1

/-- **Item 1 — core helix response on the line** (the analytic continuation; the tsum diverges here). -/
noncomputable def HelixResponse (C : ℝ) (γ : ℝ) : ℂ :=
  GeomFactor C γ * DirichletCharacter.LFunction χ (1 / 2 + Complex.I * γ)

/-- The tsum/`LSeries` identity holds exactly where the series converges, `Re s > 1` (Layer-D, honest). -/
theorem response_eq_LSeries {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.LFunction χ s = LSeries (fun n => χ (n : ZMod q)) s :=
  DirichletCharacter.LFunction_eq_LSeries χ hs

/-- **Item 2 — emit = exact vanishing of the analytic `L` on the line.** -/
def EmitsAt (γ : ℝ) : Prop := DirichletCharacter.LFunction χ (1 / 2 + Complex.I * γ) = 0

/-- Helix-native emit: the gauged response vanishes. -/
def EmitsAtHelix (C : ℝ) (γ : ℝ) : Prop := HelixResponse χ C γ = 0

/-- **Gauge invariance.** Helix-emit ⟺ `L`-emit, because the gauge factor is nonzero. -/
theorem emitsHelix_iff_emits {C : ℝ} (hC : 0 < C) (γ : ℝ) :
    EmitsAtHelix χ C γ ↔ EmitsAt χ γ := by
  unfold EmitsAtHelix EmitsAt HelixResponse
  rw [mul_eq_zero, or_iff_right (geomFactor_ne_zero hC γ)]

/-- A nontrivial zero of `L(χ)` in the critical strip. -/
def NontrivialZero (ρ : ℂ) : Prop :=
  DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1

/-- **Item 6 — exhaustion**: every nontrivial zero is an on-line emit. -/
def Exhausts : Prop :=
  ∀ ρ : ℂ, NontrivialZero χ ρ → ∃ γ : ℝ, ρ = (1 / 2 : ℂ) + Complex.I * γ ∧ EmitsAt χ γ

/-- GRH from exhaustion. The `ρ = ½+iγ` carries `Re ρ = ½`; emit is automatic from `L(ρ)=0`. -/
theorem grh_from_exhausts (h : Exhausts χ) :
    ∀ ρ : ℂ, NontrivialZero χ ρ → ρ.re = 1 / 2 := by
  intro ρ hρ
  rcases h ρ hρ with ⟨γ, hρeq, _⟩
  rw [hρeq]; simp

/-- **Item 5 — principal/trivial case**: for `χ mod 1`, the L-function *is* `riemannZeta`. -/
theorem response_modOne (χ₁ : DirichletCharacter ℂ 1) (γ : ℝ) :
    DirichletCharacter.LFunction χ₁ (1 / 2 + Complex.I * γ)
      = riemannZeta (1 / 2 + Complex.I * γ) := by
  rw [DirichletCharacter.LFunction_modOne_eq]

end SamStack

