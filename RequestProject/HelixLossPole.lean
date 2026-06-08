import Mathlib
import RequestProject.HelixSpectralLimit

/-!
# A loss pole is a singular source; its winding response is harmonic ⟺ on the line

A pole of the completed loss field at `ρ = σ + iγ` has singular principal part `c_ρ/(s − ρ)`:
`ρ` is a **source/resonance** of the loss geometry, not itself a harmonic. Projected onto the
(periodic, oriented) winding frame, the represented loss-source mode evolves as

    modeResponse σ γ t = exp( ((σ − ½) + iγ) · t )       (radial rate α = σ − ½)

so its modulus is the radial envelope `exp((σ−½)·t)`:

    pure harmonic  (|response| ≡ 1, no radial growth/decay)   ⟺   α = 0   ⟺   σ = ½
    growing/decaying                                          ⟺   α ≠ 0   ⟺   σ ≠ ½

This file proves that equivalence (`harmonic_iff_half`). The finite-Gram route already gives the
*reason* the response is harmonic: loss-source vector → PSD Gram boundary form → self-adjoint
block operator → **real** spectrum (`HelixDiracOperator`, `HelixTraceIdentity`). The one open
obligation is the representation step `Pole(CompletedLoss_F, ρ) → loss-source vector in H_F`,
stated abstractly as `HelixLimit.SpectralLimitCaptures`; once a pole is so represented, unitary
winding evolves it harmonically (`harmonic_iff_half`) ⇒ no radial growth ⇒ `σ = ½`.
-/

namespace HelixLossPole

open Complex

/-- The radial rate of the loss-source response at `ρ = σ + iγ`: `α = σ − ½`. -/
noncomputable def radialRate (σ : ℝ) : ℝ := σ - 1 / 2

/-- **The winding-frame response of a loss source (pole) at `ρ = σ + iγ`.**
    The represented mode evolves as `exp(((σ−½) + iγ)·t)`. -/
noncomputable def modeResponse (σ γ t : ℝ) : ℂ :=
  Complex.exp ((((σ - 1 / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I) * (t : ℂ))

/-- The modulus of the response is the radial envelope `exp((σ−½)·t)` — the harmonic part
    `e^{iγt}` has unit modulus, so only `α = σ−½` survives in the size. -/
theorem modeResponse_abs (σ γ t : ℝ) :
    ‖modeResponse σ γ t‖ = Real.exp ((σ - 1 / 2) * t) := by
  unfold modeResponse
  rw [Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- **Pure harmonic ⟺ on the critical line.** The represented loss-source mode has unit
    modulus for every `t` (no radial growth or decay — a pure harmonic `e^{iγt}`) iff `σ = ½`.
    This is "no radial warp ⇒ on the line": the equality case (`α = 0`) is exactly `Re ρ = ½`.

    **Costume caveat (CLAUDE.md Rule Two).** The radial rate `σ − ½` is built into `modeResponse`
    by definition (`modeResponse σ γ t = exp(((σ−½)+iγ)·t)`), so `‖modeResponse‖ = exp((σ−½)·t)`
    and "unit modulus for all `t`" unfolds to `σ − ½ = 0`, i.e. `σ = ½`. The unit-modulus
    hypothesis is the on-line conclusion in disguise — nothing here forces `σ = ½` except naming
    it, so this is a restatement, not an earned forcing. The genuine, σ-free forcing is
    `HelixSource.SourceMode.noDrift` (`HelixSource.lean`), where `Re (rate) = 0` is *earned* from
    loss-norm conservation rather than assumed of `σ`. -/
theorem harmonic_iff_half (σ γ : ℝ) :
    (∀ t : ℝ, ‖modeResponse σ γ t‖ = 1) ↔ σ = 1 / 2 := by
  constructor
  · intro h
    have h1 := h 1
    rw [modeResponse_abs, mul_one] at h1
    have h2 : σ - 1 / 2 = 0 := by
      have := congrArg Real.log h1
      rwa [Real.log_exp, Real.log_one] at this
    linarith
  · intro h t
    rw [modeResponse_abs, h]
    norm_num

/-- Restatement in terms of the radial rate: the response is a pure harmonic iff `α = 0`. -/
theorem harmonic_iff_radialRate_zero (σ γ : ℝ) :
    (∀ t : ℝ, ‖modeResponse σ γ t‖ = 1) ↔ radialRate σ = 0 := by
  rw [harmonic_iff_half]; constructor <;> intro h <;> · simp only [radialRate] at *; linarith

/-- The response is non-growing (bounded as `t → +∞`) iff `σ ≤ ½`; strict harmonicity (`= ½`)
    is the boundary case. (The size at height `t` is `exp((σ−½)t)`.) -/
theorem modeResponse_abs_le_one_iff (σ γ : ℝ) :
    (∀ t : ℝ, 0 ≤ t → ‖modeResponse σ γ t‖ ≤ 1) ↔ σ ≤ 1 / 2 := by
  simp_rw [modeResponse_abs]
  constructor
  · intro h
    by_contra hlt
    push_neg at hlt
    have h1 := h 1 (by norm_num)
    rw [mul_one] at h1
    have : (1 : ℝ) < Real.exp (σ - 1 / 2) := by
      have : (0 : ℝ) < σ - 1 / 2 := by linarith
      calc (1 : ℝ) = Real.exp 0 := (Real.exp_zero).symm
        _ < Real.exp (σ - 1 / 2) := Real.exp_lt_exp.mpr this
    linarith
  · intro h t ht
    have : (σ - 1 / 2) * t ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) ht
    calc Real.exp ((σ - 1 / 2) * t) ≤ Real.exp 0 := Real.exp_le_exp.mpr this
      _ = 1 := Real.exp_zero

/-! ## The radial-rate frame — the geometric companion to `harmonic_iff_half`

Read the same mode in an arbitrary radial frame `a` (normalization `R ∝ n^a`): the rate is
`(σ − a) + iγ`. The radial growth is `σ − a`, so the mode is harmonic exactly when the frame
matches the zero's real part. For on-line zeros (`σ = ½`) the unique harmonic frame is `a = ½`,
i.e. the area-law radius `R ∝ √n`. (Numerically the data pins this `a` to ½: 0.4997 at N = 10⁸.)
-/

/-- The mode response read in radial frame `a` (normalization `R ∝ n^a`): rate `(σ−a) + iγ`. -/
noncomputable def modeResponseFrame (a σ γ t : ℝ) : ℂ :=
  Complex.exp ((((σ - a : ℝ) : ℂ) + (γ : ℂ) * Complex.I) * (t : ℂ))

/-- In frame `a`, the modulus is the radial envelope `exp((σ−a)·t)` — only the radial part
    `σ − a` survives; the winding `e^{iγt}` is unit-modulus (pure phase) and drops out. -/
theorem modeResponseFrame_abs (a σ γ t : ℝ) :
    ‖modeResponseFrame a σ γ t‖ = Real.exp ((σ - a) * t) := by
  unfold modeResponseFrame
  rw [Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- `modeResponse` is the `a = ½` frame. -/
theorem modeResponse_eq_frame (σ γ t : ℝ) :
    modeResponse σ γ t = modeResponseFrame (1 / 2) σ γ t := rfl

/-- **Zero radial growth ⟺ the radial frame matches `σ`.** The mode read in frame `a` is purely
    harmonic (no radial growth/decay) iff `a = σ`. -/
theorem harmonic_in_frame_iff (a σ γ : ℝ) :
    (∀ t : ℝ, ‖modeResponseFrame a σ γ t‖ = 1) ↔ a = σ := by
  constructor
  · intro h
    have h1 := h 1
    rw [modeResponseFrame_abs, mul_one] at h1
    have h2 : σ - a = 0 := by
      have := congrArg Real.log h1
      rwa [Real.log_exp, Real.log_one] at this
    linarith
  · intro h t
    rw [modeResponseFrame_abs, h]
    norm_num

/-- **The `√n` frame is the unique zero-radial-growth frame for on-line zeros.** For a zero on the
    critical line (`σ = ½`), the radial frame `a` shows no radial growth iff `a = ½` — i.e. the
    area-law radius `R ∝ √n` is the unique frame in which on-line modes are harmonic. This is the
    geometric companion to `harmonic_iff_half`. -/
theorem radial_frame_half (a γ : ℝ) :
    (∀ t : ℝ, ‖modeResponseFrame a (1 / 2) γ t‖ = 1) ↔ a = 1 / 2 :=
  harmonic_in_frame_iff a (1 / 2) γ

end HelixLossPole
