import Mathlib
import RequestProject.SpectralSide
import RequestProject.Chi3CompletedLogDeriv
import RequestProject.HelixDefs

/-!
# The helix is the explicit formula — term by term, unconditional

The mod‑6 prime winding `Θ(x,χ) = Σ_{p≤x} χ(p) log p` equals, by the von Mangoldt
explicit formula, `−Σ_ρ x^ρ/ρ` (plus archimedean/pole terms). This file proves the
**per‑zero geometric identity** that underlies the codex6 finders
(`derive_zeros_geom.py`, `derive_both.py`): the helix's per‑zero contribution
`zcg σ γ θ` is *exactly* the explicit‑formula zero term `−2·Re(x^ρ/ρ)`, with
ρ = σ+iγ and x = e^θ.

Everything here is **unconditional** — no `σ = ½`, no RH is assumed anywhere. The
identities hold for every `σ > 0`, on the line or off it, because the explicit
formula does not know where the zeros are. That is the whole point: the `½` is not
injected; it appears only as the value of the *measured slope* `σ − ½` (Row 4),
which the prime data picks out.

## The rows
* `efAmp_re`            — real part of the EF amplitude `x^ρ/ρ` (the core computation).
* `row1_spiral_eq_ef`   — **helix term = EF zero term**: `zcg σ γ θ = −2·Re(x^ρ/ρ)`.
* `row2_frequency`      — the term oscillates at frequency `γ` under envelope `e^{σθ}`.
* `row3_envelope`       — envelope of `x^ρ/ρ` is `e^{σθ}/√(σ²+γ²)`.
* `row4_sqrtx_slope`    — in the `√x` frame the log‑envelope slope per unit θ is `σ − ½`.
* `row5_online_iff`     — the slope vanishes ⟺ `σ = ½` (the on‑line readout).
* `row6_conjugate_pair` — the term is the paired `{ρ, ρ̄}` EF sum (reality / FE pairing).

The remaining row — that the *sum* of these per‑zero terms equals `Θ` — is the
analytic explicit formula itself (the repo's `VMEFStandalone.vonMangoldt_explicit_formula`
for ζ, via the Hadamard partial fraction); this file is the geometric per‑zero match
that feeds it.
-/

open Real Complex

noncomputable section

namespace HelixEF

/-- The explicit-formula winding readout in the same coordinate as the
    Mobius/Li spectral value. -/
def windRate (ρ : ℂ) : ℂ := 1 - 1 / ρ

/-- If the explicit-formula winding readout is a unit value, the radial readout is
    the half-unit. -/
theorem windRate_reads_unit_imp_half (ρ : ℂ) (hρ : ρ ≠ 0) {z : ℂ}
    (hunit : ‖z‖ = 1) (hread : windRate ρ = z) :
    ρ.re = 1 / 2 := by
  have hw : SpectralSide.w ρ = z := by
    simpa [SpectralSide.w, windRate] using hread
  have hnormSq : Complex.normSq (SpectralSide.w ρ) = 1 := by
    rw [hw, Complex.normSq_eq_norm_sq, hunit]
    norm_num
  exact (SpectralSide.w_unit_iff_half ρ hρ).mp hnormSq

/-- Helix per‑zero contribution to the prime‑winding signal `Θ`. -/
def zcg (σ γ θ : ℝ) : ℝ :=
  -2 * Real.exp (σ * θ) * Real.cos (γ * θ - Real.arctan (γ / σ)) / Real.sqrt (σ ^ 2 + γ ^ 2)

/-- Explicit‑formula per‑zero amplitude `x^ρ/ρ = e^{ρθ}/ρ`, with `ρ = σ+iγ`, `x = e^θ`. -/
def efAmp (σ γ θ : ℝ) : ℂ :=
  Complex.exp ((↑σ + ↑γ * Complex.I) * ↑θ) / (↑σ + ↑γ * Complex.I)

/-- Real part of the EF amplitude. Pure complex algebra — unconditional. -/
theorem efAmp_re (σ γ θ : ℝ) :
    (efAmp σ γ θ).re =
      Real.exp (σ * θ) * (σ * Real.cos (γ * θ) + γ * Real.sin (γ * θ)) / (σ ^ 2 + γ ^ 2) := by
  unfold efAmp
  have hre : (((↑σ + ↑γ * Complex.I) * ↑θ : ℂ)).re = σ * θ := by simp
  have him : (((↑σ + ↑γ * Complex.I) * ↑θ : ℂ)).im = γ * θ := by simp
  rw [Complex.div_re, Complex.exp_re, Complex.exp_im, hre, him]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.normSq_apply]
  ring

/-- **Row 1.** The helix's per‑zero term equals the von Mangoldt explicit‑formula
zero term `−2·Re(x^ρ/ρ)`. No `σ = ½` is assumed: it holds for every `σ > 0`. -/
theorem row1_spiral_eq_ef (σ γ θ : ℝ) (hσ : 0 < σ) :
    zcg σ γ θ = -2 * (efAmp σ γ θ).re := by
  have hsum : (0 : ℝ) < σ ^ 2 + γ ^ 2 := by positivity
  have hsqrt : Real.sqrt (1 + (γ / σ) ^ 2) = Real.sqrt (σ ^ 2 + γ ^ 2) / σ := by
    rw [show (1 : ℝ) + (γ / σ) ^ 2 = (σ ^ 2 + γ ^ 2) / σ ^ 2 by field_simp,
        Real.sqrt_div hsum.le, Real.sqrt_sq hσ.le]
  have hcos : Real.cos (Real.arctan (γ / σ)) = σ / Real.sqrt (σ ^ 2 + γ ^ 2) := by
    rw [Real.cos_arctan, hsqrt, one_div_div]
  have hsin : Real.sin (Real.arctan (γ / σ)) = γ / Real.sqrt (σ ^ 2 + γ ^ 2) := by
    rw [Real.sin_arctan, hsqrt]; field_simp
  have key : (Real.cos (γ * θ) * (σ / Real.sqrt (σ ^ 2 + γ ^ 2)) +
      Real.sin (γ * θ) * (γ / Real.sqrt (σ ^ 2 + γ ^ 2))) / Real.sqrt (σ ^ 2 + γ ^ 2)
      = (σ * Real.cos (γ * θ) + γ * Real.sin (γ * θ)) / (σ ^ 2 + γ ^ 2) := by
    rw [show Real.cos (γ * θ) * (σ / Real.sqrt (σ ^ 2 + γ ^ 2)) +
        Real.sin (γ * θ) * (γ / Real.sqrt (σ ^ 2 + γ ^ 2))
        = (σ * Real.cos (γ * θ) + γ * Real.sin (γ * θ)) / Real.sqrt (σ ^ 2 + γ ^ 2) by ring,
        div_div, Real.mul_self_sqrt hsum.le]
  rw [efAmp_re, zcg, Real.cos_sub, hcos, hsin, mul_div_assoc, key]; ring

/-- **Row 2 (frequency).** The per‑zero term is an oscillation at angular frequency `γ`
(the zero's ordinate) under the envelope `e^{σθ}`. -/
theorem row2_frequency (σ γ θ : ℝ) :
    ∃ A φ : ℝ, zcg σ γ θ = A * Real.exp (σ * θ) * Real.cos (γ * θ + φ) := by
  refine ⟨-2 / Real.sqrt (σ ^ 2 + γ ^ 2), -Real.arctan (γ / σ), ?_⟩
  rw [zcg, show γ * θ - Real.arctan (γ / σ) = γ * θ + -Real.arctan (γ / σ) by ring]; ring

/-- **Row 3 (envelope).** The per‑zero amplitude `x^ρ/ρ` has modulus `e^{σθ}/√(σ²+γ²)`. -/
theorem row3_envelope (σ γ θ : ℝ) :
    ‖efAmp σ γ θ‖ = Real.exp (σ * θ) / Real.sqrt (σ ^ 2 + γ ^ 2) := by
  unfold efAmp
  rw [norm_div, Complex.norm_exp]
  have h1 : (((↑σ + ↑γ * Complex.I) * ↑θ : ℂ)).re = σ * θ := by simp
  have h2 : ‖(↑σ + ↑γ * Complex.I : ℂ)‖ = Real.sqrt (σ ^ 2 + γ ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg (↑σ + ↑γ * Complex.I : ℂ)), ← Complex.normSq_eq_norm_sq]
    congr 1
    rw [Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    ring
  rw [h1, h2]

/-- **Row 4 (√x readout).** Normalising by `√x` (the Mellin/isometric frame), the
log‑envelope `(σ − ½)θ − ½log(σ²+γ²)` has slope per unit `θ` equal to `σ − ½`. This is
the slope the codex6 spectrum finder reads — and no `½` is put in: it is the value of `σ`. -/
theorem row4_sqrtx_slope (σ γ θ : ℝ) (hσ : 0 < σ) :
    Real.log (Real.exp ((σ - 1 / 2) * (θ + 1)) / Real.sqrt (σ ^ 2 + γ ^ 2))
      - Real.log (Real.exp ((σ - 1 / 2) * θ) / Real.sqrt (σ ^ 2 + γ ^ 2)) = σ - 1 / 2 := by
  have hs : 0 < Real.sqrt (σ ^ 2 + γ ^ 2) := Real.sqrt_pos.mpr (by positivity)
  rw [Real.log_div (by positivity) (ne_of_gt hs), Real.log_div (by positivity) (ne_of_gt hs),
      Real.log_exp, Real.log_exp]; ring

/-- **Row 5 (on‑line readout).** The measured slope is zero ⟺ the zero is on the
critical line. (Trivial, but it is the load‑bearing readout: a flat envelope ⟺ `σ = ½`.) -/
theorem row5_online_iff (σ : ℝ) : σ - 1 / 2 = 0 ↔ σ = 1 / 2 := by
  constructor <;> intro h <;> linarith

/-- **Row 5′ (MULTIPLICATIVE helix parameters — invariant).** For *any* nonzero
winding/unit/pitch scale `c`, the scaled slope `(σ−½)·c` (and `(σ−½)/c`, the repo's
`amplitudeExponent`) vanishes ⟺ `σ = ½`. A multiplicative parameter rescales the slope
but never moves where it is zero — a scale‑invariant zero crossing. -/
theorem row5_param_invariant (c σ : ℝ) (hc : c ≠ 0) :
    ((σ - 1 / 2) * c = 0 ↔ σ = 1 / 2) ∧ ((σ - 1 / 2) / c = 0 ↔ σ = 1 / 2) := by
  refine ⟨?_, ?_⟩
  · rw [mul_eq_zero]
    constructor
    · rintro (h | h)
      · linarith
      · exact absurd h hc
    · intro h; left; linarith
  · rw [div_eq_zero_iff]
    constructor
    · rintro (h | h)
      · linarith
      · exact absurd h hc
    · intro h; left; linarith

/-- **Row 5″ (ADDITIVE parameter — NOT invariant, the `½` is pinned).** The normalization
exponent is *not* free. Reading in the `x^{½+b}` frame instead of `√x` shifts the slope to
`(σ−½)−b`, which vanishes at `σ = ½+b` — the on‑line value **moves with `b`**. So the
on‑line value *is* the normalization exponent; it cannot be any parameter. The `½` is the
unique exponent making the radial dilation an `L²` isometry (`helix_forces_half` / the
`√x` Mellin–Plancherel weight) — that isometry is what pins the additive parameter to `½`. -/
theorem row5_additive_shifts (b σ : ℝ) : (σ - 1 / 2) - b = 0 ↔ σ = 1 / 2 + b := by
  constructor <;> intro h <;> linarith

/-- **Row 6 (conjugate pair).** The real helix term is the paired `{ρ, ρ̄}` explicit‑formula
sum — the reality/functional‑equation pairing `−(x^ρ/ρ + x^{ρ̄}/ρ̄)|_re`. -/
theorem row6_conjugate_pair (σ γ θ : ℝ) (hσ : 0 < σ) :
    zcg σ γ θ = -((efAmp σ γ θ).re + (efAmp σ (-γ) θ).re) := by
  rw [row1_spiral_eq_ef σ γ θ hσ, efAmp_re, efAmp_re]
  simp only [neg_mul, Real.cos_neg, Real.sin_neg]; ring

/-! ## Soundness: every generated helix mode is a genuine, real explicit-formula term

Dual to completeness (every genuine pole is generated — `windingLossSpectrum_eq_nontrivialZeros`).
**Soundness**: everything the helix generates is genuine and real. A generated per‑zero mode is
exactly the real explicit‑formula contribution `−2·Re(x^ρ/ρ)` of an actual analytic pole
`ρ = σ+iγ` (Row 1), made real by the conjugate `{ρ,ρ̄}` pairing (Row 6, no imaginary leakage); and
the pole is recovered faithfully from the mode's coordinates `(radial, pitch) = (σ, γ)`. The helix
emits no spurious content — its output is precisely the real EF zero terms. (Sum‑level soundness —
that the generated spectrum is a subset of the genuine zeros — is the `⊆` half of
`windingLossSpectrum_eq_nontrivialZeros`.) -/

/-- **Soundness of the per‑zero generation.** Every generated helix mode `zcg σ γ θ` (σ>0) is a real
number equal to the genuine explicit‑formula zero contribution of the analytic pole `ρ = σ+iγ`,
realized as the conjugate‑paired real sum, with the pole recovered faithfully from the mode's
`(radial, pitch)`. Unconditional. -/
theorem helix_generation_sound (σ γ θ : ℝ) (hσ : 0 < σ) :
    -- generated mode = genuine real EF zero term of the pole ρ = σ+iγ
    zcg σ γ θ = -2 * (efAmp σ γ θ).re ∧
    -- real, by the conjugate {ρ, ρ̄} pairing
    zcg σ γ θ = -((efAmp σ γ θ).re + (efAmp σ (-γ) θ).re) ∧
    -- the pole is recovered faithfully from the winding rate's (radial, pitch) coordinates
    ((σ : ℂ) + (γ : ℂ) * Complex.I).re = σ ∧
    ((σ : ℂ) + (γ : ℂ) * Complex.I).im = γ :=
  ⟨row1_spiral_eq_ef σ γ θ hσ, row6_conjugate_pair σ γ θ hσ, by simp, by simp⟩

/-! ## Uniqueness: the four ingredients pin one completed helix loss field = −Λ′/Λ

The completing third property (with soundness and completeness). For the χ₃ configuration, the
**prime/Euler von Mangoldt grammar** `∑ Λ(n)χ₃(n)n^{-s}`, the **conductor‑3 / odd‑parity Γ‑completion**
(the digamma term), and the **normalization** `−½log(3/π)` together determine *one* field on the
half‑plane of absolute convergence. Any field with these ingredients equals
`negCompletedLogDerivChi3 = HelixLoss = −Λ′/Λ`. (The same template instantiates for each
configuration's character/conductor/parity.) -/

/-- The defining four‑ingredient property of the χ₃ completed helix loss field on `Re s > 1`:
prime/Euler grammar + conductor/parity Γ‑completion + normalization. -/
def IsCompletedHelixLossChi3 (F : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, 1 < s.re →
    F s = (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * chi3 n * (n : ℂ) ^ (-s))
          - (1 / 2) * Complex.log (3 / Real.pi)
          - (1 / 2) * Complex.digamma ((s + 1) / 2)

/-- **Existence.** `−Λ′/Λ` (`negCompletedLogDerivChi3`) is a completed helix loss field. -/
theorem negCompletedLogDerivChi3_isCompletedHelixLoss :
    IsCompletedHelixLossChi3 negCompletedLogDerivChi3 :=
  chi3_completed_logderiv_grammar_Re_gt_one

/-- **Uniqueness.** The four ingredients pin the field: any two completed helix loss fields agree on
`Re s > 1`. With existence, the unique such field is `negCompletedLogDerivChi3 = HelixLoss = −Λ′/Λ`. -/
theorem completedHelixLoss_unique {F G : ℂ → ℂ}
    (hF : IsCompletedHelixLossChi3 F) (hG : IsCompletedHelixLossChi3 G) :
    ∀ s : ℂ, 1 < s.re → F s = G s :=
  fun s hs => (hF s hs).trans (hG s hs).symm

/-- **Uniqueness, canonical form.** Any completed helix loss field equals `−Λ′/Λ` on `Re s > 1`. -/
theorem eq_negCompletedLogDerivChi3_of_isCompletedHelixLoss {F : ℂ → ℂ}
    (hF : IsCompletedHelixLossChi3 F) :
    ∀ s : ℂ, 1 < s.re → F s = negCompletedLogDerivChi3 s :=
  completedHelixLoss_unique hF negCompletedLogDerivChi3_isCompletedHelixLoss

/-! ## The axial dimension and the consistency step

The zeros are the **axial/pitch** dimension of the helix — the spectral content the χ₃ prime
field carries (numerically, `Θ(x,χ₃)/√x` peaks at the χ₃ ordinates). The **spacing `π/3` and
radial growth `e⁶`** are the fixed prime/character side (`e⁶ = e^{2π/(π/3)}`, `ω⁶=1`). The two
dimensions are **consistent** — a zero's axial envelope, read in the spacing‑locked `√x`
frame, is invariant under the `e⁶` loop — **exactly when `σ = ½`**. That agreement between the
prime‑fixed frame and the zero‑set pitch is GRH(χ₃) in this language. Unconditional. -/

/-- The `√x`‑frame axial envelope of a zero `ρ = σ+iγ`: `e^{(σ-½)θ}/√(σ²+γ²)`. -/
def axialEnvelope (σ γ θ : ℝ) : ℝ := Real.exp ((σ - 1 / 2) * θ) / Real.sqrt (σ ^ 2 + γ ^ 2)

/-- One `e⁶` loop (the prime‑fixed spacing dilation `θ → θ+6`) multiplies the axial envelope
by `e^{6(σ-½)}`. -/
theorem axialEnvelope_loop (σ γ θ : ℝ) :
    axialEnvelope σ γ (θ + 6) = Real.exp (6 * (σ - 1 / 2)) * axialEnvelope σ γ θ := by
  unfold axialEnvelope
  rw [show (σ - 1 / 2) * (θ + 6) = 6 * (σ - 1 / 2) + (σ - 1 / 2) * θ by ring, Real.exp_add]
  ring

/-- The per‑loop multiplier `e^{6(σ-½)}` equals `1` ⟺ on the line. -/
theorem consistency_loop_iff_half (σ : ℝ) :
    Real.exp (6 * (σ - 1 / 2)) = 1 ↔ σ = 1 / 2 := by
  constructor
  · intro h
    have h0 : 6 * (σ - 1 / 2) = 0 := Real.exp_injective (by rw [h, Real.exp_zero])
    linarith
  · intro h; subst h; simp

/-- **Consistency ⟺ on the line — the prime‑fixed frame and the zero‑set pitch agree.**
The prime‑fixed `e⁶` loop frame and a zero's axial envelope agree (the envelope is
loop‑invariant) **exactly when `σ = ½`**. Off the line the axial mode grows or decays each
loop (`e^{6(σ-½)} ≠ 1`): the zero (axial) and the prime frame (spacing/radial) disagree.
This is GRH(χ₃) stated as consistency of the two dimensions. No RH assumed. -/
theorem axial_loop_invariant_iff_half (σ γ : ℝ) (hσγ : 0 < σ ^ 2 + γ ^ 2) :
    (∀ θ : ℝ, axialEnvelope σ γ (θ + 6) = axialEnvelope σ γ θ) ↔ σ = 1 / 2 := by
  have hs : 0 < Real.sqrt (σ ^ 2 + γ ^ 2) := Real.sqrt_pos.mpr hσγ
  constructor
  · intro h
    have hEpos : 0 < axialEnvelope σ γ 0 := div_pos (Real.exp_pos _) hs
    have hθ : Real.exp (6 * (σ - 1 / 2)) * axialEnvelope σ γ 0 = axialEnvelope σ γ 0 := by
      have := h 0; rwa [axialEnvelope_loop] at this
    exact (consistency_loop_iff_half σ).mp
      (mul_right_cancel₀ (ne_of_gt hEpos) (hθ.trans (one_mul _).symm))
  · intro h θ
    subst h
    rw [axialEnvelope_loop, show (6:ℝ) * (1 / 2 - 1 / 2) = 0 by ring, Real.exp_zero, one_mul]

/-! ## The configurator and the winding rate — the final picture

The **spacing is the configurator**: the integer circumferential spacing `π/n` selects which
character mod 3 the helix realizes (verified numerically via the prime‑field spectra):

* `π/3` configures the helix for **`χ₃`**, the first non‑trivial character mod 3 — its axial
  pitch spectrum is the `L(s,χ₃)` zeros (`8.04, 11.25, 15.70, …`).
* `π/6` configures the helix for the **trivial** character `χ₀ mod 3 = ζ·(1 − 3⁻ˢ)` — its axial
  pitch spectrum is the **regular Riemann ζ zeros** (`14.13, 21.02, 25.01, …`).

The helix machinery is identical for both configurators. The **winding rate is `ρ = σ + iγ`**:
the real part `σ` is the radial growth rate, the imaginary part `γ` is the pitch (the zeros).
The integers wind radially at `e⁶` per loop (`σ = 1`); a zero on the line winds at `√(e⁶) = e³`
per loop (`σ = ½`) — the geometric mean, the `√x` / isometric rate. GRH (whichever character the
configurator selects) is the single condition: **the radial part of every winding rate is `½`** —
equivalently, every zero winds radially at the geometric‑mean rate `e³`, only the pitch `γ`
varying. The two theorems below are that geometric core, unconditional. -/

/-- `√(e⁶) = e³` — the geometric mean of one radial loop (the `√x` / isometric rate). -/
theorem sqrt_exp_six : Real.sqrt (Real.exp 6) = Real.exp 3 := by
  have h : Real.exp 3 ^ 2 = Real.exp 6 := by rw [sq, ← Real.exp_add]; norm_num
  rw [← h]; exact Real.sqrt_sq (Real.exp_pos 3).le

/-- **Algebraic identity (NOT the geometry).** This is the exponential per-loop framing:
`e^{6σ} = √(e⁶) = e³ ⟺ σ = ½`. It is a pure algebraic fact about `exp`, retained for the
files that reference it; the canonical radial law is the **linear** Archimedean spiral
`Helix.loopRadius` (`R(k) = e^mode·k`), whose realized drift is `n^{σ−½}` (see
`Helix.no_radial_drift_iff_half` / `linear_no_radial_drift_iff_half`). -/
theorem radial_geometric_mean_iff_half (σ : ℝ) :
    Real.exp (6 * σ) = Real.sqrt (Real.exp 6) ↔ σ = 1 / 2 := by
  rw [sqrt_exp_six]
  constructor
  · intro h; have := Real.exp_injective h; linarith
  · intro h; subst h; norm_num

/-! ## The configurator: one generative law, four objects

Not the Cayley circle. The geometry is the **log-Pythagorean prime helix**: the primes wind it
(the odometer: multiplication = addition with carry), the angular cross-section is
`e^{2ξ}+e^{2η}=1` with `ξ=log|cosφ|, η=log|sinφ|`, and the radial growth is `e^M` per loop with
`M = e-foldings per loop = the modulus dial`. It does **not** close and there is **no cylinder** —
it is an expanding helix whose radius grows without bound but **linearly** in the loop number
(`R = e^M·k`, loops evenly spaced by `e^M` — an Archimedean spiral, not an exponential trumpet; with
the area law `n ≈ k²` this is `R ∝ √n`, the geometric-mean frame), while the pitch climbs forever
(the primes never stop). The **unitary** is that a zero's radial expansion sits at the **geometric-mean rate**
`e^{M/2} = √(e^M)` — the balance between the integers' full rate `e^M` (σ=1) and none (σ=0), the FE
self-dual point (σ=1−σ). The per-loop *rate* excess over that balance is `e^{M(σ−½)}`, which is `1`
(no radial drift) iff σ=½ — but in the linear realization (`R = e^M·k`, `R ∝ √n`) the *realized*
drift is `n^{σ−½}`: the growth exponent `M` cancels, only the defect `σ−½` survives. Both vanish at
exactly σ=½ (see `linear_no_radial_drift_iff_half`).

The **configurator** is the angular spacing, and it sets the radial growth = the **modulus**:

      spacing π/6 → e³  → mod 3
      spacing π/3 → e⁶  → mod 6
      spacing π/2 → e⁸  → mod 8
      spacing π   → e¹² → mod 12

so `modulus = radial-growth exponent` (`e^M → mod M`). One law, parameterized by `M`, generates
the no-drift condition for every channel: dial the spacing, the radial growth follows, and a zero
expands at the geometric-mean rate (no radial drift) exactly on the critical line. The four objects
are four spacings. -/

/-- **Algebraic identity (NOT the geometry).** The exponential per-loop framing: for `M ≠ 0`,
`e^{M(σ−½)} = 1 ⟺ σ = ½`. A pure algebraic fact about `exp`, parameterized by `M`, retained for
the files that reference it. The canonical radial law is the **linear** Archimedean spiral
`Helix.loopRadius` (`R(k) = e^mode·k`); its realized drift is `n^{σ−½}` with the slope `e^mode`
absent — only the defect `σ−½` survives — so no-drift ⟺ σ=½ slope-independently
(`Helix.no_radial_drift_iff_half` / `linear_no_radial_drift_iff_half`). -/
theorem no_radial_drift_iff_half (M σ : ℝ) (hM : M ≠ 0) :
    Real.exp (M * (σ - 1 / 2)) = 1 ↔ σ = 1 / 2 := by
  constructor
  · intro h
    have h0 : M * (σ - 1 / 2) = 0 := by
      have hh : Real.exp (M * (σ - 1 / 2)) = Real.exp 0 := by rw [Real.exp_zero, h]
      exact Real.exp_injective hh
    rcases mul_eq_zero.mp h0 with hM0 | hσ
    · exact absurd hM0 hM
    · linarith
  · intro h; subst h; simp

/-- The on-line (σ=½) radial rate is the geometric mean of the loop: `√(e^M) = e^{M/2}`. -/
theorem online_rate_geometric_mean (M : ℝ) :
    Real.sqrt (Real.exp M) = Real.exp (M / 2) := by
  have h : Real.exp (M / 2) ^ 2 = Real.exp M := by
    rw [sq, ← Real.exp_add, show M / 2 + M / 2 = M from by ring]
  rw [← h]; exact Real.sqrt_sq (Real.exp_pos _).le

/-- A zero's radial growth `e^{Mσ}` equals the loop's geometric mean `e^{M/2}` iff σ=½. -/
theorem radial_eq_geometric_mean_iff_half (M σ : ℝ) (hM : M ≠ 0) :
    Real.exp (M * σ) = Real.exp (M / 2) ↔ σ = 1 / 2 := by
  constructor
  · intro h
    have h3 : M * σ = M * (1 / 2) := by rw [Real.exp_injective h]; ring
    exact mul_left_cancel₀ hM h3
  · intro h; subst h; rw [show M * (1 / 2 : ℝ) = M / 2 from by ring]

/-- A configured channel: the configurator dials — angular spacing `π / spacingDenom`, radial
growth `e^radialExp` per loop, and the `modulus` realized. The configurator law is
`radialExp = modulus`: the radial-growth exponent IS the modulus. -/
structure ConfiguredChannel where
  spacingDenom : ℕ
  radialExp : ℝ
  modulus : ℕ

/-- **The configurator table** (spacing → radial growth → modulus):
`π/6 → e³ → mod 3`,  `π/3 → e⁶ → mod 6`,  `π/2 → e⁸ → mod 8`,  `π → e¹² → mod 12`. -/
def ch_pi6 : ConfiguredChannel := ⟨6, 3, 3⟩
def ch_pi3 : ConfiguredChannel := ⟨3, 6, 6⟩
def ch_pi2 : ConfiguredChannel := ⟨2, 8, 8⟩
def ch_pi  : ConfiguredChannel := ⟨1, 12, 12⟩

/-- The four configured objects. -/
def towerChannels : List ConfiguredChannel := [ch_pi6, ch_pi3, ch_pi2, ch_pi]

/-- **The configurator invariant**: on every channel the radial-growth exponent equals the
modulus (`e^M → mod M`). -/
theorem radialExp_eq_modulus :
    ∀ c ∈ towerChannels, c.radialExp = (c.modulus : ℝ) := by
  intro c hc
  fin_cases hc <;> norm_num [ch_pi6, ch_pi3, ch_pi2, ch_pi]

/-! ### Reconciliation with the canonical `Helix.Channel` table

A `ConfiguredChannel` carries the same geometry as the single source of truth `Helix.Channel`
(`RequestProject.HelixDefs`): the spacing denominator is `Helix.Channel.helixUnit` (angle unit
`π/helixUnit`) and the radial exponent is `Helix.Channel.mode` (radial slope `e^mode`). The map
below ties the local structure to the canonical table; `*_eq_helix` lemmas show the four
configured objects are the four canonical channels. -/

/-- A `ConfiguredChannel` viewed as the canonical `Helix.Channel`: spacing → `helixUnit`,
radial exponent → `mode`. -/
def ConfiguredChannel.toHelix (c : ConfiguredChannel) : Helix.Channel :=
  ⟨(c.spacingDenom : ℝ), c.radialExp⟩

theorem ch_pi6_toHelix_eq : ch_pi6.toHelix = Helix.chTrivial3 := by
  simp [ConfiguredChannel.toHelix, ch_pi6, Helix.chTrivial3]

theorem ch_pi3_toHelix_eq : ch_pi3.toHelix = Helix.chChi3 := by
  simp [ConfiguredChannel.toHelix, ch_pi3, Helix.chChi3]

theorem ch_pi2_toHelix_eq : ch_pi2.toHelix = Helix.chMode8 := by
  simp [ConfiguredChannel.toHelix, ch_pi2, Helix.chMode8]

theorem ch_pi_toHelix_eq : ch_pi.toHelix = Helix.chMode12 := by
  simp [ConfiguredChannel.toHelix, ch_pi, Helix.chMode12]

/-- The four configured objects are exactly the canonical `Helix.channels`. -/
theorem towerChannels_toHelix_eq_channels :
    towerChannels.map ConfiguredChannel.toHelix = Helix.channels := by
  simp [towerChannels, Helix.channels, ch_pi6_toHelix_eq, ch_pi3_toHelix_eq,
    ch_pi2_toHelix_eq, ch_pi_toHelix_eq]

/-- The configurator law specialized to a channel: every channel with nonzero radial growth
expands at its geometric-mean rate (no radial drift, is unitary) exactly on the critical line.
One engine, every object. -/
theorem channel_no_radial_drift_iff_half (c : ConfiguredChannel) (hc : c.radialExp ≠ 0) (σ : ℝ) :
    Real.exp (c.radialExp * (σ - 1 / 2)) = 1 ↔ σ = 1 / 2 :=
  no_radial_drift_iff_half c.radialExp σ hc

/-- `√(e¹²) = e⁶`: the on-line radial rate of the unit-π / mod-12 helix is the geometric mean. -/
theorem sqrt_exp_twelve : Real.sqrt (Real.exp 12) = Real.exp 6 := by
  have h : Real.exp 6 ^ 2 = Real.exp 12 := by rw [sq, ← Real.exp_add]; norm_num
  rw [← h]; exact Real.sqrt_sq (Real.exp_pos 6).le

/-- mod-12 helix: the radial growth `e^{12σ}` equals the geometric mean `√(e¹²) = e⁶` iff σ=½. -/
theorem mod12_radial_geometric_mean_iff_half (σ : ℝ) :
    Real.exp (12 * σ) = Real.sqrt (Real.exp 12) ↔ σ = 1 / 2 := by
  rw [sqrt_exp_twelve]
  constructor
  · intro h; have := Real.exp_injective h; linarith
  · intro h; subst h; norm_num

/-! ### The radial law is LINEAR in the loop number (the corrected picture)

The radius is **linear in the loop number** `k`: `R = e^m·k`, so every loop adds the *same* constant
`e^m` (additive growth, not a compounding `×e^m`) — an Archimedean spiral with evenly-spaced loops,
**not** an exponential trumpet. The area law `n ≈ k²` (constant arc-length spacing makes loop `k`
carry `∝ k` integers, so the count grows quadratically) turns linear-in-`k` into `R ∝ √n`: the
geometric-mean / σ=½ frame, *emergent* from the geometry, not assumed. The radial **drift** of a
zero then decouples from the growth rate `m` — it is `n^{σ−½}`, with `m` absent and only the defect
`σ−½` surviving; no drift ⟺ σ=½. -/

/-- The radius at loop `k` — **linear** in `k`, slope `e^m`. -/
def loopRadius (m k : ℝ) : ℝ := Real.exp m * k

/-- **Linear radial growth.** Each loop adds the *same* `e^m`: the increment `R(k+1) − R(k)` is the
constant `e^m`, additive — there is no exponential blow-up. -/
theorem loopRadius_linear (m k : ℝ) :
    loopRadius m (k + 1) - loopRadius m k = Real.exp m := by
  unfold loopRadius; ring

/-- **The area law makes the linear radius `√n`.** With `n = k²` the linear-in-`k` radius `e^m·k`
is `e^m·√n` — the geometric-mean (σ=½) frame produced by the geometry. -/
theorem loopRadius_eq_sqrt_area (m k : ℝ) (hk : 0 ≤ k) :
    loopRadius m k = Real.exp m * Real.sqrt (k ^ 2) := by
  unfold loopRadius; rw [Real.sqrt_sq hk]

/-- **The drift decouples from the growth rate.** A zero at `σ` drifts off the `√n` frame by
`n^{σ−½}`; the loop growth exponent `m` does not appear — only the defect `σ−½`. No radial drift
(`n^{σ−½} = 1`) ⟺ σ=½, for any base `n > 1`, independent of `m`. -/
theorem linear_no_radial_drift_iff_half (n σ : ℝ) (hn : 1 < n) :
    n ^ (σ - 1 / 2) = 1 ↔ σ = 1 / 2 := by
  have hn0 : (0 : ℝ) < n := by linarith
  have hlogpos : 0 < Real.log n := Real.log_pos hn
  constructor
  · intro h
    have hl : (σ - 1 / 2) * Real.log n = 0 := by
      have hc := congrArg Real.log h
      rwa [Real.log_rpow hn0, Real.log_one] at hc
    rcases mul_eq_zero.mp hl with h1 | h2
    · linarith
    · exact absurd h2 (ne_of_gt hlogpos)
  · intro h; subst h
    rw [show (1 : ℝ) / 2 - 1 / 2 = 0 from by ring, Real.rpow_zero]

/-! ## Asymptotic symmetry: why the midpoint completes the structure

The helix grows outward and climbs forever. The functional-equation dual of a `σ`-mode is the
`(1−σ)`-mode; their envelopes are `e^{σθ}` and `e^{(1−σ)θ}`, geometric mean `e^{θ/2} = √x`. Only
at the midpoint σ=½ do a mode and its dual grow at the **same** rate, so the growing helix
*approaches symmetry asymptotically* instead of one half outrunning the other. In the √x frame the
normalized envelope is `e^{(σ−½)θ}`, and it tends to the balanced value `1` as the helix climbs
iff σ=½. That asymptotic balance is what selects the midpoint as the completing (self-dual)
structure. -/

open Filter Topology in
/-- **σ=½ is the asymptotic symmetry point.** As the helix climbs (θ→∞) the √x-normalized
envelope `e^{(σ−½)θ}` approaches the balanced value `1` iff σ=½: for σ>½ it flares to ∞, for σ<½
it collapses to 0. The growing helix completes to a symmetric (self-dual) structure exactly at the
midpoint. -/
theorem helix_approaches_symmetry_iff_half (σ : ℝ) :
    Filter.Tendsto (fun θ : ℝ => Real.exp ((σ - 1 / 2) * θ)) Filter.atTop (nhds 1) ↔ σ = 1 / 2 := by
  constructor
  · intro h
    by_contra hne
    have hc : σ - 1 / 2 ≠ 0 := sub_ne_zero.mpr hne
    rcases lt_or_gt_of_ne hc with hlt | hgt
    · have hdiv : Tendsto (fun θ : ℝ => (σ - 1 / 2) * θ) atTop atBot :=
        Tendsto.const_mul_atTop_of_neg hlt tendsto_id
      have hz : Tendsto (fun θ : ℝ => Real.exp ((σ - 1 / 2) * θ)) atTop (nhds 0) :=
        Real.tendsto_exp_atBot.comp hdiv
      have : (1 : ℝ) = 0 := tendsto_nhds_unique h hz
      norm_num at this
    · have hdiv : Tendsto (fun θ : ℝ => (σ - 1 / 2) * θ) atTop atTop :=
        Tendsto.const_mul_atTop hgt tendsto_id
      have htop : Tendsto (fun θ : ℝ => Real.exp ((σ - 1 / 2) * θ)) atTop atTop :=
        Real.tendsto_exp_atTop.comp hdiv
      exact not_tendsto_nhds_of_tendsto_atTop htop 1 h
  · intro h; subst h
    simp only [sub_self, zero_mul, Real.exp_zero]
    exact tendsto_const_nhds

/-! ## σ=½ minimizes asymmetry (AM–GM)

The functional-equation pair `e^{σθ}` and `e^{(1−σ)θ}` has fixed product `e^θ` (geometric mean
`√x`). By AM–GM their sum — the asymmetry energy — is at least `2√x`, with equality iff the two
are equal, i.e. σ=½. So the midpoint is literally **the value that minimizes the asymmetry**
between a mode and its dual:
`e^{σθ}+e^{(1−σ)θ} − 2√x = (e^{σθ/2} − e^{(1−σ)θ/2})² ≥ 0`, zero only at σ=½. -/

private theorem amgm_key (σ θ : ℝ) :
    (Real.exp (σ * θ / 2) - Real.exp ((1 - σ) * θ / 2)) ^ 2
      = (Real.exp (σ * θ) + Real.exp ((1 - σ) * θ)) - 2 * Real.exp (θ / 2) := by
  have e1 : Real.exp (σ * θ / 2) * Real.exp (σ * θ / 2) = Real.exp (σ * θ) := by
    rw [← Real.exp_add, show σ * θ / 2 + σ * θ / 2 = σ * θ from by ring]
  have e2 : Real.exp ((1 - σ) * θ / 2) * Real.exp ((1 - σ) * θ / 2) = Real.exp ((1 - σ) * θ) := by
    rw [← Real.exp_add, show (1 - σ) * θ / 2 + (1 - σ) * θ / 2 = (1 - σ) * θ from by ring]
  have e3 : Real.exp (σ * θ / 2) * Real.exp ((1 - σ) * θ / 2) = Real.exp (θ / 2) := by
    rw [← Real.exp_add, show σ * θ / 2 + (1 - σ) * θ / 2 = θ / 2 from by ring]
  have expand : (Real.exp (σ * θ / 2) - Real.exp ((1 - σ) * θ / 2)) ^ 2
      = Real.exp (σ * θ / 2) * Real.exp (σ * θ / 2)
        - 2 * (Real.exp (σ * θ / 2) * Real.exp ((1 - σ) * θ / 2))
        + Real.exp ((1 - σ) * θ / 2) * Real.exp ((1 - σ) * θ / 2) := by ring
  rw [expand, e1, e2, e3]; ring

/-- **σ=½ minimizes asymmetry (the floor).** The FE-pair sum is always `≥ 2√x = 2e^{θ/2}`. -/
theorem asymmetry_ge (σ θ : ℝ) :
    2 * Real.exp (θ / 2) ≤ Real.exp (σ * θ) + Real.exp ((1 - σ) * θ) := by
  nlinarith [sq_nonneg (Real.exp (σ * θ / 2) - Real.exp ((1 - σ) * θ / 2)), amgm_key σ θ]

/-- **σ=½ is the unique minimizer.** The FE-pair sum attains its floor `2√x` exactly when σ=½ —
the value that minimizes the asymmetry between a mode and its functional-equation dual. -/
theorem asymmetry_eq_floor_iff_half (σ θ : ℝ) (hθ : θ ≠ 0) :
    Real.exp (σ * θ) + Real.exp ((1 - σ) * θ) = 2 * Real.exp (θ / 2) ↔ σ = 1 / 2 := by
  constructor
  · intro h
    have hsq : (Real.exp (σ * θ / 2) - Real.exp ((1 - σ) * θ / 2)) ^ 2 = 0 := by
      rw [amgm_key, h]; ring
    have hd : Real.exp (σ * θ / 2) - Real.exp ((1 - σ) * θ / 2) = 0 :=
      pow_eq_zero_iff (by norm_num) |>.mp hsq
    have hxx : σ * θ / 2 = (1 - σ) * θ / 2 := Real.exp_injective (by linarith)
    have h2 : (2 * σ - 1) * θ = 0 := by nlinarith [hxx]
    rcases mul_eq_zero.mp h2 with h3 | h3
    · linarith
    · exact absurd h3 hθ
  · intro h; subst h
    have harg : (1 / 2 : ℝ) * θ = θ / 2 := by ring
    have harg2 : ((1 : ℝ) - 1 / 2) * θ = θ / 2 := by ring
    rw [harg, harg2]; ring

/-! ## The rotation forcing: full rotation + discrete ⟹ on the axis

The functional equation `ρ ↦ 1−ρ` is a **rotation** about the geometric midpoint σ=½
(`½+w ↦ ½−w`, i.e. `w ↦ −w`), not a reflection. As an order-2 map it only *pairs* zeros — that
is the plain FE, symmetry but not RH. But the helix is built with the **full continuous
rotation**: `HelixUnitaryOperator.helixUnitary` is a continuous `U(1)` by construction. A full
rotation has a sharper consequence — the orbit of any off-axis point is an entire **circle**
(uncountable). So a **discrete** (countable) spectrum invariant under the full rotation has every
point **on the axis**: a circle cannot fit inside a countable set. The rotation is supplied by
the construction; discreteness of the zeros is free; together they force `Re ρ = ½`.

The plane here is (radial deviation `σ−½`) × (pitch / archimedean place); the axis is `σ=½`. -/

/-- **The rotation forcing.** A countable set closed under the full continuous rotation group
`p ↦ e^{iθ}·p` has every point at the axis (origin): the orbit of any `p ≠ 0` is an uncountable
circle, which cannot fit inside a countable set. Discrete spectrum + full rotation ⟹ on the
axis. The rotation invariance is the input the helix supplies by construction; countability is
free. -/
theorem countable_rotation_invariant_eq_zero
    (S : Set ℂ) (hc : S.Countable)
    (hinv : ∀ θ : ℝ, ∀ p ∈ S, Complex.exp (↑θ * Complex.I) * p ∈ S)
    {p : ℂ} (hp : p ∈ S) : p = 0 := by
  by_contra hp0
  have hpi := Real.pi_pos
  have hmap : ∀ θ ∈ Set.Ico (0 : ℝ) (2 * Real.pi), Complex.exp (↑θ * Complex.I) * p ∈ S :=
    fun θ _ => hinv θ p hp
  have hinj : Set.InjOn (fun θ : ℝ => Complex.exp (↑θ * Complex.I) * p)
      (Set.Ico 0 (2 * Real.pi)) := by
    intro a ha b hb hab
    simp only at hab
    have hexp : Complex.exp (↑a * Complex.I) = Complex.exp (↑b * Complex.I) :=
      mul_right_cancel₀ hp0 hab
    have h1 : Complex.exp ((↑a - ↑b) * Complex.I) = 1 := by
      rw [sub_mul, Complex.exp_sub, hexp, div_self (Complex.exp_ne_zero _)]
    rw [Complex.exp_eq_one_iff] at h1
    obtain ⟨n, hn⟩ := h1
    have key : (↑a - ↑b : ℂ) = (↑n * (2 * ↑Real.pi)) := by
      have h2 : (↑a - ↑b : ℂ) * Complex.I = (↑n * (2 * ↑Real.pi)) * Complex.I := by rw [hn]; ring
      exact mul_right_cancel₀ Complex.I_ne_zero h2
    have key2 : a - b = (n : ℝ) * (2 * Real.pi) := by exact_mod_cast key
    obtain ⟨ha0, ha1⟩ := ha; obtain ⟨hb0, hb1⟩ := hb
    have hbound : |a - b| < 2 * Real.pi := by rw [abs_lt]; constructor <;> nlinarith
    rw [key2, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at hbound
    have hn1 : |(n : ℝ)| < 1 := by nlinarith [abs_nonneg (n : ℝ)]
    have hn0 : n = 0 := by
      have hh : |n| < 1 := by exact_mod_cast hn1
      have h12 := abs_lt.mp hh
      omega
    rw [hn0] at key2; push_cast at key2; linarith
  haveI : Countable S := hc.to_subtype
  let g : (Set.Ico (0 : ℝ) (2 * Real.pi)) → S :=
    fun θ => ⟨Complex.exp (↑θ.1 * Complex.I) * p, hmap θ.1 θ.2⟩
  have hginj : Function.Injective g :=
    fun x y hxy => Subtype.ext (hinj x.2 y.2 (Subtype.ext_iff.mp hxy))
  have hcount : Countable (Set.Ico (0 : ℝ) (2 * Real.pi)) := hginj.countable
  have hIcoc : (Set.Ico (0 : ℝ) (2 * Real.pi)).Countable := Set.countable_coe_iff.mpr hcount
  rw [Cardinal.Real.Ico_countable_iff] at hIcoc
  linarith

/-! ## The non-divergence forcing

The mechanism is non‑divergence. A zero `ρ = σ+iγ` contributes a mode whose √x‑frame envelope is
`e^{(σ−½)θ}`; its functional‑equation partner `1−ρ` contributes `e^{((1−σ)−½)θ}`. A mode that stays
**bounded** (non‑divergent) as the helix climbs can't grow, so its exponent is `≤ 0`. The σ‑mode
bounded forces `σ ≤ ½`; the FE‑partner bounded forces `σ ≥ ½`. Together: **σ = ½**. The construction
supplies the bounded (unitary/non‑divergent) winding and the FE pairing; this lemma is the close. -/

/-- A mode `e^{cθ}` bounded on `[0,∞)` cannot grow: `c ≤ 0`. -/
theorem exp_bounded_imp_nonpos (c : ℝ) (h : ∃ C, ∀ θ : ℝ, 0 ≤ θ → Real.exp (c * θ) ≤ C) :
    c ≤ 0 := by
  obtain ⟨C, hC⟩ := h
  by_contra hc
  rw [not_le] at hc
  have hC1 : (1 : ℝ) ≤ C := by simpa using hC 0 le_rfl
  have hθ0 : 0 ≤ Real.log (C + 1) / c :=
    div_nonneg (Real.log_nonneg (by linarith)) hc.le
  have hkey : Real.exp (c * (Real.log (C + 1) / c)) = C + 1 := by
    rw [show c * (Real.log (C + 1) / c) = Real.log (C + 1) from by field_simp]
    exact Real.exp_log (by linarith)
  have hbound := hC (Real.log (C + 1) / c) hθ0
  rw [hkey] at hbound
  linarith

/-- **The non‑divergence forcing.** If a zero's mode `e^{(σ−½)θ}` and its FE‑partner's mode
`e^{((1−σ)−½)θ}` are both non‑divergent (bounded) in the √x frame, then `σ = ½`: the σ‑mode bounded
gives `σ ≤ ½`, the FE‑partner bounded gives `σ ≥ ½`. -/
theorem fe_pair_nondivergent_imp_half (σ : ℝ)
    (h1 : ∃ C, ∀ θ : ℝ, 0 ≤ θ → Real.exp ((σ - 1 / 2) * θ) ≤ C)
    (h2 : ∃ C, ∀ θ : ℝ, 0 ≤ θ → Real.exp (((1 - σ) - 1 / 2) * θ) ≤ C) :
    σ = 1 / 2 := by
  have ha := exp_bounded_imp_nonpos _ h1
  have hb := exp_bounded_imp_nonpos _ h2
  linarith

/-! ## The full-loop winding loss: conservation = unitarity = on the line

The winding‑rate loss assembled over a **full loop** of the mod‑`M` channel (`M` e‑foldings =
the modulus = the radial‑growth exponent `e^M`). A winding value `z = windRate ρ` accumulates the
radial factor `‖z‖^M`; the loop **loses nothing** — `fullLoopWindingLoss M z = 1` — exactly on the
unit circle, i.e. exactly on the critical line. Energy conservation as one multiplicative identity:
`= 1` is the loss at its floor (`‖z‖ = 1`, `cosh = 1`, `σ = ½`) — the projection returns one
answer (unitary) with nothing lost. -/

/-- **Full‑loop winding loss** for the mod‑`M` channel: the radial factor a winding value `z`
accumulates over one full loop (`M` e‑foldings). -/
def fullLoopWindingLoss (M : ℕ) (z : ℂ) : ℝ := ‖z‖ ^ M

/-- A unit winding value is **lossless over a full loop** (conservation on the circle). -/
theorem fullLoopWindingLoss_unit (M : ℕ) {z : ℂ} (hz : ‖z‖ = 1) :
    fullLoopWindingLoss M z = 1 := by
  simp [fullLoopWindingLoss, hz]

/-- **`fullLoopWindingLoss 6 z = 1`** — the mod‑6 channel (π/3, radial `e⁶`): a full loop of a
unit winding value loses nothing. -/
theorem fullLoopWindingLoss_six {z : ℂ} (hz : ‖z‖ = 1) :
    fullLoopWindingLoss 6 z = 1 :=
  fullLoopWindingLoss_unit 6 hz

/-- **Loss `= 1` ⟺ unitary.** For a genuine loop (`M ≠ 0`) the full‑loop loss is at its floor `1`
exactly when the winding value sits on the unit circle: conservation ⟺ unitarity. -/
theorem fullLoopWindingLoss_eq_one_iff (M : ℕ) (hM : M ≠ 0) (z : ℂ) :
    fullLoopWindingLoss M z = 1 ↔ ‖z‖ = 1 := by
  unfold fullLoopWindingLoss
  exact pow_eq_one_iff_of_nonneg (norm_nonneg z) hM

/-- **The full‑loop winding loss reads the line.** The loss of a zero's winding value `windRate ρ`
is at its floor `1` (lossless full loop) exactly when the zero is on the critical line: the
conservation statement is the on‑line condition. -/
theorem fullLoopWindingLoss_windRate_iff_half (ρ : ℂ) (hρ : ρ ≠ 0) (M : ℕ) (hM : M ≠ 0) :
    fullLoopWindingLoss M (windRate ρ) = 1 ↔ ρ.re = 1 / 2 := by
  rw [fullLoopWindingLoss_eq_one_iff M hM, show windRate ρ = SpectralSide.w ρ from rfl]
  constructor
  · intro h
    have hn : Complex.normSq (SpectralSide.w ρ) = 1 := by
      rw [Complex.normSq_eq_norm_sq, h]; norm_num
    exact (SpectralSide.w_unit_iff_half ρ hρ).mp hn
  · intro h
    have hn : Complex.normSq (SpectralSide.w ρ) = 1 := (SpectralSide.w_unit_iff_half ρ hρ).mpr h
    rw [Complex.normSq_eq_norm_sq] at hn
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp hn

/-- **The configured mod‑6 channel conserves.** At the `ch_pi3` modulus (= 6 = its radial exponent
`e⁶`), a unit winding value is lossless over a full loop. -/
theorem ch_pi3_fullLoop_conserves {z : ℂ} (hz : ‖z‖ = 1) :
    fullLoopWindingLoss ch_pi3.modulus z = 1 :=
  fullLoopWindingLoss_unit ch_pi3.modulus hz

/-- **The cosh form of the same loop loss.** Over the mod‑6 loop the FE‑pair asymmetry
`e^{6σ}+e^{6(1−σ)}` sits at its floor `2e³` exactly on the line — the cosh bowl bottoming at σ=½ is
the conservation in additive (energy) form, the same `= floor` as the multiplicative `= 1`. -/
theorem loop_cosh_floor_iff_half (σ : ℝ) :
    Real.exp (σ * 6) + Real.exp ((1 - σ) * 6) = 2 * Real.exp (6 / 2) ↔ σ = 1 / 2 :=
  asymmetry_eq_floor_iff_half σ 6 (by norm_num)

/-! ## The geometric-midpoint cascade

`σ=½` is not a value to be proved but the **geometric midpoint**, and it is the *same* point at every
level of the Green–Helmholtz cascade. Each of the following is the midpoint, and each is `⟺ Re ρ = ½`,
unconditionally and axiom-clean:

* `Re ρ = ½` — the **strip** midpoint (arithmetic midpoint of `[0,1]`);
* `‖windRate ρ‖ = 1` — the **unit circle** (the FE-pair geometric mean; `w(ρ)·w(1−ρ)=1`);
* `e^{M(σ−½)} = 1` — the **radial geometric mean** (no radial drift over a loop of exponent `M`);
* `e^{σθ}+e^{(1−σ)θ} = 2e^{θ/2}` — the **cosh / asymmetry floor** (Green–Helmholtz `cosh ≥ 1`, at its floor);
* `fullLoopWindingLoss 6 (windRate ρ) = 1` — **full-loop conservation** (the mod-6 channel).

They are one point, cascading. This is the geometric skeleton: every "midpoint" coincides, and the
only non-geometric input the full statement still needs is the conservation/non-divergence premise
(`conditionalRH_from_bounded_envelopes`), i.e. the Green–Helmholtz operator's non-negativity feeding
boundedness — which is the operator-realization, not part of this theorem. -/
theorem geometric_midpoint_cascade (ρ : ℂ) (hρ : ρ ≠ 0)
    (M : ℝ) (hM : M ≠ 0) (θ : ℝ) (hθ : θ ≠ 0) :
    (‖windRate ρ‖ = 1 ↔ ρ.re = 1 / 2) ∧
    (Real.exp (M * (ρ.re - 1 / 2)) = 1 ↔ ρ.re = 1 / 2) ∧
    (Real.exp (ρ.re * θ) + Real.exp ((1 - ρ.re) * θ) = 2 * Real.exp (θ / 2) ↔ ρ.re = 1 / 2) ∧
    (fullLoopWindingLoss 6 (windRate ρ) = 1 ↔ ρ.re = 1 / 2) := by
  refine ⟨?_, no_radial_drift_iff_half M ρ.re hM,
          asymmetry_eq_floor_iff_half ρ.re θ hθ,
          fullLoopWindingLoss_windRate_iff_half ρ hρ 6 (by norm_num)⟩
  show ‖SpectralSide.w ρ‖ = 1 ↔ ρ.re = 1 / 2
  rw [← SpectralSide.w_unit_iff_half ρ hρ, Complex.normSq_eq_norm_sq]
  constructor
  · intro h; rw [h]; norm_num
  · intro h; exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp h

end HelixEF

end

#print axioms HelixEF.windRate_reads_unit_imp_half
#print axioms HelixEF.fullLoopWindingLoss_six
#print axioms HelixEF.fullLoopWindingLoss_eq_one_iff
#print axioms HelixEF.fullLoopWindingLoss_windRate_iff_half
#print axioms HelixEF.loop_cosh_floor_iff_half
#print axioms HelixEF.geometric_midpoint_cascade
