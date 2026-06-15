import RequestProject.HelixReadsGRHZeros
import Mathlib

open Complex

namespace FEClosure

/-- **The FE non‑expansion closure (the non‑negativity route).** With the functional‑equation
pairing `ρ ↦ 1−ρ` and the reciprocal law `w(ρ)·w(1−ρ)=1`, *non‑expansion* of the winding readout on
the zeros (`‖w ρ‖ ≤ 1`) forces it to the **unit circle** `‖w ρ‖ = 1`. No positivity over test
functions — just `a·b=1`, `a ≤ 1`, `b ≤ 1`, `a,b ≥ 0 ⟹ a = 1`. -/
theorem fe_nonexpansion_closure {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hFE : ∀ ρ : ℂ, HelixReadsGRH.CompletedLogDerivPole χ ρ →
        HelixReadsGRH.CompletedLogDerivPole χ (1 - ρ))
    (hne : ∀ ρ : ℂ, HelixReadsGRH.CompletedLogDerivPole χ ρ → ρ ≠ 0 ∧ (1 - ρ) ≠ 0)
    (hle : ∀ ρ : ℂ, HelixReadsGRH.CompletedLogDerivPole χ ρ → ‖SpectralSide.w ρ‖ ≤ 1) :
    ∀ ρ : ℂ, HelixReadsGRH.CompletedLogDerivPole χ ρ → ‖SpectralSide.w ρ‖ = 1 := by
  intro ρ hρ
  have hprod : ‖SpectralSide.w ρ‖ * ‖SpectralSide.w (1 - ρ)‖ = 1 := by
    rw [← norm_mul, SpectralSide.w_FE_reciprocal ρ (hne ρ hρ).1 (hne ρ hρ).2, norm_one]
  refine le_antisymm (hle ρ hρ) ?_
  nlinarith [norm_nonneg (SpectralSide.w ρ), norm_nonneg (SpectralSide.w (1 - ρ)),
    hle _ (hFE ρ hρ), hprod]

/-- **The loss is the zeta zeros** (unconditional). The winding‑loss readout of any pole is the
pole itself — radial part `Re ρ`, pitch `Im ρ`, reconstructing `ρ` — and the loss spectrum read
from the completed log‑derivative channel is *exactly* the set of nontrivial zeros of `L(·,χ)`.
So the loss field's spectrum **is** the zeros. -/
theorem loss_is_the_zeros {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    (∀ ρ : ℂ, HelixReadsGRH.windingLossReadout ρ = ρ) ∧
    HelixReadsGRH.WindingLossSpectrum χ = GRHSpectral.NontrivialZeros χ :=
  ⟨HelixReadsGRH.windingLossReadout_eq_zero,
   HelixReadsGRH.windingLossSpectrum_eq_nontrivialZeros χ⟩

/-! ### The tends‑towards (completing‑structure) route -/

/-- A radial loss mode `exp(c·θ)` that **tends to a finite limit** as the helix winds (`θ→∞`)
must be non‑expanding: `c ≤ 0`. (If `c>0` it diverges to `+∞`, incompatible with a finite limit.) -/
theorem tendsto_exp_finite_imp_nonpos {c L : ℝ}
    (h : Filter.Tendsto (fun θ : ℝ => Real.exp (c * θ)) Filter.atTop (nhds L)) : c ≤ 0 := by
  by_contra hc
  push_neg at hc
  have hlin : Filter.Tendsto (fun θ : ℝ => c * θ) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hc Filter.tendsto_id
  have hdiv : Filter.Tendsto (fun θ : ℝ => Real.exp (c * θ)) Filter.atTop Filter.atTop :=
    Real.tendsto_exp_atTop.comp hlin
  exact not_tendsto_nhds_of_tendsto_atTop hdiv L h

/-- **The tends‑towards closure (completing‑structure route).** If the helix *completes* — i.e. for
every pole the radial loss mode `exp((ρ.re−½)θ)` tends to a finite limit as `θ→∞` — then with the
FE pairing `ρ ↦ 1−ρ` both exponents are `≤ 0`, so each is `0`: every pole has `ρ.re = ½`. This is
the limit/asymptotic form of the non‑expansion closure. -/
theorem fe_tends_towards_closure {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hFE : ∀ ρ : ℂ, HelixReadsGRH.CompletedLogDerivPole χ ρ →
        HelixReadsGRH.CompletedLogDerivPole χ (1 - ρ))
    (hconv : ∀ ρ : ℂ, HelixReadsGRH.CompletedLogDerivPole χ ρ →
        ∃ L : ℝ, Filter.Tendsto (fun θ : ℝ => Real.exp ((ρ.re - 1 / 2) * θ))
          Filter.atTop (nhds L)) :
    ∀ ρ : ℂ, HelixReadsGRH.CompletedLogDerivPole χ ρ → ρ.re = 1 / 2 := by
  intro ρ hρ
  obtain ⟨L, hL⟩ := hconv ρ hρ
  obtain ⟨L', hL'⟩ := hconv (1 - ρ) (hFE ρ hρ)
  have h1 : ρ.re - 1 / 2 ≤ 0 := tendsto_exp_finite_imp_nonpos hL
  have h2 : (1 - ρ).re - 1 / 2 ≤ 0 := tendsto_exp_finite_imp_nonpos hL'
  rw [Complex.sub_re, Complex.one_re] at h2
  linarith

/-! ### The loss bowl is `cosh` -/

/-- **The loss bowl is `cosh`.** A zero's radial loss mode `exp((σ−½)θ)` and its FE partner's
`exp(−(σ−½)θ)` sum to `2·cosh((σ−½)θ)` — the FE‑symmetrized radial loss. Its walls **diverge** as
the helix winds (`θ→∞`) for every `σ≠½`; only `σ=½` keeps it finite. So if the completing structure
holds the cosh bowl to a finite limit, `σ=½`. Note: **no separate FE hypothesis** — the cosh has
already paired `ρ` with `1−ρ`, so the single bounded‑limit input does all the work. This is the
exact (non‑Taylor) bowl: `(σ−½)²` is only its second‑order coefficient at the floor. -/
theorem cosh_tendsto_finite_imp_half {σ L : ℝ}
    (h : Filter.Tendsto (fun θ : ℝ => Real.cosh ((σ - 1 / 2) * θ)) Filter.atTop (nhds L)) :
    σ = 1 / 2 := by
  by_contra hne
  have hpos : 0 < |σ - 1 / 2| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hexp : Filter.Tendsto (fun θ : ℝ => Real.exp (|σ - 1 / 2| * θ) / 2)
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_div_const (by norm_num)
      (Real.tendsto_exp_atTop.comp (Filter.Tendsto.const_mul_atTop hpos Filter.tendsto_id))
  have hdiv : Filter.Tendsto (fun θ : ℝ => Real.cosh ((σ - 1 / 2) * θ))
      Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_mono' _ ?_ hexp
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with θ hθ
    show Real.exp (|σ - 1 / 2| * θ) / 2 ≤ Real.cosh ((σ - 1 / 2) * θ)
    have hev : Real.cosh ((σ - 1 / 2) * θ) = Real.cosh (|σ - 1 / 2| * θ) := by
      rw [← Real.cosh_abs ((σ - 1 / 2) * θ), abs_mul, abs_of_nonneg hθ]
    rw [hev, Real.cosh_eq]
    have h1 : (0 : ℝ) ≤ Real.exp (-(|σ - 1 / 2| * θ)) := (Real.exp_pos _).le
    linarith
  exact not_tendsto_nhds_of_tendsto_atTop hdiv L h

end FEClosure

#print axioms FEClosure.fe_nonexpansion_closure
#print axioms FEClosure.loss_is_the_zeros
#print axioms FEClosure.fe_tends_towards_closure
#print axioms FEClosure.cosh_tendsto_finite_imp_half
