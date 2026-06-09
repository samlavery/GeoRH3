import RequestProject.HelixSource
import RequestProject.WeilContourMultiplicity

/-!
# Order-faithful pole of `L'/L` at a nontrivial zero

`logDeriv_pole_of_order` (proved in `WeilContourMultiplicity`) composed with
`analyticOrderAt_LFunction_eq_pos_nat` (proved in `HelixSource`) gives the **order-faithful** Laurent
form of `L'/L` at a nontrivial zero `ρ`: a *simple* pole (order `-1`) whose **residue equals the
multiplicity `n`**.

**Sign (now consistent).** `logDeriv L = L'/L` has residue `+n` at `ρ`. `HelixSource.sourceTrace` is
`∑ₙ[(s−cₙ)⁻¹ + cₙ⁻¹]`, residue `+1` per pole-coord, and `HelixSource.SourceTraceIdentity` is
`sourceTrace = logDeriv L` (residue `+1` ↔ `+n`), in agreement with the repo's own
`DirichletLHadamard`: `logDeriv L = A + ∑_ρ (ord ρ)·[1/(s−ρ) + 1/ρ]` (positive coefficients).
[History: `SourceTraceIdentity` previously read `sourceTrace = −logDeriv L`; that opposite-sign form
forced `#{n : cₙ = ρ} = −n < 0` at any captured zero — unsatisfiable — and was corrected.] Under the
corrected sign the residue match reads `#{n : cₙ = ρ} = n`: genuine order-faithful capture.
-/

open Complex Filter Topology

namespace HelixSource

variable {N : ℕ} [NeZero N]

/-- **Order-faithful pole of `L'/L` at a nontrivial zero.** At `ρ ∈ NontrivialZeros χ` the
    logarithmic derivative `L'/L` has a *simple* pole with **residue equal to the multiplicity**
    `n = analyticOrderAt (LFunction χ) ρ ≥ 1`:

    `L'/L (s) = n · (s − ρ)⁻¹ + g'/g (s)`  on a punctured nhd, with `g` analytic, `g ρ ≠ 0`.

    σ-free: no mention of `Re ρ`. (Combines `analyticOrderAt_LFunction_eq_pos_nat` with the general
    `WeilContourMultiplicity.logDeriv_pole_of_order`.) -/
theorem LFunction_logDeriv_residue_eq_order (χ : DirichletCharacter ℂ N) {ρ : ℂ}
    (hρ : ρ ∈ GRHSpectral.NontrivialZeros χ) :
    ∃ (n : ℕ) (g : ℂ → ℂ), 1 ≤ n ∧ AnalyticAt ℂ g ρ ∧ g ρ ≠ 0 ∧
      analyticOrderAt (DirichletCharacter.LFunction χ) ρ = (n : ℕ∞) ∧
      ∀ᶠ s in nhdsWithin ρ {ρ}ᶜ,
        logDeriv (DirichletCharacter.LFunction χ) s
          = (n : ℂ) * (s - ρ)⁻¹ + deriv g s / g s := by
  obtain ⟨n, hn, hord⟩ := analyticOrderAt_LFunction_eq_pos_nat χ hρ
  obtain ⟨_, hre1, _⟩ := hρ
  have hρ1 : ρ ≠ 1 := by intro h; rw [h] at hre1; simp at hre1
  have hf : AnalyticAt ℂ (DirichletCharacter.LFunction χ) ρ :=
    LFunction_analyticOnNhd χ ρ (Set.mem_compl_singleton_iff.mpr hρ1)
  obtain ⟨g, hg, hgne, hform⟩ :=
    ZD.WeilPositivity.Contour.logDeriv_pole_of_order hf hord hn
  refine ⟨n, g, hn, hg, hgne, hord, ?_⟩
  filter_upwards [hform] with s hs
  rw [logDeriv_apply]; exact hs

/-- **Order-faithful capture.** Granting the (corrected) trace identity `sourceTrace = logDeriv L`,
    the source trace has a *simple* pole at every nontrivial zero `ρ` whose **residue is the zero's
    multiplicity** `n = mult_ρ(L) ≥ 1`:

    `sourceTrace modes s = n · (s − ρ)⁻¹ + g'/g s`   on a punctured nhd, `g` analytic, `g ρ ≠ 0`.

    This strengthens `poleCapture_of_traceIdentity` from *location* (`ρ` is some `cₙ`) to *weight*:
    the identity reproduces each zero with its exact multiplicity as the residue. The multiplicity
    `n` is read off the `L`-function side (`analyticOrderAt L`, via `LFunction_logDeriv_residue_eq_order`)
    and inherited through the identity — the source trace is never summed. The mode count
    `#{n : cₙ = ρ}` is a construction-side detail, not needed here: the multiplicity is an `L` fact. -/
theorem orderFaithful_capture (modes : ℕ → SourceMode) (χ : DirichletCharacter ℂ N)
    (hid : SourceTraceIdentity modes χ) {ρ : ℂ}
    (hρ : ρ ∈ GRHSpectral.NontrivialZeros χ) :
    ∃ (n : ℕ) (g : ℂ → ℂ), 1 ≤ n ∧ AnalyticAt ℂ g ρ ∧ g ρ ≠ 0 ∧
      analyticOrderAt (DirichletCharacter.LFunction χ) ρ = (n : ℕ∞) ∧
      ∀ᶠ s in nhdsWithin ρ {ρ}ᶜ,
        sourceTrace modes s = (n : ℂ) * (s - ρ)⁻¹ + deriv g s / g s := by
  obtain ⟨n, g, hn, hg, hgne, hord, hform⟩ := LFunction_logDeriv_residue_eq_order χ hρ
  refine ⟨n, g, hn, hg, hgne, hord, ?_⟩
  filter_upwards [hform] with s hs
  rw [hid s]; exact hs

end HelixSource

#print axioms HelixSource.LFunction_logDeriv_residue_eq_order
#print axioms HelixSource.orderFaithful_capture
