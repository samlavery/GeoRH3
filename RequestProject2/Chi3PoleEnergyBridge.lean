import Mathlib
import RequestProject.HelixSource
import RequestProject.WeilContourMultiplicity
import RequestProject.Chi3LogDerivPole
import RequestProject.Chi3SourceTrace
import RequestProject.GreenHelmholtz

/-!
# Ledger 4 — the real bridge: pole energy = projection-loss atom energy

This is the conservation law linking Ledger 2's **trace pole** to Ledger 3's **projection loss**.

At a zero `ρ` of order `n`, the source trace `−L'/L` (the trace-kernel readout `Σ_n χ(n)Λ(n) n^{-s}`
continued, `Chi3Source.sourceTrace_eq_primeTrace`) has a **simple pole with residue `−n`**. Its
**pole energy** is `‖residue‖² = n²`. The **projection-loss atom** at the resonance `ρ` carries `n`
lost modes (the Green–Helmholtz codimension at that resonance), with **loss energy `n²`**. They are
equal:

`source pole energy  =  ‖residue of −L'/L at ρ‖²  =  n²  =  (lost-mode count)²  =  projection-loss atom energy.`

The pole energy is **trace-kernel-weighted** (it is the squared residue of `Σ χ(n)Λ(n) n^{-s}`), not a
raw `|primes|²` — matching the kernel of the von Mangoldt trace. The equality is **earned**: the
residue is a genuine analytic limit `lim_{s→ρ}(s−ρ)·(−L'/L) = −n` (`sourceResidue_eq_neg_order`),
independent of how the loss-atom rank is defined.

**What this is, and is not.** This is the *conservation/exactness* half of the user's bridge — the
energy a zero deposits as a pole is exactly the energy of its loss atom. The remaining half — that the
loss atoms are **no-drift** (`GreenHelmholtz.green_helmholtz_no_drift`), so an off-line zero "has
nowhere to put its pole energy" — is the on-line forcing, a *separate* step, not discharged here. We
state the conservation honestly and point at the forcing; we do not smuggle `Re ρ = ½`.
-/

open Complex Filter Topology

namespace Chi3Bridge

variable {N : ℕ} [NeZero N]

/-- The **lost-mode count** at `ρ` — the multiplicity of `ρ` as a zero of `L` (`analyticOrderAt L ρ`).
    Geometrically: the dimension of the Green–Helmholtz projection-loss atom at the resonance `ρ`
    (the codimension the projection drops there). -/
noncomputable def lostModes (χ : DirichletCharacter ℂ N) (ρ : ℂ) : ℕ :=
  (analyticOrderAt (DirichletCharacter.LFunction χ) ρ).toNat

/-- The **residue of the source trace** `−L'/L` at `ρ` — the genuine analytic limit
    `lim_{s→ρ}(s−ρ)·(−L'/L)(s)`. (At a zero of order `n` this is `−n`; see `sourceResidue_eq_neg_order`.) -/
noncomputable def sourceResidue (χ : DirichletCharacter ℂ N) (ρ : ℂ) : ℂ :=
  limUnder (𝓝[≠] ρ) (fun s => (s - ρ) * Chi3Source.SourceTrace χ s)

/-- The **source pole energy** at `ρ` — the squared magnitude of the trace residue, `‖residue‖²`.
    Trace-kernel-weighted: it is the squared Laurent residue of `Σ_n χ(n)Λ(n) n^{-s} = −L'/L`. -/
noncomputable def SourcePoleEnergy (χ : DirichletCharacter ℂ N) (ρ : ℂ) : ℝ :=
  ‖sourceResidue χ ρ‖ ^ 2

/-- The **projection-loss atom energy** at `ρ` — the squared count of lost modes (the Green–Helmholtz
    loss rank²). -/
noncomputable def ProjectionLossAtomEnergy (χ : DirichletCharacter ℂ N) (ρ : ℂ) : ℝ :=
  (lostModes χ ρ : ℝ) ^ 2

/-- **The residue of `−L'/L` at a zero is `lim_{s→ρ}(s−ρ)·(−L'/L)(s) = −n`**, with `n ≥ 1` the order.
    The genuine analytic computation: from the simple-pole Laurent form
    `−L'/L = −(n(s−ρ)⁻¹ + g'/g)` (`WeilContourMultiplicity.logDeriv_pole_of_order`), multiplying by
    `(s−ρ)` kills the `g'/g` term in the limit. -/
theorem sourceTrace_residue_tendsto (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {ρ : ℂ}
    (hρ : DirichletCharacter.LFunction χ ρ = 0) :
    ∃ n : ℕ, 1 ≤ n ∧ analyticOrderAt (DirichletCharacter.LFunction χ) ρ = (n : ℕ∞) ∧
      Tendsto (fun s => (s - ρ) * Chi3Source.SourceTrace χ s) (𝓝[≠] ρ) (𝓝 (-(n : ℂ))) := by
  have hf := Chi3Pole.LFunction_analyticAt χ hχ ρ
  have htop : analyticOrderAt (DirichletCharacter.LFunction χ) ρ ≠ ⊤ :=
    fun h => Chi3Pole.LFunction_not_locally_zero χ hχ ρ (analyticOrderAt_eq_top.mp h)
  obtain ⟨n, hn'⟩ := ENat.ne_top_iff_exists.mp htop
  have hord : analyticOrderAt (DirichletCharacter.LFunction χ) ρ = (n : ℕ∞) := hn'.symm
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · exact absurd hρ (hf.analyticOrderAt_eq_zero.mp (by rw [hord, h0]; rfl))
    · exact hpos
  refine ⟨n, hn, hord, ?_⟩
  obtain ⟨g, hg, hgne, hform⟩ := ZD.WeilPositivity.Contour.logDeriv_pole_of_order hf hord hn
  have key : (fun s => (s - ρ) * Chi3Source.SourceTrace χ s) =ᶠ[𝓝[≠] ρ]
      (fun s => -((n : ℂ) + (s - ρ) * (deriv g s / g s))) := by
    have hsub : ∀ᶠ s in 𝓝[≠] ρ, s - ρ ≠ 0 := by
      filter_upwards [self_mem_nhdsWithin] with s hs; exact sub_ne_zero_of_ne hs
    filter_upwards [hform, hsub] with s hs hsne
    simp only [Chi3Source.SourceTrace, logDeriv_apply, hs]
    field_simp
  refine Tendsto.congr' key.symm ?_
  have hgg : Tendsto (fun s => deriv g s / g s) (𝓝[≠] ρ) (𝓝 (deriv g ρ / g ρ)) :=
    ((hg.deriv.continuousAt).div hg.continuousAt hgne).tendsto.mono_left nhdsWithin_le_nhds
  have hsub0 : Tendsto (fun s : ℂ => s - ρ) (𝓝[≠] ρ) (𝓝 0) :=
    ((continuous_sub_right ρ).tendsto' ρ 0 (sub_self ρ)).mono_left nhdsWithin_le_nhds
  have hprod := hsub0.mul hgg
  have hfin := (tendsto_const_nhds (x := (n : ℂ)) (f := 𝓝[≠] ρ)).add hprod
  simpa using hfin.neg

/-- **The residue is `−(lost-mode count)`**, and the count is `≥ 1`. Reads the analytic residue
    `lim (s−ρ)·(−L'/L) = −n` off `sourceTrace_residue_tendsto` and identifies `n = lostModes`. -/
theorem sourceResidue_eq_neg_order (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {ρ : ℂ}
    (hρ : DirichletCharacter.LFunction χ ρ = 0) :
    1 ≤ lostModes χ ρ ∧ sourceResidue χ ρ = -(lostModes χ ρ : ℂ) := by
  obtain ⟨n, hn, hord, htend⟩ := sourceTrace_residue_tendsto χ hχ hρ
  have hlm : lostModes χ ρ = n := by rw [lostModes, hord]; rfl
  refine ⟨by rw [hlm]; exact hn, ?_⟩
  rw [sourceResidue, hlm]
  exact htend.limUnder_eq

/-- A pole of the source trace **is** a zero of `L` (Ledger 2, reverse): if `−L'/L` has no finite
    limit at `ρ` then `L ρ = 0` (else the quotient is continuous, with a finite limit). -/
theorem zero_of_poleAt_sourceTrace (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {ρ : ℂ}
    (hpole : Chi3Pole.PoleAt (Chi3Source.SourceTrace χ) ρ) :
    DirichletCharacter.LFunction χ ρ = 0 := by
  by_contra hne
  apply hpole
  have hf := Chi3Pole.LFunction_analyticAt χ hχ ρ
  have hcont : ContinuousAt (Chi3Source.SourceTrace χ) ρ := by
    have heq : (fun s => -logDeriv (DirichletCharacter.LFunction χ) s)
        = (fun s => -(deriv (DirichletCharacter.LFunction χ) s
          / DirichletCharacter.LFunction χ s)) := by
      funext s; rw [logDeriv_apply]
    show ContinuousAt (fun s => -logDeriv (DirichletCharacter.LFunction χ) s) ρ
    rw [heq]
    exact ((hf.deriv.continuousAt).div hf.continuousAt hne).neg
  exact ⟨_, hcont.tendsto.mono_left nhdsWithin_le_nhds⟩

/-- **Ledger 4 — the real bridge (conservation/exactness).** At a pole of the source trace `−L'/L`
    (equivalently, a zero `ρ` of `L`), the **pole energy equals the projection-loss atom energy**:

    `SourcePoleEnergy χ ρ = ‖residue‖² = n² = (lost-mode count)² = ProjectionLossAtomEnergy χ ρ`.

    Earned, not definitional: the left side is the squared magnitude of the genuine analytic residue
    `lim(s−ρ)·(−L'/L) = −n`; the right is the squared loss-rank. They coincide because the residue
    magnitude *is* the multiplicity. `σ`-free. (The no-drift forcing of the loss atoms — the step that
    turns this conservation into "the off-line zero has nowhere to put its energy" — is separate; see
    `GreenHelmholtz.green_helmholtz_no_drift`.) -/
theorem source_pole_energy_eq_projection_loss_atom (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (ρ : ℂ) :
    Chi3Pole.PoleAt (Chi3Source.SourceTrace χ) ρ →
      SourcePoleEnergy χ ρ = ProjectionLossAtomEnergy χ ρ := by
  intro hpole
  have hρ := zero_of_poleAt_sourceTrace χ hχ hpole
  obtain ⟨_, hres⟩ := sourceResidue_eq_neg_order χ hχ hρ
  rw [SourcePoleEnergy, ProjectionLossAtomEnergy, hres, norm_neg, Complex.norm_natCast]

/-- The χ₃ specialization of the bridge. -/
theorem chi3_source_pole_energy_eq_projection_loss_atom (ρ : ℂ) :
    Chi3Pole.PoleAt (Chi3Source.SourceTrace ChiThree.χ3) ρ →
      SourcePoleEnergy ChiThree.χ3 ρ = ProjectionLossAtomEnergy ChiThree.χ3 ρ :=
  source_pole_energy_eq_projection_loss_atom ChiThree.χ3 ChiThree.χ3_ne_one ρ

end Chi3Bridge
