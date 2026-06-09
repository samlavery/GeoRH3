import RequestProject.RadialEnergy
import RequestProject.HelixSource

open Complex
open scoped BigOperators

/-!
# Downward inheritance of no-drift: `E_radial(receiver) = 0`

This file proves the exact implication

```
   NoDrift(source) ∧ DriftPreservingProjection(source → receiver)  ⟹  E_radial(receiver) = 0
```

and instantiates it on the repo's real objects.

**What this is (Rule Five).** This is the *downward inheritance* of the projection chain
`3D source ──project──▶ 1D receiver`: a property established at the **source** (no radial
drift) is carried to its **projection** (zero radial energy at the receiver) along a
drift-preserving projection. Downward inheritance is free and valid; the implication below
is therefore an *unconditional* theorem — kernel-clean, no gaps, no custom assumptions.

**Why it is not circular (Rule Two).** The conclusion `β ρ = ½` (equivalently
`E_radial = 0`) is *derived* by composing **two independently-meaningful facts about two
different objects**:

* `NoDrift driftS` — the **source mode's** radial rate is `0`;
* `preserves` / `covers` — the **receiver's** transverse coordinate `β ρ − ½` is the
  *transported* source drift (the projection is a genuine identification).

Neither hypothesis alone says `β ρ = ½`; `β` is never set to `½` by hand. This is honest
downward inheritance, not a `rfl`-deep costume.

**Where the content actually lives (Rules Five & Eight).** The implication is the *free*
step. The two upstream obligations are the real work, and the concrete instantiation below
shows exactly where each stands:

* `NoDrift(source)` is **earned, not assumed** — it is the *theorem* `SourceMode.noDrift`
  (σ-free, from conservation `source_noDrift`), so it is discharged here, not hypothesized.
* `DriftPreservingProjection` is precisely **`SourceComplete`** (every nontrivial zero is the
  drift-preserving shadow of a source mode). That is the open analytic content — the unbuilt
  weld. This file **consumes** it; it does **not** discharge it.

Net: `E_radial_zero_of_sourceComplete` reduces "`E_radial = 0`" to `SourceComplete`, the same
open obligation as GRH itself (`sourceComplete_iff_grh`). No new GRH is smuggled — the
radial-energy conclusion is shown to be the *inherited shadow* of the source's earned
no-drift, gated only by the identification.
-/

namespace RadialInheritance

open RadialEnergy HelixSource

variable {ιS ιR : Type*}

/-- **No drift at the source.** Every source mode `ψ` has radial drift `driftS ψ = 0`.
    In the concrete instantiation this is the *theorem* `SourceMode.noDrift` (σ-free), not a
    hypothesis. -/
def NoDrift (driftS : ιS → ℝ) : Prop := ∀ ψ, driftS ψ = 0

/-- **A drift-preserving projection `source → receiver`.** A downward projection map `proj`
    (Rule Five: source ↦ its receiver shadow) that

    * `preserves` the radial drift: `driftR (proj ψ) = driftS ψ` — the receiver's drift at a
      shadow is exactly the source mode's drift; and
    * `covers` the receiver set `s`: every receiver point is the shadow of some source mode
      (projection is many-to-one, so we only need a preimage).

    This is the *genuine identification* obligation of Rule Five (b): the receiver's
    transverse coordinate is the transported source drift, established without ever asserting
    it is zero. -/
structure DriftPreservingProjection (driftS : ιS → ℝ) (s : Finset ιR) (driftR : ιR → ℝ) where
  /-- the downward projection source ↦ receiver shadow. -/
  proj : ιS → ιR
  /-- drift is carried along the projection. -/
  preserves : ∀ ψ, driftR (proj ψ) = driftS ψ
  /-- every receiver point is a shadow of some source mode. -/
  covers : ∀ ρ ∈ s, ∃ ψ, proj ψ = ρ

/-- **The inheritance theorem (unconditional).**
    `NoDrift(source) ∧ DriftPreservingProjection(source → receiver) ⟹ E_radial(receiver) = 0`.

    The receiver's radial drift is `driftR ρ = β ρ − ½`, the very quantity `E_radial` squares.
    Each receiver point `ρ ∈ s` is the shadow of a source mode `ψ`; its drift `β ρ − ½` equals
    `driftS ψ` (`preserves`), which is `0` (`NoDrift`). So every term of the sum vanishes.
    Pure downward inheritance — no zero is placed, nothing is assumed on-line. -/
theorem E_radial_zero_of_noDrift_of_driftPreserving
    (s : Finset ιR) (m w β : ιR → ℝ) (driftS : ιS → ℝ)
    (hND : NoDrift driftS)
    (P : DriftPreservingProjection driftS s (fun ρ => β ρ - 1 / 2)) :
    E_radial s m w β = 0 := by
  unfold RadialEnergy.E_radial
  refine Finset.sum_eq_zero fun ρ hρ => ?_
  obtain ⟨ψ, hψ⟩ := P.covers ρ hρ
  have hdr : β ρ - 1 / 2 = 0 := by
    have hp := P.preserves ψ
    rw [hψ] at hp
    exact hp.trans (hND ψ)
  rw [hdr]; ring

/-! ## Concrete instantiation on the repo's real objects

`ιR := ℂ` (receiver = the nontrivial zeros), `ιS := SourceMode` (the source modes),
`driftS ψ := ψ.rate.re` (the source mode's radial rate), `β := Complex.re`. Then:

* `NoDrift driftS` **is** `SourceMode.noDrift` — discharged as a theorem.
* `DriftPreservingProjection` **is extracted from** `SourceComplete` — the open content. -/

variable {N : ℕ} [NeZero N]

/-- **The projection is `SourceComplete`.** From `SourceComplete χ`, the map `ψ ↦ ψ.poleCoord`
    is a drift-preserving projection of the source modes onto any finite set `s` of nontrivial
    zeros: it `preserves` drift because `poleCoord = ½ + rate` gives `poleCoord.re − ½ = rate.re`
    (a pure identity, *no* no-drift used here), and it `covers` `s` because every zero is some
    `ψ.poleCoord`. -/
noncomputable def sourceProjection (χ : DirichletCharacter ℂ N) (h : SourceComplete χ)
    {s : Finset ℂ} (hs : ↑s ⊆ GRHSpectral.NontrivialZeros χ) :
    DriftPreservingProjection (fun ψ : SourceMode => ψ.rate.re) s (fun ρ : ℂ => ρ.re - 1 / 2) where
  proj ψ := ψ.poleCoord
  preserves ψ := by
    show ψ.poleCoord.re - 1 / 2 = ψ.rate.re
    rw [SourceMode.poleCoord, Complex.add_re]; norm_num
  covers ρ hρ := by
    obtain ⟨ψ, hψ⟩ := h ρ (hs (Finset.mem_coe.mpr hρ))
    exact ⟨ψ, hψ.symm⟩

/-- **`SourceComplete χ ⟹ E_radial(zeros) = 0`** — the inheritance, fully concrete.
    `NoDrift` is supplied *as a theorem* by `SourceMode.noDrift` (σ-free conservation), so the
    only input is `SourceComplete` (the identification weld). The radial-energy conclusion is
    the inherited shadow of the source's earned no-drift, for any finite set of nontrivial
    zeros and any weights `m, w`. -/
theorem E_radial_zero_of_sourceComplete (χ : DirichletCharacter ℂ N) (h : SourceComplete χ)
    (m w : ℂ → ℝ) {s : Finset ℂ} (hs : ↑s ⊆ GRHSpectral.NontrivialZeros χ) :
    E_radial s m w Complex.re = 0 :=
  E_radial_zero_of_noDrift_of_driftPreserving s m w Complex.re
    (fun ψ : SourceMode => ψ.rate.re) SourceMode.noDrift (sourceProjection χ h hs)

/-- **Per-zero set form.** The radial term `m ρ · w ρ · (Re ρ − ½)²` vanishes at every
    nontrivial zero, from `SourceComplete` + source no-drift. This is the exact `hRad` input of
    `RadialEnergyGRH.grh_of_radial_zero`, making the radial route to GRH and the source route
    (`grh_of_sourceComplete`) one and the same — both gated only on `SourceComplete`. -/
theorem radialTerm_zero_of_sourceComplete (χ : DirichletCharacter ℂ N) (h : SourceComplete χ)
    (m w : ℂ → ℝ) :
    ∀ ρ ∈ GRHSpectral.NontrivialZeros χ, m ρ * w ρ * (ρ.re - 1 / 2) ^ 2 = 0 := by
  intro ρ hρ
  obtain ⟨ψ, hψ⟩ := h ρ hρ
  have hdr : ρ.re - 1 / 2 = 0 := by
    rw [hψ, SourceMode.poleCoord, Complex.add_re, SourceMode.noDrift]; norm_num
  rw [hdr]; ring

/-! ## What the unconditional "no-drift cascade" does and does not settle

Two facts here are **unconditional**, and one is the open weld — keep them apart (Rule Three:
"no drift" overloads two different conditions):

* **Source no-drift is earned, not assumed (sense B: the radial *rate* is zero).**
  `noDrift_source_unconditional` below is just `SourceMode.noDrift` retyped — every source
  mode's `Re (rate) = 0`, from σ-free conservation (`source_noDrift`). So in
  `E_radial_zero_of_sourceComplete` the `NoDrift` antecedent is a *theorem*; the only open
  input is `SourceComplete`.

* **The orthogonal projection cascade preserves no-drift (sense A: orthogonality).**
  `GreenHelmholtz.green_helmholtz_no_drift` / `cascade_each_stage_no_drift` prove
  `⟪Gx, x − Gx⟫ = 0` through 3D→2D→1D, kernel-clean. This is the inheritance *mechanism*.

  **Caveat (the honest boundary).** Sense-A no-drift is `projection ⊥ loss`, which holds for
  *every* orthogonal projection and does **not** make the loss `‖x − Gx‖²` vanish
  (`green_helmholtz_pythagorean` keeps it). `E_radial = Σ (Re ρ − ½)² = 0` is sense B — the
  radial loss *vanishing*, i.e. every zero on the line. So the unconditional orthogonal cascade
  alone does not deliver `E_radial = 0` over the actual zeros.

* **The open weld: `DriftPreservingProjection` for the *actual* zeros = `SourceComplete`.**
  Turning the earned source no-drift into receiver `E_radial = 0` needs the receiver to *be* the
  projected source — every nontrivial zero captured by a source mode (`sourceProjection`). By
  `sourceComplete_iff_grh` that identification is equivalent to GRH; it is consumed here, never
  discharged. (Contrast the `ConcreteOperators.zero_embed` bookkeeping, where `radial := σ − ½`
  and the cascade *defines* `radial := 0` by moving it into `loss` — `(apply_cascade v).radial = 0`
  is then `rfl`-deep and the displacement survives in the loss, so it forces nothing.) -/

/-- **The source antecedent is unconditional.** `NoDrift(source)` is a theorem, not a hypothesis:
    every source mode's radial rate is `0` (`SourceMode.noDrift`, σ-free `source_noDrift`). Hence
    the standing implication's *only* open input is the identification `SourceComplete`. -/
theorem noDrift_source_unconditional : NoDrift (fun ψ : SourceMode => ψ.rate.re) :=
  SourceMode.noDrift

end RadialInheritance
