import RequestProject.HilbertPolyaChain

/-!
# Helix → RH: the full route assembled in one place, with the single open step isolated

This file puts the Hilbert–Pólya / helix route to `RiemannHypothesis` in one place. Everything
that is proven elsewhere is wired together here; the one remaining step is isolated, named, and
shown — at the kernel level — to be **exactly** RH, not a smaller lemma.

## Proven, kernel-clean (cited from across the repo)
* `HelixForm.gramOp_isSelfAdjoint` — the Gram/loss operator `G∞ = B∞*B∞` is self-adjoint
  (von Neumann's `T*T`), unconditionally ⟹ real spectrum.
* `CriticalLinePhasor.MobiusMidpoint.norm_one_sub_inv_eq_one_iff` — the faithful Möbius
  readout: `‖1 − 1/ρ‖ = 1 ↔ Re ρ = ½`.
* `HelixStandingWave.zeta_zero_on_line_iff_standingWave_node` — on-line ζ-zeros ↔ nodes.
* `HelixSource.source_noDrift` — σ-free no-drift: conserved loss ⟹ `Re (rate) = 0`.
* `HelixSource.SourceMode.phaseModulus_eq_eigenvectorEnergy` — phase modulus = eigenvector energy.

## RH from the identification (clean, conditional)
`helix_RH_of_sourceComplete` derives `RiemannHypothesis` from `SourceComplete` via the σ-free
forcing (`grh_of_sourceComplete`) and the GRH→RH bridge (`RH_by_GRH`). No `sorry`.

## The single open step, and what it actually is
`sourceComplete_attempt` tries to discharge `SourceComplete` directly. Building the capturing
source mode at an arbitrary nontrivial zero `ρ` needs its `conserved` field, which holds iff
`Re (ρ − ½) = 0`, i.e. `Re ρ = ½`. So the residual is **literally `ρ.re = 1/2`** — RH for that
zero. The route is fully wired; the one missing fact is the conclusion itself.
-/

open Complex

/-- **RH for ζ from the identification.** If every nontrivial ζ-zero is captured by a source
mode (`SourceComplete`), then `RiemannHypothesis`, via the σ-free no-drift forcing and the
GRH→RH bridge. Clean, conditional — no `sorry`. -/
theorem helix_RH_of_sourceComplete
    (h : HelixSource.SourceComplete (1 : DirichletCharacter ℂ 1)) : RiemannHypothesis :=
  RH_by_GRH (HelixSource.grh_of_sourceComplete (1 : DirichletCharacter ℂ 1) h)

/-- **The attempt to discharge the identification, and the exact residual.** Everything except
one `have` is wired: given `ρ.re = ½`, the source mode `rate := ρ − ½` is conserved (because
`Re (ρ − ½) = 0`) and its pole-coordinate is `ρ`. So `SourceComplete` reduces to the single
`sorry` `ρ.re = 1/2` — which is RH for `ρ`. The weld is RH itself, not a reduction. -/
theorem sourceComplete_attempt :
    HelixSource.SourceComplete (1 : DirichletCharacter ℂ 1) := by
  intro ρ hρ
  have hhalf : ρ.re = 1 / 2 := by
    sorry
  have hre : (ρ - 1 / 2 : ℂ).re = 0 := by
    simp [Complex.sub_re, hhalf]
  refine ⟨{ rate := ρ - 1 / 2, amp := 1, amp_ne := one_ne_zero, conserved := ?_ }, ?_⟩
  · intro τ
    rw [hre]; simp
  · show ρ = 1 / 2 + (ρ - 1 / 2)
    ring
