import Mathlib
import RequestProject.ChiThreeLogDerivIdentity
import RequestProject.GRHSpectralCriterion
import RequestProject.HelixSource
import RequestProject.Chi3LogDerivPole
import RequestProject.Chi3SourceTrace

/-!
# The functional-equation reflection, the pairwise conservation, and the exact weld

Attacking the on-line forcing honestly. The repo's `HelixSource.SourceMode` bakes a `conserved` field
(`∀τ, e^{(rate.re)·τ}·amp = amp`) which `source_noDrift` turns into `rate.re = 0`. But building the
mode that *captures* a zero `ρ` (poleCoord `½+rate = ρ`, so `rate = ρ−½`) requires supplying
`conserved`, i.e. `e^{(Re ρ−½)τ}·amp = amp ∀τ`, i.e. `Re ρ = ½`. So discharging `conserved` for the
actual zeros **is** GRH — the `SourceComplete`/`grh_of_sourceComplete` route smuggles the conclusion
into that field (a Rule-Ten landmine). To earn anything we need a *genuine, independent* reason the
transport conserves at the real zeros.

**What the functional equation genuinely earns (unconditional, kernel-clean):**

* `chi3_zero_reflection` — the nontrivial zeros are **symmetric about the critical line**: `ρ` a zero
  ⟹ `1−ρ` a zero. (From Mathlib's `IsPrimitive.completedLFunction_one_sub`, with `χ₃⁻¹ = χ₃`
  (quadratic) and the odd Γ-factor non-vanishing in the strip. The direction we need is *free* — the
  FE multiplies the zero through.)
* `chi3_pair_drift_sum_zero` — writing the **radial drift** `δ(ρ) := Re ρ − ½`, a reflection pair has
  `δ(ρ) + δ(1−ρ) = 0`: the drifts are **equal and opposite**.
* `chi3_pair_jointly_conserved` — therefore the **doublet** `{ρ, 1−ρ}` is genuinely conserved:
  `e^{δ(ρ)·τ}·e^{δ(1−ρ)·τ} = 1` for all `τ`. One mode drifts out, its mirror drifts in, at exactly
  opposite rates — the *pair's* loss-norm is preserved. This is real joint unitarity, not assumed.
* `chi3_pair_centroid_half` — the pair's centroid is exactly on the line: `(Re ρ + Re(1−ρ))/2 = ½`.

**The exact weld (open — this is GRH, stated plainly, not dressed as a reduction).** The `conserved`
field needs each mode *individually* conserved, `δ(ρ) = 0`. The FE earns only the **pairwise**
version `δ(ρ) + δ(1−ρ) = 0`. The gap "pair sum `0` ⟹ each `0`" is precisely: the reflection doublet
is *degenerate* (`ρ = 1−ρ`, both on the line). That degeneracy is GRH. The FE alone is consistent
with a non-degenerate off-line doublet `{ρ, 1−ρ}` whose drifts merely cancel. So the honest residue is
**"force the doublet to collapse"**, and nothing here — no costume, no `σ−½` relabel — closes it.
-/

open Complex DirichletCharacter

namespace Chi3Reflection

/-! ## Functional-equation inputs for χ₃ (all earned, unconditional) -/

/-- χ₃ is **primitive**: its conductor divides the prime `3` and isn't `1` (χ₃ ≠ 1), so it is `3`. -/
theorem χ3_primitive : (ChiThree.χ3).IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def]
  have hdvd : (ChiThree.χ3).conductor ∣ 3 := DirichletCharacter.conductor_dvd_level _
  have hne1 : (ChiThree.χ3).conductor ≠ 1 := fun h =>
    ChiThree.χ3_ne_one (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h)
  rcases (Nat.prime_three).eq_one_or_self_of_dvd _ hdvd with h | h
  · exact absurd h hne1
  · exact h

/-- χ₃ is **odd**: `χ₃(−1) = χ₃(2) = −1`. -/
theorem χ3_odd : (ChiThree.χ3).Odd := by
  show ChiThree.χ3 (-1) = -1
  rw [show (-1 : ZMod 3) = 2 from by decide, ChiThree.χ3_two]

/-- χ₃ is its **own inverse** (a quadratic character: values in `{0, ±1}` are self-inverse). -/
theorem χ3_inv : (ChiThree.χ3)⁻¹ = ChiThree.χ3 :=
  ((quadraticChar_isQuadratic (ZMod 3)).comp _ : (ChiThree.χ3).IsQuadratic).inv

/-- The odd Γ-factor `Gammaℝ(s+1)` of χ₃ is **non-vanishing** for `Re s > −1` (in particular the
    whole strip): `Γ` has no zeros and the shifted argument has positive real part. -/
theorem gammaFactor_chi3_ne_zero {s : ℂ} (hs : -1 < s.re) :
    gammaFactor ChiThree.χ3 s ≠ 0 := by
  rw [χ3_odd.gammaFactor_def]
  apply Complex.Gammaℝ_ne_zero_of_re_pos
  rw [Complex.add_re, Complex.one_re]; linarith

/-- In the strip, a zero of `L` is a zero of the **completed** `L` (the Γ-factor is finite, nonzero). -/
theorem completedL_chi3_zero_of_L_zero {ρ : ℂ} (hs : -1 < ρ.re)
    (h : LFunction ChiThree.χ3 ρ = 0) : completedLFunction ChiThree.χ3 ρ = 0 := by
  have hdiv := LFunction_eq_completed_div_gammaFactor ChiThree.χ3 ρ (Or.inr (by norm_num))
  rw [h] at hdiv
  rcases div_eq_zero_iff.mp hdiv.symm with h' | h'
  · exact h'
  · exact absurd h' (gammaFactor_chi3_ne_zero hs)

/-- A zero of the **completed** `L` is a zero of `L` (free: `0 / Γ = 0`). -/
theorem L_chi3_zero_of_completedL_zero {ρ : ℂ}
    (h : completedLFunction ChiThree.χ3 ρ = 0) : LFunction ChiThree.χ3 ρ = 0 := by
  rw [LFunction_eq_completed_div_gammaFactor ChiThree.χ3 ρ (Or.inr (by norm_num)), h, zero_div]

/-- **The χ₃ functional equation** (Mathlib's `IsPrimitive.completedLFunction_one_sub`, with
    `χ₃⁻¹ = χ₃`): `Λ(1−s) = 3^{s−½}·ε·Λ(s)`. -/
theorem chi3_completedL_one_sub (s : ℂ) :
    completedLFunction ChiThree.χ3 (1 - s)
      = (3 : ℂ) ^ (s - 1 / 2) * rootNumber ChiThree.χ3 * completedLFunction ChiThree.χ3 s := by
  have h := χ3_primitive.completedLFunction_one_sub s
  rw [χ3_inv] at h; rw [h]; norm_num

/-! ## The earned reflection symmetry -/

/-- **The reflection symmetry — earned, unconditional.** If `ρ` is a nontrivial zero of `L(·,χ₃)`,
    so is `1 − ρ`. The two sit symmetrically across the critical line. (The needed direction is free:
    `Λ(1−ρ) = (factor)·Λ(ρ) = (factor)·0 = 0`; `rootNumber ≠ 0` is *not* required.) -/
theorem chi3_zero_reflection {ρ : ℂ} (hρ : ρ ∈ GRHSpectral.NontrivialZeros ChiThree.χ3) :
    (1 - ρ) ∈ GRHSpectral.NontrivialZeros ChiThree.χ3 := by
  obtain ⟨h0, h1, hz⟩ := hρ
  refine ⟨?_, ?_, ?_⟩
  · rw [Complex.sub_re, Complex.one_re]; linarith
  · rw [Complex.sub_re, Complex.one_re]; linarith
  · apply L_chi3_zero_of_completedL_zero
    rw [chi3_completedL_one_sub, completedL_chi3_zero_of_L_zero (by linarith) hz]; ring

/-! ## The pairwise conservation the FE earns -/

/-- The **radial drift** of a zero: `δ(ρ) = Re ρ − ½`. The on-line condition is `δ(ρ) = 0`; this is
    `HelixProjectionLoss.zeroLoss` by another name — *but here it is a measured quantity, not a
    coordinate we are free to set.* -/
noncomputable def drift (ρ : ℂ) : ℝ := ρ.re - 1 / 2

/-- **The pair drift-sum law — earned.** A reflection pair `{ρ, 1−ρ}` has equal-and-opposite drift:
    `δ(ρ) + δ(1−ρ) = 0`. (Pure algebra on `Re(1−ρ) = 1 − Re ρ`; the *content* is that `1−ρ` is a
    genuine zero, `chi3_zero_reflection`.) -/
theorem chi3_pair_drift_sum_zero (ρ : ℂ) : drift ρ + drift (1 - ρ) = 0 := by
  simp only [drift, Complex.sub_re, Complex.one_re]; ring

/-- **The doublet is jointly conserved — earned.** Because the drifts cancel, the *product* of the
    two modes' loss-norm factors is preserved for all transport times:
    `e^{δ(ρ)·τ} · e^{δ(1−ρ)·τ} = 1`. This is the genuine `SourceMode.conserved` condition — but for
    the **pair**, not for either mode alone. One drifts out, its mirror drifts in, at exactly
    opposite rates. -/
theorem chi3_pair_jointly_conserved (ρ : ℂ) (τ : ℝ) :
    Real.exp (drift ρ * τ) * Real.exp (drift (1 - ρ) * τ) = 1 := by
  rw [← Real.exp_add]
  have : drift ρ * τ + drift (1 - ρ) * τ = (drift ρ + drift (1 - ρ)) * τ := by ring
  rw [this, chi3_pair_drift_sum_zero, zero_mul, Real.exp_zero]

/-- **The pair centroid is exactly on the line — earned.** `(Re ρ + Re(1−ρ))/2 = ½`. The doublet's
    center of mass is on the critical line, regardless of where `ρ` itself sits. -/
theorem chi3_pair_centroid_half (ρ : ℂ) : (ρ.re + (1 - ρ).re) / 2 = 1 / 2 := by
  rw [Complex.sub_re, Complex.one_re]; ring

/-- **Both members of a reflection pair are poles of the source trace** (Ledger 2): the energy bridge
    `Chi3Bridge.source_pole_energy_eq_projection_loss_atom` therefore applies to `1−ρ` exactly as to
    `ρ`. The conserved doublet carries pole energy on *both* legs. -/
theorem chi3_reflection_poleAt {ρ : ℂ} (hρ : ρ ∈ GRHSpectral.NontrivialZeros ChiThree.χ3) :
    Chi3Pole.PoleAt (Chi3Source.SourceTrace ChiThree.χ3) (1 - ρ) := by
  have hz : LFunction ChiThree.χ3 (1 - ρ) = 0 := (chi3_zero_reflection hρ).2.2
  have hpole := (Chi3Pole.zero_iff_logDeriv_pole ChiThree.χ3 ChiThree.χ3_ne_one (1 - ρ)).mp hz
  have hfun : Chi3Source.SourceTrace ChiThree.χ3
      = (fun z => -deriv (LFunction ChiThree.χ3) z / LFunction ChiThree.χ3 z) := by
    funext z; simp only [Chi3Source.SourceTrace, logDeriv_apply]; ring
  rw [hfun]; exact hpole

/-! ## The exact weld (open — GRH, stated plainly)

The `SourceMode.conserved` field for the mode capturing `ρ` is `∀τ, e^{δ(ρ)·τ}·amp = amp`, i.e.
`δ(ρ) = 0`. The FE earns the **pairwise** law `δ(ρ) + δ(1−ρ) = 0` (`chi3_pair_drift_sum_zero`) and the
joint conservation (`chi3_pair_jointly_conserved`) — but **not** `δ(ρ) = 0` for each `ρ`. The missing
implication is:

> `δ(ρ) + δ(1−ρ) = 0`  ⟹  `δ(ρ) = 0`  (the doublet `{ρ, 1−ρ}` is degenerate, `ρ = 1−ρ`).

This is exactly **GRH for χ₃**. It is *not* discharged here, and must not be faked: setting `δ := 0`
by fiat is the `zero_embed`/`σ−½` costume (Rule Two); writing `grh_of_<pair⇒each>` is a Rule-Ten
landmine. The honest state: the FE collapses the obligation from "every zero on the line" to "every
reflection doublet is degenerate" — a real, equivalent restatement, still open. -/

end Chi3Reflection
