import Mathlib
import RequestProject.HelixCollapseReality

/-!
# The on-line forcing: bounded radial drift + functional equation ⇒ `Re ρ = ½`

The forcing half of the Hilbert–Pólya certificate, with **no** Pythagorean split, **no**
Green/Helmholtz decomposition, **no** explicit formula, **no** Li/Weil. It is an elementary `rpow`
fact folded by the functional equation:

* the radial drift of a mode at real part `σ` against the `√n` baseline (`HelixArcLength`) is
  `drift σ x = x^{σ−½}`;
* it is **bounded on `[1,∞)` iff `σ ≤ ½`** (`rpow` monotonicity — off-line `σ>½` it diverges);
* the functional equation pairs a zero `ρ` with `1−ρ` (`completedRiemannZeta_one_sub`), so if both are
  *captured* (bounded drift) then `σ ≤ ½` **and** `1−σ ≤ ½`, forcing `σ = ½`.

The bounded-drift hypothesis is the **capture / identification** (that an actual zero is a bounded mode
of this geometry) — the one remaining piece, and a geometric one. Everything here is on the log-free
side.
-/

open Real

namespace HelixForcing

/-- The radial drift of a mode at real part `σ`, at scale `x`: `x^{σ−½}` (deviation from the `√n`
    baseline). -/
noncomputable def drift (σ x : ℝ) : ℝ := x ^ (σ - 1 / 2)

/-- **The drift is bounded on `[1,∞)` iff `σ ≤ ½`** — pure `rpow` monotonicity. Off-line (`σ > ½`)
    the drift `x^{σ−½}` diverges; on or below the line it stays `≤ 1`. -/
theorem drift_bounded_iff (σ : ℝ) :
    (∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → drift σ x ≤ C) ↔ σ ≤ 1 / 2 := by
  unfold drift
  constructor
  · rintro ⟨C, hC⟩
    by_contra h
    have hlt : (1 : ℝ) / 2 < σ := not_le.mp h
    have hpos : 0 < σ - 1 / 2 := by linarith
    obtain ⟨x, hgt, hge⟩ := (((tendsto_rpow_atTop hpos).eventually_gt_atTop C).and
      (Filter.eventually_ge_atTop 1)).exists
    exact absurd (hC x hge) (not_le.mpr hgt)
  · intro hσ
    exact ⟨1, fun x hx => Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith)⟩

/-- **The forcing.** If the drift at `σ` and at `1−σ` are both bounded, then `σ = ½`. (Applied to a
    zero `ρ` and its functional-equation partner `1−ρ`, each captured.) -/
theorem online_of_drift_bounded {σ : ℝ}
    (h : ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → drift σ x ≤ C)
    (h' : ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → drift (1 - σ) x ≤ C) : σ = 1 / 2 := by
  have h1 := (drift_bounded_iff σ).mp h
  have h2 := (drift_bounded_iff (1 - σ)).mp h'
  linarith

/-- **The functional equation pairs zeros**: if `Λ(ρ)=0` then `Λ(1−ρ)=0`. This is why both `ρ` and its
    mirror are captured, feeding the two hypotheses of `online_of_drift_bounded`. -/
theorem zero_pair {ρ : ℂ} (hρ : completedRiemannZeta ρ = 0) :
    completedRiemannZeta (1 - ρ) = 0 := by
  rw [completedRiemannZeta_one_sub]; exact hρ

/-- **On-line forcing for a captured zero** (the forcing half, assembled): a zero `ρ` whose mode and
    whose functional-equation mirror's mode both have **bounded drift** lies on the critical line,
    `Re ρ = ½`. The bounded-drift hypotheses are the CAPTURE — the one remaining (geometric)
    identification; the FE-pairing (`zero_pair`) is why the mirror is also a zero, hence also captured. -/
theorem online_of_captured_zero {ρ : ℂ}
    (hcap : ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → drift ρ.re x ≤ C)
    (hcap' : ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → drift (1 - ρ.re) x ≤ C) : ρ.re = 1 / 2 :=
  online_of_drift_bounded hcap hcap'

end HelixForcing
