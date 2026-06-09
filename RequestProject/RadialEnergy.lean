import Mathlib

open scoped BigOperators

namespace RadialEnergy

variable {ι : Type*} (s : Finset ι) (m w β : ι → ℝ)

/-- **Radial energy** of the zero set: `Σ_ρ  m_ρ · w_ρ · (β_ρ − ½)²` — each zero's transverse
    displacement from the critical line, squared, weighted by multiplicity `m` and weight `w`.
    This is the `E_radial` of the decomposition `E_cancellation = E_axis + E_radial`. -/
noncomputable def E_radial : ℝ := ∑ ρ ∈ s, m ρ * w ρ * (β ρ - 1 / 2) ^ 2

/-- **E_radial ≥ 0.** A sum of non-negative terms (`m,w ≥ 0`, and a square). This step is real. -/
theorem E_radial_nonneg (hm : ∀ ρ ∈ s, 0 ≤ m ρ) (hw : ∀ ρ ∈ s, 0 ≤ w ρ) :
    0 ≤ E_radial s m w β :=
  Finset.sum_nonneg fun ρ hρ =>
    mul_nonneg (mul_nonneg (hm ρ hρ) (hw ρ hρ)) (sq_nonneg _)

/-- **E_radial = 0 ⟹ every zero on the line.** Strictly positive weights ⇒ each squared
    displacement vanishes ⇒ `β_ρ = ½`. This step is also real. -/
theorem beta_half_of_E_radial_zero (hm : ∀ ρ ∈ s, 0 < m ρ) (hw : ∀ ρ ∈ s, 0 < w ρ)
    (h : E_radial s m w β = 0) : ∀ ρ ∈ s, β ρ = 1 / 2 := by
  have hterms : ∀ σ ∈ s, 0 ≤ m σ * w σ * (β σ - 1 / 2) ^ 2 := fun σ hσ =>
    mul_nonneg (mul_nonneg (hm σ hσ).le (hw σ hσ).le) (sq_nonneg _)
  intro ρ hρ
  have hzero : m ρ * w ρ * (β ρ - 1 / 2) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hterms).mp h ρ hρ
  have hpos : 0 < m ρ * w ρ := mul_pos (hm ρ hρ) (hw ρ hρ)
  have hsq : (β ρ - 1 / 2) ^ 2 = 0 := by
    rcases mul_eq_zero.mp hzero with h1 | h2
    · exact absurd h1 (ne_of_gt hpos)
    · exact h2
  have hlin : β ρ - 1 / 2 = 0 := by rw [pow_two] at hsq; exact mul_self_eq_zero.mp hsq
  linarith

/-- **The premise IS the conclusion.** With strictly positive weights, `E_radial = 0` is *logically
    equivalent* to `∀ρ, β_ρ = ½`. So the input `E_radial = 0` — i.e. `E_cancellation = E_axis`, the
    "no transverse displacement" / no-drift claim — already states GRH; it is not a different
    hypothesis from the conclusion. The positivity (`E_radial_nonneg`, `beta_half_of_E_radial_zero`)
    is genuine and proved. The entire GRH content sits in establishing `E_radial = 0` **without**
    assuming `β = ½`, which the universal energy equality (`geometric = spectral`, an `=`) does not
    give: it equates the two traces, it does not assert the cancellation energy is purely axial. -/
theorem E_radial_zero_iff_grh (hm : ∀ ρ ∈ s, 0 < m ρ) (hw : ∀ ρ ∈ s, 0 < w ρ) :
    E_radial s m w β = 0 ↔ ∀ ρ ∈ s, β ρ = 1 / 2 := by
  refine ⟨beta_half_of_E_radial_zero s m w β hm hw, fun h => ?_⟩
  refine Finset.sum_eq_zero fun ρ hρ => ?_
  rw [h ρ hρ]; ring

end RadialEnergy
