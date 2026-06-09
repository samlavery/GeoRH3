import RequestProject.HelixSource
import RequestProject.RadialEnergy

open Complex

namespace RadialEnergyGRH

open GRHSpectral

variable {N : ℕ} [NeZero N]

/-- **The plumbing: radial energy zero ⟹ GRH** (your `grh_of_radialEnergy_zero`, step 5).
    If at every nontrivial zero the radial term `m_ρ · w_ρ · (Re ρ − ½)²` vanishes, with strictly
    positive multiplicity `m` and weight `w`, then every zero is on the line. This is the
    trace-identity side: it consumes `E_radial = 0` (the no-drift *output*) plus strict positivity
    and delivers GRH — no zero-placement, just coercivity. The **open input is `hRad` itself**
    (`E_radial = 0`), which is the source no-drift; that is the unbuilt weld, not this. -/
theorem grh_of_radial_zero (χ : DirichletCharacter ℂ N) (m w : ℂ → ℝ)
    (hm : ∀ ρ ∈ NontrivialZeros χ, 0 < m ρ) (hw : ∀ ρ ∈ NontrivialZeros χ, 0 < w ρ)
    (hRad : ∀ ρ ∈ NontrivialZeros χ, m ρ * w ρ * (ρ.re - 1 / 2) ^ 2 = 0) :
    GRH χ := by
  intro ρ hρ
  have hpos : 0 < m ρ * w ρ := mul_pos (hm ρ hρ) (hw ρ hρ)
  have hsq : (ρ.re - 1 / 2) ^ 2 = 0 := by
    rcases mul_eq_zero.mp (hRad ρ hρ) with h1 | h2
    · exact absurd h1 (ne_of_gt hpos)
    · exact h2
  have hlin : ρ.re - 1 / 2 = 0 := by rw [pow_two] at hsq; exact mul_self_eq_zero.mp hsq
  linarith

end RadialEnergyGRH
