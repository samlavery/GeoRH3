import Mathlib
import RequestProject.GRHSpectralCriterion

/-!
# The Dirichlet-`L` Hadamard partial fraction — the general-`χ` GRH identification

Generalizes the repo's ζ-only `ZD.xi_logDeriv_partial_fraction` to a general nontrivial Dirichlet
character `χ`. The **target** (Step 7 of the plan) is

  `logDeriv (completedLFunction χ) s = A + ∑'_ρ (ord ρ) · [1/(s−ρ) + 1/ρ]`

over the nontrivial zeros `ρ` — the **GRH identification**: the zeros are exactly the poles of the
(prime-built) trace, an unconditional classical-analysis identity over the *actual* zeros (whose
real parts are unknown). It is **not** the on-line forcing `Re ρ = ½`, which stays open behind the
Weil/Li floor non-negativity.

This file builds the routine **foundation bricks**: definitions, entireness of `completedLFunction χ`
for `χ ≠ 1`, the fact that nontrivial zeros are zeros of the completed `L`, and the vanishing order
`≥ 1` there. The hard analytic brick (order-1 growth ⇒ summability of `ord(ρ)/‖ρ‖²`) and the
product-side / Liouville assembly are staged for the port from the repo's ζ apparatus.
-/

open Complex

namespace DirichletLHadamard

variable {N : ℕ} [NeZero N]

/-- The vanishing order (multiplicity) of the completed `L` at a point. -/
noncomputable def lOrderNat (χ : DirichletCharacter ℂ N) (ρ : ℂ) : ℕ :=
  analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ

/-- **The completed `L` is entire** for `χ ≠ 1` (no pole to remove, unlike ζ at `s = 1`). -/
theorem completedLFunction_differentiable {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    Differentiable ℂ (DirichletCharacter.completedLFunction χ) :=
  DirichletCharacter.differentiable_completedLFunction hχ

/-- Hence the completed `L` is analytic at every point. -/
theorem completedLFunction_analyticAt {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (z : ℂ) :
    AnalyticAt ℂ (DirichletCharacter.completedLFunction χ) z :=
  ((completedLFunction_differentiable hχ).differentiableOn.analyticOnNhd isOpen_univ) z
    (Set.mem_univ z)

/-- **The Archimedean Gamma factor is nonzero for `Re s > 0`** (`Gammaℝ` has zeros only at the
    non-positive even integers, both branches shifted into `Re > 0`). -/
theorem gammaFactor_ne_zero {χ : DirichletCharacter ℂ N} {s : ℂ} (hs : 0 < s.re) :
    χ.gammaFactor s ≠ 0 := by
  rcases χ.even_or_odd with h | h
  · rw [h.gammaFactor_def]
    exact Complex.Gammaℝ_ne_zero_of_re_pos hs
  · rw [h.gammaFactor_def]
    refine Complex.Gammaℝ_ne_zero_of_re_pos ?_
    rw [Complex.add_re, Complex.one_re]; linarith

/-- **A nontrivial zero of `L` is a zero of the completed `L`** (the Γ-factor is nonzero in the
    strip, so vanishing transfers). -/
theorem completedLFunction_eq_zero_of_mem {χ : DirichletCharacter ℂ N} {ρ : ℂ}
    (hρ : ρ ∈ GRHSpectral.NontrivialZeros χ) :
    DirichletCharacter.completedLFunction χ ρ = 0 := by
  obtain ⟨hre0, _, hzero⟩ := hρ
  have hρ0 : ρ ≠ 0 := fun h => by rw [h, Complex.zero_re] at hre0; exact lt_irrefl 0 hre0
  have hrel := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ ρ (Or.inl hρ0)
  rw [hzero] at hrel
  rcases div_eq_zero_iff.mp hrel.symm with h | h
  · exact h
  · exact absurd h (gammaFactor_ne_zero hre0)

/-- **The completed `L` is nonzero at `s = 2`** (`L(χ,2) ≠ 0` and the Γ-factor is nonzero). -/
theorem completedLFunction_two_ne_zero {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    DirichletCharacter.completedLFunction χ 2 ≠ 0 := by
  have hrel := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ 2
    (Or.inl (by norm_num))
  have hLne : DirichletCharacter.LFunction χ 2 ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by norm_num)
  intro hc
  rw [hc, zero_div] at hrel
  exact hLne hrel

/-- **The completed `L` is not locally zero** (entire on the connected plane, nonzero at `2`). -/
theorem completedLFunction_not_eventuallyEq_zero {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    {ρ : ℂ} : ¬ DirichletCharacter.completedLFunction χ =ᶠ[nhds ρ] 0 := by
  intro hev
  have hanalytic : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) Set.univ :=
    fun z _ => completedLFunction_analyticAt hχ z
  have hEq := hanalytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (isPreconnected_univ) (Set.mem_univ ρ) hev
  exact completedLFunction_two_ne_zero hχ (hEq (Set.mem_univ 2))

/-- **The vanishing order is `≥ 1` at every nontrivial zero** (analytic, vanishes, not locally
    zero). -/
theorem lOrderNat_pos {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {ρ : ℂ}
    (hρ : ρ ∈ GRHSpectral.NontrivialZeros χ) : 1 ≤ lOrderNat χ ρ := by
  have hana : AnalyticAt ℂ (DirichletCharacter.completedLFunction χ) ρ :=
    completedLFunction_analyticAt hχ ρ
  have hz : DirichletCharacter.completedLFunction χ ρ = 0 := completedLFunction_eq_zero_of_mem hρ
  have hne0 : analyticOrderAt (DirichletCharacter.completedLFunction χ) ρ ≠ 0 :=
    analyticOrderAt_ne_zero.mpr ⟨hana, hz⟩
  have hnetop : analyticOrderAt (DirichletCharacter.completedLFunction χ) ρ ≠ ⊤ := fun h =>
    completedLFunction_not_eventuallyEq_zero hχ (analyticOrderAt_eq_top.mp h)
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hnetop
  have hm0 : m ≠ 0 := by rintro rfl; exact hne0 hm.symm
  have : lOrderNat χ ρ = m := by
    rw [lOrderNat, analyticOrderNatAt, ← hm]; rfl
  omega

/-- **TARGET (Step 7): the general-`χ` Hadamard partial fraction** — the GRH identification. The
    log-derivative of the completed `L` is a constant plus the multiplicity-weighted resolvent sum
    over the actual nontrivial zeros. Unconditional; the on-line forcing `Re ρ = ½` is NOT here. -/
def HadamardPartialFraction (χ : DirichletCharacter ℂ N) : Prop :=
  ∃ A : ℂ, ∀ s ∉ GRHSpectral.NontrivialZeros χ,
    logDeriv (DirichletCharacter.completedLFunction χ) s
      = A + ∑' ρ : {ρ : ℂ // ρ ∈ GRHSpectral.NontrivialZeros χ},
          (lOrderNat χ ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val)

end DirichletLHadamard
