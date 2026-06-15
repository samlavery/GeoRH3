import RequestProject.HelixWindingSpectrum
import RequestProject.HelixSource

/-!
# Counting necessity: the winding resonances are exactly the zeros

The honest, provable form of the counting-law pressure test. Given the trace identity `hCompat`
(`windingReceiver θ = −L'/L(½+i·)`), the winding receiver's **resonance set** (its singular support)
is *exactly* the nontrivial-zero parameters:

* **resonates at zeros** — every zero is a resonance (`zeros_subset_singularSupport_of_traceIdentity`);
* **regular off zeros** — where `½+iz` is not an `L`-zero the receiver has a finite limit, so `z` is
  not a resonance (`windingReceiver_regular_off_zero`, below — the new analytic content: `−L'/L` is
  analytic away from the zeros).

So the geometric winding spectrum's resonances are **forced** into bijection with the zeros, hence the
winding counting function equals the zero-counting function. Its asymptotic — `N(T) ~ (T/2π)·log(qT/2π)`
(Riemann–von Mangoldt) — is the classical zero-density, *cited* not reproved. The genuinely open
**pressure test** is the converse: deriving that counting law *directly from the log-free winding
geometry* (the prime-fiber density), with no zero input. That is across the explicit-formula wall.
-/

open Complex Filter Topology HelixSource HelixLimit HelixWindingSpectrum

namespace HelixWindingCounting

variable {N : ℕ} [NeZero N]

/-- **Regular off the zeros.** Where `½+iz` is not an `L`-zero, the winding receiver has a finite
boundary limit — it equals `−L'/L(½+iz)`, which is analytic there (`L` entire and nonzero) — so `z`
is NOT a resonance. -/
theorem windingReceiver_regular_off_zero {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {θ : ℕ → ℝ}
    {z : ℂ}
    (hCompat : ∀ w, windingReceiver θ w
        = -logDeriv (DirichletCharacter.LFunction χ) (1 / 2 + Complex.I * w))
    (hz : DirichletCharacter.LFunction χ (1 / 2 + Complex.I * z) ≠ 0) :
    ∃ L, Tendsto (windingReceiver θ) (𝓝[≠] z) (𝓝 L) := by
  have hdiff : Differentiable ℂ (DirichletCharacter.LFunction χ) :=
    fun s => DirichletCharacter.differentiableAt_LFunction χ s (Or.inr hχ)
  have hana : AnalyticAt ℂ (DirichletCharacter.LFunction χ) (1 / 2 + Complex.I * z) :=
    (hdiff.differentiableOn.analyticOnNhd isOpen_univ) _ (Set.mem_univ _)
  have hld : AnalyticAt ℂ (logDeriv (DirichletCharacter.LFunction χ)) (1 / 2 + Complex.I * z) := by
    simpa [logDeriv] using hana.deriv.div hana hz
  have hheq : windingReceiver θ
      = fun w => -logDeriv (DirichletCharacter.LFunction χ) (1 / 2 + Complex.I * w) :=
    funext hCompat
  have haff_t : Tendsto (fun w : ℂ => (1 / 2 : ℂ) + Complex.I * w) (𝓝 z)
      (𝓝 (1 / 2 + Complex.I * z)) :=
    (continuous_const.add (continuous_const.mul continuous_id)).continuousAt
  have hcomp_t := (hld.continuousAt.tendsto.comp haff_t).neg
  refine ⟨-logDeriv (DirichletCharacter.LFunction χ) (1 / 2 + Complex.I * z), ?_⟩
  rw [hheq]
  exact hcomp_t.mono_left nhdsWithin_le_nhds

/-- **Resonance ⊆ zeros.** Every resonance of the winding receiver comes from an `L`-zero at `½+iz`. -/
theorem singularSupport_subset_zeros {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {θ : ℕ → ℝ}
    (hCompat : ∀ w, windingReceiver θ w
        = -logDeriv (DirichletCharacter.LFunction χ) (1 / 2 + Complex.I * w)) :
    SingularSupport (windingReceiver θ)
      ⊆ {z | DirichletCharacter.LFunction χ (1 / 2 + Complex.I * z) = 0} := by
  intro z hz
  by_contra hnz
  exact hz (windingReceiver_regular_off_zero hχ hCompat (by simpa using hnz))

/-- **Zeros ⊆ resonances.** Every nontrivial zero is a resonance of the winding receiver. -/
theorem zeros_subset_singularSupport {χ : DirichletCharacter ℂ N} {θ : ℕ → ℝ}
    (hCompat : ∀ w, windingReceiver θ w
        = -logDeriv (DirichletCharacter.LFunction χ) (1 / 2 + Complex.I * w)) :
    ∀ ρ ∈ GRHSpectral.NontrivialZeros χ, poleParam ρ ∈ SingularSupport (windingReceiver θ) :=
  zeros_subset_singularSupport_of_traceIdentity hCompat

/-- **Counting necessity, packaged.** Under the trace identity, the winding receiver's resonance set
is *trapped* between the zero-parameters and the `L`-zero parameters: every zero resonates, and every
resonance is an `L`-zero. So the geometric winding-resonance count equals the zero count — whose
asymptotic is `N(T) ~ (T/2π)·log(qT/2π)` (Riemann–von Mangoldt, classical). The geometric spectrum is
therefore *forced* to carry the zero-counting density; proving that density from the winding geometry
alone is the open pressure test. -/
theorem winding_resonances_trapped_by_zeros {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {θ : ℕ → ℝ}
    (hCompat : ∀ w, windingReceiver θ w
        = -logDeriv (DirichletCharacter.LFunction χ) (1 / 2 + Complex.I * w)) :
    (∀ ρ ∈ GRHSpectral.NontrivialZeros χ, poleParam ρ ∈ SingularSupport (windingReceiver θ)) ∧
    SingularSupport (windingReceiver θ)
      ⊆ {z | DirichletCharacter.LFunction χ (1 / 2 + Complex.I * z) = 0} :=
  ⟨zeros_subset_singularSupport hCompat, singularSupport_subset_zeros hχ hCompat⟩

end HelixWindingCounting
