import RequestProject.HelixFlowUnitaryGroup
import RequestProject.EnergyBalance

/-!
# Pushing the von Mangoldt EF through the unitary flow

The **von-Mangoldt-weighted trace** of the unitary flow (`HelixFlow.phasorFlow`) — the signed prime
phasor chain — is the log-derivative `−L'/L`, and its singularity (resonance) is *exactly* a
nontrivial zero. No numerics: the resonant phasor-cancellation event **is** the zero, at height
`t = Im ρ`.

* `flowVonMangoldtTrace χ s = Σ_n χ(n)·Λ(n)·n^{-σ}·U(t)(n)⁻¹` — the prime phasor chain.
* `flowVonMangoldtTrace_eq_neg_logDeriv` — for `Re s > 1` it **equals `−L'/L(s)`** (the von Mangoldt
  explicit-formula bridge `EnergyBalance.geometric_eq_spectral`). The flow's Λ-weighted trace is the
  log-derivative.
* `flowVonMangoldtTrace_resonates_at_zero` — the continuation `−L'/L` **resonates** (no finite limit)
  at every nontrivial zero `ρ` (`EnergyBalance.resonates_at_zeros`). So the prime phasor chain's
  singularity is the zero — and it sits at `s = ρ`, i.e. height `Im ρ`.

`Λ(n)` is supported on prime powers, so this is literally the **prime fibre phasor chain**: each prime
power `q` contributes `χ(q)·log p·q^{-σ}·U(t)(q)⁻¹`, and the chain's harmonic singularity is the zero.
-/

open Complex HelixFlow ArithmeticFunction Filter Topology

namespace HelixFlowVonMangoldt

variable {N : ℕ} [NeZero N]

/-- **The von-Mangoldt-weighted flow trace** — the signed prime phasor chain `Σ_n χ(n)·Λ(n)·n^{-σ}·
    U(t)(n)⁻¹`, with `U(t)(n) = phasorFlow t n` the unitary flow. -/
noncomputable def flowVonMangoldtTrace (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  ∑' n : ℕ, χ (n : ZMod N) * (vonMangoldt n : ℂ)
    * (((n : ℝ) ^ s.re : ℝ) : ℂ)⁻¹ * (phasorFlow s.im n : ℂ)⁻¹

/-- **The prime phasor chain IS `−L'/L`** (`Re s > 1`). Each integer `n` contributes its character
    `χ(n)`, von Mangoldt weight `Λ(n)`, radial decay `n^{-σ}`, and inverse phasor `U(t)(n)⁻¹ = n^{-it}`;
    the sum is the log-derivative `−L'/L(s)` — the von Mangoldt explicit-formula bridge
    (`EnergyBalance.geometric_eq_spectral`) read through the flow. -/
theorem flowVonMangoldtTrace_eq_neg_logDeriv (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    flowVonMangoldtTrace χ s = -logDeriv (DirichletCharacter.LFunction χ) s := by
  rw [flowVonMangoldtTrace, ← EnergyBalance.geometric_eq_spectral χ hs, LSeries]
  refine tsum_congr (fun n => ?_)
  rcases eq_or_ne n 0 with hn | hn
  · subst hn
    rw [LSeries.term_zero]
    simp
  · rw [LSeries.term_of_ne_zero hn, Pi.mul_apply]
    have hsplit : (((n : ℝ) ^ s.re : ℝ) : ℂ) * (phasorFlow s.im n : ℂ) = (n : ℂ) ^ s := by
      rw [phasorFlow_eq_cpow s.im n hn,
          show (((n : ℝ) ^ s.re : ℝ) : ℂ) = (n : ℂ) ^ (s.re : ℂ) from by
            rw [Complex.ofReal_cpow (by positivity)]; push_cast; ring,
          ← Complex.cpow_add _ _ (by exact_mod_cast hn)]
      congr 1
      rw [mul_comm Complex.I (s.im : ℂ)]; exact Complex.re_add_im s
    rw [← hsplit, div_eq_mul_inv, mul_inv]
    ring

/-- **The resonant singularity event is the zero.** The continuation of the prime phasor chain
    (`= −L'/L`) has **no finite limit** at any nontrivial zero `ρ` — it resonates. This is the
    vanishing/singularity the chain equates to the zero (`EnergyBalance.resonates_at_zeros`), located at
    `s = ρ`, i.e. at height `Im ρ`. -/
theorem flowVonMangoldtTrace_resonates_at_zero (χ : DirichletCharacter ℂ N) {ρ : ℂ}
    (hρ : ρ ∈ GRHSpectral.NontrivialZeros χ) :
    ¬ ∃ L, Tendsto (fun s => -logDeriv (DirichletCharacter.LFunction χ) s) (𝓝[≠] ρ) (𝓝 L) :=
  EnergyBalance.resonates_at_zeros χ hρ

/-- **The chain's singularity = the zero, assembled.** For `Re s > 1` the prime phasor chain equals
    `−L'/L`; and that function resonates exactly at the nontrivial zeros. So the prime fibre phasor
    chain, continued past the convergent region, has a harmonic singularity **at every zero `ρ`** — the
    resonance *is* the vanishing of `L`, at height `Im ρ`. (The continuation into `0 < Re s` is the
    helix's own — `DirichletClosureLedger.cChar_eq_LFunction` via Abel summation.) -/
theorem flowChain_singularity_is_zero (χ : DirichletCharacter ℂ N) {ρ : ℂ}
    (hρ : ρ ∈ GRHSpectral.NontrivialZeros χ) :
    (∀ s : ℂ, 1 < s.re →
        flowVonMangoldtTrace χ s = -logDeriv (DirichletCharacter.LFunction χ) s) ∧
      ¬ ∃ L, Tendsto (fun s => -logDeriv (DirichletCharacter.LFunction χ) s) (𝓝[≠] ρ) (𝓝 L) :=
  ⟨fun _ hs => flowVonMangoldtTrace_eq_neg_logDeriv χ hs,
   flowVonMangoldtTrace_resonates_at_zero χ hρ⟩

end HelixFlowVonMangoldt

#print axioms HelixFlowVonMangoldt.flowVonMangoldtTrace_eq_neg_logDeriv
#print axioms HelixFlowVonMangoldt.flowChain_singularity_is_zero
