import RequestProject.HelixSource

open Complex ArithmeticFunction Filter Topology

namespace EnergyBalance

variable {N : ℕ} [NeZero N]

/-! # Unconditional energy balance: geometric side − spectral side = 0

The geometric prime-fiber counting readout `Σ Λ(n)·χ(n)·n^{-s}` and the spectral readout `−L'/L(s)`
are the **same function**; their difference vanishes. No hypothesis, no Hadamard, no GRH — just the
von Mangoldt identity. -/

/-- **Energy balance, difference form.** Geometric prime side minus spectral side is `0`. -/
theorem energy_balance (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeries ((fun n : ℕ => χ ↑n) * fun n => (vonMangoldt n : ℂ)) s
        - (-logDeriv (DirichletCharacter.LFunction χ) s) = 0 := by
  rw [HelixSource.neg_logDeriv_LFunction_eq_vonMangoldt χ hs]; ring

/-- **Energy balance, identity form.** Geometric prime side `=` spectral side `−L'/L`. -/
theorem geometric_eq_spectral (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeries ((fun n : ℕ => χ ↑n) * fun n => (vonMangoldt n : ℂ)) s
      = -logDeriv (DirichletCharacter.LFunction χ) s :=
  (HelixSource.neg_logDeriv_LFunction_eq_vonMangoldt χ hs).symm

/-- **Past the strip — the balance becomes a statement about where the zeros sit.**
    `Re s = 1` is only where the prime *sum* stops converging; the geometric readout continued is
    `−L'/L`, which has no such boundary (and neither does the helix winding). Pushed past the strip,
    it **resonates** — has no finite limit — at exactly the nontrivial zeros. So the global energy
    balance's singular support *is* the zero set: the zeros are precisely where the geometric/spectral
    readout blows up. Unconditional. (That this singular support lies on `ℝ` — the zeros on the line —
    is the Hilbert–Pólya / self-adjoint step, not contained here.) -/
theorem resonates_at_zeros (χ : DirichletCharacter ℂ N) {ρ : ℂ}
    (hρ : ρ ∈ GRHSpectral.NontrivialZeros χ) :
    ¬ ∃ L, Tendsto (fun s => -logDeriv (DirichletCharacter.LFunction χ) s) (𝓝[≠] ρ) (𝓝 L) :=
  HelixSource.LFunction_logDeriv_not_tendsto χ hρ

end EnergyBalance
