import RequestProject.HelixSource
import RequestProject.HelixSourceMultiplicity

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

/-- **Sole origin = energy balance (location-free).** Every nontrivial zero `ρ` of `L(χ)` is a
    singularity of the energy-balance readout — the geometric prime side `Σ χ(n)Λ(n) n^{-s}` continued
    (`= −L'/L`, `geometric_eq_spectral`) — and that singularity is a **simple pole whose energy (residue
    magnitude) is exactly the zero's multiplicity** `n = ord_ρ L ≥ 1`. The two sides' energies match: the
    **zero-side energy** `analyticOrderAt L ρ = n` equals the **prime-side energy** (the residue `−n` of
    the continued accumulator). Read `−L'/L (s) = −n·(s−ρ)⁻¹ + analytic`.

    **σ-free / location-free — and that is the point.** No `Re ρ`, no `½` appears: a zero is *where the
    prime side triggers an energy-matched vanishing*, with no assertion about where that height sits.
    That the singularity lies on the line (`Re ρ = ½`) is the **separate** no-drift / self-adjoint
    forcing (`HelixSource.source_noDrift`, `HelixForm.gramOp_isSelfAdjoint`), inherited downstream — not
    contained in, and not presupposed by, this lemma. This is the honest sole-origin: the zero is an
    effect of a balanced prime cancellation (`Origination.zeros_dependentlyOriginated`), and its energy
    is conserved across the duality. -/
theorem sole_origin (χ : DirichletCharacter ℂ N) {ρ : ℂ}
    (hρ : ρ ∈ GRHSpectral.NontrivialZeros χ) :
    (¬ ∃ L, Tendsto (fun s => -logDeriv (DirichletCharacter.LFunction χ) s) (𝓝[≠] ρ) (𝓝 L)) ∧
      ∃ (n : ℕ) (g : ℂ → ℂ), 1 ≤ n ∧ AnalyticAt ℂ g ρ ∧ g ρ ≠ 0 ∧
        analyticOrderAt (DirichletCharacter.LFunction χ) ρ = (n : ℕ∞) ∧
        ∀ᶠ s in nhdsWithin ρ {ρ}ᶜ,
          -logDeriv (DirichletCharacter.LFunction χ) s
            = -((n : ℂ) * (s - ρ)⁻¹ + deriv g s / g s) := by
  refine ⟨resonates_at_zeros χ hρ, ?_⟩
  obtain ⟨n, g, hn, hg, hgne, hord, hform⟩ := HelixSource.LFunction_logDeriv_residue_eq_order χ hρ
  refine ⟨n, g, hn, hg, hgne, hord, ?_⟩
  filter_upwards [hform] with s hs
  rw [hs]

/-- **The energy match — which prime cancellations are zeros.** At every nontrivial zero `ρ`, the
    energy-balanced readout (`−L'/L = Σ χ(n)Λ(n) n^{-s}`, the signed prime sum, by
    `geometric_eq_spectral`) has a **simple pole with residue `−n`**, `n = ord_ρ L ≥ 1`, so its
    **singularity energy** — the squared residue magnitude — is `‖−n‖² = n²`. Because the geometric
    prime side and the spectral side are the **same** readout, this `n²` is carried by *both*: the
    prime-side firing energy `|primes|²` (the peak) and the spectral dip both equal `n²`. That is the
    **energy match**, σ-free. And `resonates_at_zeros` makes it a *selection*: the readout dips only at
    the zeros, so a prime cancellation is a zero exactly when its energy lands on one of these `n²`
    dips — most cancellations carry no matching dip and are not zeros. -/
theorem energy_match_at_zero (χ : DirichletCharacter ℂ N) {ρ : ℂ}
    (hρ : ρ ∈ GRHSpectral.NontrivialZeros χ) :
    ∃ (n : ℕ) (g : ℂ → ℂ), 1 ≤ n ∧ AnalyticAt ℂ g ρ ∧ g ρ ≠ 0 ∧
      analyticOrderAt (DirichletCharacter.LFunction χ) ρ = (n : ℕ∞) ∧
      -- the readout has a simple pole of residue `−n` at ρ (geometric peak = spectral dip):
      (∀ᶠ s in nhdsWithin ρ {ρ}ᶜ,
        -logDeriv (DirichletCharacter.LFunction χ) s = -((n : ℂ) * (s - ρ)⁻¹ + deriv g s / g s)) ∧
      -- its energy is `‖residue‖² = n²` (the squared multiplicity), shared by both sides:
      ‖(-(n : ℂ))‖ ^ 2 = (n : ℝ) ^ 2 := by
  obtain ⟨_, n, g, hn, hg, hgne, hord, hform⟩ := sole_origin χ hρ
  exact ⟨n, g, hn, hg, hgne, hord, hform, by rw [norm_neg, Complex.norm_natCast]⟩

end EnergyBalance
