import Mathlib
import RequestProject.GRHSpectralCriterion

/-!
# The source: σ-free no-drift + the identification/completeness obligation

The honest, non-circular Hilbert–Pólya route (Sam's decomposition):

* **Source object** — the completed 3D helix's projection-loss field. A *source mode* `ψ` carries a
  complex flow-rate `λ` (the winding-transport exponent). Its loss-norm evolves as
  `‖U(τ)ψ‖ = e^{(Re λ)·τ}·‖ψ‖`. This object is defined with **no reference to zeros, `ρ`, or `σ`.**
* **σ-free no-drift** (`SourceMode.noDrift`): area/energy-preserving top-down transport conserves
  the loss-norm, `‖U(τ)ψ‖ = ‖ψ‖`, which forces `Re λ = 0`. Mentions no σ, ρ, or critical line.
* **Identification / completeness** (`SourceComplete`): every nontrivial zero of `L` is the
  pole-coordinate `½ + λ` of a *source mode* `ψ` (`λ = ψ.rate`). This bundles the trace identity
  `T_F(z) = −Λ_F'/Λ_F(½+iz)` and `pole_to_sourceMode`. It is the open analytic content.
* **GRH** (`grh_of_sourceComplete`): completeness + the source modes' no-drift ⟹ every zero on the
  line. Non-circular: `Re λ = 0` is the *source mode's*, supplied by `noDrift`, never assumed of `ρ`.
-/

namespace HelixSource

open Complex

variable {N : ℕ} [NeZero N]

/-- **σ-free no-drift.** If winding-transport conserves a mode's loss-norm
    (`e^{(Re λ)·τ}·c = c` for all `τ`, `c = ‖ψ‖ ≠ 0`), then its growth rate `Re λ = 0`.
    No `σ`, no `ρ`, no critical line — pure conservation of the source geometry. -/
theorem source_noDrift (lam : ℂ) (c : ℝ) (hc : c ≠ 0)
    (hconserv : ∀ τ : ℝ, Real.exp (lam.re * τ) * c = c) : lam.re = 0 := by
  have h1 : Real.exp lam.re * c = c := by simpa using hconserv 1
  have h2 : Real.exp lam.re = 1 := mul_right_cancel₀ hc (by rw [h1, one_mul])
  have := congrArg Real.log h2
  rwa [Real.log_exp, Real.log_one] at this

/-- A **source mode**: a mode of the conservative winding-transport flow with complex flow-rate
    `rate`. `conserved` records that the (area/energy-preserving) flow keeps its loss-norm — the
    σ-free source geometry. -/
structure SourceMode where
  rate : ℂ
  amp : ℝ
  amp_ne : amp ≠ 0
  conserved : ∀ τ : ℝ, Real.exp (rate.re * τ) * amp = amp

/-- Every source mode has **no radial drift**: `Re (rate) = 0` (from conservation, σ-free). -/
theorem SourceMode.noDrift (ψ : SourceMode) : ψ.rate.re = 0 :=
  source_noDrift ψ.rate ψ.amp ψ.amp_ne ψ.conserved

/-- The pole-coordinate of a source mode: `½ + rate`. By `noDrift` its real part is `½`. -/
noncomputable def SourceMode.poleCoord (ψ : SourceMode) : ℂ := 1 / 2 + ψ.rate

/-- A source mode's pole sits **on the critical line**: `Re (½ + rate) = ½`. -/
theorem SourceMode.poleCoord_re (ψ : SourceMode) : ψ.poleCoord.re = 1 / 2 := by
  rw [SourceMode.poleCoord, Complex.add_re, ψ.noDrift]
  norm_num

/-- **Earned mode from a real spectral value.** Any real `μ` yields a source mode with `rate := i·μ`;
    its `conserved` field holds because `Re (i·μ) = 0`, with **no** input about zeros, `ρ`, or `σ`.
    This is the non-circular direction: a real eigenvalue (e.g. of the self-adjoint `A_N`) produces an
    on-line mode, with pole-coordinate `½ + i·μ`. -/
noncomputable def SourceMode.ofReal (μ : ℝ) : SourceMode where
  rate := Complex.I * μ
  amp := 1
  amp_ne := one_ne_zero
  conserved := by
    intro τ
    have hre : (Complex.I * (μ : ℂ)).re = 0 := by simp
    rw [hre]; simp

@[simp] theorem SourceMode.ofReal_rate (μ : ℝ) :
    (SourceMode.ofReal μ).rate = Complex.I * μ := rfl

theorem SourceMode.ofReal_poleCoord (μ : ℝ) :
    (SourceMode.ofReal μ).poleCoord = 1 / 2 + Complex.I * μ := rfl

/-- **Phase modulus = eigenvector energy** at a real-eigenvalue source mode. The unit-circle
    spectral phase `e^{i·μ·t}` has modulus exactly `1` for every time `t`, equal to the conserved
    eigenvector energy `amp² = 1` of `ofReal μ`. Both are `1`, and both hold because the rate
    `i·μ` is imaginary (`Re = 0`): a real eigenvalue gives a unit-circle phase *and* a conserved
    unit energy — the same σ-free reality, read once on the phase and once on the energy. -/
theorem SourceMode.phaseModulus_eq_eigenvectorEnergy (μ t : ℝ) :
    ‖Complex.exp (Complex.I * (μ : ℂ) * (t : ℂ))‖ = (SourceMode.ofReal μ).amp ^ 2 := by
  have hre : (Complex.I * (μ : ℂ) * (t : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [Complex.norm_exp, hre, Real.exp_zero]
  simp [SourceMode.ofReal]

/-- **The identification / completeness obligation** (the open analytic content): every nontrivial
    zero of `L` is the pole-coordinate of some source mode. Bundles `sourceTrace_identity`
    (`T_F = Λ_F'/Λ_F(½+iz)`) and `pole_to_sourceMode`. NOT circular: it asserts that `ρ` is
    *captured by a source mode*, whose `Re (rate) = 0` is established independently by `noDrift`. -/
def SourceComplete (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ ρ ∈ GRHSpectral.NontrivialZeros χ, ∃ ψ : SourceMode, ρ = ψ.poleCoord

/-- **GRH from the source.** If every nontrivial zero is captured by a source mode, then — since
    every source mode has no radial drift (`noDrift`, σ-free) — every zero lies on the critical
    line. The forcing is the source geometry's conservation; the open input is the completeness. -/
theorem grh_of_sourceComplete (χ : DirichletCharacter ℂ N) (h : SourceComplete χ) :
    GRHSpectral.GRH χ := by
  intro ρ hρ
  obtain ⟨ψ, hρeq⟩ := h ρ hρ
  rw [hρeq, ψ.poleCoord_re]

-- (Commented out at request.) Backward direction `GRH χ → SourceComplete χ` — the trivial
-- necessity: each on-line zero ρ yields a source mode `rate := ρ − ½` (`Re = 0` since `Re ρ = ½`).
-- Not used in the forward attack (`grh_of_sourceComplete` is the σ-free reduction); it stays a
-- 5-line fact, re-derivable on demand.
-- /-- Reverse of `grh_of_sourceComplete`: if every nontrivial zero is on the line, each is captured by
--     the source mode with `rate := ρ − ½`, whose `conserved` field holds because `Re ρ = ½` gives
--     `Re (rate) = 0`. -/
-- theorem sourceComplete_of_grh (χ : DirichletCharacter ℂ N) (h : GRHSpectral.GRH χ) :
--     SourceComplete χ := by
--   intro ρ hρ
--   have hre : (ρ - 1 / 2 : ℂ).re = 0 := by
--     rw [Complex.sub_re, h ρ hρ]; norm_num
--   refine ⟨{ rate := ρ - 1 / 2, amp := 1, amp_ne := one_ne_zero, conserved := ?_ }, ?_⟩
--   · intro τ; rw [hre]; simp
--   · show ρ = 1 / 2 + (ρ - 1 / 2); ring

-- (Commented out at request.) The packaged equivalence `SourceComplete χ ↔ GRH χ`.
-- Note: both directions remain available individually — `grh_of_sourceComplete` (forward, the
-- substantive σ-free reduction) and `sourceComplete_of_grh` (backward, the one-line `rate := ρ−½`
-- construction). The equivalence is therefore still a fact even with this named theorem removed.
-- /-- `SourceComplete χ ↔ GRH χ`. Forward: the σ-free source forcing (`grh_of_sourceComplete`).
--     Backward: build the capturing modes from the on-line locations (`sourceComplete_of_grh`). -/
-- theorem sourceComplete_iff_grh (χ : DirichletCharacter ℂ N) :
--     SourceComplete χ ↔ GRHSpectral.GRH χ :=
--   ⟨grh_of_sourceComplete χ, sourceComplete_of_grh χ⟩

/-! ## The regularized source trace and the trace-identity target (DEPRECATED PATH)

This resolvent / partial-fraction source-trace route (`sourceTrace = L′/L` over the on-line
source-mode pole-coords) is **deprecated** — retained for reference, no longer the active
approach.  It is still honest and GRH-equivalent, and `→ GRH` is fully wired
(`grh_of_traceIdentity`).  The active route is the spectral / characteristic-determinant
(Frobenius-eigenphase) trace identity, which realizes the nontrivial zeros as the spectrum of
the spin/Frobenius operator (`det(1 − T·Frob)`) rather than as poles of this partial fraction. -/

/-- **The regularized source trace** of a source-mode family — the Hadamard-regularized resolvent
    sum `T_F(s) = ∑ₙ [1/(s − poleCoordₙ) + 1/poleCoordₙ]`. The counterterms `1/poleCoordₙ` make the
    series converge (each term `~ 1/|poleCoordₙ|²`), matching the convergent partial-fraction form
    of `L'/L`; the poles are still exactly the (on-line) source-mode pole-coords. -/
noncomputable def sourceTrace (modes : ℕ → SourceMode) (s : ℂ) : ℂ :=
  ∑' n, ((s - (modes n).poleCoord)⁻¹ + (modes n).poleCoord⁻¹)

/-- **DEPRECATED PATH** (superseded by the spectral / characteristic-determinant Frobenius route).
    The resolvent / partial-fraction source-trace identity: the source trace equals the
    log-derivative `L'/L` of the channel `χ` (so `−sourceTrace` is the von Mangoldt prime field
    `−L'/L`), with the on-line source-mode pole-coords as its poles. Still honest and
    GRH-equivalent — `SourceTraceIdentity ⟺ {nontrivial zeros} = {on-line pole-coords}` — and
    `→ GRH` is wired (`grh_of_traceIdentity`, via pole-matching + `SourceComplete`). But it is **no
    longer the active route**: the current approach realizes the zeros as the *spectrum* of the
    spin/Frobenius operator (characteristic determinant `det(1 − T·Frob)`), not as poles of this
    partial fraction. Retained for reference. σ-free: mentions no `σ`, `ρ`, or critical line.

    Sign: each pole-coord `cₙ` gives `sourceTrace` residue `+1`, matching the residue `+n` of `L'/L`
    at a zero of multiplicity `n` (`LFunction_logDeriv_residue_eq_order`). -/
def SourceTraceIdentity (modes : ℕ → SourceMode) (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ s : ℂ, sourceTrace modes s = logDeriv (DirichletCharacter.LFunction χ) s

/-- **Capture ⟹ completeness.** If every nontrivial zero equals some source-mode pole-coord, then
    `SourceComplete` holds. The capture (`pole_to_sourceMode`) is what the trace identity plus
    pole-matching of `T_F = L'/L` supplies — both poles must coincide, and the source poles are
    on the line. -/
theorem sourceComplete_of_poleCapture (modes : ℕ → SourceMode) (χ : DirichletCharacter ℂ N)
    (hcap : ∀ ρ ∈ GRHSpectral.NontrivialZeros χ, ∃ n, ρ = (modes n).poleCoord) :
    SourceComplete χ := fun ρ hρ => let ⟨n, hn⟩ := hcap ρ hρ; ⟨modes n, hn⟩

/-- **GRH from the trace-identity route**, assembled: a source-mode family whose pole-coords capture
    every nontrivial zero ⟹ GRH. The capture is exactly what `SourceTraceIdentity` + pole-matching
    delivers; the on-line forcing is `SourceMode.noDrift` (σ-free). -/
theorem grh_of_poleCapture (modes : ℕ → SourceMode) (χ : DirichletCharacter ℂ N)
    (hcap : ∀ ρ ∈ GRHSpectral.NontrivialZeros χ, ∃ n, ρ = (modes n).poleCoord) :
    GRHSpectral.GRH χ :=
  grh_of_sourceComplete χ (sourceComplete_of_poleCapture modes χ hcap)

open Filter Topology in
/-- **Pole-matching ⟹ capture.** Given the trace identity `T_F = L'/L`, plus the two analytic
    facts — `−L'/L` is **singular** at every nontrivial zero (`hLsing`) and `T_F` is **regular**
    off its pole-coords (`hTreg`) — every zero must coincide with a source-mode pole-coord. These
    two facts are the meromorphic content of `pole_to_sourceMode`; isolating them verifies the
    logical bridge from the identity to the capture (and neither mentions `σ`). -/
theorem poleCapture_of_traceIdentity (modes : ℕ → SourceMode) (χ : DirichletCharacter ℂ N)
    (hid : SourceTraceIdentity modes χ)
    (hTreg : ∀ ρ ∈ GRHSpectral.NontrivialZeros χ, (∀ n, ρ ≠ (modes n).poleCoord) →
        ∃ L, Tendsto (sourceTrace modes) (𝓝[≠] ρ) (𝓝 L))
    (hLsing : ∀ ρ ∈ GRHSpectral.NontrivialZeros χ,
        ¬ ∃ L, Tendsto (fun s => logDeriv (DirichletCharacter.LFunction χ) s) (𝓝[≠] ρ) (𝓝 L)) :
    ∀ ρ ∈ GRHSpectral.NontrivialZeros χ, ∃ n, ρ = (modes n).poleCoord := by
  intro ρ hρ
  by_contra h
  push_neg at h
  obtain ⟨L, hL⟩ := hTreg ρ hρ h
  refine hLsing ρ hρ ⟨L, ?_⟩
  have heq : (fun s => logDeriv (DirichletCharacter.LFunction χ) s) = sourceTrace modes := by
    funext s; exact (hid s).symm
  rw [heq]; exact hL

open Filter Topology in
/-- **GRH from the trace identity**, fully assembled: the identity `T_F = L'/L`, the singularity of
    `−L'/L` at the zeros, and the regularity of `T_F` off its (on-line) pole-coords ⟹ GRH. The
    on-line forcing is `SourceMode.noDrift` (σ-free); the three hypotheses are the analytic content
    (`sourceTrace_identity` + the pole structure). -/
theorem grh_of_traceIdentity (modes : ℕ → SourceMode) (χ : DirichletCharacter ℂ N)
    (hid : SourceTraceIdentity modes χ)
    (hTreg : ∀ ρ ∈ GRHSpectral.NontrivialZeros χ, (∀ n, ρ ≠ (modes n).poleCoord) →
        ∃ L, Tendsto (sourceTrace modes) (𝓝[≠] ρ) (𝓝 L))
    (hLsing : ∀ ρ ∈ GRHSpectral.NontrivialZeros χ,
        ¬ ∃ L, Tendsto (fun s => logDeriv (DirichletCharacter.LFunction χ) s) (𝓝[≠] ρ) (𝓝 L)) :
    GRHSpectral.GRH χ :=
  grh_of_poleCapture modes χ (poleCapture_of_traceIdentity modes χ hid hTreg hLsing)

/-! ## Discharging `hLsing`: `−L'/L` is singular at every zero

The logarithmic derivative of an analytic function has a simple pole (`meromorphicOrderAt = -1`) at
an isolated zero, hence tends to `cobounded` and has no finite limit. Applied to the `L`-function,
this discharges `hLsing` for every nontrivial zero. All of this is σ-free. -/

open Filter Topology

/-- **`logDeriv f` has a *simple* pole at an isolated zero — exact order `−1`.** If `f` is analytic
    at `ρ`, vanishes there, and is not locally zero, then `meromorphicOrderAt (logDeriv f) ρ = −1`,
    *regardless* of the zero's multiplicity `m`: `logDeriv f = f'/f` and `f ~ c(z−ρ)^m` give
    `f'/f ~ m/(z−ρ)`, a simple pole. The multiplicity `m` is the *residue* (`logDeriv_pole_of_order`),
    not the pole order. So the counting function `−L'/L` charges each zero **location** once (order 1)
    and carries its multiplicity in the residue. -/
theorem meromorphicOrderAt_logDeriv_eq_neg_one {f : ℂ → ℂ} {ρ : ℂ}
    (hf : AnalyticAt ℂ f ρ) (hfρ : f ρ = 0) (hne : ¬ f =ᶠ[𝓝 ρ] 0) :
    meromorphicOrderAt (logDeriv f) ρ = -1 := by
  have hdf : AnalyticAt ℂ (deriv f) ρ := hf.deriv
  have htop : analyticOrderAt f ρ ≠ ⊤ := fun h => hne (analyticOrderAt_eq_top.mp h)
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp htop
  have hderiv : analyticOrderAt (deriv f) ρ + 1 = analyticOrderAt f ρ := by
    have h := hf.analyticOrderAt_deriv_add_one
    rwa [show (fun x => f x - f ρ) = f by funext x; rw [hfρ, sub_zero]] at h
  obtain ⟨k, hk⟩ : ∃ k : ℕ, analyticOrderAt (deriv f) ρ = (k : ℕ∞) := by
    rcases eq_or_ne (analyticOrderAt (deriv f) ρ) ⊤ with h | h
    · rw [h, top_add] at hderiv; exact absurd hderiv.symm htop
    · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp h
      exact ⟨k, hk.symm⟩
  have hkm : k + 1 = m := by
    have hc : (k : ℕ∞) + 1 = (m : ℕ∞) := by rw [← hk, hderiv, ← hm]
    exact_mod_cast hc
  have e1 : meromorphicOrderAt f ρ = (m : ℤ) := by
    rw [hf.meromorphicOrderAt_eq, ← hm]; simp
  have e2 : meromorphicOrderAt (deriv f) ρ = (k : ℤ) := by
    rw [hdf.meromorphicOrderAt_eq, hk]; simp
  have hlog : logDeriv f = (deriv f) / f := by funext x; exact logDeriv_apply f x
  rw [hlog, meromorphicOrderAt_div hdf.meromorphicAt hf.meromorphicAt, e1, e2]
  have heq : (k : ℤ) - (m : ℤ) = -1 := by omega
  rw [show (-1 : WithTop ℤ) = ((-1 : ℤ) : WithTop ℤ) from by norm_cast]
  exact_mod_cast heq

/-- **`logDeriv f` has a simple pole at an isolated zero**: if `f` is analytic at `ρ`, vanishes
    there, and is not locally zero, then `meromorphicOrderAt (logDeriv f) ρ < 0`. -/
theorem meromorphicOrderAt_logDeriv_neg {f : ℂ → ℂ} {ρ : ℂ}
    (hf : AnalyticAt ℂ f ρ) (hfρ : f ρ = 0) (hne : ¬ f =ᶠ[𝓝 ρ] 0) :
    meromorphicOrderAt (logDeriv f) ρ < 0 := by
  have hdf : AnalyticAt ℂ (deriv f) ρ := hf.deriv
  have htop : analyticOrderAt f ρ ≠ ⊤ := fun h => hne (analyticOrderAt_eq_top.mp h)
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp htop          -- hm : ↑m = analyticOrderAt f ρ
  have hderiv : analyticOrderAt (deriv f) ρ + 1 = analyticOrderAt f ρ := by
    have h := hf.analyticOrderAt_deriv_add_one
    rwa [show (fun x => f x - f ρ) = f by funext x; rw [hfρ, sub_zero]] at h
  obtain ⟨k, hk⟩ : ∃ k : ℕ, analyticOrderAt (deriv f) ρ = (k : ℕ∞) := by
    rcases eq_or_ne (analyticOrderAt (deriv f) ρ) ⊤ with h | h
    · rw [h, top_add] at hderiv; exact absurd hderiv.symm htop
    · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp h
      exact ⟨k, hk.symm⟩
  have hkm : k + 1 = m := by
    have hc : (k : ℕ∞) + 1 = (m : ℕ∞) := by rw [← hk, hderiv, ← hm]
    exact_mod_cast hc
  have e1 : meromorphicOrderAt f ρ = (m : ℤ) := by
    rw [hf.meromorphicOrderAt_eq, ← hm]; simp
  have e2 : meromorphicOrderAt (deriv f) ρ = (k : ℤ) := by
    rw [hdf.meromorphicOrderAt_eq, hk]; simp
  have hlog : logDeriv f = (deriv f) / f := by funext x; exact logDeriv_apply f x
  rw [hlog, meromorphicOrderAt_div hdf.meromorphicAt hf.meromorphicAt, e1, e2]
  have hlt : (k : ℤ) - (m : ℤ) < 0 := by omega
  exact_mod_cast hlt

/-- **`−logDeriv f` has no finite limit at an isolated zero.** Since `logDeriv f` has a pole there
    it tends to `cobounded`, which is disjoint from every neighbourhood filter. -/
theorem logDeriv_not_tendsto {f : ℂ → ℂ} {ρ : ℂ}
    (hf : AnalyticAt ℂ f ρ) (hfρ : f ρ = 0) (hne : ¬ f =ᶠ[𝓝 ρ] 0) :
    ¬ ∃ L, Tendsto (fun s => -logDeriv f s) (𝓝[≠] ρ) (𝓝 L) := by
  rintro ⟨L, hL⟩
  have htend : Tendsto (logDeriv f) (𝓝[≠] ρ) (Bornology.cobounded ℂ) :=
    tendsto_cobounded_of_meromorphicOrderAt_neg (meromorphicOrderAt_logDeriv_neg hf hfρ hne)
  have hL' : Tendsto (logDeriv f) (𝓝[≠] ρ) (𝓝 (-L)) := by simpa using hL.neg
  exact htend.not_tendsto (Metric.disjoint_cobounded_nhds (-L)) hL'

/-- The `L`-function is analytic away from `s = 1`. -/
theorem LFunction_analyticOnNhd (χ : DirichletCharacter ℂ N) :
    AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) ({1}ᶜ) := by
  apply DifferentiableOn.analyticOnNhd ?_ isOpen_compl_singleton
  intro w hw
  exact (DirichletCharacter.differentiableAt_LFunction χ w
    (Or.inl (Set.mem_compl_singleton_iff.mp hw))).differentiableWithinAt

/-- **The `L`-function is not locally zero** at any `ρ ≠ 1`: identity theorem on the (preconnected)
    punctured plane `{1}ᶜ` together with non-vanishing at `s = 2`. -/
theorem LFunction_not_eventuallyEq_zero (χ : DirichletCharacter ℂ N) {ρ : ℂ} (hρ1 : ρ ≠ 1) :
    ¬ DirichletCharacter.LFunction χ =ᶠ[𝓝 ρ] 0 := by
  intro hev
  have hpre : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isPathConnected_compl_singleton_of_one_lt_rank
      (by rw [Complex.rank_real_complex]; exact_mod_cast Nat.one_lt_two) (1 : ℂ)).isConnected.isPreconnected
  have hEq := (LFunction_analyticOnNhd χ).eqOn_zero_of_preconnected_of_eventuallyEq_zero hpre
    (Set.mem_compl_singleton_iff.mpr hρ1) hev
  have h2 : DirichletCharacter.LFunction χ 2 = 0 := by
    simpa using hEq (Set.mem_compl_singleton_iff.mpr (by norm_num : (2 : ℂ) ≠ 1))
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (s := 2) (Or.inr (by norm_num))
    (by norm_num) h2

/-- **`hLsing` discharged for the `L`-function**: `−L'/L` has no finite limit at any nontrivial
    zero `ρ`. -/
theorem LFunction_logDeriv_not_tendsto (χ : DirichletCharacter ℂ N) {ρ : ℂ}
    (hρ : ρ ∈ GRHSpectral.NontrivialZeros χ) :
    ¬ ∃ L, Tendsto (fun s => -logDeriv (DirichletCharacter.LFunction χ) s) (𝓝[≠] ρ) (𝓝 L) := by
  obtain ⟨_, hre1, hzero⟩ := hρ
  have hρ1 : ρ ≠ 1 := by intro h; rw [h] at hre1; simp at hre1
  exact logDeriv_not_tendsto
    (LFunction_analyticOnNhd χ ρ (Set.mem_compl_singleton_iff.mpr hρ1)) hzero
    (LFunction_not_eventuallyEq_zero χ hρ1)

/-- **A nontrivial `L(·,χ)` zero has positive natural multiplicity.** Its `analyticOrderAt` is a
    finite (not locally zero) nonzero (it *is* a zero) natural number `n ≥ 1`. This is the order
    `n` that `logDeriv_pole_of_order` reads off as the **residue** of `L'/L` at `ρ` — the weight the
    counting function assigns to the zero. σ-free: no mention of `Re ρ`. -/
theorem analyticOrderAt_LFunction_eq_pos_nat (χ : DirichletCharacter ℂ N) {ρ : ℂ}
    (hρ : ρ ∈ GRHSpectral.NontrivialZeros χ) :
    ∃ n : ℕ, 1 ≤ n ∧ analyticOrderAt (DirichletCharacter.LFunction χ) ρ = (n : ℕ∞) := by
  obtain ⟨_, hre1, hzero⟩ := hρ
  have hρ1 : ρ ≠ 1 := by intro h; rw [h] at hre1; simp at hre1
  have hf : AnalyticAt ℂ (DirichletCharacter.LFunction χ) ρ :=
    LFunction_analyticOnNhd χ ρ (Set.mem_compl_singleton_iff.mpr hρ1)
  have htop : analyticOrderAt (DirichletCharacter.LFunction χ) ρ ≠ ⊤ :=
    fun h => LFunction_not_eventuallyEq_zero χ hρ1 (analyticOrderAt_eq_top.mp h)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
  refine ⟨n, ?_, hn.symm⟩
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · exact absurd hzero (hf.analyticOrderAt_eq_zero.mp (by rw [← hn, h0]; rfl))
  · exact hpos

/-- **GRH from the trace identity, with `hLsing` discharged.** Only the identity `T_F = L'/L` and
    the regularity of `T_F` off its (on-line) pole-coords remain as hypotheses — the singularity of
    `−L'/L` at the zeros is now a theorem. -/
theorem grh_of_traceIdentity' (modes : ℕ → SourceMode) (χ : DirichletCharacter ℂ N)
    (hid : SourceTraceIdentity modes χ)
    (hTreg : ∀ ρ ∈ GRHSpectral.NontrivialZeros χ, (∀ n, ρ ≠ (modes n).poleCoord) →
        ∃ L, Tendsto (sourceTrace modes) (𝓝[≠] ρ) (𝓝 L)) :
    GRHSpectral.GRH χ :=
  grh_of_traceIdentity modes χ hid hTreg
    (fun _ hρ => by rintro ⟨M, hM⟩; exact LFunction_logDeriv_not_tendsto χ hρ ⟨-M, hM.neg⟩)

/-- **`hTreg` reduces to continuity of the regularized trace.** If `T_F` is continuous at each zero
    off its pole-coords, the punctured limit exists. This is *not* GRH-hard: it is the regularity of
    the regularized resolvent trace `Tr_reg`, a structural property of the regularization (the sum
    `∑ 1/(s−poleCoordₙ)` converging locally uniformly off its poles), with no `σ`. -/
theorem hTreg_of_continuousAt (modes : ℕ → SourceMode) (χ : DirichletCharacter ℂ N)
    (hcont : ∀ ρ ∈ GRHSpectral.NontrivialZeros χ, (∀ n, ρ ≠ (modes n).poleCoord) →
        ContinuousAt (sourceTrace modes) ρ) :
    ∀ ρ ∈ GRHSpectral.NontrivialZeros χ, (∀ n, ρ ≠ (modes n).poleCoord) →
        ∃ L, Tendsto (sourceTrace modes) (𝓝[≠] ρ) (𝓝 L) := fun ρ hρ hne =>
  ⟨sourceTrace modes ρ, (hcont ρ hρ hne).tendsto.mono_left nhdsWithin_le_nhds⟩

/-- **GRH from the trace identity — both glue lemmas discharged.** The only remaining inputs are the
    frontier identity `T_F = L'/L` (`SourceTraceIdentity`) and continuity of the regularized trace
    off its (on-line) pole-coords. The singularity of `−L'/L` at the zeros (`hLsing`) is now a
    theorem; the on-line forcing is `SourceMode.noDrift` (σ-free). -/
theorem grh_of_traceIdentity'' (modes : ℕ → SourceMode) (χ : DirichletCharacter ℂ N)
    (hid : SourceTraceIdentity modes χ)
    (hcont : ∀ ρ ∈ GRHSpectral.NontrivialZeros χ, (∀ n, ρ ≠ (modes n).poleCoord) →
        ContinuousAt (sourceTrace modes) ρ) :
    GRHSpectral.GRH χ :=
  grh_of_traceIdentity' modes χ hid (hTreg_of_continuousAt modes χ hcont)

/-! ## Discharging the regularization: the Weierstrass M-test

The regularity of `T_F` off its poles (`hcont`) is the analytic content of the regularization. It
follows from a **Weierstrass M-test**: a neighbourhood of `ρ` on which each resolvent summand is
continuous and dominated by a summable bound. This is `continuousOn_tsum` from mathlib, applied to
the Hadamard-regularized summands `s ↦ 1/(s−cₙ) + 1/cₙ` (whose tail bound is `~ 1/|cₙ|²`). All σ-free.
-/

/-- The summands `g` have a **local Weierstrass M-test** at `ρ`: a neighbourhood `s ∈ 𝓝 ρ` on which
    each `g n` is continuous and dominated by a summable sequence `u`. This is the σ-free,
    standard regularization condition (no `σ`, `ρ`-location, or critical line). -/
def HasLocalMtest (g : ℕ → ℂ → ℂ) (ρ : ℂ) : Prop :=
  ∃ s ∈ 𝓝 ρ, (∀ n, ContinuousOn (g n) s) ∧
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n, ∀ x ∈ s, ‖g n x‖ ≤ u n

/-- **M-test ⟹ continuity at a point.** A locally uniformly-summable series of locally-continuous
    summands is continuous at `ρ` (`continuousOn_tsum` + `ContinuousOn.continuousAt`). -/
theorem continuousAt_tsum_of_localMtest {g : ℕ → ℂ → ℂ} {ρ : ℂ} (h : HasLocalMtest g ρ) :
    ContinuousAt (fun z => ∑' n, g n z) ρ := by
  obtain ⟨s, hs, hg, u, hu, hb⟩ := h
  exact (continuousOn_tsum hg hu hb).continuousAt hs

/-- **The regularized trace is continuous off its poles** wherever the resolvent series satisfies a
    local M-test. -/
theorem continuousAt_sourceTrace_of_localMtest (modes : ℕ → SourceMode) {ρ : ℂ}
    (h : HasLocalMtest (fun n s => (s - (modes n).poleCoord)⁻¹ + (modes n).poleCoord⁻¹) ρ) :
    ContinuousAt (sourceTrace modes) ρ :=
  continuousAt_tsum_of_localMtest h

/-- **GRH from the trace identity + the regularization M-test.** The regularization obligation is now
    fully concrete and standard: at each nontrivial zero off the source poles, the Hadamard-regularized
    resolvent series satisfies a Weierstrass M-test. Combined with the frontier identity `T_F = L'/L`
    this gives GRH. (`hLsing` is a theorem; the on-line forcing is `SourceMode.noDrift`, σ-free.) -/
theorem grh_of_traceIdentity_mtest (modes : ℕ → SourceMode) (χ : DirichletCharacter ℂ N)
    (hid : SourceTraceIdentity modes χ)
    (hmtest : ∀ ρ ∈ GRHSpectral.NontrivialZeros χ, (∀ n, ρ ≠ (modes n).poleCoord) →
        HasLocalMtest (fun n s => (s - (modes n).poleCoord)⁻¹ + (modes n).poleCoord⁻¹) ρ) :
    GRHSpectral.GRH χ :=
  grh_of_traceIdentity'' modes χ hid
    (fun ρ hρ hne => continuousAt_sourceTrace_of_localMtest modes (hmtest ρ hρ hne))

open Filter in
/-- **The regularization M-test holds** under the standard analytic inputs (all σ-free): `ρ` is
    separated from every pole, the poles escape to infinity, and the resolvent is trace-class
    (`∑ 1/‖cₙ‖² < ∞`). Proof: on `ball ρ (δ/2)` the Hadamard summand is `‖s‖/(‖s−cₙ‖‖cₙ‖)`, bounded
    by `R/((δ/2)‖cₙ‖)` for the finitely many small poles and by `2R/‖cₙ‖²` for the (summable) tail. -/
theorem hasLocalMtest_resolvent (modes : ℕ → SourceMode) {ρ : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ n, δ ≤ ‖ρ - (modes n).poleCoord‖)
    (htends : Tendsto (fun n => ‖(modes n).poleCoord‖) atTop atTop)
    (hsum : Summable (fun n => ‖(modes n).poleCoord‖⁻¹ ^ 2)) :
    HasLocalMtest (fun n s => (s - (modes n).poleCoord)⁻¹ + (modes n).poleCoord⁻¹) ρ := by
  set R := ‖ρ‖ + δ with hRdef
  have hRpos : 0 < R := by have := norm_nonneg ρ; rw [hRdef]; linarith
  have hcne : ∀ n, (modes n).poleCoord ≠ 0 := by
    intro n h
    have h2 := (modes n).poleCoord_re
    rw [h, Complex.zero_re] at h2
    norm_num at h2
  have hcpos : ∀ n, 0 < ‖(modes n).poleCoord‖ := fun n => norm_pos_iff.mpr (hcne n)
  have hdist : ∀ n, ∀ x ∈ Metric.ball ρ (δ / 2), δ / 2 ≤ ‖x - (modes n).poleCoord‖ := by
    intro n x hx
    rw [Metric.mem_ball, Complex.dist_eq] at hx
    have h2 : ‖ρ - (modes n).poleCoord‖ ≤ ‖x - ρ‖ + ‖x - (modes n).poleCoord‖ := by
      calc ‖ρ - (modes n).poleCoord‖
          = ‖(ρ - x) + (x - (modes n).poleCoord)‖ := by congr 1; ring
        _ ≤ ‖ρ - x‖ + ‖x - (modes n).poleCoord‖ := norm_add_le _ _
        _ = ‖x - ρ‖ + ‖x - (modes n).poleCoord‖ := by rw [norm_sub_rev]
    have := hsep n
    linarith
  have hxR : ∀ x ∈ Metric.ball ρ (δ / 2), ‖x‖ ≤ R := by
    intro x hx
    rw [Metric.mem_ball, Complex.dist_eq] at hx
    calc ‖x‖ = ‖(x - ρ) + ρ‖ := by congr 1; ring
      _ ≤ ‖x - ρ‖ + ‖ρ‖ := norm_add_le _ _
      _ ≤ R := by rw [hRdef]; linarith
  have hdist2 : ∀ n, ∀ x ∈ Metric.ball ρ (δ / 2),
      ‖(modes n).poleCoord‖ - R ≤ ‖x - (modes n).poleCoord‖ := by
    intro n x hx
    have h1 := norm_sub_norm_le (modes n).poleCoord x
    rw [norm_sub_rev] at h1
    have := hxR x hx
    linarith
  have hfin : {n | ‖(modes n).poleCoord‖ ≤ 2 * R}.Finite := by
    have hev : ∀ᶠ n in atTop, 2 * R < ‖(modes n).poleCoord‖ := htends.eventually_gt_atTop (2 * R)
    rw [← Nat.cofinite_eq_atTop, Filter.eventually_cofinite] at hev
    exact hev.subset (fun n hn => not_lt.mpr hn)
  refine ⟨Metric.ball ρ (δ / 2), Metric.ball_mem_nhds ρ (by linarith), ?_, ?_⟩
  · intro n
    have hne : ∀ x ∈ Metric.ball ρ (δ / 2), x - (modes n).poleCoord ≠ 0 := by
      intro x hx h
      have := hdist n x hx
      rw [h, norm_zero] at this
      linarith
    exact ((continuousOn_id.sub continuousOn_const).inv₀ hne).add continuousOn_const
  · refine ⟨fun n => (if ‖(modes n).poleCoord‖ ≤ 2 * R then R / ((δ / 2) * ‖(modes n).poleCoord‖)
        else 0) + 2 * R * ‖(modes n).poleCoord‖⁻¹ ^ 2, ?_, ?_⟩
    · apply Summable.add _ (hsum.mul_left (2 * R))
      apply summable_of_ne_finset_zero (s := hfin.toFinset)
      intro b hb
      rw [Set.Finite.mem_toFinset] at hb
      simp only [Set.mem_setOf_eq] at hb
      rw [if_neg hb]
    · intro n x hx
      dsimp only
      have hcn : (modes n).poleCoord ≠ 0 := hcne n
      have hcp : 0 < ‖(modes n).poleCoord‖ := hcpos n
      have hd1 := hdist n x hx
      have hxRx := hxR x hx
      have hxcp : 0 < ‖x - (modes n).poleCoord‖ := by linarith
      have hxc : x - (modes n).poleCoord ≠ 0 := norm_pos_iff.mp hxcp
      have hid : (x - (modes n).poleCoord)⁻¹ + (modes n).poleCoord⁻¹
               = x / ((x - (modes n).poleCoord) * (modes n).poleCoord) := by field_simp; ring
      rw [hid, norm_div, norm_mul]
      by_cases hcond : ‖(modes n).poleCoord‖ ≤ 2 * R
      · rw [if_pos hcond]
        have key : ‖x‖ * (δ / 2) ≤ R * ‖x - (modes n).poleCoord‖ :=
          mul_le_mul hxRx hd1 (by linarith) hRpos.le
        have hbound : ‖x‖ / (‖x - (modes n).poleCoord‖ * ‖(modes n).poleCoord‖)
                    ≤ R / ((δ / 2) * ‖(modes n).poleCoord‖) := by
          rw [div_le_div_iff₀ (mul_pos hxcp hcp) (mul_pos (by linarith) hcp)]
          nlinarith [key, hcp.le]
        have hnn : (0:ℝ) ≤ 2 * R * ‖(modes n).poleCoord‖⁻¹ ^ 2 := by positivity
        linarith
      · rw [if_neg hcond]
        push_neg at hcond
        have hd2 := hdist2 n x hx
        have hxc2 : ‖(modes n).poleCoord‖ / 2 ≤ ‖x - (modes n).poleCoord‖ := by linarith
        have key : ‖x‖ * (‖(modes n).poleCoord‖ / 2) ≤ R * ‖x - (modes n).poleCoord‖ :=
          mul_le_mul hxRx hxc2 (by positivity) hRpos.le
        have hbound : ‖x‖ / (‖x - (modes n).poleCoord‖ * ‖(modes n).poleCoord‖)
                    ≤ R / ((‖(modes n).poleCoord‖ / 2) * ‖(modes n).poleCoord‖) := by
          rw [div_le_div_iff₀ (mul_pos hxcp hcp) (mul_pos (by linarith) hcp)]
          nlinarith [key, hcp.le]
        have heq : R / ((‖(modes n).poleCoord‖ / 2) * ‖(modes n).poleCoord‖)
                 = 2 * R * ‖(modes n).poleCoord‖⁻¹ ^ 2 := by field_simp
        rw [heq] at hbound
        linarith

/-- **GRH from the trace identity + standard regularization inputs.** Fully grounds the
    regularization in pole-separation, escape-to-infinity, and trace-class summability — all σ-free
    — leaving only the frontier identity `T_F = L'/L`. -/
theorem grh_of_traceIdentity_separated (modes : ℕ → SourceMode) (χ : DirichletCharacter ℂ N)
    (hid : SourceTraceIdentity modes χ)
    (hreg : ∀ ρ ∈ GRHSpectral.NontrivialZeros χ, (∀ n, ρ ≠ (modes n).poleCoord) →
        ∃ δ > 0, (∀ n, δ ≤ ‖ρ - (modes n).poleCoord‖) ∧
          Filter.Tendsto (fun n => ‖(modes n).poleCoord‖) Filter.atTop Filter.atTop ∧
          Summable (fun n => ‖(modes n).poleCoord‖⁻¹ ^ 2)) :
    GRHSpectral.GRH χ :=
  grh_of_traceIdentity_mtest modes χ hid fun ρ hρ hne =>
    let ⟨δ, hδ, hsep, htends, hsum⟩ := hreg ρ hρ hne
    hasLocalMtest_resolvent modes hδ hsep htends hsum

/-! ## The Euler-product (prime-side) ingredient — and the honest wall

`SourceTraceIdentity` asserts the **zero-side** (Hadamard) expansion `∑ₙ[1/(s−cₙ)+1/cₙ] = L'/L`,
where the `cₙ` are the source-mode pole-coords (all on the line by `SourceMode.noDrift`). By
`grh_of_traceIdentity_separated`, that identity *implies GRH* — so it cannot be proven without proving
GRH. What Euler product + completion genuinely give is the **prime-side** identity below: `−L'/L`
equals the von Mangoldt Dirichlet series `∑ χ(n)Λ(n)n^{-s}` (the helix's prime field). The bridge from
this prime side to the zero side is the explicit/trace formula (classical, hard — only the local
`MeromorphicOn.extract_zeros_poles_log` is in mathlib), and forcing the resulting zero-modes on-line
is exactly GRH. So the "projection-loss geometry / identification" step is the GRH content itself. -/

open ArithmeticFunction in
/-- **Euler-product prime-side form of `−L'/L`** (`Re s > 1`): the log-derivative equals the von
    Mangoldt Dirichlet series `∑ χ(n)Λ(n) n^{-s}`. This is the genuine, classical content of "Euler
    product + completion": the helix's prime field reproduces `−L'/L` on the prime side. -/
theorem neg_logDeriv_LFunction_eq_vonMangoldt (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    -logDeriv (DirichletCharacter.LFunction χ) s
      = LSeries ((fun n : ℕ => χ ↑n) * fun n => (vonMangoldt n : ℂ)) s := by
  rw [logDeriv_apply, DirichletCharacter.LFunction_eq_LSeries χ hs,
    DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
    DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs]
  ring

/-- **A Hadamard factorization datum**: an enumeration `Z` of the **actual** nontrivial zeros with
    the zero-side identity `L'/L(s) = ∑ₙ [1/(s−Zₙ) + 1/Zₙ]` (residue `+1` per `Zₙ`, matching `L'/L`).
    The `Zₙ` carry their genuine real parts — **nothing forces them on-line.** (Classical; not in
    mathlib for Dirichlet `L`.) -/
def HadamardData (χ : DirichletCharacter ℂ N) (Z : ℕ → ℂ) : Prop :=
  ∀ s, logDeriv (DirichletCharacter.LFunction χ) s = ∑' n, ((s - Z n)⁻¹ + (Z n)⁻¹)

open ArithmeticFunction in
/-- **The explicit formula** (prime side = zero side), σ-free, from Euler product + Hadamard: for
    `Re s > 1` the von Mangoldt prime series `−L'/L` equals minus the Hadamard sum over the **actual**
    zeros. This is the genuine, GRH-free content Hadamard buys. -/
theorem explicitFormula (χ : DirichletCharacter ℂ N) (Z : ℕ → ℂ) (h : HadamardData χ Z)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries ((fun n : ℕ => χ ↑n) * fun n => (vonMangoldt n : ℂ)) s
      = -∑' n, ((s - Z n)⁻¹ + (Z n)⁻¹) := by
  rw [← neg_logDeriv_LFunction_eq_vonMangoldt χ hs, h s]

/-- **The whole gap, exactly.** `SourceTraceIdentity` is *precisely* a Hadamard factorization over the
    source-mode pole-coords — which are on the line by `SourceMode.noDrift`. So proving it is proving
    Hadamard holds with the zeros being those on-line coords, i.e. the **actual** zeros are on-line:
    GRH. Hadamard over the actual zeros (`HadamardData`) does not supply this — the actual `Zₙ` need
    not be source-mode coords. -/
theorem sourceTraceIdentity_iff_hadamard (modes : ℕ → SourceMode) (χ : DirichletCharacter ℂ N) :
    SourceTraceIdentity modes χ ↔ HadamardData χ (fun n => (modes n).poleCoord) := by
  constructor
  · intro h s; exact (h s).symm
  · intro h s; exact (h s).symm

end HelixSource
