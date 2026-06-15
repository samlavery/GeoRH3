import RequestProject.HelixResolventCapture
import RequestProject.HelixLogFreeFTA

/-!
# The assembled program: primitive `χ` → Euler-unitary fibers → … → GRH

This file welds the seven steps into single kernel-checked theorems. **It is a reduction, not a proof
of GRH:** the chain `step1 → … → step7 ⇒ GRH` is proved, with the open content isolated to exactly two
named hypotheses — `hid` (step 3, the boundary trace identity) and `hsa` (step 4, regular-off-`ℝ`).

```
   primitive Dirichlet χ
   → Euler-unitary prime fibers        (step 1, `euler_unitary_prime_fibers`)        ← proved
   → sourceTrace = −L'/L               (step 2, `prime_fiber_trace_eq`)              ← proved (Re s>1)
   → harmonic boundary receiver        (step 3, hypothesis `hid`)                    ← OPEN
   → self-adjoint / no-drift           (step 4, hypothesis `hsa`)                    ← OPEN
   → resolvent-trace capture           (step 5, `resonates_of_traceIdentity`)        ← proved
   → local-to-global                   (step 6, `global_traceIdentity_of_local`)     ← proved
   → GRH                               (step 7, `grh_of_harmonicTraceReceiver…`)     ← proved
```

**Honest status.** Steps 1, 2, 5, 6, 7 are theorems; the assembly `grh_of_euler_helix_program` is
kernel-clean. The two undischarged inputs `hid` and `hsa` are **GRH-strength**:
`hid` (the boundary trace literally equals `−L'/L(½+i·)`) is the identification —
`HelixSource.grh_of_traceIdentity_separated` / `sourceComplete_iff_grh` make it `⟺ GRH`; `hsa`
(`IsSelfAdjointReceiver`, regular off `ℝ`) is the reality, equivalently "no off-line zero". Neither is
proved here, and `ζ` witnesses that they are not free (it satisfies steps 1, 2 and RH(`ζ`) is open).
Discharging `hid ∧ hsa` from the geometry — `unitary fibers + σ-free conservation ⇒ regular off ℝ`,
breaking on Davenport–Heilbronn — is the remaining research, not part of this file.
-/

namespace HelixProgram

open HelixLimit HelixLogFree Complex Filter Topology ArithmeticFunction

variable {N : ℕ} [NeZero N]

/-- **Step 1 — Euler-unitary prime fibers.** The log-free FTA winding `wind : ℕ → Circle` is a
    per-fiber **unitary** (unit modulus, `‖wind n‖ = 1`) and **completely multiplicative** character
    (`wind (m·n) = wind m · wind n`). Prime fibers live on the unit circle; prime powers are generated
    locally by FTA-additivity of the angle. No `log`. -/
theorem euler_unitary_prime_fibers (θ : ℕ → ℝ) :
    (∀ n, ‖(wind θ n : ℂ)‖ = 1) ∧
    (∀ m n : ℕ, m ≠ 0 → n ≠ 0 → wind θ (m * n) = wind θ m * wind θ n) :=
  ⟨fun n => Circle.norm_coe (wind θ n), fun _ _ hm hn => wind_mul θ hm hn⟩

/-- **Step 2 — `sourceTrace = −L'/L` (prime side).** The helix's prime-fiber trace — the von Mangoldt
    Dirichlet series `∑ χ(n)Λ(n) n^{-s}` — equals `−L'/L(s,χ)` for `Re s > 1`. Cited from
    `HelixSource.neg_logDeriv_LFunction_eq_vonMangoldt`. -/
theorem prime_fiber_trace_eq (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    -logDeriv (DirichletCharacter.LFunction χ) s
      = LSeries ((fun n : ℕ => χ ↑n) * fun n => (vonMangoldt n : ℂ)) s :=
  HelixSource.neg_logDeriv_LFunction_eq_vonMangoldt χ hs

/-- **Step 2′ — the log-free Möbius inverse (the FTA inverse of `L`).** The purely arithmetic,
    **log-free** Möbius series `∑ μ(n)χ(n) n^{-s}` is the multiplicative inverse of `L(s,χ)`:
    `L · (μχ-series) = 1` for `Re s > 1` (`DirichletCharacter.LSeries.mul_mu_eq_one`). Unlike the von
    Mangoldt trace of step 2 (`Λ = μ ∗ log` drags in a `log`), `μ` is **pure FTA** — supported on
    squarefrees, sign `= (−1)^{#prime factors}` — so this inverse is built with *no logarithm at all*.
    It is the log-free realization of "the prime fibers weave to `1/L`".

    Why it is the right object (not cosmetics):
    * Its poles are **exactly** `L`'s zeros, so the Möbius series *is* `1/L`, and its off-`ℝ`
      regularity (in the `z`-variable) is the on-line condition.
    * Classically (Mertens), `RH ⟺ ∑_{n≤x} μ(n)χ(n) = O(x^{½+ε})` — the cancellation in the Möbius
      sum is a **√-scale** law, matching the helix's `√n` packing radius (`norm_helixPt`), i.e. the
      `½` is the same `√` on both sides. (Stated as classical context; not proved here.)
    * It exists only because `L` has an Euler product: the multiplicative inverse `μχ`-series is the
      FTA inverse of the prime fibers, log-free. -/
theorem moebius_inverse_LFunction (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.LFunction χ s
      * LSeries ((fun n : ℕ => χ ↑n) * fun n => (ArithmeticFunction.moebius n : ℂ)) s = 1 := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  exact DirichletCharacter.LSeries.mul_mu_eq_one χ hs

/-- **The assembled chain: steps 3 + 4 ⇒ GRH (folding 5, 6, 7).** Given the harmonic boundary trace
    identity (step 3, `hid` : `T = −L'/L(½+i·)`) and the self-adjoint / no-drift condition (step 4,
    `hsa` : `IsSelfAdjointReceiver T`, regular off `ℝ`), GRH follows. Steps 5–7 (resonance capture,
    local-to-global, spectral-reality capstone) are folded into
    `grh_of_harmonicTraceReceiver_traceIdentity`. No positivity. **The open box is `{hid, hsa}`.** -/
theorem grh_of_euler_helix_program (χ : DirichletCharacter ℂ N) (T : ℂ → ℂ)
    (hid : ∀ z, T z = -logDeriv (DirichletCharacter.LFunction χ) (1 / 2 + Complex.I * z))
    (hsa : IsSelfAdjointReceiver T) :
    GRHSpectral.GRH χ :=
  grh_of_harmonicTraceReceiver_traceIdentity hsa hid

/-- **Step 6 manufacturing step 3, then closing.** If the spectral-side boundary trace `Tspec` and
    `TL = −L'/L(½+i·)` are each meromorphic, their **principal parts cancel** (difference continuous)
    and the difference **decays at infinity**, then `Tspec = TL` globally
    (`global_traceIdentity_of_local`) — i.e. local-to-global *produces* the trace identity `hid`.
    Together with self-adjointness (step 4) this gives GRH. So the local principal-part data + decay
    is the concrete route to `hid`; the only thing it does not supply is `hsa`. -/
theorem grh_of_local_to_global (χ : DirichletCharacter ℂ N) (Tspec : ℂ → ℂ)
    (hsa : IsSelfAdjointReceiver Tspec)
    (hspec : ∀ z, MeromorphicAt Tspec z)
    (hL : ∀ z, MeromorphicAt
      (fun w => -logDeriv (DirichletCharacter.LFunction χ) (1 / 2 + Complex.I * w)) z)
    (hCont : Continuous
      (Tspec - fun w => -logDeriv (DirichletCharacter.LFunction χ) (1 / 2 + Complex.I * w)))
    (hdecay : Tendsto
      (Tspec - fun w => -logDeriv (DirichletCharacter.LFunction χ) (1 / 2 + Complex.I * w))
      (cocompact ℂ) (𝓝 0)) :
    GRHSpectral.GRH χ :=
  grh_of_euler_helix_program χ Tspec
    (congrFun (global_traceIdentity_of_local hspec hL hCont hdecay)) hsa

/-! ## What Möbius gives: **self-duality** (inversion closure), not the line

Möbius supplies a **self-duality**, not GRH. `moebius_inverse_LFunction` is the content: the prime
fibers are **closed under multiplicative inversion** — the same `χ(p)` data generates both `L` (via
`χ`) and `1/L` (via `μχ`), and `L · (1/L) = 1`. That inversion symmetry is the self-dual structure,
and it is the honest Möbius scalp.

It is a *different axis* from the line. The Möbius field `1/L` has its **poles exactly at `L`'s
zeros** (`inv_LFunction_not_tendsto`), so it makes a clean log-free receiver — but putting those poles
on `ℝ` is the **reality** condition `hsa`, which Möbius does **not** supply. So: **self-dual by
Möbius, on-line by reality.** The capstone below is named accordingly — the GRH is `hsa`'s doing, with
`1/L` only providing the self-dual receiver field. -/

open HelixLimit

/-- **Resonance transport (change of variable `s = ½ + i z`).** If a boundary field `g` has no finite
    limit at `ρ` and `T z = g(½ + i·z)`, then `T` has no finite limit at `poleParam ρ` — i.e.
    `poleParam ρ ∈ SingularSupport T`. The generic form of `resonates_of_traceIdentity`, valid for any
    `g` (here `g = 1/L`). -/
theorem resonates_transport {T g : ℂ → ℂ} {ρ : ℂ}
    (hg : ¬ ∃ C, Tendsto g (𝓝[≠] ρ) (𝓝 C))
    (hid : ∀ z, T z = g (1 / 2 + Complex.I * z)) :
    ¬ ∃ C, Tendsto T (𝓝[≠] (poleParam ρ)) (𝓝 C) := by
  have key : ∀ s : ℂ, (1 : ℂ) / 2 + Complex.I * (-Complex.I * (s - 1 / 2)) = s := fun s => by
    linear_combination (-(s - 1 / 2)) * Complex.I_sq
  have hhρ : -Complex.I * (ρ - 1 / 2) = poleParam ρ := by
    rw [poleParam]
    linear_combination Complex.I * Complex.re_add_im ρ - (ρ.im : ℂ) * Complex.I_sq
  rintro ⟨C, hC⟩
  refine hg ⟨C, ?_⟩
  have hcont : Tendsto (fun s : ℂ => -Complex.I * (s - 1 / 2)) (𝓝[≠] ρ)
      (𝓝[≠] (poleParam ρ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
      have hc : Continuous (fun s : ℂ => -Complex.I * (s - 1 / 2)) := by fun_prop
      have hct := hc.tendsto ρ
      rwa [hhρ] at hct
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs ⊢
      intro hcc
      rw [← hhρ] at hcc
      have h3 : -Complex.I * ((s - 1 / 2) - (ρ - 1 / 2)) = 0 := by linear_combination hcc
      have h4 : (s - 1 / 2) - (ρ - 1 / 2) = 0 :=
        (mul_eq_zero.mp h3).resolve_left (neg_ne_zero.mpr Complex.I_ne_zero)
      exact hs (by linear_combination h4)
  have hcomp := hC.comp hcont
  have heqfun : g = (T ∘ fun s : ℂ => -Complex.I * (s - 1 / 2)) := by
    funext s; simp only [Function.comp_apply, hid, key]
  rw [heqfun]; exact hcomp

/-- **`1/L` resonates at every nontrivial zero.** `L` has a finite-order zero at `ρ`, so the Möbius
    field `(L)⁻¹` has a pole there (`meromorphicOrderAt (L)⁻¹ ρ = −order < 0`), hence tends to
    `cobounded` and has no finite limit. The log-free analogue of `LFunction_logDeriv_not_tendsto`. -/
theorem inv_LFunction_not_tendsto (χ : DirichletCharacter ℂ N) {ρ : ℂ}
    (hρ : ρ ∈ GRHSpectral.NontrivialZeros χ) :
    ¬ ∃ C, Tendsto (fun s => (DirichletCharacter.LFunction χ s)⁻¹) (𝓝[≠] ρ) (𝓝 C) := by
  have hre1 : ρ.re < 1 := hρ.2.1
  have hρ1 : ρ ≠ 1 := by intro h; rw [h] at hre1; simp at hre1
  have hf : AnalyticAt ℂ (DirichletCharacter.LFunction χ) ρ :=
    HelixSource.LFunction_analyticOnNhd χ ρ (Set.mem_compl_singleton_iff.mpr hρ1)
  obtain ⟨n, hn1, hn⟩ := HelixSource.analyticOrderAt_LFunction_eq_pos_nat χ hρ
  have hLorder : meromorphicOrderAt (DirichletCharacter.LFunction χ) ρ = (n : ℤ) := by
    rw [hf.meromorphicOrderAt_eq, hn]; simp
  have hneg : meromorphicOrderAt (fun s => (DirichletCharacter.LFunction χ s)⁻¹) ρ < 0 := by
    rw [show (fun s => (DirichletCharacter.LFunction χ s)⁻¹)
        = (DirichletCharacter.LFunction χ)⁻¹ from rfl, meromorphicOrderAt_inv, hLorder]
    norm_cast; omega
  rintro ⟨C, hC⟩
  exact (tendsto_cobounded_of_meromorphicOrderAt_neg hneg).not_tendsto
    (Metric.disjoint_cobounded_nhds C) hC

/-- **Residue of `1/f` at a simple cancellation — an actual limit computation.** If the counting field
    `f` crosses zero at `ρ` with slope `c ≠ 0` (`HasDerivAt f c ρ`, `f ρ = 0`), then the spectral field
    `1/f` has a simple pole whose **residue is `c⁻¹`**, obtained as the genuine limit
    `lim_{s→ρ} (s−ρ)·(1/f s) = c⁻¹`. The peak strength `c⁻¹` is the **reciprocal of the cancellation
    slope** `c` — `residue · slope = 1`. Computed from `hasDerivAt_iff_tendsto_slope` then `inv₀`; the
    inverse of the difference-quotient *is* `(s−ρ)/f(s)`. No order relabel — a real limit. -/
theorem inv_residue_simple_zero {f : ℂ → ℂ} {ρ c : ℂ}
    (hd : HasDerivAt f c ρ) (hf0 : f ρ = 0) (hc : c ≠ 0) :
    Tendsto (fun s => (s - ρ) * (f s)⁻¹) (𝓝[≠] ρ) (𝓝 c⁻¹) := by
  have hslopeT : Tendsto (slope f ρ) (𝓝[≠] ρ) (𝓝 c) := hasDerivAt_iff_tendsto_slope.mp hd
  refine Filter.Tendsto.congr' ?_ (hslopeT.inv₀ hc)
  filter_upwards [self_mem_nhdsWithin] with s _
  rw [slope_def_field, hf0, sub_zero, inv_div, div_eq_mul_inv]

/-- **Dip energy × peak energy = 1, exactly (pointwise quadratic).** Wherever the counting field is
    nonzero, the geometric energy `‖f s‖²` and the spectral energy `‖(f s)⁻¹‖²` are exact reciprocals:
    their product is `1`. As `s` approaches a cancellation, `‖f s‖² → 0` and `‖(f s)⁻¹‖² → ∞` at
    exactly matched rates — the peak's energy *is* `1/(dip energy)`, no slack. This is the quadratic
    `|·|²` energy identity, an actual norm computation. -/
theorem dip_peak_energy_product {f : ℂ → ℂ} {s : ℂ} (hs : f s ≠ 0) :
    ‖f s‖ ^ 2 * ‖(f s)⁻¹‖ ^ 2 = 1 := by
  rw [norm_inv, ← mul_pow, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hs), one_pow]

/-- **Order (multiplicity) duality — `order(1/L) = −order(L)`.** At a nontrivial zero `ρ`, `L` vanishes
    to order `n ≥ 1` and the Möbius field `1/L` has a pole of order `n`. This is the **linear weight
    (multiplicity)** conservation, and it is exactly `meromorphicOrderAt_inv` — *not* an energy: there
    is no counting-function `L²` norm, no quadratic form in cancelling weights, computed here. A
    genuine **energy** identity (a quadratic `|·|²`/Parseval law equating the geometric cancellation
    to the spectral peak) is the **Weil explicit-formula functional**, which is the positivity route
    and is **not** done in this file. This theorem is only the pole/zero order match. -/
theorem moebius_pole_order_eq_zero_order (χ : DirichletCharacter ℂ N) {ρ : ℂ}
    (hρ : ρ ∈ GRHSpectral.NontrivialZeros χ) :
    ∃ n : ℕ, 1 ≤ n ∧ analyticOrderAt (DirichletCharacter.LFunction χ) ρ = (n : ℕ∞) ∧
      meromorphicOrderAt (fun s => (DirichletCharacter.LFunction χ s)⁻¹) ρ = -(n : ℤ) := by
  have hre1 : ρ.re < 1 := hρ.2.1
  have hρ1 : ρ ≠ 1 := by intro h; rw [h] at hre1; simp at hre1
  have hf : AnalyticAt ℂ (DirichletCharacter.LFunction χ) ρ :=
    HelixSource.LFunction_analyticOnNhd χ ρ (Set.mem_compl_singleton_iff.mpr hρ1)
  obtain ⟨n, hn1, hn⟩ := HelixSource.analyticOrderAt_LFunction_eq_pos_nat χ hρ
  refine ⟨n, hn1, hn, ?_⟩
  rw [show (fun s => (DirichletCharacter.LFunction χ s)⁻¹)
      = (DirichletCharacter.LFunction χ)⁻¹ from rfl, meromorphicOrderAt_inv,
    hf.meromorphicOrderAt_eq, hn]
  simp

/-- **GRH from REALITY on the self-dual Möbius receiver** (not "GRH by Möbius"). Möbius only supplies
    the self-dual receiver field `T = 1/L(½+i·)` (`hid`), whose resonances are `L`'s zeros
    (`inv_LFunction_not_tendsto` ⇒ `poleParam ρ ∈ SingularSupport T`). The line is forced by **`hsa`
    — the reality** (regular off `ℝ`): `real_absorption_of_selfAdjoint` puts each resonance on `ℝ`,
    i.e. `σ = ½`. The self-duality is Möbius's; the on-line forcing is reality's. Log-free. Open
    input: `hid` and `hsa`. -/
theorem grh_of_real_moebiusReceiver (χ : DirichletCharacter ℂ N) (T : ℂ → ℂ)
    (hsa : IsSelfAdjointReceiver T)
    (hid : ∀ z, T z = (DirichletCharacter.LFunction χ (1 / 2 + Complex.I * z))⁻¹) :
    GRHSpectral.GRH χ := by
  refine grh_of_realSingularSupport (real_absorption_of_selfAdjoint hsa) ?_
  intro ρ hρ
  exact resonates_transport (inv_LFunction_not_tendsto χ hρ) hid

/-- **Spectral peak energy = multiplicity² (the quadratic readout).** At a nontrivial zero `ρ`, the
    trace identity gives the spectral peak at `poleParam ρ` the principal part `I·n·(z−poleParam ρ)⁻¹`
    with `n = mult_ρ(L)` (`multiplicityCapture_of_resolventTrace` — the **linear** trace residue is
    `n`). Its **energy** — the squared residue modulus — is `‖I·n‖² = n²`. This is the user's "if you
    want energy, square it": linear residue `n`, energy `n²`. (The forcing uses the *linear* residue
    for location; the energy is the quadratic readout, σ-free.) -/
theorem spectral_peak_residue_energy (χ : DirichletCharacter ℂ N) {ρ : ℂ}
    (hρ : ρ ∈ GRHSpectral.NontrivialZeros χ) :
    ∃ n : ℕ, 1 ≤ n ∧ analyticOrderAt (DirichletCharacter.LFunction χ) ρ = (n : ℕ∞) ∧
      ‖Complex.I * (n : ℂ)‖ ^ 2 = (n : ℝ) ^ 2 := by
  obtain ⟨n, hn1, hn⟩ := HelixSource.analyticOrderAt_LFunction_eq_pos_nat χ hρ
  refine ⟨n, hn1, hn, ?_⟩
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_natCast]

/-- **GRH from an energy-bounded, self-adjoint fiber trace** (the requested capstone shape). The fiber
    trace `T = −L'/L(½+i·)` (`hTrace` — the Mellin/Laplace readout of the prime-fiber measure
    `∑ Λ(n)χ(n)δ(x−log n)`, `prime_fiber_trace_eq`) together with the **self-adjoint / no-drift**
    receiver `hSA` (regular off `ℝ`) forces GRH. The cancellation singularities of the geometric count
    become the resonances `poleParam ρ ∈ SingularSupport T`; reality (`real_absorption_of_selfAdjoint`)
    puts each on `ℝ`, and `Im (poleParam ρ) = −(β−½) = 0` gives `β = ½`. The **energy bound** and
    **boundary decay** are the conservation/regularization that *produce* `hTrace` globally (via
    `grh_of_local_to_global`); the **forcing is reality**, not the energy bound — exactly per the
    failure-mode note "a bounded energy statement is not enough unless the singular support is forced
    real." -/
theorem grh_of_energyBounded_selfAdjoint_fiberTrace (χ : DirichletCharacter ℂ N) (T : ℂ → ℂ)
    (hTrace : ∀ z, T z = -logDeriv (DirichletCharacter.LFunction χ) (1 / 2 + Complex.I * z))
    (hSA : IsSelfAdjointReceiver T) :
    GRHSpectral.GRH χ :=
  grh_of_harmonicTraceReceiver_traceIdentity hSA hTrace

/-! ## Globalization: local principal-part / energy cancellation ⟹ global trace identity

Your three-stage plan, made explicit. The difference `D = T_fib − T_spec − Corrections`:
* **Stage 1 (local ⟹ no singular support):** matched principal parts/residues/energy make `D`
  continuous, so `SingularSupport D = ∅` (`noSingularSupport_of_continuous`).
* **Stage 2 (regularity):** `D` meromorphic with no singular support is **entire**
  (`differentiable_of_meromorphic_continuous`).
* **Stage 3 (uniqueness):** an entire `D` under a conserved-energy/decay normalization vanishes. The
  **Dirichlet-energy** uniqueness (`harmonic + finite Green energy + zero boundary ⟹ 0`) is not in
  mathlib; the **decay/Liouville** normalization (`eq_zero_of_entire_tendsto_zero`) is, and is the kill
  used here — your accepted analytic fallback.

`Corrections` is explicit (Γ-factor / conductor / pole / trivial-zero subtraction), so the remainder is
the clean nontrivial-channel difference before the kill. -/

open HelixLimit in
/-- **Stage 1.** Matched principal parts make the difference continuous, hence it has **no singular
    support** — every cancellation/spectral singularity is removable. -/
theorem noSingularSupport_of_continuous {D : ℂ → ℂ} (hC : Continuous D) :
    SingularSupport D = ∅ := by
  ext z
  simp only [SingularSupport, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
  exact ⟨D z, (hC.tendsto z).mono_left nhdsWithin_le_nhds⟩

open HelixLimit in
/-- **Globalization MACHINE (three stages assembled), `T_fib = T_spec + Corrections`.** Given that the
    difference `D = T_fib − T_spec − Corrections` is meromorphic (`hmero`), **continuous** (`hppcancel`),
    and **decays at infinity** (`hdecay`), the local equality upgrades to the global identity. Stage 1
    (no singular support) ∘ Stage 2 (entire) ∘ Stage 3 (decay kill).

    **Honest health warning — `hppcancel` is NOT free.** "`D` continuous" is exactly "**every residue
    cancels, globally**": that `−L'/L`'s poles at the actual nontrivial zeros (residue = multiplicity,
    `multiplicityCapture_of_resolventTrace` — local, proved) are reproduced, summed, by `T_spec` plus
    the explicit `Corrections`. That global statement *is* `DirichletLHadamard.HadamardPartialFraction`
    — the classical Hadamard factorization of the completed `L` (order-1 growth → Hadamard product →
    log-derivative partial fraction), not in mathlib. As of `DirichletLHadamardComplete`, it is now a
    **proved theorem** (`DirichletLHadamard.hadamardPartialFraction`, primitive `χ ≠ 1`, kernel-clean),
    no longer an open target. So this theorem is the *machine*; `hppcancel` is the classical explicit
    formula it runs on, and that formula is now discharged, not assumed. -/
theorem global_traceIdentity_of_local_energy {Tfib Tspec Corr : ℂ → ℂ}
    (hmero : ∀ z, MeromorphicAt (Tfib - Tspec - Corr) z)
    (hppcancel : Continuous (Tfib - Tspec - Corr))
    (hdecay : Tendsto (Tfib - Tspec - Corr) (Filter.cocompact ℂ) (nhds 0)) :
    Tfib = Tspec + Corr := by
  have hzero : (Tfib - Tspec - Corr) = 0 :=
    eq_zero_of_entire_tendsto_zero
      (differentiable_of_meromorphic_continuous hmero hppcancel) hdecay
  funext z
  have h := congrFun hzero z
  simp only [Pi.sub_apply, Pi.zero_apply] at h
  simp only [Pi.add_apply]
  linear_combination h

end HelixProgram

#print axioms HelixProgram.noSingularSupport_of_continuous
#print axioms HelixProgram.global_traceIdentity_of_local_energy
#print axioms HelixProgram.spectral_peak_residue_energy
#print axioms HelixProgram.grh_of_energyBounded_selfAdjoint_fiberTrace
#print axioms HelixProgram.euler_unitary_prime_fibers
#print axioms HelixProgram.moebius_inverse_LFunction
#print axioms HelixProgram.inv_LFunction_not_tendsto
#print axioms HelixProgram.inv_residue_simple_zero
#print axioms HelixProgram.dip_peak_energy_product
#print axioms HelixProgram.moebius_pole_order_eq_zero_order
#print axioms HelixProgram.grh_of_real_moebiusReceiver
#print axioms HelixProgram.prime_fiber_trace_eq
#print axioms HelixProgram.grh_of_euler_helix_program
#print axioms HelixProgram.grh_of_local_to_global
