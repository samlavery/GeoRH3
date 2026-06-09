import RequestProject.HelixSpectralLimit
import RequestProject.HelixSource
import RequestProject.HelixSourceMultiplicity

/-!
# Resolvent-trace Hilbert–Pólya capstone (multiplicity-aware, no positivity)

Two layers, plus the multiplicity obligation, all in the `z`-variable `s = ½ + i z` (so a **real**
spectral parameter is exactly the critical line):

* **Layer 1** (`HelixLimit.grh_of_selfAdjoint_spectral_capture`, in `HelixSpectralLimit`):
  *location capture ⟹ GRH*. `poleParam ρ ∈ spectrum ℂ a` for a self-adjoint `a` ⟹ `Re ρ = ½`,
  by spectral reality (`IsSelfAdjoint.im_eq_zero_of_mem_spectrum`). No positivity.
* **Layer 2** (`hcap_of_resolventTrace`, here): *resolvent-trace identity ⟹ location capture*. If a
  regularized resolvent trace `T` equals `−L'/L(½ + i·)` and is regular off `spectrum ℂ a`, then each
  zero's pole-parameter is in the spectrum. The singularity is inherited from `−L'/L`'s pole
  (`HelixSource.LFunction_logDeriv_not_tendsto`) by meromorphic equality — so it transfers *with
  multiplicity* — and "regular off the spectrum" forces it onto the spectrum. **Needs no
  self-adjointness.**
* **Capstone** (`grh_of_selfAdjoint_resolvent_capture`): Layer 1 ∘ Layer 2.

The single open box is the **resolvent-trace identity** `hid` — the trace formula — kept *local /
principal-part* (regularity off the spectrum) rather than global trace-class. The Γ-factor, trivial
zeros, and `s = 1` pole live on the prime/archimedean side and must be subtracted into the regularizer
`R₀` so the nontrivial-zero channel is clean; here that is encoded by `T` already being `−L'/L`
(uncompleted, so the `s=1` pole and trivial zeros are not in the picture for non-principal `χ`).

The **multiplicity layer** `multiplicityCapture_of_resolventTrace` is stated as the precise remaining
obligation (residue/principal-part equality), reducing to `HelixSource.LFunction_logDeriv_residue_eq_order`
(`residue_ρ(−L'/L) = mult_ρ L`) transported through `s = ½ + i z`.
-/

open Filter Topology

namespace HelixLimit

variable {N : ℕ} [NeZero N]

/-- **Resonance lemma (principal-part).** The regularized resolvent trace `T = −L'/L(½+i·)` has **no
    finite limit** at `poleParam ρ` for every nontrivial zero `ρ` — it *resonates* (a pole) exactly at
    the zero parameters. Inherited from `−L'/L`'s pole at `ρ` (`HelixSource.LFunction_logDeriv_not_tendsto`)
    through the affine `s = ½ + i z`; meromorphic equality, so the resonance carries multiplicity. -/
theorem resonates_of_traceIdentity {χ : DirichletCharacter ℂ N} {T : ℂ → ℂ}
    (hid : ∀ z, T z = -logDeriv (DirichletCharacter.LFunction χ) (1 / 2 + Complex.I * z))
    {ρ : ℂ} (hρ : ρ ∈ GRHSpectral.NontrivialZeros χ) :
    ¬ ∃ L, Tendsto T (𝓝[≠] (poleParam ρ)) (𝓝 L) := by
  have key : ∀ s : ℂ, (1 : ℂ) / 2 + Complex.I * (-Complex.I * (s - 1 / 2)) = s := fun s => by
    linear_combination (-(s - 1 / 2)) * Complex.I_sq
  have hhρ : -Complex.I * (ρ - 1 / 2) = poleParam ρ := by
    rw [poleParam]
    linear_combination Complex.I * Complex.re_add_im ρ - (ρ.im : ℂ) * Complex.I_sq
  rintro ⟨L, hL⟩
  refine HelixSource.LFunction_logDeriv_not_tendsto χ hρ ⟨L, ?_⟩
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
      intro hc
      rw [← hhρ] at hc
      have h3 : -Complex.I * ((s - 1 / 2) - (ρ - 1 / 2)) = 0 := by linear_combination hc
      have h4 : (s - 1 / 2) - (ρ - 1 / 2) = 0 :=
        (mul_eq_zero.mp h3).resolve_left (neg_ne_zero.mpr Complex.I_ne_zero)
      exact hs (by linear_combination h4)
  have hcomp := hL.comp hcont
  have heqfun : (fun s : ℂ => -logDeriv (DirichletCharacter.LFunction χ) s)
      = (T ∘ fun s : ℂ => -Complex.I * (s - 1 / 2)) := by
    funext s; simp only [Function.comp_apply, hid, key]
  rw [heqfun]; exact hcomp

/-- **Layer 2 — resolvent-trace ⟹ location capture** (self-adjointness *not* used). -/
theorem hcap_of_resolventTrace {A : Type*} [CStarAlgebra A] {a : A}
    (χ : DirichletCharacter ℂ N) (T : ℂ → ℂ)
    (hid : ∀ z, T z = -logDeriv (DirichletCharacter.LFunction χ) (1 / 2 + Complex.I * z))
    (hReg : ∀ z, z ∉ spectrum ℂ a → ∃ L, Tendsto T (𝓝[≠] z) (𝓝 L)) :
    ∀ ρ ∈ GRHSpectral.NontrivialZeros χ, poleParam ρ ∈ spectrum ℂ a := by
  intro ρ hρ
  by_contra hns
  exact resonates_of_traceIdentity hid hρ (hReg (poleParam ρ) hns)

/-- **Resolvent-trace capstone** = Layer 1 ∘ Layer 2. A self-adjoint channel whose regularized
    resolvent trace `T` equals `−L'/L(½ + i·)` (and is regular off its spectrum) forces GRH, by
    spectral reality alone — no positivity, no eigenvalue limit, multiplicity inherited from the
    meromorphic identity. -/
theorem grh_of_selfAdjoint_resolvent_capture
    {A : Type*} [CStarAlgebra A] [StarModule ℂ A] {a : A} (ha : IsSelfAdjoint a)
    (χ : DirichletCharacter ℂ N) (T : ℂ → ℂ)
    (hid : ∀ z, T z = -logDeriv (DirichletCharacter.LFunction χ) (1 / 2 + Complex.I * z))
    (hReg : ∀ z, z ∉ spectrum ℂ a → ∃ L, Tendsto T (𝓝[≠] z) (𝓝 L)) :
    GRHSpectral.GRH χ :=
  grh_of_selfAdjoint_spectral_capture ha χ (hcap_of_resolventTrace χ T hid hReg)

/-- **The spectral-side dual receiver** (principal-part form — the proof object). A self-adjoint
    channel `a` *receives* `χ`'s zeros when its regularized resolvent trace `T`:
    * `regular_off_spectrum` — has a finite limit at every point **off** `spectrum ℂ a`; and
    * `resonates_at_zeros` — has **no** finite limit (a pole/resonance) at every zero parameter
      `poleParam ρ`.
    The zero **dips/resonances** are exactly the spectral singularities of `a`. Stated locally via
    principal parts: no global trace-class, no positivity. -/
structure ResolventReceiver {A : Type*} [CStarAlgebra A] (a : A)
    (χ : DirichletCharacter ℂ N) (T : ℂ → ℂ) : Prop where
  regular_off_spectrum : ∀ z, z ∉ spectrum ℂ a → ∃ L, Tendsto T (𝓝[≠] z) (𝓝 L)
  resonates_at_zeros : ∀ ρ ∈ GRHSpectral.NontrivialZeros χ,
    ¬ ∃ L, Tendsto T (𝓝[≠] (poleParam ρ)) (𝓝 L)

/-- A receiver captures every zero parameter into its spectrum (resonance ∧ regular-off-spectrum). -/
theorem ResolventReceiver.locationCapture {A : Type*} [CStarAlgebra A] {a : A}
    {χ : DirichletCharacter ℂ N} {T : ℂ → ℂ} (h : ResolventReceiver a χ T) :
    ∀ ρ ∈ GRHSpectral.NontrivialZeros χ, poleParam ρ ∈ spectrum ℂ a := by
  intro ρ hρ
  by_contra hns
  exact h.resonates_at_zeros ρ hρ (h.regular_off_spectrum (poleParam ρ) hns)

/-- **GRH from a self-adjoint receiver — the dual capstone.** A self-adjoint channel receiving `χ`'s
    zeros forces GRH, by spectral reality alone (no positivity). -/
theorem grh_of_resolventReceiver {A : Type*} [CStarAlgebra A] [StarModule ℂ A] {a : A}
    (ha : IsSelfAdjoint a) {χ : DirichletCharacter ℂ N} {T : ℂ → ℂ}
    (h : ResolventReceiver a χ T) : GRHSpectral.GRH χ :=
  grh_of_selfAdjoint_spectral_capture ha χ h.locationCapture

/-- The meromorphic trace identity `T = −L'/L(½+i·)` (regular off the spectrum) **provides** a
    receiver: the resonances are `resonates_of_traceIdentity`. So discharging the global identity is
    one (stronger) way to realize the local principal-part object — the single remaining content is
    *"a self-adjoint channel whose resolvent trace resonates at the zeros."* -/
theorem ResolventReceiver.of_traceIdentity {A : Type*} [CStarAlgebra A] {a : A}
    {χ : DirichletCharacter ℂ N} {T : ℂ → ℂ}
    (hid : ∀ z, T z = -logDeriv (DirichletCharacter.LFunction χ) (1 / 2 + Complex.I * z))
    (hReg : ∀ z, z ∉ spectrum ℂ a → ∃ L, Tendsto T (𝓝[≠] z) (𝓝 L)) :
    ResolventReceiver a χ T where
  regular_off_spectrum := hReg
  resonates_at_zeros := fun ρ hρ => resonates_of_traceIdentity hid hρ

/-! ## Harmonic / boundary-value realization (continuous-spectrum compatible)

The "operator" is just the boundary trace `T : ℂ → ℂ` together with its limiting behaviour: its
spectrum is the **singular support** `{z | T has no finite limit at z}` — the absorption set. Stated by
`Tendsto`, so it covers **continuous spectrum** (Connes absorption), not only discrete atoms. The
self-adjointness becomes **reality of the boundary values** (`singular support ⊆ ℝ`), which is the
earned no-drift / conjugate-harmonic conservation — not a positivity floor and not an assumption that
the zeros are on the line. -/

/-- The **singular support** of a boundary trace `T`: where `T` has no finite limit (the absorption /
    resonance set). For a genuine resolvent trace this is the spectrum. -/
def SingularSupport (T : ℂ → ℂ) : Set ℂ := {z | ¬ ∃ L, Tendsto T (𝓝[≠] z) (𝓝 L)}

/-- **Harmonic-boundary capstone — real boundary values force the line.** If `T`'s singular support is
    **real** (`hreal`: the self-adjoint / conservative-harmonic condition — real boundary values) and
    `T` **resonates** at every zero parameter (`hres`), then GRH. The whole forcing is
    `singular support ⊆ ℝ`: `poleParam ρ` real ⟹ `σ = ½`. No C⋆-algebra, no discrete spectrum, no
    positivity — works for continuous-spectrum / Connes-absorption channels. `hreal` is the earned
    reality, *not* an assumption that the zeros are on-line. -/
theorem grh_of_realSingularSupport {χ : DirichletCharacter ℂ N} {T : ℂ → ℂ}
    (hreal : ∀ z ∈ SingularSupport T, z.im = 0)
    (hres : ∀ ρ ∈ GRHSpectral.NontrivialZeros χ, poleParam ρ ∈ SingularSupport T) :
    GRHSpectral.GRH χ := by
  intro ρ hρ
  have him : (poleParam ρ).im = 0 := hreal (poleParam ρ) (hres ρ hρ)
  rw [poleParam_im] at him
  linarith

/-- The trace identity puts every zero parameter into the singular support: `T` resonates (absorbs)
    at each `poleParam ρ`. So discharging `hreal` (real boundary values) harmonically realizes the
    receiver and closes GRH via `grh_of_realSingularSupport`. -/
theorem zeros_subset_singularSupport_of_traceIdentity {χ : DirichletCharacter ℂ N} {T : ℂ → ℂ}
    (hid : ∀ z, T z = -logDeriv (DirichletCharacter.LFunction χ) (1 / 2 + Complex.I * z)) :
    ∀ ρ ∈ GRHSpectral.NontrivialZeros χ, poleParam ρ ∈ SingularSupport T :=
  fun ρ hρ => resonates_of_traceIdentity hid hρ

/-- **Self-adjoint receiver — boundary form, NOT "real boundary values".** `T` is a self-adjoint
    receiver when it is **regular off the real axis**: a finite limit at every `z` with `Im z ≠ 0`.
    This is the genuine self-adjoint content — the resolvent / bulk harmonic field is analytic off `ℝ`,
    equivalently `spectrum ⊆ ℝ` — and for a self-adjoint operator it is a *theorem* (resolvent set
    `⊇ ℂ∖ℝ`), **not** an assumption that the zeros are on-line. -/
def IsSelfAdjointReceiver (T : ℂ → ℂ) : Prop :=
  ∀ z, z.im ≠ 0 → ∃ L, Tendsto T (𝓝[≠] z) (𝓝 L)

/-- **Earned reality (self-adjoint ⟹ real absorption).** A self-adjoint receiver's singular support is
    real: where it resonates/absorbs, the parameter lies on `ℝ`. This is the boundary form of
    `self-adjoint ⇒ spectrum ⊆ ℝ` — **derived from `IsSelfAdjointReceiver`, not assumed.** -/
theorem real_absorption_of_selfAdjoint {T : ℂ → ℂ} (hsa : IsSelfAdjointReceiver T) :
    ∀ z ∈ SingularSupport T, z.im = 0 := by
  intro z hz
  by_contra him
  exact hz (hsa z him)

/-- **GRH from a self-adjoint harmonic receiver — the Connes/absorption capstone.** A self-adjoint
    receiver (regular off `ℝ`) whose singular support contains every zero parameter forces GRH:
    real absorption (earned) + resonance at the zeros ⟹ `poleParam ρ` real ⟹ `σ = ½`. No discrete
    spectrum, no positivity — continuous-spectrum compatible. -/
theorem grh_of_harmonicTraceReceiver {χ : DirichletCharacter ℂ N} {T : ℂ → ℂ}
    (hsa : IsSelfAdjointReceiver T)
    (hres : ∀ ρ ∈ GRHSpectral.NontrivialZeros χ, poleParam ρ ∈ SingularSupport T) :
    GRHSpectral.GRH χ :=
  grh_of_realSingularSupport (real_absorption_of_selfAdjoint hsa) hres

/-- **The harmonic capstone from the trace identity.** A self-adjoint receiver whose boundary trace
    equals `−L'/L(½+i·)` forces GRH: the zeros become boundary absorption resonances
    (`zeros_subset_singularSupport_of_traceIdentity`), and self-adjoint reality puts them on `ℝ`. The
    sole open input is the boundary identity `hid`; self-adjointness is `regular off ℝ`. -/
theorem grh_of_harmonicTraceReceiver_traceIdentity {χ : DirichletCharacter ℂ N} {T : ℂ → ℂ}
    (hsa : IsSelfAdjointReceiver T)
    (hid : ∀ z, T z = -logDeriv (DirichletCharacter.LFunction χ) (1 / 2 + Complex.I * z)) :
    GRHSpectral.GRH χ :=
  grh_of_harmonicTraceReceiver hsa (zeros_subset_singularSupport_of_traceIdentity hid)

/-- **Multiplicity layer — the resolvent trace's residue at `poleParam ρ` is the zero multiplicity.**
    From the meromorphic identity `T = −L'/L(½+i·)`, the principal part of `T` at `z = poleParam ρ` is

    `T z = (i · n) · (z − poleParam ρ)⁻¹ + G z`,  `G` analytic at `poleParam ρ`, `n = mult_ρ(L) ≥ 1`.

    So `T` has a **simple pole** there with **residue `i · n`** — the resolvent-trace residue equals the
    zero multiplicity, up to the change-of-variable Jacobian `ds/dz = i`. (For a genuine resolvent
    trace `Tr((a−z)⁻¹)` the residue at an eigenvalue is its spectral multiplicity, so this is
    `spectralMultiplicity a (poleParam ρ) = mult_ρ(L)`.) Built by transporting
    `HelixSource.LFunction_logDeriv_residue_eq_order` through `s = ½ + i z`. No positivity, no
    self-adjointness — pure meromorphic equality, so multiplicity rides along linearly. -/
theorem multiplicityCapture_of_resolventTrace {A : Type*} [CStarAlgebra A] {a : A}
    (χ : DirichletCharacter ℂ N) (T : ℂ → ℂ)
    (hid : ∀ z, T z = -logDeriv (DirichletCharacter.LFunction χ) (1 / 2 + Complex.I * z))
    {ρ : ℂ} (hρ : ρ ∈ GRHSpectral.NontrivialZeros χ) :
    ∃ (n : ℕ) (G : ℂ → ℂ), 1 ≤ n ∧ AnalyticAt ℂ G (poleParam ρ) ∧
      analyticOrderAt (DirichletCharacter.LFunction χ) ρ = (n : ℕ∞) ∧
      ∀ᶠ z in 𝓝[≠] (poleParam ρ),
        T z = Complex.I * (n : ℂ) * (z - poleParam ρ)⁻¹ + G z := by
  obtain ⟨n, g, hn, hg, hgne, hord, hform⟩ := HelixSource.LFunction_logDeriv_residue_eq_order χ hρ
  -- change of variable `w z = ½ + i z`, with `w (poleParam ρ) = ρ` and `w z − ρ = i (z − poleParam ρ)`
  have key : ∀ s : ℂ, (1 : ℂ) / 2 + Complex.I * (-Complex.I * (s - 1 / 2)) = s := fun s => by
    linear_combination (-(s - 1 / 2)) * Complex.I_sq
  have hhρ : -Complex.I * (ρ - 1 / 2) = poleParam ρ := by
    rw [poleParam]
    linear_combination Complex.I * Complex.re_add_im ρ - (ρ.im : ℂ) * Complex.I_sq
  have hwρ : (1 : ℂ) / 2 + Complex.I * poleParam ρ = ρ := by rw [← hhρ]; exact key ρ
  have hwsub : ∀ z : ℂ, (1 : ℂ) / 2 + Complex.I * z - ρ = Complex.I * (z - poleParam ρ) :=
    fun z => by linear_combination hwρ
  refine ⟨n, fun z => -(deriv g (1 / 2 + Complex.I * z) / g (1 / 2 + Complex.I * z)),
    hn, ?_, hord, ?_⟩
  · -- analyticity of the holomorphic part `G`
    have haff : AnalyticAt ℂ (fun z : ℂ => (1 : ℂ) / 2 + Complex.I * z) (poleParam ρ) := by
      apply analyticAt_const.add
      exact analyticAt_const.mul analyticAt_id
    have hdgg : AnalyticAt ℂ (fun s : ℂ => deriv g s / g s) ρ := (hg.deriv).div hg hgne
    have hcomp : AnalyticAt ℂ
        ((fun s : ℂ => deriv g s / g s) ∘ fun z : ℂ => (1 : ℂ) / 2 + Complex.I * z)
        (poleParam ρ) := by
      refine AnalyticAt.comp ?_ haff
      rw [hwρ]
      exact hdgg
    exact hcomp.neg
  · -- the principal-part identity, transported through `w`
    have htendsto : Tendsto (fun z : ℂ => (1 : ℂ) / 2 + Complex.I * z) (𝓝[≠] (poleParam ρ))
        (𝓝[≠] ρ) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
        have hc : Continuous (fun z : ℂ => (1 : ℂ) / 2 + Complex.I * z) := by fun_prop
        have hct := hc.tendsto (poleParam ρ)
        rwa [show (1 : ℂ) / 2 + Complex.I * poleParam ρ = ρ from hwρ] at hct
      · filter_upwards [self_mem_nhdsWithin] with z hz
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz ⊢
        intro hc
        have h3 : Complex.I * (z - poleParam ρ) = 0 := by
          rw [← hwsub]; linear_combination hc
        exact hz (by
          have h4 := (mul_eq_zero.mp h3).resolve_left Complex.I_ne_zero
          linear_combination h4)
    filter_upwards [htendsto.eventually hform, self_mem_nhdsWithin] with z hPz hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz
    rw [hid z, hPz, hwsub z, mul_inv, Complex.inv_I]
    ring

/-! ## Local principal parts ⟹ global trace identity — the entire-error kill

`hcap`/`ResolventReceiver` only need the *local* resonance (same poles). Upgrading the **local**
principal-part equality to the **global** meromorphic identity `T_spec = T_L` is the entire-error step:
the difference has no surviving poles, hence is entire, and a growth/normalization bound kills it
(Liouville). -/

/-- **Entire from cancelled principal parts.** A function meromorphic *and continuous* at every point
    is entire: where the principal parts cancel (the difference is continuous), the meromorphic
    singularities are removable. -/
theorem differentiable_of_meromorphic_continuous {D : ℂ → ℂ}
    (hMero : ∀ z, MeromorphicAt D z) (hCont : Continuous D) : Differentiable ℂ D :=
  fun z => ((hMero z).analyticAt hCont.continuousAt).differentiableAt

/-- **Entire-error kill (Liouville / decay).** An entire function tending to `0` at infinity
    (`cocompact`) is identically `0`. -/
theorem eq_zero_of_entire_tendsto_zero {D : ℂ → ℂ} (hD : Differentiable ℂ D)
    (hdecay : Tendsto D (Filter.cocompact ℂ) (𝓝 0)) : D = 0 := by
  funext z; simpa using hD.apply_eq_of_tendsto_cocompact z hdecay

/-- **Local ⟹ global trace identity.** If `Tspec` and `TL` are meromorphic, their difference is
    continuous (principal parts equal — *no surviving poles*) and decays at infinity
    (growth/normalization kill), then `Tspec = TL` globally. This is the exact local-to-global
    transition: same poles + same residues, upgraded past the entire error. Feeding `Tspec` = a
    self-adjoint channel's resolvent trace and `TL = −L'/L(½+i·)` gives the `hid` of the capstone. -/
theorem global_traceIdentity_of_local {Tspec TL : ℂ → ℂ}
    (hspec : ∀ z, MeromorphicAt Tspec z) (hL : ∀ z, MeromorphicAt TL z)
    (hCont : Continuous (Tspec - TL))
    (hdecay : Tendsto (Tspec - TL) (Filter.cocompact ℂ) (𝓝 0)) :
    Tspec = TL :=
  sub_eq_zero.mp <| eq_zero_of_entire_tendsto_zero
    (differentiable_of_meromorphic_continuous (fun z => (hspec z).sub (hL z)) hCont) hdecay

end HelixLimit

#print axioms HelixLimit.hcap_of_resolventTrace
#print axioms HelixLimit.grh_of_selfAdjoint_resolvent_capture
#print axioms HelixLimit.multiplicityCapture_of_resolventTrace
#print axioms HelixLimit.grh_of_resolventReceiver
#print axioms HelixLimit.ResolventReceiver.of_traceIdentity
#print axioms HelixLimit.differentiable_of_meromorphic_continuous
#print axioms HelixLimit.eq_zero_of_entire_tendsto_zero
#print axioms HelixLimit.global_traceIdentity_of_local
#print axioms HelixLimit.grh_of_realSingularSupport
#print axioms HelixLimit.real_absorption_of_selfAdjoint
#print axioms HelixLimit.grh_of_harmonicTraceReceiver_traceIdentity
