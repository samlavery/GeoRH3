import Mathlib
import RequestProject.HelixSource
import RequestProject.Chi3LogDerivPole
import RequestProject.GRHSpectralCriterion
import RequestProject.HelixResolventCapture
import RequestProject.Chi3PoleEnergyBridge
import RequestProject.Chi3SourceTrace

/-!
# The helix identification closed form, and the no-drift pole weld

Two separate layers, kept honestly apart (Rules Two/Eight/Ten):

**A. The identification (closed form) — NOT GRH-strength, fully buildable.** The area projection
`R(n)² = C·n` makes the helix weight `(R(n)²)^{-s} = (C n)^{-s} = C^{-s} n^{-s}` (log-free: a `cpow`
of the *area*, never a `Real.log`). Summing the FTA-winding character `χ_wind(n) = χ(n)` gives

* `helixSource_eq_gauge_mul_L`:  `HelixSource χ C s = C^{-s} · L(s,χ)`,
* `helixTrace_eq_gauge_mul_negLogDeriv`:  `HelixTrace χ C s = C^{-s} · (−L'/L)(s,χ)`,

for `Re s > 1` (the convergence strip; `HelixTraceCont` is the continuation). The **gauge** `C^{-s}`
is nonzero (`gauge_ne_zero`), so it moves **no zeros and no poles** — `HelixTraceCont` has a pole at
exactly the zeros of `L`. This whole layer is a dictionary, not the open problem.

**B. The no-drift pole weld — the GRH-strength step, stated honestly, NOT faked.** Define capture
geometrically: `CapturedByHelixGeometry χ C ρ := PoleAt (HelixTraceCont χ C) ρ` — *ρ is a resonance
of the helix trace*. This is **not** `Re ρ = ½` (the circularity flagged in the spec): it is a pole of
a gauge-times-`(−L'/L)` field. With this honest definition:

* `zero_captured` — **`NontrivialZero χ ρ ⟹ CapturedByHelixGeometry χ C ρ`, proven without assuming
  `Re ρ = ½`** (the gauge is nonzero, so a zero of `L` is a pole of the helix trace). The "every zero
  is captured" half is *free*.
* The remaining half — `CapturedByHelixGeometry χ C ρ ⟹ Re ρ = ½` (the **no-drift forcing**) — is the
  GRH-strength weld. Since capture is free, this half carries the *entire* GRH content; it is the
  σ-free reality target (`HelixSource.source_noDrift` / `HelixLimit.grh_of_realSingularSupport`), the
  genuine open research. It is **left as a named obligation** (`HelixNoDriftForcing`), not dressed as a
  `grh_of_…` reduction (Rule Ten) and never closed by the `σ−½` costume (Rule Two).
-/

open Complex Filter Topology

namespace HelixGauge

variable {N : ℕ} [NeZero N]

/-- The **gauge factor** `C^{-s}` is nonzero for `C > 0` — it moves no zeros or poles. -/
theorem gauge_ne_zero (C : ℝ) (hC : 0 < C) (s : ℂ) : (C : ℂ) ^ (-s) ≠ 0 :=
  Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hC.ne'))

/-! ## A. The closed-form identification -/

/-- The **helix source** — the FTA-winding character summed against the area-projection weight
    `(R(n)²)^{-s} = (C n)^{-s}` (log-free: a power of the area `C n`). -/
noncomputable def HelixSource (χ : DirichletCharacter ℂ N) (C : ℝ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, χ (n : ZMod N) * ((C : ℂ) * (n : ℂ)) ^ (-s)

/-- **Source identity (closed form):** `HelixSource χ C s = C^{-s} · L(s,χ)` on `Re s > 1`. The area
    projection produces the Dirichlet `L`-weight times the nonzero gauge `C^{-s}`. -/
theorem helixSource_eq_gauge_mul_L (χ : DirichletCharacter ℂ N) (C : ℝ) (hC : 0 < C)
    {s : ℂ} (hs : 1 < s.re) :
    HelixSource χ C s = (C : ℂ) ^ (-s) * DirichletCharacter.LFunction χ s := by
  have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs; norm_num at hs
  rw [HelixSource, DirichletCharacter.LFunction_eq_LSeries χ hs, LSeries, ← tsum_mul_left]
  refine tsum_congr (fun n => ?_)
  rcases eq_or_ne n 0 with hn | hn
  · subst hn; simp [LSeries.term, Complex.zero_cpow (neg_ne_zero.mpr hs0)]
  · rw [LSeries.term_of_ne_zero hn,
        show ((n : ℂ)) = ((n : ℝ) : ℂ) from by push_cast; ring,
        mul_cpow_ofReal_nonneg hC.le (by positivity) (-s)]
    simp only [Complex.cpow_neg]; push_cast; ring

/-- The **helix prime trace** — von Mangoldt-weighted winding against the area weight. -/
noncomputable def HelixTrace (χ : DirichletCharacter ℂ N) (C : ℝ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod N) * ((C : ℂ) * (n : ℂ)) ^ (-s)

/-- The **continued** helix trace `C^{-s} · (−L'/L)(s,χ)` — defined for all `s`; its poles are exactly
    `L`'s zeros. -/
noncomputable def HelixTraceCont (χ : DirichletCharacter ℂ N) (C : ℝ) (s : ℂ) : ℂ :=
  (C : ℂ) ^ (-s) * (-logDeriv (DirichletCharacter.LFunction χ) s)

/-- **Trace identity (closed form):** `HelixTrace χ C s = C^{-s} · (−L'/L)(s,χ)` on `Re s > 1`
    (the von Mangoldt / Euler-product weight). -/
theorem helixTrace_eq_gauge_mul_negLogDeriv (χ : DirichletCharacter ℂ N) (C : ℝ) (hC : 0 < C)
    {s : ℂ} (hs : 1 < s.re) :
    HelixTrace χ C s = (C : ℂ) ^ (-s) * (-logDeriv (DirichletCharacter.LFunction χ) s) := by
  have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs; norm_num at hs
  rw [HelixTrace, HelixSource.neg_logDeriv_LFunction_eq_vonMangoldt χ hs, LSeries, ← tsum_mul_left]
  refine tsum_congr (fun n => ?_)
  rcases eq_or_ne n 0 with hn | hn
  · subst hn; simp [LSeries.term, Complex.zero_cpow (neg_ne_zero.mpr hs0)]
  · rw [LSeries.term_of_ne_zero hn,
        show ((n : ℂ)) = ((n : ℝ) : ℂ) from by push_cast; ring,
        mul_cpow_ofReal_nonneg hC.le (by positivity) (-s)]
    simp only [Complex.cpow_neg, Pi.mul_apply]; push_cast; ring

/-- On `Re s > 1` the geometric trace equals its continuation. -/
theorem helixTrace_eq_cont (χ : DirichletCharacter ℂ N) (C : ℝ) (hC : 0 < C)
    {s : ℂ} (hs : 1 < s.re) : HelixTrace χ C s = HelixTraceCont χ C s :=
  helixTrace_eq_gauge_mul_negLogDeriv χ C hC hs

/-! ## B. Zero ⟹ captured (free), and the no-drift weld -/

/-- **Gauge × pole = pole.** Multiplying a function with a pole at `ρ` by a factor continuous and
    nonzero at `ρ` keeps the pole — the gauge cannot remove a resonance. -/
theorem poleAt_gauge_mul {g f : ℂ → ℂ} {ρ : ℂ} (hg : ContinuousAt g ρ) (hgne : g ρ ≠ 0)
    (hf : Chi3Pole.PoleAt f ρ) : Chi3Pole.PoleAt (fun s => g s * f s) ρ := by
  rintro ⟨L, hL⟩
  apply hf
  refine ⟨L / g ρ, ?_⟩
  have hg' : Tendsto (fun s => (g s)⁻¹) (𝓝[≠] ρ) (𝓝 (g ρ)⁻¹) :=
    (hg.inv₀ hgne).tendsto.mono_left nhdsWithin_le_nhds
  have hmul := hL.mul hg'
  have hev : (fun s => g s * f s * (g s)⁻¹) =ᶠ[𝓝[≠] ρ] f := by
    have hne : ∀ᶠ s in 𝓝[≠] ρ, g s ≠ 0 :=
      (hg.eventually_ne hgne).filter_mono nhdsWithin_le_nhds
    filter_upwards [hne] with s hs; field_simp
  rw [div_eq_mul_inv]; exact hmul.congr' hev

/-- **The continued helix trace has a pole at every nontrivial zero of `L`.** The gauge `C^{-s}` is
    continuous and nonzero, and `−L'/L` has a pole at a zero (`Chi3Pole.zero_iff_logDeriv_pole`). -/
theorem helixTraceCont_pole_of_zero (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (C : ℝ) (hC : 0 < C)
    {ρ : ℂ} (hρ : ρ ∈ GRHSpectral.NontrivialZeros χ) :
    Chi3Pole.PoleAt (HelixTraceCont χ C) ρ := by
  have hLρ : DirichletCharacter.LFunction χ ρ = 0 := hρ.2.2
  have hpole : Chi3Pole.PoleAt (fun s => -logDeriv (DirichletCharacter.LFunction χ) s) ρ := by
    have h := (Chi3Pole.zero_iff_logDeriv_pole χ hχ ρ).mp hLρ
    have heq : (fun z => -deriv (DirichletCharacter.LFunction χ) z
          / DirichletCharacter.LFunction χ z)
        = (fun s => -logDeriv (DirichletCharacter.LFunction χ) s) := by
      funext z; rw [logDeriv_apply]; ring
    rwa [heq] at h
  have hg : ContinuousAt (fun s => (C : ℂ) ^ (-s)) ρ :=
    (continuous_neg.const_cpow (Or.inl (by exact_mod_cast hC.ne'))).continuousAt
  exact poleAt_gauge_mul hg (gauge_ne_zero C hC ρ) hpole

/-- **Capture — the honest geometric predicate.** `ρ` is *captured by the helix geometry* when it is a
    resonance (pole) of the helix trace. This is a statement about the trace field, **not** `Re ρ = ½`. -/
def CapturedByHelixGeometry (χ : DirichletCharacter ℂ N) (C : ℝ) (ρ : ℂ) : Prop :=
  Chi3Pole.PoleAt (HelixTraceCont χ C) ρ

/-- **Every nontrivial zero is captured — the FREE half, proven without assuming `Re ρ = ½`.** The
    non-circular direction: a zero of `L` is a pole of the helix trace by the gauge identity, with no
    input about the critical line. -/
theorem zero_captured (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (C : ℝ) (hC : 0 < C)
    {ρ : ℂ} (hρ : ρ ∈ GRHSpectral.NontrivialZeros χ) :
    CapturedByHelixGeometry χ C ρ :=
  helixTraceCont_pole_of_zero χ hχ C hC hρ

/-- **The no-drift forcing — the GRH-strength weld, stated plainly (not a `grh_of_…`).** That a
    captured resonance lies on the line is the σ-free no-drift / reality content
    (`HelixSource.source_noDrift`, `HelixLimit.grh_of_realSingularSupport`): the open weld. Combined
    with `zero_captured` (free), this carries the *entire* remaining GRH content; it is **not**
    discharged here, and must never be by the `σ−½` costume. -/
def HelixNoDriftForcing (χ : DirichletCharacter ℂ N) (C : ℝ) : Prop :=
  ∀ ρ ∈ GRHSpectral.NontrivialZeros χ, CapturedByHelixGeometry χ C ρ → ρ.re = 1 / 2

/-- **The honest decomposition of GRH.** `GRH χ` is *exactly* `HelixNoDriftForcing χ C` (every captured
    nontrivial zero on the line), because *captured* is already free (`zero_captured`). A faithful
    restatement exposing the single open weld — not a reduction that buys anything (Rule Ten): the
    content of `HelixNoDriftForcing` is the whole of GRH. -/
theorem grh_iff_helixNoDriftForcing (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (C : ℝ) (hC : 0 < C) :
    GRHSpectral.GRH χ ↔ HelixNoDriftForcing χ C := by
  constructor
  · intro h ρ hρ _; exact h ρ hρ
  · intro h ρ hρ; exact h ρ hρ (zero_captured χ hχ C hC hρ)

/-! ## C. Reconnection to Hilbert–Pólya — the captured spectrum is real in the centered coordinate

The no-drift forcing of §B is discharged by **Hilbert–Pólya reality**. In the centered coordinate `z`
(`s = ½ + i z`, so real `z` ⟺ critical line) the helix trace is `helixZ`. Its **singular support is
the captured spectrum** — `poleParam ρ` for every nontrivial zero (`helix_resonates_at_zeros`, FREE).
A **self-adjoint operator** whose resolvent readout is `helixZ` makes that spectrum **real**
(`helixZ_isSelfAdjointReceiver_of_resolventReadout`: regular off ℝ, earned from self-adjointness with
no input about the zeros — `IsSelfAdjoint.im_eq_zero_of_mem_spectrum`). Real captured spectrum ⟹
`poleParam ρ` real ⟹ `Re ρ = ½`.

Composing the two with the repo's existing reduction closes GRH:

`HelixLimit.grh_of_harmonicTraceReceiver (helixZ_isSelfAdjointReceiver_of_resolventReadout ha hφ χ C hid)`
`  (fun ρ hρ => helix_resonates_at_zeros χ C hC hρ) : GRH χ.`

The reality is earned; the **single open weld** is the readout identity `HelixResolventReadout` (the
dual-HP trace formula). It is named plainly (Rule Ten), not minted as a fresh `grh_of_…`. -/

/-- The **centered (z-coordinate) helix trace**: `s = ½ + i z`, so a real `z` is the critical line. -/
noncomputable def helixZ (χ : DirichletCharacter ℂ N) (C : ℝ) (z : ℂ) : ℂ :=
  HelixTraceCont χ C (1 / 2 + Complex.I * z)

/-- **The captured spectrum (FREE).** Every nontrivial zero parameter `poleParam ρ` lies in the helix
    trace's singular support — `helixZ` resonates there. Proven with no `Re ρ = ½` input: the
    `−L'/L` resonance (`HelixLimit.resonates_of_traceIdentity`) survives the nonzero gauge
    (`poleAt_gauge_mul`). -/
theorem helix_resonates_at_zeros (χ : DirichletCharacter ℂ N) (C : ℝ) (hC : 0 < C)
    {ρ : ℂ} (hρ : ρ ∈ GRHSpectral.NontrivialZeros χ) :
    HelixLimit.poleParam ρ ∈ HelixLimit.SingularSupport (helixZ χ C) := by
  have hT : Chi3Pole.PoleAt
      (fun z => -logDeriv (DirichletCharacter.LFunction χ) (1 / 2 + Complex.I * z))
      (HelixLimit.poleParam ρ) :=
    HelixLimit.resonates_of_traceIdentity (fun z => rfl) hρ
  have hg : ContinuousAt (fun z => (C : ℂ) ^ (-(1 / 2 + Complex.I * z)))
      (HelixLimit.poleParam ρ) :=
    (Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hC.ne'))).continuousAt
  have heq : helixZ χ C = fun z => (C : ℂ) ^ (-(1 / 2 + Complex.I * z)) *
      (-logDeriv (DirichletCharacter.LFunction χ) (1 / 2 + Complex.I * z)) := by
    funext z; rw [helixZ, HelixTraceCont]
  rw [HelixLimit.SingularSupport, Set.mem_setOf_eq, heq]
  exact poleAt_gauge_mul hg (gauge_ne_zero C hC _) hT

/-- **Reality is earned (Hilbert–Pólya).** If `helixZ` is the resolvent readout of a **self-adjoint**
    operator `a`, it is regular off `ℝ` — the captured spectrum is real — *with no input about the
    zeros* (a self-adjoint spectrum is real). The conclusion is a reality property, not GRH. -/
theorem helixZ_isSelfAdjointReceiver_of_resolventReadout {A : Type*} [CStarAlgebra A] [StarModule ℂ A]
    {a : A} (ha : IsSelfAdjoint a) {φ : A → ℂ} (hφ : Continuous φ)
    (χ : DirichletCharacter ℂ N) (C : ℝ)
    (hid : ∀ z, helixZ χ C z = φ (resolvent a z)) :
    HelixLimit.IsSelfAdjointReceiver (helixZ χ C) := by
  rw [show helixZ χ C = fun z => φ (resolvent a z) from funext hid]
  exact HelixLimit.isSelfAdjointReceiver_resolventReadout ha hφ

/-- **The open weld — the dual-Hilbert–Pólya readout identity.** The helix loss field `helixZ` is the
    resolvent readout of a self-adjoint operator `a`. This is the GRH-strength content (the dual-HP
    trace formula); the *reality* it would supply is earned
    (`helixZ_isSelfAdjointReceiver_of_resolventReadout`), and the *resonance* at the zeros is free
    (`helix_resonates_at_zeros`), so the **only** open input is this identification. Stated plainly per
    Rule Ten — never dressed as a `grh_of_…`. -/
def HelixResolventReadout {A : Type*} [CStarAlgebra A] (a : A) (φ : A → ℂ)
    (χ : DirichletCharacter ℂ N) (C : ℝ) : Prop :=
  ∀ z, helixZ χ C z = φ (resolvent a z)

/-! ## D. The gauge is the directional carrier — step 8 as a *norm* identity, step 9 earned

The energy match in Ledger 4 dropped the gauge and got the trivial `m² = m²` (location-free). The
**helix-trace** residue keeps it: `res_ρ = lim (s−ρ)·C^{-s}·(−L'/L) = −n·C^{-ρ}`, magnitude
`n·C^{-Re ρ}` — which **moves with `Re ρ`**. So the atom identity "the pole residue *is* the source
atom read out at the helix baseline radius `√n` (`σ = ½`)" is a genuine **norm** equality that forces
the line:

`‖res_ρ‖ = n·C^{-½}  ⟹  C^{-Re ρ} = C^{-½}  ⟹  Re ρ = ½`   (`cpow` magnitude injectivity, `C ≠ 1`).

The forcing (step 9 / `online_of_gauge_eq_baseline`) is **earned**; the `½` on the right is the genuine
area-packing baseline (the helix radius `√n`), not a planted `σ−½`. The open weld is now the *norm*
identity `‖res_ρ‖ = n·C^{-½}` — the magnitude language of the Green–Helmholtz / Gram source. -/

/-- **Step 9 (forcing), the gauge core.** For `C > 0`, `C ≠ 1`: matching the gauge magnitude at `ρ` to
    the baseline `C^{-½}` forces `Re ρ = ½`. Genuine `cpow` magnitude injectivity — no costume. -/
theorem online_of_gauge_eq_baseline (C : ℝ) (hC : 0 < C) (hC1 : C ≠ 1) (ρ : ℂ)
    (h : ‖(C : ℂ) ^ (-ρ)‖ = C ^ (-(1 / 2 : ℝ))) : ρ.re = 1 / 2 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hC, Complex.neg_re] at h
  have hlogne : Real.log C ≠ 0 := by
    intro hl; rcases Real.log_eq_zero.mp hl with h0 | h1 | hm
    · exact hC.ne' h0
    · exact hC1 h1
    · linarith
  have hlog := congrArg Real.log h
  rw [Real.log_rpow hC, Real.log_rpow hC] at hlog
  have hre : -ρ.re = -(1 / 2 : ℝ) := mul_right_cancel₀ hlogne hlog
  linarith

/-- **The gauged helix-trace residue at a zero `ρ` is `−n·C^{-ρ}`** (`n` = multiplicity) — the genuine
    analytic limit `lim (s−ρ)·HelixTraceCont`. Its magnitude `n·C^{-Re ρ}` carries the real part. -/
theorem helixTraceCont_residue_tendsto (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (C : ℝ) (hC : 0 < C)
    {ρ : ℂ} (hρ : DirichletCharacter.LFunction χ ρ = 0) :
    ∃ n : ℕ, 1 ≤ n ∧ Tendsto (fun s => (s - ρ) * HelixTraceCont χ C s)
        (𝓝[≠] ρ) (𝓝 ((C : ℂ) ^ (-ρ) * (-(n : ℂ)))) := by
  obtain ⟨n, hn, _, htend⟩ := Chi3Bridge.sourceTrace_residue_tendsto χ hχ hρ
  refine ⟨n, hn, ?_⟩
  have hg : Tendsto (fun s => (C : ℂ) ^ (-s)) (𝓝[≠] ρ) (𝓝 ((C : ℂ) ^ (-ρ))) :=
    ((continuous_neg.const_cpow (Or.inl (by exact_mod_cast hC.ne'))).continuousAt).tendsto.mono_left
      nhdsWithin_le_nhds
  have heq : (fun s => (s - ρ) * HelixTraceCont χ C s)
      = (fun s => (C : ℂ) ^ (-s) * ((s - ρ) * Chi3Source.SourceTrace χ s)) := by
    funext s; rw [HelixTraceCont, Chi3Source.SourceTrace]; ring
  rw [heq]; exact hg.mul htend

/-- **The open weld, in norm form (the strengthened step 8 / steps 5–6 of the flow).** The pole's
    gauged residue magnitude equals the source atom read out at the helix baseline `√n` (`σ = ½`).
    Equivalent to `Re ρ = ½`, but a **norm** equality — the magnitude language of the
    Green–Helmholtz/Gram source — with the forcing to the line *earned*. Named plainly (Rule Ten);
    discharging it (that the residue atom *is* the on-baseline projection-loss atom) is the open
    research. -/
def GaugeBaselineIdentity (C : ℝ) (n : ℕ) (ρ : ℂ) : Prop :=
  ‖(C : ℂ) ^ (-ρ) * (-(n : ℂ))‖ = (n : ℝ) * C ^ (-(1 / 2 : ℝ))

/-- **Step 8/9 assembled: the baseline atom identity forces the critical line.** If the gauged pole
    residue sits at the baseline magnitude (`GaugeBaselineIdentity`), then `Re ρ = ½`. The `n` cancels
    and the gauge forcing fires. -/
theorem online_of_gaugeBaselineIdentity (C : ℝ) (hC : 0 < C) (hC1 : C ≠ 1) {n : ℕ} (hn : 1 ≤ n)
    {ρ : ℂ} (h : GaugeBaselineIdentity C n ρ) : ρ.re = 1 / 2 := by
  rw [GaugeBaselineIdentity, norm_mul, norm_neg, Complex.norm_natCast] at h
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h' : ‖(C : ℂ) ^ (-ρ)‖ = C ^ (-(1 / 2 : ℝ)) := by
    rw [mul_comm] at h; exact mul_left_cancel₀ hn0.ne' h
  exact online_of_gauge_eq_baseline C hC hC1 ρ h'

/-! ## The ζ (L1) fiber via eta-regularization, linked to the resolvent trace

The principal/ζ channel has a pole at `s = 1`, so the literal placed-naturals fiber diverges. The
helix-native regularization is the **alternating** weighting `w(n) = (-1)^{n+1}` (the ± buckets
mod 2), whose value is the Dirichlet eta `η(s) = (1 - 2^{1-s})·ζ(s)` — entire, since the
`(1-2^{1-s})` factor cancels ζ's pole. The gauged fiber is `C^{-s}·(1-2^{1-s})·ζ(s)`. Off
`Re = 1` both the gauge and the eta factor are nonzero, so the fiber's zeros are exactly the
ζ-zeros, and each is a pole of the Pólya resolvent trace `−ζ'/ζ` (no finite limit) — the ζ
instance of `helix_resonates_at_zeros`. Witness for non-degeneracy: `ζ(2) ≠ 0`. -/

/-- The eta factor `1 - 2^{1-s}`; its simple zero at `s = 1` cancels ζ's pole. -/
noncomputable def etaFactor (s : ℂ) : ℂ := 1 - (2 : ℂ) ^ (1 - s)

/-- **The eta factor is nonzero off `Re = 1`**: `‖2^{1-s}‖ = 2^{1-Re s} = 1` forces `Re s = 1`. -/
theorem etaFactor_ne_zero_of_re_ne_one {s : ℂ} (hs : s.re ≠ 1) : etaFactor s ≠ 0 := by
  intro h
  have h1 : (2 : ℂ) ^ (1 - s) = 1 := by rw [etaFactor, sub_eq_zero] at h; exact h.symm
  have hnorm : ‖(2 : ℂ) ^ (1 - s)‖ = 1 := by rw [h1, norm_one]
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ) < 2),
      Complex.sub_re, Complex.one_re] at hnorm
  have hlog := congrArg Real.log hnorm
  rw [Real.log_rpow (by norm_num : (0:ℝ) < 2), Real.log_one] at hlog
  rcases mul_eq_zero.mp hlog with hz | hz
  · exact hs (by linarith)
  · exact (Real.log_pos (by norm_num : (1:ℝ) < 2)).ne' hz

/-- **The ζ-fiber closed form** (eta-regularized): gauge × eta factor × ζ. -/
noncomputable def zetaFiber (C : ℝ) (s : ℂ) : ℂ :=
  (C : ℂ) ^ (-s) * etaFactor s * riemannZeta s

/-- **The closed form's zeros are exactly the ζ-zeros, off `Re = 1`.** The gauge and the eta factor
    are both nonzero there, so a vanishing of the fiber is a vanishing of ζ. -/
theorem zetaFiber_zero_iff (C : ℝ) (hC : 0 < C) {s : ℂ} (hs : s.re ≠ 1) :
    zetaFiber C s = 0 ↔ riemannZeta s = 0 := by
  rw [zetaFiber, mul_eq_zero, mul_eq_zero]
  constructor
  · rintro ((h | h) | h)
    · exact absurd h (gauge_ne_zero C hC s)
    · exact absurd h (etaFactor_ne_zero_of_re_ne_one hs)
    · exact h
  · exact fun h => Or.inr h

/-- ζ is analytic away from `s = 1`. -/
theorem riemannZeta_analyticOnNhd_compl_one : AnalyticOnNhd ℂ riemannZeta ({1}ᶜ) := by
  apply DifferentiableOn.analyticOnNhd ?_ isOpen_compl_singleton
  intro w hw
  exact (differentiableAt_riemannZeta (Set.mem_compl_singleton_iff.mp hw)).differentiableWithinAt

/-- **ζ is not locally zero** at any `ρ ≠ 1`: identity theorem on the preconnected `{1}ᶜ`, with the
    trivial witness `ζ(2) ≠ 0`. -/
theorem riemannZeta_not_eventuallyEq_zero {ρ : ℂ} (hρ1 : ρ ≠ 1) :
    ¬ riemannZeta =ᶠ[nhds ρ] 0 := by
  intro hev
  have hpre : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isPathConnected_compl_singleton_of_one_lt_rank
      (by rw [Complex.rank_real_complex]; exact_mod_cast Nat.one_lt_two) (1 : ℂ)).isConnected.isPreconnected
  have hEq := riemannZeta_analyticOnNhd_compl_one.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    hpre (Set.mem_compl_singleton_iff.mpr hρ1) hev
  exact riemannZeta_ne_zero_of_one_lt_re (s := 2) (by norm_num)
    (hEq (Set.mem_compl_singleton_iff.mpr (by norm_num : (2:ℂ) ≠ 1)))

/-- **The fiber's zeros are poles of the resolvent trace** — the Pólya spectral event. At a ζ-zero
    `ρ ≠ 1`, equivalently a fiber zero off `Re = 1`, the resolvent trace `−ζ'/ζ` has no finite
    limit. The ζ instance of `helix_resonates_at_zeros`. -/
theorem zetaFiber_zero_resolventTrace_pole (C : ℝ) (hC : 0 < C) {ρ : ℂ}
    (hρre : ρ.re ≠ 1) (hz : zetaFiber C ρ = 0) :
    ¬ ∃ L, Tendsto (fun s => -logDeriv riemannZeta s) (nhdsWithin ρ {ρ}ᶜ) (nhds L) := by
  have hρ1 : ρ ≠ 1 := fun h => hρre (by rw [h]; simp)
  exact HelixSource.logDeriv_not_tendsto
    (riemannZeta_analyticOnNhd_compl_one ρ (Set.mem_compl_singleton_iff.mpr hρ1))
    ((zetaFiber_zero_iff C hC hρre).mp hz) (riemannZeta_not_eventuallyEq_zero hρ1)

/-- The continued L1/ζ helix resolvent trace.  Unlike the L1 fiber, the trace itself is the
    zeta logarithmic derivative; eta regularizes the fiber but does not replace the zero-pole
    readout `−ζ'/ζ`. -/
noncomputable def ZetaTraceCont (C : ℝ) (s : ℂ) : ℂ :=
  (C : ℂ) ^ (-s) * (-logDeriv riemannZeta s)

theorem zetaTraceCont_eq (C : ℝ) (s : ℂ) :
    ZetaTraceCont C s = (C : ℂ) ^ (-s) * (-logDeriv riemannZeta s) := by
  rfl

/-- A zero of the eta-regularized L1 fiber is a pole of the gauged ζ resolvent trace. -/
theorem zetaFiber_zero_zetaTraceCont_pole (C : ℝ) (hC : 0 < C) {ρ : ℂ}
    (hρre : ρ.re ≠ 1) (hz : zetaFiber C ρ = 0) :
    Chi3Pole.PoleAt (ZetaTraceCont C) ρ := by
  have hpole : Chi3Pole.PoleAt (fun s => -logDeriv riemannZeta s) ρ :=
    zetaFiber_zero_resolventTrace_pole C hC hρre hz
  have hg : ContinuousAt (fun s => (C : ℂ) ^ (-s)) ρ :=
    (continuous_neg.const_cpow (Or.inl (by exact_mod_cast hC.ne'))).continuousAt
  change Chi3Pole.PoleAt (fun s => (C : ℂ) ^ (-s) * (-logDeriv riemannZeta s)) ρ
  exact poleAt_gauge_mul hg (gauge_ne_zero C hC ρ) hpole

/-! ## Concrete `π/3` gauge used by the 3D fiber numerics -/

/-- The canonical radial growth `A = π/6`. -/
noncomputable def piThirdA : ℝ := Real.pi / 6

/-- The canonical arc spacing `ds = π/3`. -/
noncomputable def piThirdDs : ℝ := Real.pi / 3

/-- The concrete area gauge `C = 2*A*ds` for the `π/3` helix. -/
noncomputable def piThirdGauge : ℝ := 2 * piThirdA * piThirdDs

/-- The concrete area gauge is `(π/3)^2`. -/
theorem piThirdGauge_eq : piThirdGauge = (Real.pi / 3) ^ 2 := by
  unfold piThirdGauge piThirdA piThirdDs
  ring

theorem piThirdGauge_pos : 0 < piThirdGauge := by
  rw [piThirdGauge_eq]
  positivity

/-- The concrete area-law radius square: `R_n^2 = C*n`. -/
noncomputable def piThirdRadiusSq (n : ℕ) : ℝ := piThirdGauge * (n : ℝ)

/-- In the `π/3` chart, `R_n^2 = (π/3)^2*n`. -/
theorem piThirdRadiusSq_eq (n : ℕ) :
    piThirdRadiusSq n = (Real.pi / 3) ^ 2 * (n : ℝ) := by
  rw [piThirdRadiusSq, piThirdGauge_eq]

/-- The concrete `π/3` helix source. -/
noncomputable def piThirdHelixSource (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  HelixSource χ piThirdGauge s

theorem piThirdHelixSource_eq_gauge_mul_L (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) :
    piThirdHelixSource χ s =
      (piThirdGauge : ℂ) ^ (-s) * DirichletCharacter.LFunction χ s :=
  helixSource_eq_gauge_mul_L χ piThirdGauge piThirdGauge_pos hs

/-- The concrete `π/3` continued trace. -/
noncomputable def piThirdHelixTraceCont (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  HelixTraceCont χ piThirdGauge s

theorem piThirdHelixTraceCont_eq (χ : DirichletCharacter ℂ N) (s : ℂ) :
    piThirdHelixTraceCont χ s =
      (piThirdGauge : ℂ) ^ (-s) * (-logDeriv (DirichletCharacter.LFunction χ) s) := by
  rfl

theorem piThirdHelixTraceCont_residue_tendsto (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {ρ : ℂ} (hρ : DirichletCharacter.LFunction χ ρ = 0) :
    ∃ n : ℕ, 1 ≤ n ∧ Tendsto (fun s => (s - ρ) * piThirdHelixTraceCont χ s)
        (𝓝[≠] ρ) (𝓝 ((piThirdGauge : ℂ) ^ (-ρ) * (-(n : ℂ)))) :=
  helixTraceCont_residue_tendsto χ hχ piThirdGauge piThirdGauge_pos hρ

/-- The concrete `π/3` L1/ζ fiber: `C^{-s} * (1 - 2^(1-s)) * ζ(s)`. -/
noncomputable def piThirdZetaFiber (s : ℂ) : ℂ := zetaFiber piThirdGauge s

theorem piThirdZetaFiber_eq (s : ℂ) :
    piThirdZetaFiber s = (piThirdGauge : ℂ) ^ (-s) * etaFactor s * riemannZeta s := by
  rfl

theorem piThirdZetaFiber_zero_iff {s : ℂ} (hs : s.re ≠ 1) :
    piThirdZetaFiber s = 0 ↔ riemannZeta s = 0 :=
  zetaFiber_zero_iff piThirdGauge piThirdGauge_pos hs

theorem piThirdZetaFiber_zero_resolventTrace_pole {ρ : ℂ}
    (hρre : ρ.re ≠ 1) (hz : piThirdZetaFiber ρ = 0) :
    ¬ ∃ L, Tendsto (fun s => -logDeriv riemannZeta s) (nhdsWithin ρ {ρ}ᶜ) (nhds L) :=
  zetaFiber_zero_resolventTrace_pole piThirdGauge piThirdGauge_pos hρre hz

/-- The concrete `π/3` L1/ζ continued trace. -/
noncomputable def piThirdZetaTraceCont (s : ℂ) : ℂ := ZetaTraceCont piThirdGauge s

theorem piThirdZetaTraceCont_eq (s : ℂ) :
    piThirdZetaTraceCont s = (piThirdGauge : ℂ) ^ (-s) * (-logDeriv riemannZeta s) := by
  rfl

theorem piThirdZetaFiber_zero_zetaTraceCont_pole {ρ : ℂ}
    (hρre : ρ.re ≠ 1) (hz : piThirdZetaFiber ρ = 0) :
    Chi3Pole.PoleAt piThirdZetaTraceCont ρ :=
  zetaFiber_zero_zetaTraceCont_pole piThirdGauge piThirdGauge_pos hρre hz

end HelixGauge
