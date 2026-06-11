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

end HelixGauge
