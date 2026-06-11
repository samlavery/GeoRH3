import Mathlib
import RequestProject.HelixSource
import RequestProject.ChiThreeLogDerivIdentity

/-!
# Ledger 2 — the prime-trace singularity

The **singularity is on the trace side**: a zero of `L(·,χ)` is *exactly* a pole of the log-derivative
`−L'/L`. At a zero of multiplicity `m`, `−L'/L(z) = −m/(z−ρ) + analytic` — it blows up; away from a
zero, `L` is analytic and non-vanishing so `−L'/L` is continuous (a finite limit). So:

`L(s,χ) = 0  ⟺  −L'/L has a pole at s.`

This is the dual of Ledger 1 (`Chi3FibreBalance.chi3_zero_iff_fibre_balance`): the *same* zero is a
fibre **cancellation** on the L-side and a **pole** on the trace side. Character-agnostic, `σ`-free,
kernel-clean. Both directions are earned (forward from `meromorphicOrderAt_logDeriv_neg`, reverse from
continuity of the quotient where the denominator is nonzero).
-/

open Complex Filter Topology

namespace Chi3Pole

variable {N : ℕ} [NeZero N]

/-- A function `f` has a **pole** at `s` — it has no finite limit on the punctured neighbourhood.
    (For a meromorphic `f` this is the genuine pole/essential-singularity dichotomy; here `f = −L'/L`
    is meromorphic, so "no finite limit" *is* "pole".) -/
def PoleAt (f : ℂ → ℂ) (s : ℂ) : Prop := ¬ ∃ L, Tendsto f (𝓝[≠] s) (𝓝 L)

/-- **Generic zero ⟺ logDeriv-pole.** For `f` analytic at `s` and not locally zero, `f(s)=0` exactly
    when `−f'/f` has a pole at `s`. Forward: an isolated zero forces `meromorphicOrderAt (logDeriv f) < 0`,
    so `logDeriv f → cobounded` (`HelixSource.logDeriv_not_tendsto`). Reverse: if `f(s)≠0` the quotient
    `−f'/f` is continuous at `s`, hence has the finite limit `−f'(s)/f(s)`. -/
theorem zero_iff_logDeriv_pole_of_analytic {f : ℂ → ℂ} {s : ℂ}
    (hf : AnalyticAt ℂ f s) (hne : ¬ f =ᶠ[𝓝 s] 0) :
    f s = 0 ↔ PoleAt (fun z => -deriv f z / f z) s := by
  constructor
  · intro hfs
    have h := HelixSource.logDeriv_not_tendsto hf hfs hne
    have hfun : (fun z => -deriv f z / f z) = (fun z => -logDeriv f z) := by
      funext z; rw [logDeriv_apply]; ring
    rw [PoleAt, hfun]; exact h
  · intro hpole
    by_contra hfs
    apply hpole
    have hcont : ContinuousAt (fun z => -deriv f z / f z) s :=
      ((hf.deriv.continuousAt).neg).div hf.continuousAt hfs
    exact ⟨-deriv f s / f s, hcont.tendsto.mono_left nhdsWithin_le_nhds⟩

/-- `L(·,χ)` is **entire** (analytic at every `s`) for a nontrivial `χ ≠ 1`. -/
theorem LFunction_analyticAt (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (s : ℂ) :
    AnalyticAt ℂ (DirichletCharacter.LFunction χ) s := by
  have hdiff : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) Set.univ :=
    fun w _ => (DirichletCharacter.differentiableAt_LFunction χ w (Or.inr hχ)).differentiableWithinAt
  exact (hdiff.analyticOnNhd isOpen_univ) s (Set.mem_univ s)

/-- `L(·,χ)` is **not locally zero** at any `s`, for nontrivial `χ ≠ 1`: it is entire and not
    identically zero (`L(2,χ) ≠ 0`), so by the identity theorem on the preconnected plane it cannot
    vanish on any neighbourhood. -/
theorem LFunction_not_locally_zero (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (s : ℂ) :
    ¬ DirichletCharacter.LFunction χ =ᶠ[𝓝 s] 0 := by
  intro hev
  have hana : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) Set.univ :=
    fun w _ => LFunction_analyticAt χ hχ w
  have hEq := hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ s) hev
  have h2 : DirichletCharacter.LFunction χ 2 = 0 := hEq (Set.mem_univ 2)
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr (by norm_num))
    (by norm_num) h2

/-- **Ledger 2 — the prime-trace singularity (character-agnostic).** For any nontrivial `χ ≠ 1`,
    `L(s,χ) = 0` exactly when `−L'/L` has a pole at `s`. The zero on the L-side **is** the pole on the
    trace side — same point, two ledgers. `σ`-free. -/
theorem zero_iff_logDeriv_pole (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (s : ℂ) :
    DirichletCharacter.LFunction χ s = 0 ↔
      PoleAt (fun z => -deriv (DirichletCharacter.LFunction χ) z
        / DirichletCharacter.LFunction χ z) s :=
  zero_iff_logDeriv_pole_of_analytic (LFunction_analyticAt χ hχ s)
    (LFunction_not_locally_zero χ hχ s)

/-- **The χ₃ specialization.** `L(s,χ₃) = 0 ⟺ −L'/L has a pole at `s`. Combined with
    `Chi3FibreBalance.chi3_zero_iff_fibre_balance`, the same zero is a fibre cancellation (Ledger 1)
    and a trace pole (Ledger 2). -/
theorem chi3_zero_iff_logDeriv_pole (s : ℂ) :
    DirichletCharacter.LFunction ChiThree.χ3 s = 0 ↔
      PoleAt (fun z => -deriv (DirichletCharacter.LFunction ChiThree.χ3) z
        / DirichletCharacter.LFunction ChiThree.χ3 z) s :=
  zero_iff_logDeriv_pole ChiThree.χ3 ChiThree.χ3_ne_one s

end Chi3Pole
