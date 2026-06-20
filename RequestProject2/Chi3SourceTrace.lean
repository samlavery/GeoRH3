import Mathlib
import RequestProject.HelixSource
import RequestProject.ChiThreeLogDerivIdentity

/-!
# Ledger 3 (part a) — the source-trace identification

`SourceTrace χ` is the **continued geometric prime-fiber readout** — the analytic object the prime
counter's signed sum `Σ_n χ(n)Λ(n) n^{-s}` continues to. It **is** `−L'/L`:

* `sourceTrace_eq_logDeriv` — `SourceTrace χ s = −L'(s)/L(s)`, for **all** `s` (the readout is the
  log-derivative; this is what "continued" means);
* `sourceTrace_eq_primeTrace` — in the convergence strip `Re s > 1` it agrees with the **actual prime
  sum** `Σ χ(n)Λ(n) n^{-s}` (`HelixSource.neg_logDeriv_LFunction_eq_vonMangoldt`, the von Mangoldt
  identity). This is the geometry→analytic bridge content; outside the strip the prime sum diverges and
  `SourceTrace` is its continuation.

Combined with Ledger 2 (`Chi3Pole.zero_iff_logDeriv_pole`): the source trace poles are exactly the
`L`-zeros. `σ`-free, kernel-clean.
-/

open Complex ArithmeticFunction

namespace Chi3Source

variable {N : ℕ} [NeZero N]

/-- The **continued geometric prime-fiber readout** — `−L'/L`, the analytic continuation of the signed
    prime trace `Σ_n χ(n)Λ(n) n^{-s}`. -/
noncomputable def SourceTrace (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  -logDeriv (DirichletCharacter.LFunction χ) s

/-- **Ledger 3a — the source trace is the log-derivative.** `SourceTrace χ s = −L'(s)/L(s)` for all
    `s`. This is `SourceTrace`'s defining identity (the continued readout *is* `−L'/L`); it carries the
    pole structure of Ledger 2 unchanged. -/
theorem sourceTrace_eq_logDeriv (χ : DirichletCharacter ℂ N) (s : ℂ) :
    SourceTrace χ s
      = -deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s := by
  rw [SourceTrace, logDeriv_apply]; ring

/-- **The geometry→analytic bridge.** In the convergence strip `Re s > 1`, the continued source trace
    agrees with the **actual signed prime sum** `Σ_n χ(n)Λ(n) n^{-s}` — the geometric prime-fiber
    counter. (Outside the strip the prime sum diverges; `SourceTrace` is its analytic continuation.)
    This is the genuine content identifying the geometric readout with the analytic `−L'/L`. -/
theorem sourceTrace_eq_primeTrace (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    SourceTrace χ s = LSeries ((fun n : ℕ => χ ↑n) * fun n => (vonMangoldt n : ℂ)) s := by
  rw [SourceTrace]; exact HelixSource.neg_logDeriv_LFunction_eq_vonMangoldt χ hs

/-- The χ₃ specialization of the source-trace identity. -/
theorem chi3_sourceTrace_eq_logDeriv (s : ℂ) :
    SourceTrace ChiThree.χ3 s
      = -deriv (DirichletCharacter.LFunction ChiThree.χ3) s
        / DirichletCharacter.LFunction ChiThree.χ3 s :=
  sourceTrace_eq_logDeriv ChiThree.χ3 s

end Chi3Source
