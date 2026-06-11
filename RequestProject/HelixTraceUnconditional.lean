import Mathlib
import RequestProject.Chi3SourceTrace

/-!
# Unconditional helix trace identity — the closed form, no capture

`HelixTrace χ C s` reads each integer `n` at its **area-projected** helix scale `(C·n)^{-s}`
(the projection `R(n)² = C·n`), weighted by von Mangoldt × character. Two facts, both
**unconditional and kernel-clean** (no GRH, no `zero_embed`, no hypothesis equivalent to the
conclusion):

* `helixTrace_eq_gauge_logDeriv` — for **all** `s`:  `HelixTrace χ C s = C^{-s}·(−L'/L)(s,χ)`.
* `helixTrace_eq_primeSum` — in the strip `Re s > 1`, it is the **actual helix prime readout**
  `Σ_{n} Λ(n) χ(n) (C·n)^{-s}` (the area-projected source sum).

So the poles of `HelixTrace` are exactly the `L`-zeros (the gauge `C^{-s} ≠ 0` moves nothing).
This is the *identification* — the closed form (Rule Eight: the gauge plumbing), and that is all it is.

**What is NOT here, by design.** The GRH-strength step — "every captured helix pole is no-drift,
hence `Re = ½`" — is *not* a theorem in this repo and is *not* stated as a placeholder `Prop`,
because any honest version of `CapturedByLogFreeHelixWinding` is GRH-equivalent (and the lazy
versions — `radial := σ−½`, or "∃ *some* unitary flow") are costumes that assert the conclusion.
The capture / Hilbert–Pólya spectral realization is exhibited only **numerically**
(`scratch_helix_spectrum.py`): the prime/helix winding's resonance spectrum *is* the zeros, with
GUE spacing and the Weyl density. Unconditional in Lean = the identification; the capture = Python.
-/

open Complex ArithmeticFunction

namespace HelixTraceId

variable {N : ℕ} [NeZero N]

/-- The area-projected helix trace: the gauge-`C^{-s}`-shifted source trace `−L'/L`. -/
noncomputable def HelixTrace (χ : DirichletCharacter ℂ N) (C : ℝ) (s : ℂ) : ℂ :=
  (C : ℂ) ^ (-s) * Chi3Source.SourceTrace χ s

/-- **Unconditional identification (all `s`):** `HelixTrace χ C s = C^{-s}·(−L'/L)(s,χ)`. -/
theorem helixTrace_eq_gauge_logDeriv (χ : DirichletCharacter ℂ N) (C : ℝ) (s : ℂ) :
    HelixTrace χ C s
      = (C : ℂ) ^ (-s)
        * (-deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s) := by
  rw [HelixTrace, Chi3Source.sourceTrace_eq_logDeriv]

/-- **The helix readout is the prime sum (`Re s > 1`):**
    `HelixTrace χ C s = Σ_n Λ(n) χ(n) (C·n)^{-s}` — each prime power placed at its area-projected
    scale. The genuine geometry→analytic content (no GRH). -/
theorem helixTrace_eq_primeSum (χ : DirichletCharacter ℂ N) (C : ℝ) (hC : 0 < C) {s : ℂ}
    (hs : 1 < s.re) :
    HelixTrace χ C s
      = ∑' n : ℕ, (χ ↑n * (vonMangoldt n : ℂ)) * ((C : ℂ) * (n : ℂ)) ^ (-s) := by
  rw [HelixTrace, Chi3Source.sourceTrace_eq_primeTrace χ hs, LSeries, ← tsum_mul_left]
  refine tsum_congr (fun n => ?_)
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term, ArithmeticFunction.map_zero]
  · rw [LSeries.term_of_ne_zero hn, Pi.mul_apply]
    have hcast : (C : ℂ) * (n : ℂ) = ((C : ℝ) : ℂ) * ((n : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, Complex.mul_cpow_ofReal_nonneg hC.le (Nat.cast_nonneg n)]
    push_cast
    simp only [Complex.cpow_neg, div_eq_mul_inv]
    ring

end HelixTraceId
