import RequestProject.HelixImaginaryAxis
import RequestProject.HelixMultiplicative

/-!
# The unitary phasor flow — step 2 of the Hilbert–Pólya program, with the fiber/phasor view

The Hilbert–Pólya route, stated correctly (the self-adjointness is *free*, not a weld):

1. the helix Hilbert space — integers as an orthonormal family, `e_n`;
2. **the FTA/Euler-welded phasor dynamics is a unitary flow** `U(t)` — *this file*;
3. its self-adjoint generator (Stone's theorem — *free* from a unitary one-parameter group; absent from
   Mathlib, a real ingredient still to build, Rule Ten);
4. the completed `L`'s real-line standing wave is the spectral determinant / trace readout of `U`;
5. zeros are spectral events of the self-adjoint generator;
6. a self-adjoint spectrum is real ⟹ zeros real ⟹ on the line.

This file builds **2**, with the **two multiplicativities** that make it the right flow:

* `phasorFlow_add` — `U(s+t) = U(s)·U(t)`, the one-parameter group **in time**; its generator (Stone) is
  multiplication by the winding rate `log n`.
* `phasorFlow_mul` — `U(t)(mn) = U(t)(m)·U(t)(n)`, the **FTA / Euler welding across integers**: the
  flow respects the prime skeleton, so the character fibres are the flow's invariant structure.

`U(t)(n) = wind(t,n) = n^{it}` is a `Circle` element (modulus 1), so `U(t)` is unitary. The **fibre /
phasor view** is `lfunction_eq_flowTrace`: the completed/continued `L` is the **`χ`-weighted trace** of
the flow — `L(s,χ) = Σ_n χ(n)·n^{-σ}·U(s.im)(n)⁻¹` — so the standing wave of step 4 is exactly this trace,
and its zeros (step 5) are where the χ-weighted phasor trace closes.

**Honest scope.** This is step 2 (unitary flow) plus the step-4 trace identity for `Re s > 1`. The
self-adjoint generator (step 3) needs Stone's theorem (Mathlib-missing). The substantive weld is step
4→5 *on the line*: that the continued trace's zeros are the generator's spectral events (the
determinant identification), where the deep content lives. The naive generator's spectrum is `{log n}`
(the primes); the zeros are its **resonances** via the trace — that identification is the open work.
-/

open Complex HelixLogFree HelixImaginaryAxis

namespace HelixFlow

variable {N : ℕ} [NeZero N]

/-- The **unitary phasor flow**: `U(t)` winds integer `n` by `wind(t,n) = n^{it}`, a `Circle` element
    (modulus 1), so `U(t)` is unitary on the helix Hilbert space. -/
noncomputable def phasorFlow (t : ℝ) (n : ℕ) : Circle := wind (fun p => t * Real.log p) n

/-- Identity of the flow at `t = 0`: `U(0) = 1`. -/
theorem phasorFlow_zero (n : ℕ) : phasorFlow 0 n = 1 := by
  simp [phasorFlow, wind, windAngle, Finsupp.sum]

/-- **One-parameter group in time:** `U(s+t) = U(s)·U(t)`. The self-adjoint generator (Stone) lives
    here — `U(t) = e^{it·log n}`, generator = multiplication by the winding rate `log n`. -/
theorem phasorFlow_add (s t : ℝ) (n : ℕ) (hn : n ≠ 0) :
    phasorFlow (s + t) n = phasorFlow s n * phasorFlow t n := by
  unfold phasorFlow wind
  rw [windAngle_log_bridge (s + t) n hn, windAngle_log_bridge s n hn, windAngle_log_bridge t n hn,
      ← Circle.exp_add]
  congr 1; ring

/-- **FTA / Euler welding across integers:** `U(t)(mn) = U(t)(m)·U(t)(n)`. The flow respects the prime
    skeleton — the character fibres are its invariant structure. -/
theorem phasorFlow_mul (t : ℝ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    phasorFlow t (m * n) = phasorFlow t m * phasorFlow t n :=
  wind_mul _ hm hn

/-- Explicit form: `U(t)(n) = n^{it}`. -/
theorem phasorFlow_eq_cpow (t : ℝ) (n : ℕ) (hn : n ≠ 0) :
    (phasorFlow t n : ℂ) = (n : ℂ) ^ (I * t) :=
  wind_eq_cpow t n hn

/-- **The fibre/phasor trace readout (step 4).** For `Re s > 1`, the `L`-function is the **`χ`-weighted
    trace of the flow**: `L(s,χ) = Σ_n χ(n)·(n^σ)⁻¹·U(s.im)(n)⁻¹`. The character `χ` weights the fibres;
    the flow `U(s.im)` supplies the phasors. The standing wave is this trace; its zeros (step 5) are the
    heights where the χ-weighted phasor trace closes. -/
theorem lfunction_eq_flowTrace (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.LFunction χ s
      = ∑' n : ℕ, χ (n : ZMod N) * (((n : ℝ) ^ s.re : ℝ) : ℂ)⁻¹ * ((phasorFlow s.im n : ℂ))⁻¹ :=
  lfunction_eq_phasorSum χ hs

/-! ## The welded flow IS exactly the Dirichlet fibre the L-functions use

The character-twisted flow `χ(n)·U(t)(n)` is — *definitionally* — `HelixMult.helixChar`, the
completely-multiplicative Dirichlet term `χ(n)·wind(t,n)` the genuine `L`-function is built from. Its
trace is the genuine Mathlib `DirichletCharacter.LFunction` (`lfunction_eq_flowTrace`), and its
prime-factorisation is the Euler product (`HelixMult.helixSource_eq_eulerProduct`). So the FTA/Euler
welding of the flow is *not a lookalike* — it is the Dirichlet fibre itself. -/

/-- **The welded flow's fibre IS the Dirichlet fibre `helixChar`**, the same object: `χ(n)·U(t)(n) =
    helixChar χ (t·log) n = χ(n)·wind(t,n)`. -/
theorem charFlow_eq_dirichletFibre (χ : DirichletCharacter ℂ N) (t : ℝ) (n : ℕ) :
    χ (n : ZMod N) * (phasorFlow t n : ℂ) = HelixMult.helixChar χ (fun p => t * Real.log p) n := rfl

/-- **The fibre is completely multiplicative** — `Ψ(mn) = Ψ(m)·Ψ(n)` (`HelixMult.helixChar_mul`): the
    Euler/FTA welding, identical to the L-function's prime factorisation. -/
theorem charFlow_mul (χ : DirichletCharacter ℂ N) (t : ℝ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    χ ((m * n : ℕ) : ZMod N) * (phasorFlow t (m * n) : ℂ)
      = (χ (m : ZMod N) * (phasorFlow t m : ℂ)) * (χ (n : ZMod N) * (phasorFlow t n : ℂ)) := by
  show HelixMult.helixChar χ _ (m * n) = HelixMult.helixChar χ _ m * HelixMult.helixChar χ _ n
  exact HelixMult.helixChar_mul χ _ hm hn

end HelixFlow
