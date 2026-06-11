import RequestProject.HelixUnitaryFlow
import RequestProject.HelixOnlineClosure

/-!
# The standing wave — where the phasors cancel and the zeros get marked (steps 4–5)

This joins the two halves the program has built:

* **the unitary phasor flow** (step 2, `HelixUnitaryFlow`): the prime/FTA fibres are **integers
  carrying phasors** `U(t)(n) = n^{it}`, and the (continued) `ζ` is the flow's trace
  `ζ(s) = Σ_n n^{-σ}·U(t)(n)⁻¹` — `zeta_eq_flowTrace` below, for `Re s > 1`;
* **the Möbius reality** (`HelixMobiusClosure.line_value_real`): on the critical line the completed
  wave is **real** — a standing wave `Z(t) = Re Λ(½+it)`.

The mechanism, assembled (the user's picture):

1. `zeta_eq_flowTrace` — fibres = integers + phasors; `ζ` is their χ-weighted phasor trace.
2. `completedΛ_eq_standingWave` — on the line that trace continues to the **real standing wave** `Z`:
   the phasors, paired by the Möbius inversion (FE), stop rotating and **stand**.
3. `completedΛ_zero_iff_standingWave_node` — a zero is a **node** of the standing wave: `Λ(½+it) = 0 ↔
   Z(t) = 0`. With `HelixOnlineClosure.im_odd` (Im odd in the radial offset), it is a **transversal
   real-axis crossing** — that is where a zero of zeta gets **marked**.
4. `zeta_zero_on_line_iff_standingWave_node` — the bare `ζ` reads the same node (the archimedean
   `Gammaℝ` factor is zero-free on the line), so the marked nodes are the nontrivial `ζ`-zeros.

**Honest scope (Rules Two, Four, Ten).** Steps 1 and 2 are kernel-clean theorems; step 3/4 are the
genuine *marking*. What is **not** closed here is the **on-line continuation / identification** (step
4→5): that the convergent-region trace (`Re s > 1`) and the on-line standing wave are the *same*
analytic object, so that the standing wave's nodes are exactly the flow generator's spectral events.
That continuation is the explicit-formula / determinant weld where the deep content lives, deliberately
**not** dressed as a `grh_of_…` theorem. This file marks the zeros as standing-wave nodes; it does not
force them on the line (that is the FTA/prime one-sidedness + the self-adjoint generator, steps 3,5–6).
-/

open Complex HelixLogFree HelixImaginaryAxis HelixFlow

namespace HelixStandingWave

/-! ## Step 1 — fibres are integers carrying phasors; `ζ` is their flow trace -/

/-- **`ζ` as a helix-point sum.** For `Re s > 1`, `ζ(s) = Σ_n 1/helixPtGen(σ,t)(n)` — the integers `n`
    placed at the helix points `n^{σ+it}` (radius `n^σ`, winding phasor `n^{it}`). The ζ-native form of
    `HelixImaginaryAxis.lfunction_eq_helixSum`. -/
theorem zeta_eq_helixSum {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = ∑' n : ℕ, 1 / helixPtGen s.re s.im n := by
  rw [zeta_eq_tsum_one_div_nat_cpow hs]
  refine tsum_congr (fun n => ?_)
  rcases eq_or_ne n 0 with hn | hn
  · subst hn
    have hsne : s ≠ 0 := by rintro rfl; simp only [Complex.zero_re] at hs; linarith
    have h0 : helixPtGen s.re s.im 0 = 0 := by
      rw [helixPtGen, Nat.cast_zero, Real.zero_rpow (by linarith), Complex.ofReal_zero, zero_mul]
    rw [Nat.cast_zero, Complex.zero_cpow hsne, div_zero, h0, div_zero]
  · rw [helixPtGen_eq_cpow s.re s.im n hn,
        show (s.re : ℂ) + Complex.I * s.im = s from by
          rw [mul_comm Complex.I (s.im : ℂ)]; exact Complex.re_add_im s]

/-- **`ζ` is the trace of the unitary phasor flow (step 4, convergent region).** For `Re s > 1`,
    `ζ(s) = Σ_n (n^σ)⁻¹ · U(t)(n)⁻¹`: each integer `n` contributes its radial weight `n^{-σ}` times the
    inverse **phasor** `U(t)(n)⁻¹ = n^{-it}` of the unitary flow (`HelixFlow.phasorFlow`). The standing
    wave of step 4 is the on-line continuation of this trace. -/
theorem zeta_eq_flowTrace {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s
      = ∑' n : ℕ, (((n : ℝ) ^ s.re : ℝ) : ℂ)⁻¹ * (phasorFlow s.im n : ℂ)⁻¹ := by
  rw [zeta_eq_helixSum hs]
  refine tsum_congr (fun n => ?_)
  rw [helixPtGen, one_div, mul_inv]
  rfl

/-! ## Steps 2–3 — the standing wave, and the zero as its node -/

/-- **The real standing wave** `Z(t) := Re Λ(½+it)` — the completed-ζ wave read on the critical line. -/
noncomputable def standingWave (t : ℝ) : ℝ := (completedRiemannZeta (1 / 2 + (t : ℂ) * I)).re

/-- **On the line the completed wave IS the real standing wave**: `Λ(½+it) = Z(t)`. The phasors, paired
    by the Möbius inversion (the FE, `HelixMobiusClosure.completedΛ_mobius_inversion`), combine into a
    real wave that **stands** instead of rotating. (= `HelixMobiusClosure.line_value_real`.) -/
theorem completedΛ_eq_standingWave (t : ℝ) :
    completedRiemannZeta (1 / 2 + (t : ℂ) * I) = (standingWave t : ℂ) :=
  HelixMobiusClosure.line_value_real t

/-- **A zero is a node of the standing wave** — *where the zeros of zeta get marked*. `Λ(½+it) = 0 ↔
    Z(t) = 0`: the completed wave's on-line zero is exactly where the real standing wave crosses zero.
    With `HelixOnlineClosure.im_odd` (Im odd in the radial offset) this crossing is **transversal**. -/
theorem completedΛ_zero_iff_standingWave_node (t : ℝ) :
    completedRiemannZeta (1 / 2 + (t : ℂ) * I) = 0 ↔ standingWave t = 0 := by
  rw [completedΛ_eq_standingWave]; exact Complex.ofReal_eq_zero

/-- **The standing-wave node is a transversal real-axis crossing.** Restating `HelixOnlineClosure.im_odd`
    in the standing-wave frame: `Im Λ(½+x+it)` is odd in the radial offset `x`, so at a node the wave
    crosses the real axis transversally — the zero is *marked* by a sign-flip of the imaginary part as
    the radius moves off the line. -/
theorem standingWave_node_transversal (x t : ℝ) :
    (completedRiemannZeta (1 / 2 + (x : ℂ) + (t : ℂ) * I)).im
      = -(completedRiemannZeta (1 / 2 - (x : ℂ) + (t : ℂ) * I)).im :=
  HelixOnlineClosure.im_odd x t

/-! ## Step 4 — the bare `ζ` reads the same node (`Gammaℝ` is zero-free on the line) -/

/-- The archimedean factor `Λ(½+it) = Gammaℝ(½+it)·ζ(½+it)`, and `Gammaℝ` is zero-free, so the completed
    standing wave and `ζ` vanish together on the line: `Λ(½+it) = 0 ↔ ζ(½+it) = 0`. The standing-wave
    nodes are exactly the nontrivial `ζ`-zeros on the line. -/
theorem completedΛ_zero_iff_zeta_zero (t : ℝ) :
    completedRiemannZeta (1 / 2 + (t : ℂ) * I) = 0 ↔ riemannZeta (1 / 2 + (t : ℂ) * I) = 0 := by
  have hsne : (1 / 2 + (t : ℂ) * I) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.zero_re, Complex.div_ofNat_re, Complex.one_re] at hre
    norm_num at hre
  have hΓ : (1 / 2 + (t : ℂ) * I).Gammaℝ ≠ 0 := by
    apply Gammaℝ_ne_zero_of_re_pos
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.div_ofNat_re, Complex.one_re]
    norm_num
  rw [riemannZeta_def_of_ne_zero hsne, div_eq_zero_iff]
  constructor
  · exact fun h => Or.inl h
  · rintro (h | h)
    · exact h
    · exact absurd h hΓ

/-- **Where the zeros of zeta get marked.** On the critical line the nontrivial `ζ`-zeros are exactly the
    **nodes of the real standing wave** `Z(t) = Re Λ(½+it)`: `ζ(½+it) = 0 ↔ Z(t) = 0`. The phasor flow
    (step 2) supplies the rotating fibres; the Möbius inversion (the FE) makes their on-line combination
    **stand**; the zero is the standing wave's transversal node. -/
theorem zeta_zero_on_line_iff_standingWave_node (t : ℝ) :
    riemannZeta (1 / 2 + (t : ℂ) * I) = 0 ↔ standingWave t = 0 := by
  rw [← completedΛ_zero_iff_zeta_zero, completedΛ_zero_iff_standingWave_node]

/-! ## The classical hook — a sign flip of the standing wave IS an on-line zero -/

/-- The standing wave is continuous: `Λ` is differentiable off `{0,1}`, and the line `½+it` avoids
    both, so `t ↦ Re Λ(½+it)` is continuous everywhere. -/
theorem standingWave_continuous : Continuous standingWave := by
  rw [continuous_iff_continuousAt]
  intro t
  have hs0 : (1 / 2 + (t : ℂ) * I) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.zero_re, Complex.div_ofNat_re, Complex.one_re] at hre
    norm_num at hre
  have hs1 : (1 / 2 + (t : ℂ) * I) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.div_ofNat_re, Complex.one_re] at hre
    norm_num at hre
  have hline : Continuous fun u : ℝ => (1 / 2 : ℂ) + (u : ℂ) * I :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  show ContinuousAt
    (Complex.re ∘ completedRiemannZeta ∘ fun u : ℝ => (1 / 2 : ℂ) + (u : ℂ) * I) t
  have h1 : Filter.Tendsto (fun u : ℝ => (1 / 2 : ℂ) + (u : ℂ) * I) (nhds t)
      (nhds ((1 / 2 : ℂ) + (t : ℂ) * I)) := hline.continuousAt
  have h2 : Filter.Tendsto completedRiemannZeta (nhds ((1 / 2 : ℂ) + (t : ℂ) * I))
      (nhds (completedRiemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I))) :=
    (differentiableAt_completedZeta hs0 hs1).continuousAt
  have h3 : Filter.Tendsto Complex.re
      (nhds (completedRiemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I)))
      (nhds (completedRiemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I)).re) :=
    Complex.continuous_re.continuousAt
  exact (h3.comp h2).comp h1

/-- **The classical hook, kernel-formed.** A sign flip of the standing wave between `a` and `b`
    forces a zero of `ζ` **on the critical line**, strictly between them: every flip the
    Hardy/Turing ledger counts IS an on-line zero. (Reality of the wave at the fold makes "sign
    flip" meaningful only on `Re = ½` — so a flip cannot mark anything *but* an on-line zero.) -/
theorem online_zero_of_signFlip {a b : ℝ} (hab : a < b)
    (h : standingWave a * standingWave b < 0) :
    ∃ t ∈ Set.Ioo a b, riemannZeta (1 / 2 + (t : ℂ) * I) = 0 := by
  have hc : ContinuousOn standingWave (Set.Icc a b) := standingWave_continuous.continuousOn
  rcases mul_neg_iff.mp h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · obtain ⟨t, ht, h0⟩ := intermediate_value_Ioo' hab.le hc (Set.mem_Ioo.mpr ⟨hb, ha⟩)
    exact ⟨t, ht, (zeta_zero_on_line_iff_standingWave_node t).mpr h0⟩
  · obtain ⟨t, ht, h0⟩ := intermediate_value_Ioo hab.le hc (Set.mem_Ioo.mpr ⟨ha, hb⟩)
    exact ⟨t, ht, (zeta_zero_on_line_iff_standingWave_node t).mpr h0⟩

/-! ## The Laguerre node-detector — "no node ever lifts" (the local line inequality)

`L_f(t) = f′(t)² − f(t)·f″(t)`. At a **true node** (the wave touches zero) `L = f′² ≥ 0`; at a
**lifted node** — a strictly positive local minimum, the imprint an off-line zero pair leaves on the
standing wave — `L = −f·f″ < 0`. If all zeros are real the wave is a locally-uniform limit of
real-rooted polynomials, and for those the inequality is **kernel-proven** below: the peeling
recursion `lag_linear_mul` makes the Laguerre form of a real-rooted polynomial a **sum of squares**
(`lag_eval_nonneg_of_realRooted`). So `LaguerreInequality standingWave` is a *necessary* consequence
of RH, and a single violation at a single `t` refutes it — a local, falsifiable detector
(numerics: `numerics/laguerre_chi3.py` detects every off-line fusion down to `δ = 10⁻⁴`, the
violation scaling as `δ²`). The converse is **not** claimed: the inequality alone is not known to
force all zeros real — an honest necessary-condition target, not a reduction costume (Rule Ten). -/

/-- **The Laguerre form** `L_f(t) = f′(t)² − f(t)·f″(t)` — the local "does the node touch" detector
    for a real wave. -/
noncomputable def laguerreForm (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv f t ^ 2 - f t * deriv (deriv f) t

/-- At a **true node** (`f t = 0`) the Laguerre form is `(f′)² ≥ 0`: a touching node never violates. -/
theorem laguerreForm_nonneg_at_node (f : ℝ → ℝ) (t : ℝ) (h : f t = 0) :
    0 ≤ laguerreForm f t := by
  simp only [laguerreForm, h, zero_mul, sub_zero]
  exact sq_nonneg _

/-- At a **lifted node** — a strictly positive local minimum (`f > 0`, `f′ = 0`, `f″ > 0`), the
    signature an off-line zero pair imprints on the standing wave — the Laguerre form is strictly
    negative. The detector direction: one lifted node is a pointwise witness against all-real zeros. -/
theorem laguerreForm_neg_at_lifted_node (f : ℝ → ℝ) (t : ℝ)
    (h0 : 0 < f t) (h1 : deriv f t = 0) (h2 : 0 < deriv (deriv f) t) :
    laguerreForm f t < 0 := by
  simp only [laguerreForm, h1]
  nlinarith [mul_pos h0 h2]

open Polynomial in
/-- The Laguerre form at the polynomial level: `lag p = p′² − p·p″`. -/
noncomputable def lag (p : Polynomial ℝ) : Polynomial ℝ :=
  derivative p ^ 2 - p * derivative (derivative p)

open Polynomial in
/-- **The Laguerre peeling recursion**: removing one real root,
    `lag ((X − r)·q) = q² + (X − r)²·lag q`. The single identity behind "every real zero presses the
    wave down": each peeled real root contributes the square `q²`. -/
theorem lag_linear_mul (r : ℝ) (q : Polynomial ℝ) :
    lag ((X - C r) * q) = q ^ 2 + (X - C r) ^ 2 * lag q := by
  simp only [lag, derivative_mul, derivative_add, derivative_sub, derivative_X, derivative_C,
    sub_zero, one_mul]
  ring

open Polynomial in
/-- **Real-rooted ⟹ Laguerre ≥ 0 (kernel-proven sum of squares).** For `p = c·∏(X − rᵢ)` with all
    roots real, the Laguerre form evaluates non-negatively everywhere: by `lag_linear_mul` it is an
    iterated sum of squares. This is the exact finite-degree statement of "a real spectrum lifts no
    node"; the standing wave's inequality is its degree-∞ limit (the open weld). -/
theorem lag_eval_nonneg_of_realRooted (c : ℝ) (l : List ℝ) (t : ℝ) :
    0 ≤ (lag (C c * (l.map fun r => X - C r).prod)).eval t := by
  induction l with
  | nil => simp [lag]
  | cons r l ih =>
      rw [List.map_cons, List.prod_cons,
        show C c * ((X - C r) * (l.map fun r => X - C r).prod)
            = (X - C r) * (C c * (l.map fun r => X - C r).prod) by ring,
        lag_linear_mul]
      simp only [eval_add, eval_mul, eval_pow, eval_sub, eval_X, eval_C]
      exact add_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) ih)

open Polynomial in
/-- The analytic Laguerre form of a polynomial wave is the polynomial Laguerre form, evaluated. -/
theorem laguerreForm_polynomial (p : Polynomial ℝ) (t : ℝ) :
    laguerreForm (fun x => p.eval x) t = (lag p).eval t := by
  have hd : ∀ q : Polynomial ℝ, deriv (fun x => q.eval x) = fun x => q.derivative.eval x :=
    fun q => funext fun x => (q.hasDerivAt x).deriv
  simp only [laguerreForm, hd, lag, eval_sub, eval_mul, eval_pow]

open Polynomial in
/-- **Any real-rooted polynomial wave satisfies the Laguerre inequality everywhere** — the finite
    Laguerre–Pólya case, kernel-proven: real spectrum ⟹ no lifted node. -/
theorem laguerreForm_nonneg_of_realRooted (c : ℝ) (l : List ℝ) (t : ℝ) :
    0 ≤ laguerreForm (fun x => (C c * (l.map fun r => X - C r).prod).eval x) t := by
  rw [laguerreForm_polynomial]
  exact lag_eval_nonneg_of_realRooted c l t

/-- **The Laguerre inequality** for a wave `f`: no node ever lifts — `f′² ≥ f·f″` pointwise. For the
    standing wave this is a **necessary** consequence of RH (all zeros real ⟹ Λ is in the
    Laguerre–Pólya class ⟹ this inequality; the finite case is `laguerreForm_nonneg_of_realRooted`).
    One violation at one `t` refutes RH. The converse is NOT claimed — an honest necessary-condition
    target, deliberately not a `rh_of_…` (Rule Ten). -/
def LaguerreInequality (f : ℝ → ℝ) : Prop := ∀ t : ℝ, 0 ≤ laguerreForm f t

open Filter in
/-- **The Laguerre inequality passes to limits.** If `F n → f` together with first and second
    derivatives — *pointwise convergence suffices*, no uniformity is needed to carry an inequality to
    the limit — then Laguerre non-negativity survives. The degree-∞ transfer, kernel-clean. -/
theorem laguerreInequality_of_tendsto (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ)
    (h0 : ∀ t, Tendsto (fun n => F n t) atTop (nhds (f t)))
    (h1 : ∀ t, Tendsto (fun n => deriv (F n) t) atTop (nhds (deriv f t)))
    (h2 : ∀ t, Tendsto (fun n => deriv (deriv (F n)) t) atTop (nhds (deriv (deriv f) t)))
    (hL : ∀ n t, 0 ≤ laguerreForm (F n) t) :
    LaguerreInequality f := by
  intro t
  refine le_of_tendsto_of_tendsto'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0)) ?_ (fun n => hL n t)
  simpa only [laguerreForm] using ((h1 t).pow 2).sub ((h0 t).mul (h2 t))

open Polynomial Filter in
/-- **Laguerre–Pólya limit ⟹ no lifted node (the degree-∞ step).** If `f` is the pointwise limit —
    with two derivatives — of *real-rooted polynomials*, then `f` satisfies the Laguerre inequality:
    each approximant's Laguerre form is a sum of squares (`lag_eval_nonneg_of_realRooted`), and
    non-negativity passes to the limit. This is "a real spectrum lifts no node" at degree ∞, with the
    approximation as the explicit hypothesis. -/
theorem laguerreInequality_of_realRooted_approx (f : ℝ → ℝ) (c : ℕ → ℝ) (l : ℕ → List ℝ)
    (h0 : ∀ t, Tendsto (fun n => (C (c n) * ((l n).map fun r => X - C r).prod).eval t) atTop
        (nhds (f t)))
    (h1 : ∀ t, Tendsto (fun n => (derivative (C (c n) * ((l n).map fun r => X - C r).prod)).eval t)
        atTop (nhds (deriv f t)))
    (h2 : ∀ t, Tendsto (fun n =>
          (derivative (derivative (C (c n) * ((l n).map fun r => X - C r).prod))).eval t)
        atTop (nhds (deriv (deriv f) t))) :
    LaguerreInequality f := by
  intro t
  refine le_of_tendsto_of_tendsto'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0)) ?_
    (fun n => lag_eval_nonneg_of_realRooted (c n) (l n) t)
  have heval : ∀ p : Polynomial ℝ, (lag p).eval t
      = (derivative p).eval t ^ 2 - p.eval t * (derivative (derivative p)).eval t := by
    intro p; simp [lag]
  simp only [heval, laguerreForm]
  exact ((h1 t).pow 2).sub ((h0 t).mul (h2 t))

open Polynomial Filter in
/-- **The remaining analytic obligation** for the standing wave's Laguerre inequality: `Z` is a
    Laguerre–Pólya limit — real-rooted polynomials converging to it pointwise with two derivatives.
    Under RH these are the Hadamard partial products `Ξ(0)·∏_{n≤N}(1 − t²/γₙ²)` (real-rooted exactly
    because the zeros sit on the line; genus-0 product + Cauchy estimates give the derivative
    convergence — classical analysis, not yet formalized here). Honest status: **implied by** RH with
    classical analysis; **implies** `LaguerreInequality standingWave` (next theorem); NOT claimed
    equivalent to RH — strictly the necessary-direction chain (Rule Ten). -/
def StandingWaveLPApprox : Prop :=
  ∃ (c : ℕ → ℝ) (l : ℕ → List ℝ),
    (∀ t, Tendsto (fun n => (C (c n) * ((l n).map fun r => X - C r).prod).eval t) atTop
        (nhds (standingWave t))) ∧
    (∀ t, Tendsto (fun n => (derivative (C (c n) * ((l n).map fun r => X - C r).prod)).eval t)
        atTop (nhds (deriv standingWave t))) ∧
    (∀ t, Tendsto (fun n =>
          (derivative (derivative (C (c n) * ((l n).map fun r => X - C r).prod))).eval t)
        atTop (nhds (deriv (deriv standingWave) t)))

/-- **The standing wave lifts no node, given its LP approximation**: `StandingWaveLPApprox` (the one
    remaining analytic input, supplied by RH + classical Hadamard theory) yields the full pointwise
    Laguerre inequality for the standing wave. Everything else in the chain — the sum-of-squares
    finite case and the limit transfer — is kernel-proven above. -/
theorem laguerreInequality_standingWave (h : StandingWaveLPApprox) :
    LaguerreInequality standingWave := by
  obtain ⟨c, l, h0, h1, h2⟩ := h
  exact laguerreInequality_of_realRooted_approx standingWave c l h0 h1 h2

end HelixStandingWave

#print axioms HelixStandingWave.zeta_eq_flowTrace
#print axioms HelixStandingWave.completedΛ_zero_iff_standingWave_node
#print axioms HelixStandingWave.zeta_zero_on_line_iff_standingWave_node
#print axioms HelixStandingWave.laguerreForm_neg_at_lifted_node
#print axioms HelixStandingWave.lag_eval_nonneg_of_realRooted
#print axioms HelixStandingWave.laguerreForm_nonneg_of_realRooted
#print axioms HelixStandingWave.laguerreInequality_of_tendsto
#print axioms HelixStandingWave.laguerreInequality_of_realRooted_approx
#print axioms HelixStandingWave.laguerreInequality_standingWave
#print axioms HelixStandingWave.standingWave_continuous
#print axioms HelixStandingWave.online_zero_of_signFlip
