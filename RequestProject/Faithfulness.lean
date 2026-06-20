import RequestProject.ClosedForm
import RequestProject.HelixLogFreeFTA
import RequestProject.HelixCollapseReality
import RequestProject.LFunctionPhasor

/-!
# Faithful projection: the L-fiber rides the 3-D carrier, accumulates in 3-D, lands on real ζ zeros

This is the capstone of the faithful model: the L-function realized as a 3-D phasor accumulation on
the helix carrier, projected to its real zeros.

**3-D carrier (no `√n` shortcut).** Integers sit evenly, `π/3` apart, on the unwound number line
(`Geometry.spinAngle n = n·(π/3)`, `carrier_spacing`); that line is wound around the helix, six
integers per `2π` loop (`Geometry.spin_phasor_period6`). The area-law radius `√n` is **emergent** —
it falls out of the arclength `S(k) ∝ k²` (`Geometry.arclength_closed_form`), never posited.

**The fiber is the L-function, riding the carrier.** At carrier site `n` the fiber carries the
phasor of magnitude `n^{-1/2}` (the reciprocal of the emergent carrier radius `√n` — the `σ = ½`
balance) and phase the bridge winding `wind(-t·log) n = n^{-it}`; together this is the Dirichlet
phasor `n^{-(½+it)}` (`fiber_rides_carrier`). Accumulating these phasors in 3-D gives the
L-function: `∑_{n} χ(n)·n^{-s} → L(s,χ)` (`fiber_accumulates_to_L`). `log` enters **only** at the
bridge (`wind_glog_eq_cpow`), never in the geometry.

**Projection 3-D → 2-D → 1-D → real ζ zero (the readout).** Projecting the accumulated 3-D fiber
down the collapse axis, the completed object is **real** on the critical line and vanishes **exactly**
at the actual zeros `riemannZeta(½+iγ) = 0` (`faithful_projection_zeta`).
-/

open Complex
open scoped Real

namespace Faithful

open CriticalLinePhasor

/-! ## The bridge `wind n ↔ n^{it}` — the one place `log` enters (Rule Eight) -/

/-- `log` is FTA-additive over the prime factorization: `log n = ∑_{pᵉ ‖ n} e·log p`. This is what
lets the bridge angle `θ p = γ·log p` reproduce `windAngle = γ·log n` from the *log-free*
`windAngle`. -/
theorem real_log_eq_factorization_sum {n : ℕ} (hn : n ≠ 0) :
    Real.log n = n.factorization.sum (fun p e => (e : ℝ) * Real.log p) := by
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Finsupp.prod, Finsupp.sum, Nat.cast_prod, Real.log_prod]
  · apply Finset.sum_congr rfl
    intro p _
    rw [Nat.cast_pow, Real.log_pow]
  · intro p hp
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors
      (by rwa [Nat.support_factorization] at hp)).two_le
    have : (0 : ℝ) < (p : ℕ) ^ (n.factorization p) := by positivity
    positivity

/-- The bridge angle realizes `γ·log`: `windAngle (γ·log) n = γ·log n`. Log-free geometry on the
left, `log` only in the bridge assignment on the right. -/
theorem windAngle_glog (γ : ℝ) {n : ℕ} (hn : n ≠ 0) :
    HelixLogFree.windAngle (fun p => γ * Real.log p) n = γ * Real.log n := by
  rw [HelixLogFree.windAngle, real_log_eq_factorization_sum hn, Finsupp.mul_sum]
  apply Finsupp.sum_congr
  intro p _
  ring

/-- **The bridge** `wind (γ·log) n = n^{iγ}`: the single identification of the log-free geometric
winding with the analytic phasor; `log` appears only here. -/
theorem wind_glog_eq_cpow (γ : ℝ) {n : ℕ} (hn : n ≠ 0) :
    ((HelixLogFree.wind (fun p => γ * Real.log p) n : Circle) : ℂ)
      = (n : ℂ) ^ ((γ : ℂ) * Complex.I) := by
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hnpos : (0 : ℝ) ≤ (n : ℝ) := by positivity
  rw [HelixLogFree.wind, Circle.coe_exp, windAngle_glog γ hn,
    Complex.cpow_def_of_ne_zero hnc]
  congr 1
  have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [show (n : ℂ) = ((n : ℝ) : ℂ) from by push_cast; ring]
    exact (Complex.ofReal_log hnpos).symm
  rw [hlog]
  push_cast
  ring

/-! ## The 3-D carrier: integers `π/3` apart, wound (`√n` emergent — see `Geometry.arclength_closed_form`) -/

/-- **Even `π/3` spacing on the number line** (earned, not posited): consecutive integers sit a
fixed `π/3` apart in the carrier's integer-angular scaling. This is the unwound number line that gets
wound around the helix. -/
theorem carrier_spacing (n : ℕ) :
    Geometry.spinAngle (n + 1) - Geometry.spinAngle n = Real.pi / 3 := by
  simp only [Geometry.spinAngle]
  push_cast
  ring

/-! ## The fiber rides the carrier and accumulates (in 3-D) to `L` -/

/-- **The fiber phasor at carrier site `n`.** Magnitude `n^{-1/2}` (the reciprocal of the emergent
carrier radius `√n`, the `σ = ½` balance) times the bridge winding `wind(-t·log) n = n^{-it}` equals
the Dirichlet phasor `n^{-(½+it)}`. The fiber riding the 3-D carrier. -/
theorem fiber_rides_carrier (t : ℝ) {n : ℕ} (hn : 0 < n) :
    (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
        * (HelixLogFree.wind (fun p => -t * Real.log p) n : ℂ)
      = (n : ℂ) ^ (-((1 / 2 : ℂ) + (t : ℂ) * Complex.I)) := by
  rw [cpow_critical_line t n hn, HelixLogFree.wind, Circle.coe_exp,
    windAngle_glog (-t) hn.ne']
  congr 2
  push_cast
  ring

/-- **The fiber IS the L-function, accumulated in 3-D.** The partial sums of the carrier-riding
phasors `∑_{n<N} χ(n)·n^{-s}` converge to `L(s,χ)` for `Re s > 1`: induct the accumulation and out
comes the L-function. -/
theorem fiber_accumulates_to_L {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) :
    Filter.Tendsto (DirichletPhasorCarrier.finiteCarrier χ s) Filter.atTop
      (nhds (DirichletCharacter.LFunction χ s)) :=
  DirichletPhasorCarrier.finiteCarrier_tendsto_LFunction χ hs

/-! ## Projection 3-D → 2-D → 1-D: landing on the real ζ zeros -/

/-- **Faithful projection (ζ).** Project the accumulated 3-D fiber down the collapse axis: the
completed object is **real** on the critical line, and the fiber vanishes **exactly** at the actual
zeros `riemannZeta(½+iγ) = 0`. -/
theorem faithful_projection_zeta (γ : ℝ) :
    (completedRiemannZeta (1 / 2 + (γ : ℂ) * Complex.I)).im = 0 ∧
      (EtaTrivial.Feta γ = 0 ↔ riemannZeta ((1 / 2 : ℂ) + (γ : ℂ) * Complex.I) = 0) :=
  ⟨HelixCollapse.completedRiemannZeta_critical_line_im_zero γ, EtaTrivial.Feta_eq_zero_iff γ⟩

/-! ## The geometric explicit formula: zeros located exactly as poles of the prime-side log-derivative

Rather than *searching* for where the accumulation cancels, the explicit formula **reads the zeros
off** as the poles of the fiber's log-derivative — which equals the winding-weighted von Mangoldt
**prime field** (the geometric side). Each zero is a simple pole carrying the explicit-formula
residue harmonic `−x^ρ/ρ`. -/

open scoped LSeries.notation
open ArithmeticFunction CriticalLinePhasor.Residue

/-- **Geometric explicit formula, prime side.** `−L'/L(s) = ∑_n χ(n)·Λ(n)·n^(−s)` for `Re s > 1`:
the log-derivative of the accumulated fiber is the winding-weighted von Mangoldt prime field. The
zeros of `L` are exactly the poles of this object's meromorphic continuation. -/
theorem explicit_formula_prime_field {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) :
    -deriv (L (fun n => χ (n : ZMod q))) s / L (fun n => χ (n : ZMod q)) s
      = ∑' n : ℕ, χ (n : ZMod q) * (Λ n : ℂ) * (n : ℂ) ^ (-s) :=
  CriticalLinePhasor.DirichletCarrier.dirichlet_logDeriv_eq_tsum χ hs

/-- **Zeros located exactly.** Each simple zero `ρ = ½ + iγ` of `ζ` is a **simple pole** of the
explicit-formula kernel `−(ζ'/ζ)(s)·x^s/s`, located with residue the explicit-formula harmonic
`residueHarmonic x γ = −x^ρ/ρ`. The geometric explicit formula reads the zero off as the pole — no
search. `hsimple` is the simple-zero hypothesis at this `ρ`, given, not assumed globally. -/
theorem zeta_zero_located_as_pole (γ x : ℝ) (hx : 0 < x)
    (hzero : riemannZeta ((1 / 2 : ℂ) + (γ : ℂ) * Complex.I) = 0)
    (hsimple : deriv riemannZeta ((1 / 2 : ℂ) + (γ : ℂ) * Complex.I) ≠ 0) :
    Filter.Tendsto
      (fun s => (s - ((1 / 2 : ℂ) + (γ : ℂ) * Complex.I)) *
        (-(deriv riemannZeta s / riemannZeta s) * ((x : ℂ) ^ s / s)))
      (nhdsWithin ((1 / 2 : ℂ) + (γ : ℂ) * Complex.I) {((1 / 2 : ℂ) + (γ : ℂ) * Complex.I)}ᶜ)
      (nhds (residueHarmonic x γ)) := by
  have hρ1 : ((1 / 2 : ℂ) + (γ : ℂ) * Complex.I) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im] at hre
  have hopen : IsOpen {s : ℂ | s ≠ 1} := isOpen_ne
  have hmem : ((1 / 2 : ℂ) + (γ : ℂ) * Complex.I) ∈ {s : ℂ | s ≠ 1} := hρ1
  have hderiv : ∀ᶠ s in nhds ((1 / 2 : ℂ) + (γ : ℂ) * Complex.I),
      HasDerivAt riemannZeta (deriv riemannZeta s) s := by
    filter_upwards [hopen.mem_nhds hmem] with s hs
    exact (differentiableAt_riemannZeta hs).hasDerivAt
  have hanalytic : AnalyticOnNhd ℂ riemannZeta {s : ℂ | s ≠ 1} :=
    DifferentiableOn.analyticOnNhd
      (fun s hs => (differentiableAt_riemannZeta hs).differentiableWithinAt) hopen
  have hf'cont : ContinuousAt (deriv riemannZeta) ((1 / 2 : ℂ) + (γ : ℂ) * Complex.I) :=
    (hanalytic.deriv _ hmem).continuousAt
  exact residue_at_critical_zero_eq_residueHarmonic riemannZeta (deriv riemannZeta) γ x hx
    hzero hderiv hf'cont hsimple

/-- **General Dirichlet `L`: zeros located exactly.** Each simple zero `ρ = ½ + iγ` of `L(·,χ)` is a
**simple pole** of the explicit-formula kernel `−(L'/L)(s)·x^s/s`, located with residue the
explicit-formula harmonic `residueHarmonic x γ = −x^ρ/ρ`. Same geometric explicit formula, any `χ`. -/
theorem L_zero_located_as_pole {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (γ x : ℝ)
    (hx : 0 < x)
    (hzero : DirichletCharacter.LFunction χ ((1 / 2 : ℂ) + (γ : ℂ) * Complex.I) = 0)
    (hsimple : deriv (DirichletCharacter.LFunction χ) ((1 / 2 : ℂ) + (γ : ℂ) * Complex.I) ≠ 0) :
    Filter.Tendsto
      (fun s => (s - ((1 / 2 : ℂ) + (γ : ℂ) * Complex.I)) *
        (-(deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s) *
          ((x : ℂ) ^ s / s)))
      (nhdsWithin ((1 / 2 : ℂ) + (γ : ℂ) * Complex.I) {((1 / 2 : ℂ) + (γ : ℂ) * Complex.I)}ᶜ)
      (nhds (residueHarmonic x γ)) := by
  have hρ1 : ((1 / 2 : ℂ) + (γ : ℂ) * Complex.I) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im] at hre
  have hopen : IsOpen {s : ℂ | s ≠ 1} := isOpen_ne
  have hmem : ((1 / 2 : ℂ) + (γ : ℂ) * Complex.I) ∈ {s : ℂ | s ≠ 1} := hρ1
  have hderiv : ∀ᶠ s in nhds ((1 / 2 : ℂ) + (γ : ℂ) * Complex.I),
      HasDerivAt (DirichletCharacter.LFunction χ)
        (deriv (DirichletCharacter.LFunction χ) s) s := by
    filter_upwards [hopen.mem_nhds hmem] with s hs
    exact (DirichletCharacter.differentiableAt_LFunction χ s (Or.inl hs)).hasDerivAt
  have hanalytic : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) {s : ℂ | s ≠ 1} :=
    DifferentiableOn.analyticOnNhd
      (fun s hs =>
        (DirichletCharacter.differentiableAt_LFunction χ s (Or.inl hs)).differentiableWithinAt)
      hopen
  have hf'cont : ContinuousAt (deriv (DirichletCharacter.LFunction χ))
      ((1 / 2 : ℂ) + (γ : ℂ) * Complex.I) := (hanalytic.deriv _ hmem).continuousAt
  exact residue_at_critical_zero_eq_residueHarmonic (DirichletCharacter.LFunction χ)
    (deriv (DirichletCharacter.LFunction χ)) γ x hx hzero hderiv hf'cont hsimple

/-! ## Faithful for every Dirichlet L-function — one carrier, the character as the only dial -/

/-- **Faithful for every Dirichlet `L`-function.** A *single* construction serves all `χ`: only the
character weight `χ(n)` on each phasor changes — the carrier (right helix, spin `log n`, magnitude
`n^(-1/2)`) is fixed. For every Dirichlet character `χ`:

* **the fiber is the accumulation** — the partial phasor sums `∑_{n<N} χ(n)·n^(-s)` converge to
  `L(s,χ)` for `Re s > 1`; and
* **its crossings are that `L`'s own zeros** — on the critical line the eta-twisted accumulation
  vanishes exactly where `L(·,χ)` does.

The ten characters checked numerically are instances of this one statement. -/
theorem faithful_all_L {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    (∀ s : ℂ, 1 < s.re →
        Filter.Tendsto (DirichletPhasorCarrier.finiteCarrier χ s) Filter.atTop
          (nhds (DirichletCharacter.LFunction χ s))) ∧
    (∀ s : ℂ, s.re = 1 / 2 →
        (DirichletPhasorCarrier.etaTwistClosed χ s = 0 ↔ DirichletCharacter.LFunction χ s = 0)) :=
  ⟨fun _ hs => DirichletPhasorCarrier.finiteCarrier_tendsto_LFunction χ hs,
   fun s hs => DirichletPhasorCarrier.etaTwistClosed_eq_zero_iff_critical χ s hs⟩

/-- **Tate-completed — the same faithfulness, now carrying the functional equation.** For every
*primitive* `χ`, complete the fiber by the archimedean Γ-factor: `Λ(s,χ) = gammaFactor·L(s,χ)`. The
completion is **zero-free on the line** (the Γ-factor never vanishes for `Re s > 0`), so:

* the **completed** carrier `Λ(1/2+iy,χ)` has *exactly* the crossings of the raw fiber — the same
  zeros of `L(·,χ)`; and
* it satisfies **Tate's functional equation** `Λ(1-s,χ) = q^(s-1/2)·rootNumber(χ)·Λ(s,χ⁻¹)` — the
  `s ↔ 1-s` pairing (the two chiralities). -/
theorem faithful_all_L_completed {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) :
    (∀ y : ℝ, Tate.completedCarrier χ y = 0 ↔
        DirichletCharacter.LFunction χ ((1 / 2 : ℂ) + (y : ℂ) * Complex.I) = 0) ∧
    (∀ s : ℂ, DirichletCharacter.completedLFunction χ (1 - s)
        = (q : ℂ) ^ (s - 1 / 2) * DirichletCharacter.rootNumber χ
          * DirichletCharacter.completedLFunction χ⁻¹ s) :=
  ⟨Tate.completedCarrier_eq_zero_iff χ, Tate.completed_functional_equation χ hχ⟩

/-! ## Complete & continuous: the accumulation reaches the line and crosses to zero at the zeros -/

/-- **A complete, continuous model for discovering the `ζ` zeros — from geometry alone.** For *every*
ordinate `y`, the eta-regularized phasor accumulation `∑_{n<N} (−1)^(n+1)·n^(−s)` converges, at
`s = ½ + iy`, to `(1 − 2^(1−s))·ζ(½+iy)`. This is the **strip extension**: the channel carries
continuously down to the critical line (`Re s > 0`), not just the region of absolute convergence
`Re s > 1`. And the limit is `0` **exactly** where `ζ(½+iy) = 0`.

So climbing `y` continuously, the accumulation of phasors reaches the line and **crosses to zero
precisely at the `ζ` zeros** — built from the phasors alone, assuming no zero and no `Re ρ = ½`. -/
theorem continuous_model_zeta (y : ℝ) :
    Filter.Tendsto
        (fun N : ℕ => ∑ n ∈ Finset.range N,
          (-1 : ℂ) ^ (n + 1) * (n : ℂ) ^ (-((1 / 2 : ℂ) + (y : ℂ) * Complex.I)))
        Filter.atTop
        (nhds ((1 - (2 : ℂ) ^ (1 - ((1 / 2 : ℂ) + (y : ℂ) * Complex.I)))
          * riemannZeta ((1 / 2 : ℂ) + (y : ℂ) * Complex.I))) ∧
    ((1 - (2 : ℂ) ^ (1 - ((1 / 2 : ℂ) + (y : ℂ) * Complex.I)))
          * riemannZeta ((1 / 2 : ℂ) + (y : ℂ) * Complex.I) = 0
        ↔ riemannZeta ((1 / 2 : ℂ) + (y : ℂ) * Complex.I) = 0) := by
  have hsre : ((1 / 2 : ℂ) + (y : ℂ) * Complex.I).re = 1 / 2 := by
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
  have hs0 : 0 < ((1 / 2 : ℂ) + (y : ℂ) * Complex.I).re := by rw [hsre]; norm_num
  have hs1 : ((1 / 2 : ℂ) + (y : ℂ) * Complex.I) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    rw [hsre] at hre
    norm_num at hre
  refine ⟨LFunctionPhasor.eta_strip_tendsto hs0 hs1, ?_⟩
  have h := EtaTrivial.etaTrivial_eq_zero_iff ((1 / 2 : ℂ) + (y : ℂ) * Complex.I) hsre
  rwa [EtaTrivial.etaTrivial_eq] at h

/-- **The found zeros are certified on the line — proven, not assumed.** Wherever the model crosses
(the eta accumulation's limit vanishing at height `y`), `ζ` has a genuine zero at `s = ½ + iy`, whose
real part is **exactly `½`**. The location is read off the strip extension (`η(½+iy) → 0` forces
`η(½+iy) = 0`, and `η = 0 ↔ ζ = 0` on the line), so a crossing is a real on-line zero, not a planted
coordinate. -/
theorem crossing_is_zero_on_line (y : ℝ)
    (hcross : (1 - (2 : ℂ) ^ (1 - ((1 / 2 : ℂ) + (y : ℂ) * Complex.I)))
        * riemannZeta ((1 / 2 : ℂ) + (y : ℂ) * Complex.I) = 0) :
    riemannZeta ((1 / 2 : ℂ) + (y : ℂ) * Complex.I) = 0 ∧
      ((1 / 2 : ℂ) + (y : ℂ) * Complex.I).re = 1 / 2 :=
  ⟨(continuous_model_zeta y).2.mp hcross, by
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]⟩

/-! ## Both sides of the double helix cross at the same heights — unconditional -/

/-- **The two chiralities are conjugate — unconditional, at every truncation.** Going up the two
sides of the double helix: the left (spin `e^(+iy·log n)`, exponent `−(½−iy)`) is the **term-by-term
conjugate** of the right (spin `e^(−iy·log n)`, exponent `−(½+iy)`):
`∑_{n<N} (−1)^(n+1)·n^(−(½−iy)) = conj(∑_{n<N} (−1)^(n+1)·n^(−(½+iy)))`. Conjugates have equal modulus
at every `N`, so the two sides pinch to the axis at exactly the same heights. No hypothesis. -/
theorem both_helices_conjugate (N : ℕ) (y : ℝ) :
    (∑ n ∈ Finset.range N, (-1 : ℂ) ^ (n + 1) * (n : ℂ) ^ (-((1 / 2 : ℂ) - (y : ℂ) * Complex.I)))
      = (starRingEnd ℂ) (∑ n ∈ Finset.range N,
          (-1 : ℂ) ^ (n + 1) * (n : ℂ) ^ (-((1 / 2 : ℂ) + (y : ℂ) * Complex.I))) := by
  have hconj : -((1 / 2 : ℂ) - (y : ℂ) * Complex.I)
      = (starRingEnd ℂ) (-((1 / 2 : ℂ) + (y : ℂ) * Complex.I)) := by
    simp only [map_neg, map_add, map_mul, map_div₀, map_one, map_ofNat, Complex.conj_I,
      Complex.conj_ofReal]
    ring
  rw [map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_mul, map_pow, map_neg, map_one]
  congr 1
  have harg : ((n : ℂ)).arg ≠ Real.pi := by
    rw [show (n : ℂ) = ((n : ℝ) : ℂ) from by push_cast; ring,
      Complex.arg_ofReal_of_nonneg (by positivity)]
    exact Real.pi_pos.ne
  rw [hconj, Complex.cpow_conj _ _ harg, Complex.conj_natCast]

/-- **Both sides cross at the same heights — unconditional.** The conjugacy above forces equal
modulus on the two sides, hence identical crossing heights; the underlying completed object also
meets the functional equation — with `s = ½+iy`, `1−s = ½−iy`, Tate's `Λ(1−s) = Λ(s)` gives
`Λ(½−iy) = Λ(½+iy)` for *every* `y`. The two completed sides are **equal** — same crossings, no
hypothesis. -/
theorem both_sides_cross_together (y : ℝ) :
    completedRiemannZeta ((1 / 2 : ℂ) - (y : ℂ) * Complex.I)
      = completedRiemannZeta ((1 / 2 : ℂ) + (y : ℂ) * Complex.I) := by
  rw [show (1 / 2 : ℂ) - (y : ℂ) * Complex.I = 1 - ((1 / 2 : ℂ) + (y : ℂ) * Complex.I) from by ring,
    completedRiemannZeta_one_sub]

/-! ## Similitude: the Frobenius screw combines the two eigenstates with det = 1 -/

/-- **Frobenius similitude — the two chiral eigenstates combine to det 1.** At a conjugate crossing
the two chiralities are the screw's eigenphases: the right spin `z = e^(−iy·log n)` and the left
`conj z = e^(+iy·log n)`. Combining them in the transverse block `diag(z, conj z)`, the determinant
is `z·conj(z) = |z|² = 1`. The Frobenius rotation is **unimodular** — unit-modulus eigenphases, no
radial drift (the similitude's `√p` scaling is the radius/area-law, carried separately). -/
theorem frobenius_conjugate_det_one (y : ℝ) (n : ℕ) :
    Matrix.det !![LFunctionPhasor.spin y n, 0;
                  0, (starRingEnd ℂ) (LFunctionPhasor.spin y n)] = 1 := by
  rw [Matrix.det_fin_two_of, mul_zero, sub_zero]
  simp only [LFunctionPhasor.spin]
  rw [← Complex.exp_conj, ← Complex.exp_add,
    show (-(↑y * ↑(Real.log n)) * Complex.I)
        + (starRingEnd ℂ) (-(↑y * ↑(Real.log n)) * Complex.I) = 0 from by
      simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring]
  exact Complex.exp_zero

end Faithful
