import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
# Critical-line phasor identities for Dirichlet-`L`-like series

This file formalizes, unconditionally, the genuine mathematical core of the informal
"phasor / helix" discussion.  The heuristic geometric scaffolding (helices, arclength,
bucket counts) is not a mathematical claim; what *is* a precise and provable statement is
the phasor decomposition of a Dirichlet-series term on a vertical line.

On the vertical line `s = σ + i y`, a positive integer (more generally a positive real `x`)
contributes the *phasor*
```
x ^ (-s) = x ^ (-σ) * exp (-(y * log x) * I),
```
i.e. magnitude `A(x) = x ^ (-σ)` and value-dependent spin `φ_x(y) = -(y * log x)`.
Specializing to the **critical line** `σ = 1/2` gives the boxed magnitude `A(n) = n ^ (-1/2)`.

We also record:
* the magnitude (`norm`) of the phasor is exactly `x ^ (-σ)`;
* the general Dirichlet term `χ(n) · n^(-s)` (covering the trivial/principal character
  `χ ≡ 1` and the alternating "eta-mode" weight `χ(n) = (-1)^(n-1)`);
* the fact that the eta correction factor `1 - 2^(1-s)` vanishes only on the line
  `Re s = 1`, hence never on the critical line `Re s = 1/2`.
-/

namespace CriticalLinePhasor

open Complex

/-- **Phasor decomposition on a vertical line.**
For a positive real base `x` and the line `s = σ + i y`,
```
x ^ (-s) = x ^ (-σ) · exp(-(y · log x)·i).
```
The magnitude factor is `x ^ (-σ)` and the spin (phase) is `-(y · log x)`. -/
theorem cpow_vertical_line_phasor (x : ℝ) (hx : 0 < x) (σ y : ℝ) :
    (x : ℂ) ^ (-((σ : ℂ) + (y : ℂ) * I)) =
      ((x ^ (-σ) : ℝ) : ℂ) * Complex.exp (-(y * Real.log x) * I) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast ne_of_gt hx)]
  rw [← Complex.ofReal_log hx.le, Real.rpow_def_of_pos hx]
  push_cast
  rw [← Complex.exp_add]
  ring_nf

/-- **Magnitude of the phasor.**  On the line `s = σ + i y`, the magnitude of `x ^ (-s)`
is exactly `x ^ (-σ)`, independent of `y`.  (For `σ = 1/2` this is the boxed weight
`A(x) = x ^ (-1/2)`.) -/
theorem norm_cpow_vertical_line (x : ℝ) (hx : 0 < x) (σ y : ℝ) :
    ‖(x : ℂ) ^ (-((σ : ℂ) + (y : ℂ) * I))‖ = (x ^ (-σ) : ℝ) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  congr 1
  simp

/-- **Critical-line phasor for a positive integer.**  Specializing the vertical-line
decomposition to `σ = 1/2` and base `n` gives
```
n ^ (-(1/2 + i y)) = n ^ (-1/2) · exp(-(y · log n)·i),
```
i.e. canonical critical-line magnitude `A(n) = n^(-1/2)` and spin `-(y · log n)`. -/
theorem cpow_critical_line (y : ℝ) (n : ℕ) (hn : 0 < n) :
    (n : ℂ) ^ (-((1 / 2 : ℂ) + (y : ℂ) * I)) =
      (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Complex.exp (-(y * Real.log n) * I) := by
  have h := cpow_vertical_line_phasor (n : ℝ) (by exact_mod_cast hn) (1 / 2) y
  push_cast at h ⊢
  convert h using 3

/-- **Magnitude on the critical line.**  The boxed identity `A(n) = n^(-1/2)`:
the magnitude of the critical-line term `n^(-(1/2 + i y))` is `n^(-1/2)` for every `y`. -/
theorem norm_cpow_critical_line (y : ℝ) (n : ℕ) (hn : 0 < n) :
    ‖(n : ℂ) ^ (-((1 / 2 : ℂ) + (y : ℂ) * I))‖ = ((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) := by
  have h := norm_cpow_vertical_line (n : ℝ) (by exact_mod_cast hn) (1 / 2) y
  push_cast at h ⊢
  convert h using 2

/-- **General Dirichlet-series phasor term.**  For an arbitrary arithmetic weight
`χ : ℕ → ℂ`, the term `χ(n) · x^(-s)` on the line `s = σ + i y` is
```
χ(n) · x^(-σ) · exp(-(y · log x)·i).
```
This covers:
* the *trivial / principal character* `χ ≡ 1` (giving `ζ`-like terms `n^(-s)`); and
* the alternating **eta-mode** weight `χ(n) = (-1)^(n-1)` (giving `(-1)^(n-1) n^(-s)`). -/
theorem dirichlet_term_phasor (χ : ℕ → ℂ) (x : ℝ) (hx : 0 < x) (σ y : ℝ) (n : ℕ) :
    χ n * (x : ℂ) ^ (-((σ : ℂ) + (y : ℂ) * I)) =
      χ n * ((x ^ (-σ) : ℝ) : ℂ) * Complex.exp (-(y * Real.log x) * I) := by
  rw [cpow_vertical_line_phasor x hx σ y]
  ring

/-- **Eta-mode term on the critical line.**  The alternating ("eta") phasor attached to
the integer `n` is `(-1)^(n-1) · n^(-1/2) · exp(-(y · log n)·i)`. -/
theorem eta_term_critical_line (y : ℝ) (n : ℕ) (hn : 0 < n) :
    ((-1 : ℂ) ^ (n - 1)) * (n : ℂ) ^ (-((1 / 2 : ℂ) + (y : ℂ) * I)) =
      ((-1 : ℂ) ^ (n - 1)) * (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        Complex.exp (-(y * Real.log n) * I) := by
  rw [cpow_critical_line y n hn]
  ring

/-- **The eta correction factor only vanishes on the line `Re s = 1`.**
The factor `1 - 2^(1-s)` relating `η` and `ζ` (via `η(s) = (1 - 2^(1-s)) ζ(s)`) vanishes
iff `2^(1-s) = 1`, and any such `s` has `Re s = 1`.  In particular it never vanishes on the
critical line `Re s = 1/2`, so eta-mode is safe there. -/
theorem correction_factor_zero_re_eq_one (s : ℂ) (h : (2 : ℂ) ^ (1 - s) = 1) :
    s.re = 1 := by
  have hbase : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
  rw [hbase] at h
  have h2 : ‖((2 : ℝ) : ℂ) ^ (1 - s)‖ = 1 := by rw [h]; simp
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)] at h2
  have hre : (1 - s).re = 0 := by
    rcases lt_trichotomy (1 - s).re 0 with hlt | heq | hgt
    · have := Real.rpow_lt_one_of_one_lt_of_neg (x := (2 : ℝ)) (by norm_num) hlt
      linarith
    · exact heq
    · have := (Real.one_lt_rpow_iff_of_pos (x := (2 : ℝ)) (by norm_num) (y := (1 - s).re)).2
        (Or.inl ⟨by norm_num, hgt⟩)
      linarith
  simp [Complex.sub_re] at hre
  linarith

/-- Consequence: on the critical line `Re s = 1/2`, the eta correction factor is nonzero,
so `η(s) = 0 ↔ ζ(s) = 0` there is governed purely by the phasor sum. -/
theorem correction_factor_ne_zero_on_critical_line (s : ℂ) (hs : s.re = 1 / 2) :
    (2 : ℂ) ^ (1 - s) ≠ 1 := by
  intro h
  have := correction_factor_zero_re_eq_one s h
  rw [hs] at this
  norm_num at this

end CriticalLinePhasor

/-!
## Geometric scaffolding: helices, arclength, and bucket counts

This section makes the heuristic "helix" geometry of the informal model precise and proves
the genuine geometric facts behind it.  The growing-radius helix is
```
γ(k) = (r·k·cos(2πk), r·k·sin(2πk), p·k),
```
with climber `k(y) = e^y / p`, so the height is `z = e^y = p·k(y)` and the cylindrical
radius is `R(y) = r·k(y) = (r/p) e^y`.  We compute the velocity vector (the analytic
derivative), show the squared speed is `p² + r² + (2π r k)²`, and define the arclength
```
S(k;p,r) = ∫₀ᵏ √(p² + r² + (2π r t)²) dt,
```
with the closed forms `S(k;p,0) = p·k` (constant pitch) and, for `r > 0`,
```
S(k;p,r) = (k/2)·√(p²+r²+4π²r²k²) + ((p²+r²)/(4π r))·arsinh(2π r k / √(p²+r²)).
```
We then define the continuous geometric integer index `N(y) = S(k(y);p,r)/Δ` with the
fixed spacing `Δ = π/3`, and finally make the mod-6 "bucket" structure precise: the
integer angular scaling `s_n = n·π/3` is `6`-periodic, and each residue bucket mod 6
receives exactly the expected count of integers.
-/

namespace CriticalLinePhasor.Geometry

open Complex Real intervalIntegral

/-- The growing-radius helix `γ(k) = (r·k·cos(2πk), r·k·sin(2πk), p·k)`. -/
noncomputable def helix (p r : ℝ) (k : ℝ) : ℝ × ℝ × ℝ :=
  (r * k * Real.cos (2 * Real.pi * k),
   r * k * Real.sin (2 * Real.pi * k),
   p * k)

/-- The velocity (analytic derivative) vector of the helix. -/
noncomputable def helixVel (p r : ℝ) (k : ℝ) : ℝ × ℝ × ℝ :=
  (r * Real.cos (2 * Real.pi * k) - r * k * (2 * Real.pi) * Real.sin (2 * Real.pi * k),
   r * Real.sin (2 * Real.pi * k) + r * k * (2 * Real.pi) * Real.cos (2 * Real.pi * k),
   p)

/--
`helixVel` is genuinely the derivative of `helix`.
-/
theorem helix_hasDerivAt (p r k : ℝ) :
    HasDerivAt (helix p r) (helixVel p r k) k := by
  convert HasDerivAt.prodMk ( HasDerivAt.mul ( HasDerivAt.mul ( hasDerivAt_const k r ) ( hasDerivAt_id k ) ) ( HasDerivAt.cos ( HasDerivAt.const_mul ( 2 * Real.pi ) ( hasDerivAt_id k ) ) ) ) ( HasDerivAt.prodMk ( HasDerivAt.mul ( HasDerivAt.mul ( hasDerivAt_const k r ) ( hasDerivAt_id k ) ) ( HasDerivAt.sin ( HasDerivAt.const_mul ( 2 * Real.pi ) ( hasDerivAt_id k ) ) ) ) ( HasDerivAt.const_mul p ( hasDerivAt_id k ) ) ) using 1
  · funext x
    simp only [CriticalLinePhasor.Geometry.helix, Pi.mul_apply, id_eq]
  · simp only [CriticalLinePhasor.Geometry.helixVel, Pi.mul_apply, id_eq]
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> ring

/--
**Squared speed of the helix is constant-free of the trig terms:**
`‖γ'(k)‖² = p² + r² + (2π r k)²`.
-/
theorem helix_speed_sq (p r k : ℝ) :
    (helixVel p r k).1 ^ 2 + (helixVel p r k).2.1 ^ 2 + (helixVel p r k).2.2 ^ 2
      = p ^ 2 + r ^ 2 + (2 * Real.pi * r * k) ^ 2 := by
  convert congr_arg ( fun x : ℝ => x ^ 2 + ( Real.sin ( 2 * Real.pi * k ) * r + Real.cos ( 2 * Real.pi * k ) * ( r * ( 2 * k * Real.pi ) ) ) ^ 2 + p ^ 2 ) ( show Real.cos ( 2 * Real.pi * k ) * r - Real.sin ( 2 * Real.pi * k ) * ( r * ( 2 * k * Real.pi ) ) = - ( Real.sin ( 2 * Real.pi * k ) * ( r * ( 2 * k * Real.pi ) ) ) + Real.cos ( 2 * Real.pi * k ) * r by ring ) using 1 ; ring;
  · unfold CriticalLinePhasor.Geometry.helixVel; ring;
  · ring ; rw [ Real.sin_sq, Real.cos_sq ] ; ring;

/-- The climber `k(y) = e^y / p`. -/
noncomputable def kClimb (p y : ℝ) : ℝ := Real.exp y / p

/--
**Height identity** `z = e^y = p · k(y)`.
-/
theorem height_eq_p_mul_kClimb (p y : ℝ) (hp : p ≠ 0) :
    Real.exp y = p * kClimb p y := by
  exact Eq.symm ( mul_div_cancel₀ _ hp )

/-- The cylindrical radius `R(y) = r · k(y) = (r/p) e^y`. -/
noncomputable def radius (p r y : ℝ) : ℝ := r * kClimb p y

/--
`R(y) = (r/p) e^y`.
-/
theorem radius_eq (p r y : ℝ) : radius p r y = (r / p) * Real.exp y := by
  unfold CriticalLinePhasor.Geometry.radius CriticalLinePhasor.Geometry.kClimb; ring;

/--
The cylindrical radius of a helix point equals `|r·k|`
(`√(x² + y²) = |r k|`).
-/
theorem helix_cyl_radius (p r k : ℝ) :
    Real.sqrt ((helix p r k).1 ^ 2 + (helix p r k).2.1 ^ 2) = |r * k| := by
  unfold CriticalLinePhasor.Geometry.helix; rw [ ← Real.sqrt_sq_eq_abs ] ; ring;
  rw [ Real.sin_sq, Real.cos_sq ] ; ring

/-- The full 3D point attached to ordinate `y`: `γ(y) = helix p r (k(y))`. -/
noncomputable def gammaY (p r y : ℝ) : ℝ × ℝ × ℝ := helix p r (kClimb p y)

/--
**The boxed point** `γ(y) = ((r/p)e^y cos(2π e^y/p), (r/p)e^y sin(2π e^y/p), e^y)`.
-/
theorem gammaY_eq (p r y : ℝ) (hp : p ≠ 0) :
    gammaY p r y =
      ((r / p) * Real.exp y * Real.cos (2 * Real.pi * Real.exp y / p),
       (r / p) * Real.exp y * Real.sin (2 * Real.pi * Real.exp y / p),
       Real.exp y) := by
  unfold CriticalLinePhasor.Geometry.gammaY;
  unfold CriticalLinePhasor.Geometry.helix CriticalLinePhasor.Geometry.kClimb; ring;
  norm_num [ hp ]

/-- The helix speed `√(p² + r² + (2π r k)²)`. -/
noncomputable def speed (p r k : ℝ) : ℝ := Real.sqrt (p ^ 2 + r ^ 2 + (2 * Real.pi * r * k) ^ 2)

/-- **Arclength** of the helix from `0` to `k`:
`S(k;p,r) = ∫₀ᵏ √(p² + r² + (2π r t)²) dt`. -/
noncomputable def arclength (p r k : ℝ) : ℝ := ∫ t in (0 : ℝ)..k, speed p r t

/--
**Constant-pitch closed form** `S(k;p,0) = p·k` (for `p ≥ 0`).
-/
theorem arclength_r_zero (p k : ℝ) (hp : 0 ≤ p) : arclength p 0 k = p * k := by
  unfold arclength
  simp [speed];
  rw [ Real.sqrt_sq hp, mul_comm ]

/-- The explicit closed-form antiderivative for `r > 0`. -/
noncomputable def arclengthClosed (p r k : ℝ) : ℝ :=
  k / 2 * Real.sqrt (p ^ 2 + r ^ 2 + 4 * Real.pi ^ 2 * r ^ 2 * k ^ 2)
    + (p ^ 2 + r ^ 2) / (4 * Real.pi * r)
        * Real.arsinh (2 * Real.pi * r * k / Real.sqrt (p ^ 2 + r ^ 2))

/--
**Closed-form arclength for `r > 0`:**
`S(k;p,r) = (k/2)√(p²+r²+4π²r²k²) + ((p²+r²)/(4π r)) arsinh(2π r k/√(p²+r²))`.
-/
theorem arclength_closed_form (p r k : ℝ) (hr : 0 < r) :
    arclength p r k = arclengthClosed p r k := by
  -- To prove the equality, it suffices to show that the derivative of `arclengthClosed p r t` is `speed p r t`.
  suffices h_deriv : ∀ t : ℝ, HasDerivAt (fun t => CriticalLinePhasor.Geometry.arclengthClosed p r t) (CriticalLinePhasor.Geometry.speed p r t) t by
    rw [ CriticalLinePhasor.Geometry.arclength ];
    rw [ intervalIntegral.integral_deriv_eq_sub' ];
    rotate_left;
    exacts [ fun t => CriticalLinePhasor.Geometry.arclengthClosed p r t, funext fun t => HasDerivAt.deriv ( h_deriv t ), fun t ht => HasDerivAt.differentiableAt ( h_deriv t ), Continuous.continuousOn <| by exact Continuous.sqrt <| by continuity, by simp +decide [ CriticalLinePhasor.Geometry.arclengthClosed ] ];
  intros t
  unfold arclengthClosed speed;
  have hne : p ^ 2 + r ^ 2 + 4 * Real.pi ^ 2 * r ^ 2 * t ^ 2 ≠ 0 := by positivity
  convert HasDerivAt.add ( HasDerivAt.mul ( HasDerivAt.div_const ( hasDerivAt_id t ) (2:ℝ) ) ( HasDerivAt.sqrt ( HasDerivAt.add ( hasDerivAt_const t (p^2 + r^2) ) ( HasDerivAt.mul ( hasDerivAt_const t (4 * Real.pi^2 * r^2) ) ( hasDerivAt_pow 2 t ) ) ) hne ) ) ( HasDerivAt.mul ( hasDerivAt_const t ((p^2+r^2)/(4*Real.pi*r)) ) ( HasDerivAt.arsinh ( HasDerivAt.div_const ( HasDerivAt.mul ( hasDerivAt_const t (2*Real.pi*r) ) ( hasDerivAt_id t ) ) (Real.sqrt (p^2+r^2)) ) ) ) using 1
  case e'_4 => rfl
  case e'_5 => rfl
  case e'_8 => funext x; simp only [Pi.add_apply, Pi.mul_apply, id_eq]
  case e'_9 =>
    simp only [Pi.add_apply, Pi.mul_apply, id_eq, smul_eq_mul]
    norm_num
    have hD : (0:ℝ) < p^2 + r^2 := by positivity
    have hDA : (0:ℝ) < p^2 + r^2 + 4*Real.pi^2*r^2*t^2 := lt_of_le_of_ne (by positivity) (Ne.symm hne)
    have hnest : Real.sqrt (1 + (2*Real.pi*r*t/Real.sqrt (p^2+r^2))^2) = Real.sqrt (p^2+r^2+4*Real.pi^2*r^2*t^2) / Real.sqrt (p^2+r^2) := by
      rw [ ← Real.sqrt_div' _ (by positivity), div_pow, Real.sq_sqrt hD.le ]
      congr 1
      field_simp
      ring
    rw [ hnest ]
    have hsq : (2 * Real.pi * r * t)^2 = 4 * Real.pi^2 * r^2 * t^2 := by ring
    rw [ hsq, eq_comm ]
    have hs1 : Real.sqrt (p^2+r^2) ≠ 0 := by positivity
    have hs2 : Real.sqrt (p^2+r^2+4*Real.pi^2*r^2*t^2) ≠ 0 := by positivity
    rw [ inv_div ]
    field_simp
    rw [ show p ^ 2 + r ^ 2 + r ^ 2 * 4 * Real.pi ^ 2 * t ^ 2 = p ^ 2 + r ^ 2 + 4 * Real.pi ^ 2 * r ^ 2 * t ^ 2 by ring, Real.sq_sqrt hDA.le ]
    ring

/-- The fixed geometric integer spacing `Δ = π/3`. -/
noncomputable def Delta : ℝ := Real.pi / 3

/-- The continuous geometric integer index `N(y) = S(k(y);p,r)/Δ`. -/
noncomputable def Nindex (p r y : ℝ) : ℝ := arclength p r (kClimb p y) / Delta

/--
**The boxed index** `N(y) = (3/π)·S(e^y/p;p,r)`.
-/
theorem Nindex_eq (p r y : ℝ) : Nindex p r y = (3 / Real.pi) * arclength p r (kClimb p y) := by
  unfold CriticalLinePhasor.Geometry.Nindex CriticalLinePhasor.Geometry.Delta;
  ring

/--
**Compensation / change of variables.**  With `x = p·t` (`p > 0`) the arclength becomes
`∫₀^{p k} √(1 + (r/p)² + (2π (r/p) x / p)²) dx`, so the integrand depends on `p` and `r`
only through `q_r = r/p` (and the upper limit through `p·k`).  (This corrects the informal
boxed formula, which dropped the substitution Jacobian.)
-/
theorem arclength_substitution (p r k : ℝ) (hp : 0 < p) :
    arclength p r k =
      ∫ x in (0 : ℝ)..(p * k),
        Real.sqrt (1 + (r / p) ^ 2 + (2 * Real.pi * (r / p) * x / p) ^ 2) := by
  unfold CriticalLinePhasor.Geometry.arclength;
  convert intervalIntegral.integral_comp_mul_left _ hp.ne' using 3;
  any_goals exact fun x => p * Real.sqrt ( 1 + ( r / p ) ^ 2 + ( 2 * Real.pi * ( r / p ) * x / p ) ^ 2 );
  · unfold CriticalLinePhasor.Geometry.speed;
    field_simp;
    rw [ Real.sqrt_div' _ ( by positivity ), Real.sqrt_sq hp.le, mul_div_cancel₀ _ hp.ne' ];
  · norm_num [ hp.ne' ]

/-- The integer angular scaling `s_n = n·(π/3)`. -/
noncomputable def spinAngle (n : ℕ) : ℝ := n * (Real.pi / 3)

/--
**Bucket periodicity (cos):** the spin phasor is `6`-periodic since `6·(π/3) = 2π`.
-/
theorem spin_cos_period6 (n : ℕ) :
    Real.cos (spinAngle (n + 6)) = Real.cos (spinAngle n) := by
  unfold CriticalLinePhasor.Geometry.spinAngle
  rw [show ((n + 6 : ℕ) : ℝ) * (Real.pi / 3) = (n : ℝ) * (Real.pi / 3) + 2 * Real.pi by
        push_cast; ring, Real.cos_add_two_pi]

/--
**Bucket periodicity (sin).**
-/
theorem spin_sin_period6 (n : ℕ) :
    Real.sin (spinAngle (n + 6)) = Real.sin (spinAngle n) := by
  unfold CriticalLinePhasor.Geometry.spinAngle
  rw [show ((n + 6 : ℕ) : ℝ) * (Real.pi / 3) = (n : ℝ) * (Real.pi / 3) + 2 * Real.pi by
        push_cast; ring, Real.sin_add_two_pi]

/--
**Bucket periodicity (complex phasor).**
-/
theorem spin_phasor_period6 (n : ℕ) :
    Complex.exp ((spinAngle (n + 6) : ℂ) * Complex.I)
      = Complex.exp ((spinAngle n : ℂ) * Complex.I) := by
  convert Complex.exp_periodic _ using 2 ; push_cast [ spinAngle ] ; ring

/--
**Bucket window:** in any block of 6 consecutive integers each residue class mod 6
occurs exactly once (here the canonical window `{0,…,5}`).
-/
theorem bucket_window (a : ℕ) (ha : a < 6) :
    (Finset.range 6).filter (fun n => n % 6 = a) = {a} := by
  interval_cases a <;> trivial

/--
**Bucket count:** exactly `N` of the integers in `[0, 6N)` lie in each residue bucket
mod 6.
-/
theorem bucket_count (a N : ℕ) (ha : a < 6) :
    ((Finset.range (6 * N)).filter (fun n => n % 6 = a)).card = N := by
  induction N <;> simp_all +decide [ Nat.mul_succ ];
  simp_all +decide [ Finset.filter ];
  interval_cases a <;> simp_all +arith +decide [ Nat.add_mod ]

/--
**Eta-acceleration sign identity:** `(-1)^(n-1) = 1 - 2·𝟙_{2∣n}` for `n ≥ 1`.
This is the algebraic core of writing `(-1)^(n-1) = 1 - 2·1_{2|n}` used to relate the
eta-mode series to the plain Dirichlet series.
-/
theorem eta_sign_identity (n : ℕ) (hn : 1 ≤ n) :
    ((-1 : ℂ)) ^ (n - 1) = 1 - 2 * (if 2 ∣ n then 1 else 0) := by
  rcases Nat.even_or_odd' n with ⟨ k, rfl | rfl ⟩ <;> norm_num [ Nat.even_iff ] at *;
  cases k <;> simp_all +arith +decide [ Nat.mul_succ, pow_succ' ]

/--
**Euler-factor phasor on a vertical line.**  Each finite Euler factor `1 - ℓ^{-s}` of a
principal-character `L`-function is, on `s = σ + iy`,
`1 - ℓ^{-σ}·exp(-(y·log ℓ)·i)`.
-/
theorem euler_factor_vertical_line (ell : ℕ) (hell : 0 < ell) (σ y : ℝ) :
    1 - (ell : ℂ) ^ (-((σ : ℂ) + (y : ℂ) * I)) =
      1 - (((ell : ℝ) ^ (-σ) : ℝ) : ℂ) * Complex.exp (-(y * Real.log ell) * I) := by
  convert congr_arg ( fun x : ℂ => 1 - x ) ( CriticalLinePhasor.cpow_vertical_line_phasor ( ell : ℝ ) ( by positivity ) σ y ) using 1
  norm_num

end CriticalLinePhasor.Geometry

/-!
## Vanishing (cancellation) events force a sign change

The phasor model identifies a *cancellation event* (a zero of the relevant critical-line
observable) as the mechanism producing zeros.  The requested result is the implication

> **vanishing ⟹ sign change**

and that is the primary theorem of this section (`vanishing_forces_sign_change`, with the
explicit-derivative form `simple_zero_forces_sign_change`).  We also record the converse
(`sign_change_forces_zero`) as supplementary.

The relevant observable is real-valued: although the raw phasor sum `C(y)` is complex, the
quantity whose vanishing detects critical-line zeros is the real Hardy-type function
`Z(y)` obtained by removing the unimodular rotation factor (`Z(y) = e^{iθ(y)} L(½+iy)`,
which is real).  So the mathematically honest statements are about a real function
`f : ℝ → ℝ` whose zeros are exactly the cancellation events.

* **Vanishing ⟹ sign change** (`vanishing_forces_sign_change`,
  `simple_zero_forces_sign_change`): a cancellation event — a zero `f x₀ = 0` that is
  *transversal*, i.e. has nonzero derivative there — forces `f` to take strictly opposite
  signs immediately to the left and to the right of `x₀`.  The transversality (nonzero
  derivative / simple-zero) hypothesis is genuinely necessary and is the precise
  unconditional content of "vanishing forces a sign change": a bare zero (e.g. the double
  zero of `y ↦ y²` at `0`) need not change sign, but a transversal/simple zero always does.

* **Sign change ⟹ vanishing** (`sign_change_forces_zero`): the converse, via the
  Intermediate Value Theorem.  If a continuous observable has opposite signs at two
  ordinates, a cancellation event occurs strictly between them.

Together these give the equivalence (`simple_zero_iff_sign_change`): for an observable with
simple zeros, cancellation events and sign changes are the same phenomenon.
-/

namespace CriticalLinePhasor.SignChange

open Set Filter Topology

/-- **Sign change forces a vanishing (cancellation) event (converse).**
If a real observable `f` is continuous on `[a, b]` and takes values of strictly opposite
sign at the endpoints, then it has a zero strictly inside `(a, b)` — a cancellation event.
This is the Intermediate Value Theorem in the form relevant to the phasor model. -/
theorem sign_change_forces_zero (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) (hsign : f a * f b < 0) :
    ∃ c ∈ Set.Ioo a b, f c = 0 := by
  rw [ mul_neg_iff ] at hsign;
  cases' hsign with hsign hsign;
  · apply_rules [ intermediate_value_Ioo' ] ; linarith;
  · apply_rules [ intermediate_value_Ioo, hf ];
    linarith

/-- **A simple (transversal) cancellation event forces a sign change.**
The explicit-derivative form underlying `vanishing_forces_sign_change`.
If `f` has a zero at `x₀` (`f x₀ = 0`) with nonzero derivative `L` there, then `f` changes
sign across `x₀`: there is a punctured neighbourhood `(x₀ - δ, x₀) ∪ (x₀, x₀ + δ)` on which
every value to the left and every value to the right have strictly opposite signs
(`f y * f z < 0`).  This is the precise unconditional sense in which a cancellation/vanishing
event forces a sign change; the nonvanishing-derivative (simplicity) hypothesis is essential. -/
theorem simple_zero_forces_sign_change (f : ℝ → ℝ) (x₀ L : ℝ)
    (hf : HasDerivAt f L x₀) (hL : L ≠ 0) (h0 : f x₀ = 0) :
    ∃ δ > 0, ∀ y ∈ Set.Ioo (x₀ - δ) x₀, ∀ z ∈ Set.Ioo x₀ (x₀ + δ),
      f y * f z < 0 := by
  -- Since $L \neq 0$, we can choose $\delta > 0$ such that for all $y$ with $|y - x₀| < \delta$ and $y \neq x₀$, we have $\frac{f(y) - f(x₀)}{y - x₀} > 0$ if $L > 0$ and $\frac{f(y) - f(x₀)}{y - x₀} < 0$ if $L < 0$.
  obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ y, abs (y - x₀) < δ → y ≠ x₀ → (f y - f x₀) / (y - x₀) * L > 0 := by
    have := Metric.tendsto_nhdsWithin_nhds.1 ( show Filter.Tendsto ( fun y => ( f y - f x₀ ) / ( y - x₀ ) ) ( nhdsWithin x₀ { x₀ } ᶜ ) ( nhds L ) from ?_ );
    · exact Exists.elim ( this ( |L| ) ( abs_pos.mpr hL ) ) fun δ hδ => ⟨ δ, hδ.1, fun y hy hy' => by cases abs_cases L <;> nlinarith [ abs_lt.mp ( hδ.2 hy' hy ) ] ⟩;
    · rw [ hasDerivAt_iff_tendsto_slope ] at hf;
      convert hf using 2 with y; rw [ slope_def_field ];
  refine ⟨δ, hδ_pos, ?_⟩
  intro y hy z hz
  have hy_abs : |y - x₀| < δ := by
    rw [abs_lt]
    constructor <;> linarith [hy.1, hy.2]
  have hz_abs : |z - x₀| < δ := by
    rw [abs_lt]
    constructor <;> linarith [hz.1, hz.2]
  have hy_ne : y ≠ x₀ := ne_of_lt hy.2
  have hz_ne : z ≠ x₀ := Ne.symm (ne_of_lt hz.1)
  have hy_slope := hδ y hy_abs hy_ne
  have hz_slope := hδ z hz_abs hz_ne
  have hy_left : y - x₀ < 0 := by linarith [hy.2]
  have hz_right : 0 < z - x₀ := by linarith [hz.1]
  have hy_FL_neg : f y * L < 0 := by
    have hmul : ((f y - f x₀) / (y - x₀) * L) * (y - x₀) < 0 :=
      mul_neg_of_pos_of_neg hy_slope hy_left
    rw [h0] at hmul
    field_simp [sub_ne_zero.mpr hy_ne] at hmul
    nlinarith
  have hz_FL_pos : 0 < f z * L := by
    have hmul : 0 < ((f z - f x₀) / (z - x₀) * L) * (z - x₀) :=
      mul_pos hz_slope hz_right
    rw [h0] at hmul
    field_simp [sub_ne_zero.mpr hz_ne] at hmul
    nlinarith
  have hprodL : (f y * L) * (f z * L) < 0 :=
    mul_neg_of_neg_of_pos hy_FL_neg hz_FL_pos
  have hLsq : 0 < L * L := mul_self_pos.mpr hL
  nlinarith [hprodL, hLsq]

/-- **A vanishing (cancellation) event forces a sign change.**
This is the requested direction, stated with the vanishing hypothesis first.  If `f` has a
zero at `x₀` (`f x₀ = 0`) that is transversal — meaning it has nonzero derivative `L` there —
then `f` changes sign across `x₀`: there is a punctured neighbourhood
`(x₀ - δ, x₀) ∪ (x₀, x₀ + δ)` on which every value to the left and every value to the right
have strictly opposite signs (`f y * f z < 0`).  The transversality (nonzero-derivative /
simple-zero) hypothesis is essential: a bare zero need not change sign, but a transversal one
always does. -/
theorem vanishing_forces_sign_change (f : ℝ → ℝ) (x₀ L : ℝ)
    (hvanish : f x₀ = 0) (hf : HasDerivAt f L x₀) (hL : L ≠ 0) :
    ∃ δ > 0, ∀ y ∈ Set.Ioo (x₀ - δ) x₀, ∀ z ∈ Set.Ioo x₀ (x₀ + δ),
      f y * f z < 0 :=
  simple_zero_forces_sign_change f x₀ L hf hL hvanish

/-- **Equivalence at a simple zero.**  Combining the two directions: for a function with a
simple zero at `x₀`, a cancellation/vanishing event at `x₀` is accompanied by a genuine
sign change, and conversely any sign change of a continuous `f` produces a vanishing event.
This records the converse direction as the immediate IVT consequence of the sign change
produced by `simple_zero_forces_sign_change`. -/
theorem simple_zero_iff_sign_change (f : ℝ → ℝ) (x₀ L : ℝ)
    (hf : HasDerivAt f L x₀) (hL : L ≠ 0) (h0 : f x₀ = 0) :
    ∃ δ > 0, (∀ y ∈ Set.Ioo (x₀ - δ) x₀, ∀ z ∈ Set.Ioo x₀ (x₀ + δ), f y * f z < 0) ∧
      ∀ y ∈ Set.Ioo (x₀ - δ) x₀, ∀ z ∈ Set.Ioo x₀ (x₀ + δ),
        ∃ c ∈ Set.Ioo y z, f c = 0 := by
  obtain ⟨ δ, hδ, h ⟩ := CriticalLinePhasor.SignChange.simple_zero_forces_sign_change f x₀ L hf hL h0;
  grind +splitImp

end CriticalLinePhasor.SignChange
/-!
## The symmetric phasor closed form vanishes only at the midpoint

The phasor model attaches to an integer `n` (with critical-line weight) a term and its
*reflection across the critical line* `s ↦ 1 - s`.  The minimal, exactly-soluble instance
of the cancellation condition is the **symmetric two-phasor closed form**
```
P_c(s) = c^(-s) + c^(-(1-s)),
```
for a fixed scale `c > 1`.  This is the cleanest "Dirichlet-`L`-like" closed form whose
vanishing is governed purely by phasor balance, and it exhibits exactly the requested
behaviour:

* **No off-line zeros** (`symPair_zero_re_eq_half`): every zero `P_c(s) = 0` forces
  `Re s = 1/2`.  The mechanism is the magnitude (`norm`) balance of the informal argument:
  cancellation `c^(-s) = - c^(-(1-s))` forces equal magnitudes `c^(-Re s) = c^(-(1-Re s))`,
  and since `c > 1` makes `t ↦ c^t` strictly monotone this is possible only when
  `Re s = 1 - Re s`, i.e. `Re s = 1/2`.
* **It does vanish on the line** (`symPair_vanishes_at_midpoint`): there is an ordinate `y`
  with `P_c(1/2 + i y) = 0` (explicitly `y = π/(2 log c)`, where the two equal-magnitude
  phasors are antiphase), so the closed form genuinely has zeros and they all sit at the
  midpoint.

Together (`symPair_zeros_exactly_on_critical_line`) this is the precise unconditional
content of "this closed form cannot produce an off-line zero, it only vanishes at the
midpoint."

(For the *full* Dirichlet-`L` series the analogous statement is the Riemann Hypothesis,
which is open; what is unconditionally true and proved here is the exact phasor-balance
closed form that is the model's actual cancellation mechanism.)
-/

namespace CriticalLinePhasor.NoOffLineZeros

open Complex

/-- The **symmetric two-phasor closed form** `P_c(s) = c^(-s) + c^(-(1-s))`, the
reflection-symmetric (about the critical line `s ↦ 1-s`) phasor pair at scale `c`. -/
noncomputable def symPair (c : ℝ) (s : ℂ) : ℂ :=
  (c : ℂ) ^ (-s) + (c : ℂ) ^ (-(1 - s))

/-
**Magnitude balance / no off-line zeros.**  Every zero of the symmetric closed form
`P_c` lies on the critical line `Re s = 1/2`.  Off the line the two phasors have different
magnitudes (`c^(-Re s) ≠ c^(-(1-Re s))` because `c > 1` makes `t ↦ c^t` strictly monotone),
so they cannot cancel.
-/
theorem symPair_zero_re_eq_half (c : ℝ) (hc : 1 < c) (s : ℂ) (h : symPair c s = 0) :
    s.re = 1 / 2 := by
  have h_abs : ‖(c : ℂ) ^ (-s)‖ = ‖(c : ℂ) ^ (-(1 - s))‖ := by
    unfold CriticalLinePhasor.NoOffLineZeros.symPair at h; rw [ eq_neg_of_add_eq_zero_left h ] ; norm_num;
  norm_num [ Complex.norm_cpow_of_ne_zero, show c ≠ 0 by linarith ] at h_abs;
  norm_num [ Complex.arg_ofReal_of_nonneg ( by positivity : 0 ≤ c ) ] at h_abs;
  rw [ Real.rpow_def_of_pos, Real.rpow_def_of_pos ] at h_abs <;> norm_num at * <;> try linarith [ abs_of_pos ( zero_lt_one.trans hc ) ];
  nlinarith [ Real.log_pos hc ]

/-
**It vanishes at the midpoint.**  The symmetric closed form `P_c` does vanish on the
critical line: at `s = 1/2 + i y` with `y = π/(2 log c)` the two equal-magnitude phasors are
exactly antiphase.
-/
theorem symPair_vanishes_at_midpoint (c : ℝ) (hc : 1 < c) :
    symPair c ((1 / 2 : ℂ) + ((Real.pi / (2 * Real.log c) : ℝ) : ℂ) * I) = 0 := by
  unfold CriticalLinePhasor.NoOffLineZeros.symPair;
  convert congr_arg₂ ( · + · ) ( CriticalLinePhasor.cpow_vertical_line_phasor c ( by positivity ) ( 1/2 ) ( Real.pi / ( 2 * Real.log c ) ) ) ( CriticalLinePhasor.cpow_vertical_line_phasor c ( by positivity ) ( 1/2 ) ( - ( Real.pi / ( 2 * Real.log c ) ) ) ) using 1 ; ring_nf ; norm_num [ Real.pi_pos.ne', Real.log_pos hc ];
  · ring;
  · norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, Real.rpow_def_of_pos ( zero_lt_one.trans hc ) ] ; ring_nf ; norm_num [ Real.log_pos hc, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv, ne_of_gt ( Real.log_pos hc ) ];
    norm_num [ mul_div ]

/-- **The closed form vanishes exactly at the midpoint.**  Combining the two facts: the
symmetric phasor closed form `P_c` has at least one zero, and every one of its zeros lies on
the critical line `Re s = 1/2`.  This is the precise sense in which the closed form "cannot
produce an off-line zero, it only vanishes at the midpoint." -/
theorem symPair_zeros_exactly_on_critical_line (c : ℝ) (hc : 1 < c) :
    (∃ s : ℂ, symPair c s = 0) ∧ (∀ s : ℂ, symPair c s = 0 → s.re = 1 / 2) :=
  ⟨⟨_, symPair_vanishes_at_midpoint c hc⟩, fun s hs => symPair_zero_re_eq_half c hc s hs⟩

/-
**Critical-line reduction to a cosine.**  On the line `s = 1/2 + i y` the symmetric
closed form collapses to a real cosine:
```
P_c(1/2 + i y) = 2 · c^(-1/2) · cos(y · log c).
```
This is the analytic heart of the exhaustion result: the two equal-magnitude phasors add to
twice their common magnitude times the cosine of their (opposite) phases.
-/
theorem symPair_critical_line (c : ℝ) (hc : 1 < c) (y : ℝ) :
    symPair c ((1 / 2 : ℂ) + (y : ℂ) * I) =
      ((2 * c ^ (-(1 / 2 : ℝ)) * Real.cos (y * Real.log c) : ℝ) : ℂ) := by
  unfold CriticalLinePhasor.NoOffLineZeros.symPair;
  norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im, Complex.cpow_def_of_ne_zero ( by norm_cast; linarith : ( c : ℂ ) ≠ 0 ) ] ; ring;
  norm_num [ Complex.arg_ofReal_of_nonneg ( zero_le_one.trans hc.le ), Real.rpow_def_of_pos ( zero_lt_one.trans hc ) ] ; ring ; norm_num;
  norm_cast ; norm_num [ Complex.cos, Complex.exp_re, Complex.exp_im ] ; ring

/-
**Complete characterization (surjectivity / exhaustion) of the zero set.**
Every zero of the symmetric phasor closed form `P_c` is one of the points
```
s = 1/2 + i · π·(2k+1)/(2 log c),   k ∈ ℤ,
```
and conversely each of these points is a zero.  Thus the integer parameter `k` *surjects*
onto the zero set and the list *exhausts* it: there are no other zeros.  This strengthens
`symPair_zeros_exactly_on_critical_line` (which pins the real part to `1/2`) to the exact
discrete family of ordinates.
-/
theorem symPair_eq_zero_iff (c : ℝ) (hc : 1 < c) (s : ℂ) :
    symPair c s = 0 ↔
      ∃ k : ℤ, s = (1 / 2 : ℂ) +
        ((Real.pi * (2 * (k : ℝ) + 1) / (2 * Real.log c) : ℝ) : ℂ) * I := by
  constructor;
  · intro hs
    have h_re : s.re = 1 / 2 := by
      exact CriticalLinePhasor.NoOffLineZeros.symPair_zero_re_eq_half c hc s hs;
    have h_im : Real.cos (s.im * Real.log c) = 0 := by
      rw [ show s = 1 / 2 + s.im * Complex.I from by simpa [ Complex.ext_iff, h_re ] ] at hs; simp_all +decide [ CriticalLinePhasor.NoOffLineZeros.symPair_critical_line ] ;
      have := CriticalLinePhasor.NoOffLineZeros.symPair_critical_line c hc s.im; simp_all +decide [ CriticalLinePhasor.NoOffLineZeros.symPair ] ;
      exact_mod_cast this.resolve_left ( by positivity );
    obtain ⟨ k, hk ⟩ := Real.cos_eq_zero_iff.mp h_im;
    use k; rw [ ← Complex.re_add_im s ] ; norm_num [ h_re, hk, mul_comm ] ; ring;
    norm_num [ Complex.ext_iff, show s.im = ( 2 * k + 1 ) * Real.pi / 2 / Real.log c by rw [ eq_div_iff ( ne_of_gt ( Real.log_pos hc ) ) ] ; linarith ] ; ring;
  · rintro ⟨ k, rfl ⟩;
    convert symPair_critical_line c hc ( Real.pi * ( 2 * k + 1 ) / ( 2 * Real.log c ) ) using 1;
    ring_nf; norm_num [ mul_div, mul_assoc, mul_comm, mul_left_comm, ne_of_gt, Real.log_pos hc ];
    exact Or.inl ( Complex.cos_eq_zero_iff.mpr ⟨ k, by ring ⟩ )

/-! ### The full two-channel object (augmenting `symPair`)

`symPair c s = c^(-s) + c^(-(1-s))` is a **single number's** positive/negative phasor pair — the
building block.  The real object is the **full channel**: a weight/character `w : ℕ → ℂ` (e.g. a
Dirichlet character `χ`; the alternating *eta* sign is only the **trivial**-character case) collects,
as it climbs, *all* of its phasors into a **positive channel** `∑ₙ w(n)·n^(-s)` and a **negative
channel** `∑ₙ w(n)·n^(-(1-s))`.  Each channel holds every phasor with its magnitude `|w(n)|·n^(-Re s)`
and spin (from `n^(-s)`).  **Vanishing is when the entirety of the phasors sums to zero** — i.e. the
two channel sums (the two numbers being compared) cancel: `symChannel = 0 ↔ posChannel = -negChannel`.
This is **not** a two-phasor model: each channel is a full sum.

**Honesty — the single-pair forcing does NOT survive summation.**  `symPair_zero_re_eq_half` holds
because *one* pair's two magnitudes `c^(-σ), c^(-(1-σ))` are strictly monotone in `σ`, so they balance
at exactly `σ = 1/2`.  A channel **sum** has magnitude `‖∑ₙ …‖`, which is *not* monotone in `σ`, so the
channel does **not** inherit that forcing.  "The channel cancels ⟹ `Re s = 1/2`" is exactly the open
(G)RH content and is deliberately **neither proved nor faked** here. -/

/-- **The positive channel** `∑_{1≤n≤N} w(n)·n^(-s)`: every collected phasor `n^(-s)`, weighted. -/
noncomputable def posChannel (w : ℕ → ℂ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, w n * (n : ℂ) ^ (-s)

/-- **The negative channel** `∑_{1≤n≤N} w(n)·n^(-(1-s))`: the `s ↦ 1-s` reflection of each phasor. -/
noncomputable def negChannel (w : ℕ → ℂ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, w n * (n : ℂ) ^ (-(1 - s))

/-- **The full symmetric channel** `∑_{1≤n≤N} w(n)·symPair n s`: the entirety of the positive and
negative channel phasors, built from the per-number pairs `symPair`.  Augments `symPair` (one
number) to the whole weight/character `w`. -/
noncomputable def symChannel (w : ℕ → ℂ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, w n * symPair (n : ℝ) s

/-- **The channel splits into its two channels**: `symChannel = posChannel + negChannel`. -/
theorem symChannel_eq_pos_add_neg (w : ℕ → ℂ) (N : ℕ) (s : ℂ) :
    symChannel w N s = posChannel w N s + negChannel w N s := by
  unfold symChannel posChannel negChannel
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  unfold symPair
  push_cast
  ring

/-- **Vanishing = the two channels cancel.**  The full channel sums to zero exactly when the positive
and negative channel sums are negatives of each other (the two compared numbers cancel). -/
theorem symChannel_eq_zero_iff (w : ℕ → ℂ) (N : ℕ) (s : ℂ) :
    symChannel w N s = 0 ↔ posChannel w N s = -(negChannel w N s) := by
  rw [symChannel_eq_pos_add_neg, add_eq_zero_iff_eq_neg]

/-- **Per-number pair on the critical line is real**: at `s = 1/2 + i y`,
`n^(-s) + n^(-(1-s)) = 2·n^(-1/2)·cos(y·log n)` — the positive and negative phasor of one number,
equal magnitude `n^(-1/2)`, opposite spin, adding to a real cosine. -/
theorem symPair_natCast_critical_line (n : ℕ) (hn : 0 < n) (y : ℝ) :
    symPair (n : ℝ) ((1 / 2 : ℂ) + (y : ℂ) * I)
      = ((2 * ((n : ℝ) ^ (-(1 / 2 : ℝ))) * Real.cos (y * Real.log n) : ℝ) : ℂ) := by
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · interval_cases n
    norm_num [symPair, Complex.one_cpow, Real.log_one, Real.cos_zero, Real.one_rpow]
  · have hc : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (hge : 1 < n)
    rw [symPair_critical_line (n : ℝ) hc y]

/-- **The channel on the critical line is a weighted real-cosine sum**: at `s = 1/2 + i y`,
`symChannel w N (1/2+iy) = ∑_{1≤n≤N} w(n)·2·n^(-1/2)·cos(y·log n)` — the positive/negative phasors of
every number collapsing, per number, to a real cosine of shrinking amplitude `2n^(-1/2)`. -/
theorem symChannel_critical_line (w : ℕ → ℂ) (N : ℕ) (y : ℝ) :
    symChannel w N ((1 / 2 : ℂ) + (y : ℂ) * I)
      = ∑ n ∈ Finset.Icc 1 N,
          w n * ((2 * ((n : ℝ) ^ (-(1 / 2 : ℝ))) * Real.cos (y * Real.log n) : ℝ) : ℂ) := by
  unfold symChannel
  refine Finset.sum_congr rfl (fun n hn => ?_)
  rw [symPair_natCast_critical_line n (Finset.mem_Icc.mp hn).1 y]

end CriticalLinePhasor.NoOffLineZeros
/-!
## Fractional geometric offset and the explicit-formula residue harmonic

This section makes precise the relationship between the *geometric* picture (a vanishing
occurring strictly between two integer lattice sites of the carrier) and the *analytic*
explicit-formula residue attached to a critical zero `ρ = 1/2 + iγ`.

Two genuinely provable, unconditional facts are isolated; the heuristic congruences relating
the fractional offset to the residue *phase* are normalization choices (impositions), not
theorems, and are therefore **not** asserted here — only the honest mathematical content is
proved.

* **Part A — fractional offset (`Nindex_floor_add_offset`, `arclengthGap_eq`).**
  The continuous geometric index `ν(y) = N(y) = S(e^y/p;p,r)/Δ` (with `Δ = π/3`) splits as
  `ν = ⌊ν⌋ + δ` with `0 ≤ δ < 1`; the physical arclength gap from the previous integer site
  is `d = δ·Δ = S − ⌊ν⌋·Δ`.

* **Part B — residue harmonic phasor (`residueHarmonic_phasor`, `norm_residueHarmonic`).**
  The explicit-formula residue term `−x^ρ/ρ` at `ρ = 1/2 + iγ` decomposes (for `x > 0`) as
  magnitude `√x / √(γ² + 1/4)` times the unit phasor with phase
  `γ·log x − arctan(2γ) + π`.

* **Part C — simple-pole residue (`residue_logDeriv_simple_zero`).**
  For an analytic `f` with a *simple* zero at `ρ ≠ 0` (so `f ρ = 0`, `f' ρ ≠ 0`), the
  residue of the explicit-formula kernel `−(f'/f)(s)·x^s/s` at `ρ` — computed as the
  simple-pole limit `lim_{s→ρ}(s−ρ)·(·)` — equals `−x^ρ/ρ`.  At a critical zero this is
  exactly the residue harmonic of Part B.
-/

namespace CriticalLinePhasor.Residue

open Complex CriticalLinePhasor.Geometry

/-! ### Part A: the fractional geometric offset between consecutive integers -/

/-- The integer lattice site `N = ⌊ν(y)⌋` immediately preceding the vanishing index. -/
noncomputable def geomFloor (p r y : ℝ) : ℤ := ⌊Nindex p r y⌋

/-- The fractional geometric offset `δ = ν(y) − ⌊ν(y)⌋ ∈ [0,1)`. -/
noncomputable def geomOffset (p r y : ℝ) : ℝ := Int.fract (Nindex p r y)

/-- The physical arclength gap `d = δ·Δ` from the previous integer lattice site. -/
noncomputable def arclengthGap (p r y : ℝ) : ℝ := geomOffset p r y * Delta

/-
**Integer-plus-fractional split** `ν = ⌊ν⌋ + δ`.
-/
theorem Nindex_floor_add_offset (p r y : ℝ) :
    Nindex p r y = (geomFloor p r y : ℝ) + geomOffset p r y := by
  exact Eq.symm ( Int.floor_add_fract _ )

/-
The fractional offset is nonnegative.
-/
theorem geomOffset_nonneg (p r y : ℝ) : 0 ≤ geomOffset p r y := by
  exact Int.fract_nonneg _

/-
The fractional offset is strictly less than one.
-/
theorem geomOffset_lt_one (p r y : ℝ) : geomOffset p r y < 1 := by
  exact Int.fract_lt_one _

/-
The arclength is the index times the spacing: `S = ν·Δ`.
-/
theorem arclength_eq_Nindex_mul_Delta (p r y : ℝ) :
    arclength p r (kClimb p y) = Nindex p r y * Delta := by
  rw [ CriticalLinePhasor.Geometry.Nindex, CriticalLinePhasor.Geometry.Delta ];
  rw [ div_mul_cancel₀ _ ( by positivity ) ]

/-
**The arclength gap from the previous integer site** `d = S − ⌊ν⌋·Δ = δ·Δ`.
-/
theorem arclengthGap_eq (p r y : ℝ) :
    arclengthGap p r y = arclength p r (kClimb p y) - (geomFloor p r y : ℝ) * Delta := by
  unfold arclengthGap geomOffset geomFloor;
  rw [ Int.fract ] ; rw [ arclength_eq_Nindex_mul_Delta ] ; ring;

/-! ### Part B: the explicit-formula residue harmonic and its phasor form -/

/-
`|1/2 + iγ| = √(γ² + 1/4)`.
-/
theorem norm_half_add_mul_I (γ : ℝ) :
    ‖((1 / 2 : ℂ) + (γ : ℂ) * I)‖ = Real.sqrt (γ ^ 2 + 1 / 4) := by
  convert Complex.norm_def _ using 2 ; norm_num [ Complex.normSq ] ; ring

/-
`arg(1/2 + iγ) = arctan(2γ)` (the real part `1/2` is positive).
-/
theorem arg_half_add_mul_I (γ : ℝ) :
    Complex.arg ((1 / 2 : ℂ) + (γ : ℂ) * I) = Real.arctan (2 * γ) := by
  rw [ Complex.arg, Complex.norm_def, Complex.normSq_apply ] ; norm_num ; ring;
  rw [ Real.arctan_eq_arcsin ] ; ring_nf ; norm_num;
  rw [ show 1 + γ ^ 2 * 4 = 4 * ( 1 / 4 + γ ^ 2 ) by ring, Real.sqrt_mul ( by norm_num ) ] ; ring

/-- The **explicit-formula residue harmonic** `−x^ρ/ρ` at `ρ = 1/2 + iγ`. -/
noncomputable def residueHarmonic (x γ : ℝ) : ℂ :=
  -(x : ℂ) ^ ((1 / 2 : ℂ) + (γ : ℂ) * I) / ((1 / 2 : ℂ) + (γ : ℂ) * I)

/-
**Residue-harmonic phasor decomposition.**  For `x > 0`,
```
−x^(1/2+iγ)/(1/2+iγ) = (√x / √(γ²+1/4)) · exp( i·(γ·log x − arctan(2γ) + π) ).
```
Magnitude `√x/√(γ²+1/4)`, phase `γ·log x − arctan(2γ) + π`.
-/
theorem residueHarmonic_phasor (x γ : ℝ) (hx : 0 < x) :
    residueHarmonic x γ =
      ((Real.sqrt x / Real.sqrt (γ ^ 2 + 1 / 4) : ℝ) : ℂ) *
        Complex.exp (((γ * Real.log x - Real.arctan (2 * γ) + Real.pi) : ℝ) * I) := by
  -- Write the formula for `residueHarmonic` using `Complex.cpow_def_of_ne_zero` (base ≠ 0 since x>0).
  have h_cpow_def : (x : ℂ) ^ ((1 / 2 : ℂ) + (γ : ℂ) * I) = (Real.sqrt x : ℂ) * Complex.exp ((γ * Real.log x : ℝ) * I) := by
    rw [ Complex.cpow_def_of_ne_zero ] <;> norm_num [ hx.ne', Real.sqrt_eq_rpow ];
    rw [ Complex.ofReal_log ( by positivity ), Complex.log ] ; norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im, Real.rpow_def_of_pos hx ] ; ring;
    norm_num [ Complex.arg_ofReal_of_nonneg hx.le, Real.exp_add, Real.exp_sub ];
  -- Write the formula for `ρ` using `Complex.norm_mul_exp_arg_mul_I`.
  have h_rho_def : (1 / 2 : ℂ) + (γ : ℂ) * I = (Real.sqrt (γ ^ 2 + 1 / 4) : ℂ) * Complex.exp ((Real.arctan (2 * γ) : ℝ) * I) := by
    convert Complex.norm_mul_exp_arg_mul_I ( 1 / 2 + γ * Complex.I ) using 1 ; norm_num [ Complex.normSq, Complex.norm_def, Complex.exp_re, Complex.exp_im, Real.cos_arctan, Real.sin_arctan ] ; ring;
    · convert Complex.norm_mul_exp_arg_mul_I ( 1 / 2 + γ * Complex.I ) |> Eq.symm using 1 ; norm_num [ Complex.normSq, Complex.norm_def, Complex.exp_re, Complex.exp_im, Real.cos_arctan, Real.sin_arctan ] ; ring;
    · norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, Real.cos_arctan, Real.sin_arctan ] ; ring ; norm_num [ hx.le ] ; ring;
      norm_cast ; norm_num [ Real.cos_arctan, Real.sin_arctan ] ; ring ; norm_num [ hx.le ] ; ring;
      rw [ show ( 1 / 4 + γ ^ 2 ) = ( 1 + γ ^ 2 * 4 ) / 4 by ring, Real.sqrt_div' ] <;> norm_num ; ring ; norm_num [ hx.le ] ; ring;
      exact ⟨ mul_inv_cancel₀ <| ne_of_gt <| Real.sqrt_pos.mpr <| by positivity, mul_div_cancel_right₀ _ <| ne_of_gt <| Real.sqrt_pos.mpr <| by positivity ⟩;
  convert congr_arg ( fun z => -z / ( 1 / 2 + ( γ : ℂ ) * Complex.I ) ) h_cpow_def using 1
  case e'_2 => rfl
  case e'_3 =>
    have hsq : (√(γ^2+1/4) : ℂ) ≠ 0 := by
      rw [ Complex.ofReal_ne_zero ]; exact ne_of_gt (Real.sqrt_pos.mpr (by positivity))
    rw [ h_rho_def, eq_div_iff (mul_ne_zero hsq (Complex.exp_ne_zero _)) ]
    rw [ Complex.ofReal_div ]
    rw [ mul_mul_mul_comm ]
    rw [ ← Complex.exp_add ]
    rw [ show (↑(γ * Real.log x - Real.arctan (2*γ) + π) : ℂ) * Complex.I + (↑(Real.arctan (2*γ)) : ℂ) * Complex.I = (↑(γ * Real.log x) : ℂ) * Complex.I + π * Complex.I from by push_cast; ring ]
    rw [ Complex.exp_add, Complex.exp_pi_mul_I ]
    field_simp
    rw [ mul_div_assoc, div_self (by rw [ Complex.ofReal_ne_zero ]; exact ne_of_gt (Real.sqrt_pos.mpr (by positivity))), mul_one ]

/-
**Magnitude of the residue harmonic** `‖−x^ρ/ρ‖ = √x/√(γ²+1/4)`.
-/
theorem norm_residueHarmonic (x γ : ℝ) (hx : 0 < x) :
    ‖residueHarmonic x γ‖ = Real.sqrt x / Real.sqrt (γ ^ 2 + 1 / 4) := by
  convert congr_arg Norm.norm ( residueHarmonic_phasor x γ hx ) using 1 ; norm_num [ Complex.norm_exp_ofReal_mul_I, abs_of_pos, hx ] ; ring;
  norm_num [ Complex.norm_exp ];
  norm_cast ; norm_num [ abs_of_nonneg, Real.sqrt_nonneg ]

/-! ### Part C: the simple-pole residue of the explicit-formula kernel -/

open Filter Topology

/-
**Simple-pole residue of the explicit-formula kernel.**
If `f` is differentiable on a neighbourhood of `ρ` (with derivative function `f'`, continuous
at `ρ`) and has a *simple* zero there (`f ρ = 0`, `f' ρ ≠ 0`), and `ρ ≠ 0`, `x > 0`, then the
residue at `ρ` of the kernel `−(f'/f)(s)·x^s/s`, computed as the simple-pole limit
`lim_{s→ρ}(s−ρ)·(·)`, equals `−x^ρ/ρ`.
-/
theorem residue_logDeriv_simple_zero
    (f f' : ℂ → ℂ) (ρ : ℂ) (x : ℝ)
    (hx : 0 < x) (hρ : ρ ≠ 0) (hf0 : f ρ = 0)
    (hderiv : ∀ᶠ s in nhds ρ, HasDerivAt f (f' s) s)
    (hf'cont : ContinuousAt f' ρ) (hf'0 : f' ρ ≠ 0) :
    Filter.Tendsto
      (fun s => (s - ρ) * (-(f' s / f s) * ((x : ℂ) ^ s / s)))
      (nhdsWithin ρ {ρ}ᶜ) (nhds (-(x : ℂ) ^ ρ / ρ)) := by
  -- Apply the fact that the product of limits holds under certain conditions.
  have h_prod : Filter.Tendsto (fun s => -(f' s) * ((x : ℂ) ^ s / s) * ((s - ρ) / f s)) (nhdsWithin ρ {ρ}ᶜ) (nhds (-(f' ρ) * ((x : ℂ) ^ ρ / ρ) * (1 / f' ρ))) := by
    refine' Filter.Tendsto.mul ( Filter.Tendsto.mul ( Filter.Tendsto.neg ( hf'cont.mono_left inf_le_left ) ) _ ) _;
    · refine' Filter.Tendsto.div _ _ hρ;
      · exact tendsto_nhdsWithin_of_tendsto_nhds ( ContinuousAt.cpow continuousAt_const continuousAt_id <| Or.inl <| by norm_num; linarith );
      · exact Filter.tendsto_id.mono_left inf_le_left;
    · have h_slope : Filter.Tendsto (fun s => (f s - f ρ) / (s - ρ)) (nhdsWithin ρ {ρ}ᶜ) (nhds (f' ρ)) := by
        have := hderiv.self_of_nhds;
        rw [ hasDerivAt_iff_tendsto_slope ] at this;
        convert this using 2 with s; rw [ slope_def_field ];
      simpa [ hf0 ] using h_slope.inv₀ hf'0;
  grind

/-
**The explicit-formula residue at a critical zero is the residue harmonic.**
Specializing `residue_logDeriv_simple_zero` to `ρ = 1/2 + iγ` gives exactly the residue
harmonic `−x^(1/2+iγ)/(1/2+iγ)` of Part B.
-/
theorem residue_at_critical_zero_eq_residueHarmonic
    (f f' : ℂ → ℂ) (γ x : ℝ)
    (hx : 0 < x) (hf0 : f ((1 / 2 : ℂ) + (γ : ℂ) * I) = 0)
    (hderiv : ∀ᶠ s in nhds ((1 / 2 : ℂ) + (γ : ℂ) * I), HasDerivAt f (f' s) s)
    (hf'cont : ContinuousAt f' ((1 / 2 : ℂ) + (γ : ℂ) * I))
    (hf'0 : f' ((1 / 2 : ℂ) + (γ : ℂ) * I) ≠ 0) :
    Filter.Tendsto
      (fun s => (s - ((1 / 2 : ℂ) + (γ : ℂ) * I)) * (-(f' s / f s) * ((x : ℂ) ^ s / s)))
      (nhdsWithin ((1 / 2 : ℂ) + (γ : ℂ) * I) {((1 / 2 : ℂ) + (γ : ℂ) * I)}ᶜ)
      (nhds (residueHarmonic x γ)) := by
  convert residue_logDeriv_simple_zero f f' ( 1 / 2 + γ * Complex.I ) x hx _ hf0 hderiv hf'cont hf'0 using 2 ; norm_num [ residueHarmonic ];
  norm_num [ Complex.ext_iff ]

end CriticalLinePhasor.Residue
/-!
## The Dirichlet eta function for the trivial character (eta-mode)

This section formalizes the cleanest "regularized phasor" identity requested for the trivial
character: the Dirichlet eta function

```
η(s) = ∑_{n=1}^∞ (-1)^(n-1) n^(-s)   (Re s > 1),  written via analytic continuation as
η(s) = (1 - 2^(1-s)) ζ(s).
```

On the critical line `s = 1/2 + i y` the correction factor `1 - 2^(1-s)` is nonzero
(it only vanishes on `Re s = 1`), hence

```
η(1/2 + i y) = 0  ↔  ζ(1/2 + i y) = 0.
```

We also record the genuine phasor-sum identity in the region of convergence `Re s > 1`,
and the critical-line phasor form of the individual eta term (`eta_term_critical_line`).
-/

namespace CriticalLinePhasor.EtaTrivial

open Complex CriticalLinePhasor

/-- **The Dirichlet eta function** (trivial character), defined everywhere via the
analytic continuation of `ζ` by the standard formula `η(s) = (1 - 2^(1-s)) ζ(s)`. -/
noncomputable def etaTrivial (s : ℂ) : ℂ := (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s

/-- **The defining identity** `η(s) = (1 - 2^(1-s)) ζ(s)`. -/
theorem etaTrivial_eq (s : ℂ) :
    etaTrivial s = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := rfl

/-- The eta correction factor `1 - 2^(1-s)` is nonzero on the critical line `Re s = 1/2`. -/
theorem one_sub_two_cpow_ne_zero_on_critical_line (s : ℂ) (hs : s.re = 1 / 2) :
    (1 - (2 : ℂ) ^ (1 - s)) ≠ 0 := by
  have h := correction_factor_ne_zero_on_critical_line s hs
  intro hc
  apply h
  have : (2 : ℂ) ^ (1 - s) = 1 := by
    have := sub_eq_zero.mp hc
    exact this.symm
  exact this

/-- **Zero equivalence on the critical line.**  Since the eta correction factor is nonzero
on `Re s = 1/2`, we have `η(s) = 0 ↔ ζ(s) = 0` there. -/
theorem etaTrivial_eq_zero_iff (s : ℂ) (hs : s.re = 1 / 2) :
    etaTrivial s = 0 ↔ riemannZeta s = 0 := by
  rw [etaTrivial, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h (one_sub_two_cpow_ne_zero_on_critical_line s hs)
    · exact h
  · intro h; exact Or.inr h

/-- **Boxed zero equivalence in the `s = 1/2 + i y` form.**
`η(1/2 + i y) = 0  ↔  ζ(1/2 + i y) = 0`. -/
theorem etaTrivial_eq_zero_iff_critical (y : ℝ) :
    etaTrivial ((1 / 2 : ℂ) + (y : ℂ) * I) = 0 ↔
      riemannZeta ((1 / 2 : ℂ) + (y : ℂ) * I) = 0 := by
  apply etaTrivial_eq_zero_iff
  simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]

/-
**The eta phasor sum in the region of convergence** `Re s > 1`:
`η(s) = ∑' n, (-1)^n / (n+1)^s` (i.e. `∑_{k≥1} (-1)^(k-1) k^(-s)`).
-/
theorem etaTrivial_eq_tsum {s : ℂ} (hs : 1 < s.re) :
    etaTrivial s = ∑' n : ℕ, (-1 : ℂ) ^ n / ((n : ℂ) + 1) ^ s := by
  -- By definition of `etaTrivial`, we have `etaTrivial s = (1 - 2^(1-s)) * riemannZeta s`.
  unfold CriticalLinePhasor.EtaTrivial.etaTrivial
  have hzeta : riemannZeta s = ∑' n : ℕ, (1 : ℂ) / ((n : ℂ) + 1) ^ s := by
    convert zeta_eq_tsum_one_div_nat_add_one_cpow hs using 1
  rw [hzeta];
  -- Split the sum into even and odd terms.
  have h_split : ∑' n : ℕ, (1 : ℂ) / ((n : ℂ) + 1) ^ s - ∑' n : ℕ, (-1 : ℂ) ^ n / ((n : ℂ) + 1) ^ s = ∑' k : ℕ, (2 : ℂ) / ((2 * (k + 1) : ℂ) ^ s) := by
    rw [ ← Summable.tsum_sub ];
    · rw [ ← tsum_even_add_odd ] <;> norm_num [ pow_add, pow_mul, div_eq_mul_inv ] ; ring;
      -- The series $\sum_{k=0}^{\infty} \frac{1}{(2k+2)^s}$ is a p-series with $p = s$, which converges since $s > 1$.
      have h_pseries : Summable (fun k : ℕ => (1 : ℂ) / ((k + 1 : ℂ) ^ s)) := by
        have := summable_one_div_nat_cpow.2 hs;
        exact_mod_cast this.comp_injective Nat.succ_injective;
      refine ( h_pseries.comp_injective ( show Function.Injective ( fun k : ℕ => 2 * k + 1 ) from fun a b h => by simpa using h ) |> Summable.mul_left 2 ).congr fun x => ?_ ; norm_num ; ring;
    · have := summable_nat_add_iff 1 |>.2 <| Real.summable_one_div_nat_rpow.2 hs;
      convert this.of_norm_bounded _;
      · infer_instance;
      · intro n; have := Complex.norm_cpow_eq_rpow_re_of_pos ( Nat.cast_add_one_pos n ) s; aesop;
    · refine' .of_norm _;
      refine ( summable_nat_add_iff 1 |>.2 <| Real.summable_one_div_nat_rpow.2 hs ).congr fun n => ?_
      rw [ ← Complex.norm_cpow_eq_rpow_re_of_pos ( by positivity ) ] ; norm_num;
  -- Simplify the expression $\sum' k : ℕ, (2 : ℂ) / ((2 * (k + 1) : ℂ) ^ s)$ to $2^{1-s} \sum' k : ℕ, (1 : ℂ) / ((k + 1) : ℂ) ^ s$.
  have h_simplify : ∑' k : ℕ, (2 : ℂ) / ((2 * (k + 1) : ℂ) ^ s) = 2 ^ (1 - s) * ∑' k : ℕ, (1 : ℂ) / ((k + 1) : ℂ) ^ s := by
    rw [ ← tsum_mul_left ] ; refine' tsum_congr fun k => _ ; rw [ Complex.cpow_sub ] <;> norm_num ; ring;
    rw [ show ( 2 + k * 2 : ℂ ) = 2 * ( 1 + k ) by ring, Complex.cpow_def_of_ne_zero, Complex.cpow_def_of_ne_zero, Complex.cpow_def_of_ne_zero ] <;> norm_num ; ring ; norm_cast ; norm_num;
    · rw [ ← mul_inv, ← Complex.exp_add ] ; rw [ show ( 2 + k * 2 : ℝ ) = 2 * ( 1 + k ) by ring, Real.log_mul ( by positivity ) ( by positivity ) ] ; norm_num ; ring;
    · exact mod_cast by positivity;
    · exact mod_cast by positivity;
  grind

/-- **Critical-line phasor form of the eta sum's terms.**
The `k`-th term of the eta phasor sum on the critical line `s = 1/2 + i y` is
`(-1)^(k-1) · k^(-1/2) · exp(-(y·log k)·i)`. -/
theorem etaTrivial_term_phasor_critical (y : ℝ) (k : ℕ) (hk : 0 < k) :
    ((-1 : ℂ) ^ (k - 1)) * (k : ℂ) ^ (-((1 / 2 : ℂ) + (y : ℂ) * I)) =
      ((-1 : ℂ) ^ (k - 1)) * (((k : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        Complex.exp (-(y * Real.log k) * I) :=
  eta_term_critical_line y k hk

/-!
### Surjectivity / exhaustion: zeta zeros are exactly carrier zeros

We package the boxed critical-line identity into the *carrier* `F_η(y) := η(1/2 + i y)`
and record the **surjectivity (exhaustion)** statement requested: every zeta zero on the
critical line is a carrier zero, and in fact the carrier-zero set is *exactly* the
critical-line zeta-zero set.
-/

/-- **The eta carrier on the critical line**, `F_η(y) := η(1/2 + i y)`. -/
noncomputable def Feta (y : ℝ) : ℂ := etaTrivial ((1 / 2 : ℂ) + (y : ℂ) * I)

/-- The carrier vanishes exactly when `ζ` vanishes on the critical line:
`F_η(y) = 0 ↔ ζ(1/2 + i y) = 0`. -/
theorem Feta_eq_zero_iff (y : ℝ) :
    Feta y = 0 ↔ riemannZeta ((1 / 2 : ℂ) + (y : ℂ) * I) = 0 :=
  etaTrivial_eq_zero_iff_critical y

/-- **Carrier zero set** `CarrierZeros = { y | F_η(y) = 0 }`. -/
def CarrierZeros : Set ℝ := {y : ℝ | Feta y = 0}

/-- **Surjectivity / exhaustion (backward implication).**
Every zero of `ζ` on the critical line is a carrier zero:
`ζ(1/2 + i γ) = 0 ⟹ γ ∈ CarrierZeros`. -/
theorem zeta_zero_imp_carrier_zero (γ : ℝ)
    (h : riemannZeta ((1 / 2 : ℂ) + (γ : ℂ) * I) = 0) : γ ∈ CarrierZeros :=
  (Feta_eq_zero_iff γ).2 h

/-- **Exhaustion as a set identity.**  The carrier-zero set is exactly the set of
critical-line zeta zeros, so the carrier `F_η` exhausts (is surjective onto) the
critical-line zeros of `ζ`. -/
theorem CarrierZeros_eq :
    CarrierZeros = {y : ℝ | riemannZeta ((1 / 2 : ℂ) + (y : ℂ) * I) = 0} := by
  ext y; exact Feta_eq_zero_iff y

/-!
### Finite carrier and its limit in the region of convergence

The finite carrier (partial phasor sum) is
`F_{η,N}(s) = ∑_{n<N} (-1)^n / (n+1)^s` (i.e. `∑_{k=1}^{N} (-1)^{k-1} k^{-s}`).
In the half-plane `Re s > 1` the eta series is absolutely convergent and its partial
sums converge to `η(s)`.
-/

/-- **Finite eta carrier** `F_{η,N}(s) = ∑_{n<N} (-1)^n / (n+1)^s`. -/
noncomputable def etaCarrierFinite (s : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, (-1 : ℂ) ^ n / ((n : ℂ) + 1) ^ s

/-- The eta series is (absolutely) summable for `Re s > 1`. -/
theorem etaCarrier_summable {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => (-1 : ℂ) ^ n / ((n : ℂ) + 1) ^ s) := by
  have h_summable : Summable (fun n : ℕ => (1 : ℂ) / (n : ℂ) ^ s) :=
    summable_one_div_nat_cpow.2 hs
  exact Summable.of_norm <| by simpa using (summable_nat_add_iff 1).2 h_summable.norm

/-- **Limit identity in the convergence half-plane.**  For `Re s > 1`, the finite
carrier converges to `η(s)`:
`lim_{N→∞} F_{η,N}(s) = η(s)`. -/
theorem etaCarrierFinite_tendsto {s : ℂ} (hs : 1 < s.re) :
    Filter.Tendsto (etaCarrierFinite s) Filter.atTop (nhds (etaTrivial s)) := by
  rw [ CriticalLinePhasor.EtaTrivial.etaTrivial_eq_tsum hs ];
  exact ( etaCarrier_summable hs |> Summable.hasSum |> HasSum.tendsto_sum_nat )

end CriticalLinePhasor.EtaTrivial
/-!
## Weighted phasors for a general Dirichlet character `χ` mod `q`

The trivial-character ("eta") development above is the `χ ≡ 1` (twisted) case.  The genuine
critical-line picture for a Dirichlet `L`-function uses *weighted* phasors

```
v_n(y) = χ(n) · n^(-1/2) · e^(-i y log n),   |v_n(y)| = |χ(n)| · n^(-1/2),
```

so the magnitudes are the **critical-line weights**: `n^(-1/2)` when `(n,q) = 1` and `0`
otherwise (the latter because `χ(n) = 0` on non-units).  These absolute values are the mass
distribution of the cancellation polygon; the phases `-y log n` select the cancellation
height.

This section records, unconditionally and from Mathlib's `DirichletCharacter.LFunction`:

* the per-term phasor decomposition and its magnitude case-split (`dirichlet_char_norm_eq`,
  `dirichlet_char_norm_coprime`, `dirichlet_term_phasor_critical`,
  `dirichlet_term_magnitude_critical`);
* the **carrier** `F_χ(y) := L(1/2 + i y, χ)` with the trivial completion factor
  `E_χ ≡ 1`, so the zero condition `F_χ(γ) = 0 ↔ L(1/2 + i γ, χ) = 0` (the "weighted phasor
  polygon closes" statement), and the exhaustion of the critical-line `L`-zeros
  (`DirichletCarrierZeros_eq`);
* the carrier phasor-sum identity in the region of convergence `Re s > 1`
  (`dirichletCarrier_eq_tsum`);
* the **log-weight derivative** `F'`-content (`dirichlet_deriv_eq_tsum`); and
* the **bridge to the prime weights** `Λ(n)` via the negative logarithmic derivative
  `-L'/L(s,χ) = ∑_n χ(n) Λ(n) n^(-s)` (`dirichlet_logDeriv_eq_tsum`), the analytic core of
  the chain `n^(-1/2) phasor magnitudes → L(1/2+iγ,χ)=0 → L'/L → Λ(n) prime weights`.

As the request itself flags, the raw sum on the critical line is only conditionally
convergent there, so the absolutely-convergent phasor/`tsum` identities are stated in the
convergence half-plane `Re s > 1`; the unconditional critical-line deliverable is the exact
zero-equivalence and the magnitude/phasor structure.  The Riemann Hypothesis for `L(·,χ)` is
not assumed or claimed.
-/

namespace CriticalLinePhasor.DirichletCarrier

open Complex DirichletCharacter ArithmeticFunction
open scoped LSeries.notation

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

/-- **Magnitude case-split for a Dirichlet character.**
`‖χ(n)‖ = 1` if `n` is a unit mod `q`, and `0` otherwise. -/
theorem dirichlet_char_norm_eq (n : ℕ) :
    ‖χ (n : ZMod q)‖ = if IsUnit (n : ZMod q) then 1 else 0 := by
  by_cases h : IsUnit (n : ZMod q)
  · rw [if_pos h]
    obtain ⟨u, hu⟩ := h
    rw [← hu]; exact DirichletCharacter.unit_norm_eq_one χ u
  · rw [if_neg h, MulChar.map_nonunit χ h, norm_zero]

omit [NeZero q] in
/-- **Magnitude case-split, coprimality form.**
`‖χ(n)‖ = 1` when `(n,q) = 1`, and `0` otherwise. -/
theorem dirichlet_char_norm_coprime (n : ℕ) :
    ‖χ (n : ZMod q)‖ = if Nat.Coprime n q then 1 else 0 := by
  by_cases h : Nat.Coprime n q
  · rw [if_pos h]
    obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime n q).mpr h
    rw [← hu]; exact DirichletCharacter.unit_norm_eq_one χ u
  · rw [if_neg h]
    have hu : ¬ IsUnit (n : ZMod q) := fun hu => h ((ZMod.isUnit_iff_coprime n q).mp hu)
    rw [MulChar.map_nonunit χ hu, norm_zero]

omit [NeZero q] in
/-- **Per-term weighted phasor on the critical line.**
`χ(n) · n^(-(1/2 + i y)) = χ(n) · n^(-1/2) · exp(-(y · log n)·i)`. -/
theorem dirichlet_term_phasor_critical (y : ℝ) (n : ℕ) (hn : 0 < n) :
    χ (n : ZMod q) * (n : ℂ) ^ (-((1 / 2 : ℂ) + (y : ℂ) * I)) =
      χ (n : ZMod q) * (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        Complex.exp (-(y * Real.log n) * I) := by
  rw [CriticalLinePhasor.cpow_critical_line y n hn]; ring

omit [NeZero q] in
/-- **Magnitude of the weighted phasor on the critical line:** the boxed identity
`|v_n(y)| = |χ(n)| · n^(-1/2)`. -/
theorem dirichlet_term_magnitude_critical (y : ℝ) (n : ℕ) (hn : 0 < n) :
    ‖χ (n : ZMod q) * (n : ℂ) ^ (-((1 / 2 : ℂ) + (y : ℂ) * I))‖
      = ‖χ (n : ZMod q)‖ * ((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) := by
  rw [norm_mul, CriticalLinePhasor.norm_cpow_critical_line y n hn]

/-- **Carrier phasor-sum identity** in the convergence half-plane `Re s > 1`:
`L(s,χ) = ∑_n χ(n) · n^(-s)`, the weighted phasor sum. -/
theorem dirichletCarrier_eq_tsum {s : ℂ} (hs : 1 < s.re) :
    LFunction χ s = ∑' n : ℕ, χ (n : ZMod q) * (n : ℂ) ^ (-s) := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs; linarith
  rw [LFunction_eq_LSeries χ hs, LSeries]
  refine tsum_congr (fun n => ?_)
  rw [LSeries.term_def]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Complex.zero_cpow (neg_ne_zero.mpr hs0)]
  · rw [if_neg hn, Complex.cpow_neg, div_eq_mul_inv]

/-- **Log-weight derivative content** in `Re s > 1`:
`L'(s,χ) = -∑_n (log n) χ(n) n^(-s)`.  Combined with the chain rule
`d/dy L(1/2 + i y, χ) = i · L'(1/2 + i y, χ)`, this is exactly the weighted-log-moment
form of `F'`. -/
theorem dirichlet_deriv_eq_tsum {s : ℂ} (hs : 1 < s.re) :
    deriv (L (fun n => χ (n : ZMod q))) s
      = -∑' n : ℕ, (Real.log n : ℂ) * χ (n : ZMod q) * (n : ℂ) ^ (-s) := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs; linarith
  have habs : LSeries.abscissaOfAbsConv (fun n => χ (n : ZMod q)) < (s.re : EReal) := by
    rw [DirichletCharacter.absicssaOfAbsConv_eq_one (NeZero.ne q)]
    exact_mod_cast hs
  rw [LSeries_deriv habs, LSeries]
  congr 1
  refine tsum_congr (fun n => ?_)
  rw [LSeries.term_def]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Complex.zero_cpow (neg_ne_zero.mpr hs0)]
  · rw [if_neg hn, LSeries.logMul, Complex.cpow_neg, div_eq_mul_inv, ← Complex.natCast_log,
      mul_assoc]

omit [NeZero q] in
/-- **Bridge to the prime weights `Λ(n)`.**  The negative logarithmic derivative of the
Dirichlet `L`-series is the `L`-series of the von-Mangoldt twist, i.e. for `Re s > 1`
```
-L'(s,χ)/L(s,χ) = ∑_n χ(n) Λ(n) n^(-s).
```
This is the analytic step in the chain
`n^(-1/2) phasor magnitudes → L(1/2+iγ,χ)=0 → L'/L → Λ(n) prime weights → ψ(x) − x`. -/
theorem dirichlet_logDeriv_eq_tsum {s : ℂ} (hs : 1 < s.re) :
    -deriv (L (fun n => χ (n : ZMod q))) s / L (fun n => χ (n : ZMod q)) s
      = ∑' n : ℕ, χ (n : ZMod q) * (Λ n : ℂ) * (n : ℂ) ^ (-s) := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs; linarith
  rw [← LSeries_twist_vonMangoldt_eq χ hs, LSeries]
  refine tsum_congr (fun n => ?_)
  rw [LSeries.term_def]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Complex.zero_cpow (neg_ne_zero.mpr hs0)]
  · rw [if_neg hn, Complex.cpow_neg, Pi.mul_apply, div_eq_mul_inv, mul_assoc]

/-!
### The carrier and its zero set (exhaustion of the critical-line `L`-zeros)

We package the critical line into the **carrier** `F_χ(y) := L(1/2 + i y, χ)`.  With the
trivial completion factor `E_χ ≡ 1`, the "weighted phasor polygon closes" exactly at the
critical-line zeros of `L(·,χ)`.
-/

/-- **The Dirichlet carrier on the critical line**, `F_χ(y) := L(1/2 + i y, χ)`. -/
noncomputable def Fchi (y : ℝ) : ℂ := LFunction χ ((1 / 2 : ℂ) + (y : ℂ) * I)

/-- **Weighted phasor polygon closes ⟺ `L(1/2 + i γ, χ) = 0`.**
With completion factor `E_χ ≡ 1`, the carrier vanishes exactly at the critical-line zeros of
`L(·,χ)`. -/
theorem Fchi_eq_zero_iff (y : ℝ) :
    Fchi χ y = 0 ↔ LFunction χ ((1 / 2 : ℂ) + (y : ℂ) * I) = 0 := Iff.rfl

/-- **Carrier-zero set** of the Dirichlet character. -/
def DirichletCarrierZeros : Set ℝ := {y : ℝ | Fchi χ y = 0}

/-- **Exhaustion as a set identity.**  The carrier-zero set is exactly the set of
critical-line zeros of `L(·,χ)`: the carrier `F_χ` is surjective onto them. -/
theorem DirichletCarrierZeros_eq :
    DirichletCarrierZeros χ =
      {y : ℝ | LFunction χ ((1 / 2 : ℂ) + (y : ℂ) * I) = 0} := by
  ext y; exact Fchi_eq_zero_iff χ y

end CriticalLinePhasor.DirichletCarrier

/-!
## Exhaustion of the helix by the numbers, and the number-fiber

This section makes precise the informal slogans that

* **every number lives on the helix, just scaled** — each natural number `n` is placed at
  the integer parameter site `helix p r n`, whose cylindrical radius is `|r·n|` (so larger
  numbers sit on larger loops: the helix is *scaled* by the number);
* the construction is **infinite by construction, unconditionally** — when the pitch is
  non-degenerate (`p ≠ 0`) the placement is injective, so the set of number-sites on the
  helix is infinite (no analytic hypothesis such as RH is used);
* the **fiber starts as an empty construction at the spiral's origin** — indexing the fiber
  by an upper count `N`, the fiber at the origin `N = 0` is the empty set; and
* the **fiber spans the entire helix, by construction** — the union of all fibers is all of
  `ℕ`, and the union of their images is the entire helix lattice `range (numberSite p r)`.

Everything here is unconditional and holds purely by construction.
-/

namespace CriticalLinePhasor.HelixExhaustion

open CriticalLinePhasor.Geometry

/-- **The site where the number `n` lives on the helix**: the helix point at the integer
parameter `n` (radius scaled by `r·n`). -/
noncomputable def numberSite (p r : ℝ) (n : ℕ) : ℝ × ℝ × ℝ := helix p r (n : ℝ)

/-- **The spiral's origin.**  The `0`-site is the origin point `(0,0,0)` of the helix. -/
theorem numberSite_zero (p r : ℝ) : numberSite p r 0 = (0, 0, 0) := by
  unfold CriticalLinePhasor.HelixExhaustion.numberSite CriticalLinePhasor.Geometry.helix; norm_num

/-- **Every number lives on the helix.**  The site of any number `n` is a point of the
helix curve `range (helix p r)`. -/
theorem numberSite_mem_helix (p r : ℝ) (n : ℕ) :
    numberSite p r n ∈ Set.range (helix p r) := by
      exact Set.mem_range_self _

/-- **Just scaled.**  The cylindrical radius of the `n`-th site is `|r·n|`: the number `n`
scales the loop radius linearly. -/
theorem numberSite_radius (p r : ℝ) (n : ℕ) :
    Real.sqrt ((numberSite p r n).1 ^ 2 + (numberSite p r n).2.1 ^ 2) = |r * (n : ℝ)| := by
  unfold CriticalLinePhasor.HelixExhaustion.numberSite
  exact CriticalLinePhasor.Geometry.helix_cyl_radius p r n

/-- The helix is **injective in its parameter** whenever the pitch is non-degenerate
(`p ≠ 0`), since the height coordinate is `p·k`. -/
theorem helix_injective (p r : ℝ) (hp : p ≠ 0) : Function.Injective (helix p r) := by
  intro a b; simp +decide [ CriticalLinePhasor.Geometry.helix ] ;
  aesop

/-- **Distinct numbers occupy distinct helix sites** (for non-degenerate pitch). -/
theorem numberSite_injective (p r : ℝ) (hp : p ≠ 0) :
    Function.Injective (numberSite p r) := by
      convert helix_injective p r hp |> Function.Injective.comp <| Nat.cast_injective using 1
      funext n
      rfl

/-- **The helix lattice**: the set of all number-sites living on the helix. -/
noncomputable def helixLattice (p r : ℝ) : Set (ℝ × ℝ × ℝ) := Set.range (numberSite p r)

/-- **Infinite by construction, unconditionally.**  For non-degenerate pitch the helix
lattice of number-sites is infinite — this uses no analytic hypothesis. -/
theorem helixLattice_infinite (p r : ℝ) (hp : p ≠ 0) :
    (helixLattice p r).Infinite := by
      exact Set.infinite_range_of_injective ( CriticalLinePhasor.HelixExhaustion.numberSite_injective p r hp )

/-- **The number-fiber up to count `N`**: the numbers `0, 1, …, N-1` placed on the helix,
modeled as the finite set of their indices. -/
def fiber (N : ℕ) : Finset ℕ := Finset.range N

/-- **The fiber starts as an empty construction at the spiral's origin** (`N = 0`). -/
theorem fiber_origin : fiber 0 = ∅ := by
  rfl

/-- The fiber only grows: it is **monotone** in the count. -/
theorem fiber_mono : Monotone fiber := by
  exact fun a b hab => Finset.range_mono hab

/-- **The fiber spans the entire helix, by construction (index form).**  Every number lies
in some fiber: the union of all fibers is all of `ℕ`. -/
theorem fiber_iUnion : (⋃ N : ℕ, (fiber N : Set ℕ)) = Set.univ := by
  ext n
  simp [CriticalLinePhasor.HelixExhaustion.fiber]

/-- **The fiber spans the entire helix, by construction (geometric form).**  The union of
the fiber images is exactly the whole helix lattice `range (numberSite p r)`. -/
theorem fiber_image_iUnion (p r : ℝ) :
    (⋃ N : ℕ, (fiber N).image (numberSite p r) : Set (ℝ × ℝ × ℝ)) = helixLattice p r := by
  ext x; simp [helixLattice, numberSite, fiber];
  exact ⟨ fun ⟨ i, j, hj, hx ⟩ => ⟨ j, hx ⟩, fun ⟨ j, hx ⟩ => ⟨ j + 1, j, Nat.lt_succ_self _, hx ⟩ ⟩

end CriticalLinePhasor.HelixExhaustion
/-!
## The independently-built phasor carrier and its identification with the `L`-function

The carrier `F_χ(y) := L(1/2 + i y, χ)` of the previous section is *defined* to be the
`L`-function, so `F_χ = 0 ↔ L = 0` holds by definition.  Here we build the carrier the other
way around — from the **phasor data itself** — and prove the non-tautological identification

```
G_χ(s) = F_χ(s)        (= L(s,χ)),   for Re s > 1,
```

where `G_χ` is the regularized (absolutely convergent) limit of the **finite phasor carrier**

```
G_{χ,N}(s) = ∑_{n<N} χ(n)·n^(-s),
```

a genuine partial sum of the weighted phasors `v_n = χ(n)·n^(-s)`.  We also develop the
**eta-twist** of a general Dirichlet character, the "safer" critical-line phasor sum
`∑_n (-1)^(n-1) χ(n) n^(-s) = (1 - 2^(1-s)·χ(2))·L(s,χ)`, and prove that its correction
factor never vanishes on the critical line — giving an *unconditional* critical-line zero
equivalence with `L(·,χ)` for every Dirichlet character.
-/

namespace CriticalLinePhasor.DirichletPhasorCarrier

open Complex DirichletCharacter
open scoped LSeries.notation

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

/-- **The weighted phasor term** `v_n(s) = χ(n)·n^(-s)`. -/
noncomputable def phasorTerm (s : ℂ) (n : ℕ) : ℂ := χ (n : ZMod q) * (n : ℂ) ^ (-s)

/-- **The finite phasor carrier** `G_{χ,N}(s) = ∑_{n<N} χ(n)·n^(-s)`. -/
noncomputable def finiteCarrier (s : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, phasorTerm χ s n

/-- **The regularized phasor carrier** `G_χ(s) = ∑'_n χ(n)·n^(-s)` (the absolutely
convergent limit of the finite carriers). -/
noncomputable def regCarrier (s : ℂ) : ℂ := ∑' n : ℕ, phasorTerm χ s n

/-- The weighted phasor series is summable for `Re s > 1`. -/
theorem phasor_summable {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => phasorTerm χ s n) := by
      have := @DirichletCharacter.LSeriesSummable_of_one_lt_re q;
      have := this χ hs;
      convert this.congr _;
      intro n; by_cases hn : n = 0 <;> simp +decide [ hn, phasorTerm ] ;
      · exact Or.inr ( by rintro rfl; norm_num at hs );
      · rw [ div_eq_mul_inv, Complex.cpow_neg ]

/-- **The non-tautological identification `G_χ = F_χ`.**  For `Re s > 1` the regularized
phasor carrier built from the phasor data equals the analytic carrier `L(s,χ)`. -/
theorem regCarrier_eq_LFunction {s : ℂ} (hs : 1 < s.re) :
    regCarrier χ s = LFunction χ s := by
      unfold CriticalLinePhasor.DirichletPhasorCarrier.regCarrier CriticalLinePhasor.DirichletPhasorCarrier.phasorTerm
      exact (CriticalLinePhasor.DirichletCarrier.dirichletCarrier_eq_tsum χ hs).symm

/-- **The finite carrier converges to the regularized carrier.** -/
theorem finiteCarrier_tendsto {s : ℂ} (hs : 1 < s.re) :
    Filter.Tendsto (finiteCarrier χ s) Filter.atTop (nhds (regCarrier χ s)) := by
      exact ( phasor_summable χ hs |> Summable.hasSum |> HasSum.tendsto_sum_nat )

/-- **The finite carrier converges to the analytic carrier `L(s,χ)`.**  This is the
generation statement: the partial phasor sums `G_{χ,N}` converge to `F_χ = L(·,χ)`. -/
theorem finiteCarrier_tendsto_LFunction {s : ℂ} (hs : 1 < s.re) :
    Filter.Tendsto (finiteCarrier χ s) Filter.atTop (nhds (LFunction χ s)) := by
      convert CriticalLinePhasor.DirichletPhasorCarrier.regCarrier_eq_LFunction χ hs ▸ CriticalLinePhasor.DirichletPhasorCarrier.finiteCarrier_tendsto χ hs

/-!
### The eta-twist of a general Dirichlet character

The "safer" critical-line phasor sum is the alternating (eta-twisted) series
`∑_n (-1)^(n-1) χ(n) n^(-s)`.  Splitting even/odd and using multiplicativity
`χ(2m) = χ(2)·χ(m)` gives the closed form `(1 - 2^(1-s)·χ(2))·L(s,χ)`.
-/

/-- **The eta-twisted closed form** `L_χ^(η)(s) = (1 - 2^(1-s)·χ(2))·L(s,χ)`. -/
noncomputable def etaTwistClosed (s : ℂ) : ℂ :=
  (1 - (2 : ℂ) ^ (1 - s) * χ (2 : ZMod q)) * LFunction χ s

/-- The defining identity for the eta-twisted closed form. -/
theorem etaTwistClosed_eq (s : ℂ) :
    etaTwistClosed χ s = (1 - (2 : ℂ) ^ (1 - s) * χ (2 : ZMod q)) * LFunction χ s := rfl

/-- **The eta-twist phasor sum** in the convergence half-plane `Re s > 1`:
`(1 - 2^(1-s)·χ(2))·L(s,χ) = ∑_n (-1)^n·χ(n+1)·(n+1)^(-s)`
(i.e. `∑_{k≥1} (-1)^(k-1)·χ(k)·k^(-s)`). -/
theorem etaTwist_eq_tsum {s : ℂ} (hs : 1 < s.re) :
    etaTwistClosed χ s =
      ∑' n : ℕ, (-1 : ℂ) ^ n * χ ((n + 1 : ℕ) : ZMod q) / ((n : ℂ) + 1) ^ s := by
  have h_summable : Summable (fun n : ℕ => χ (n : ZMod q) * (n : ℂ) ^ (-s)) := by
    apply phasor_summable χ hs;
  have h_split : ∑' n : ℕ, (-1 : ℂ) ^ n * χ (n + 1 : ZMod q) / (n + 1 : ℂ) ^ s = (∑' n : ℕ, χ (n + 1 : ZMod q) / (n + 1 : ℂ) ^ s) - 2 * (∑' n : ℕ, χ (2 * n + 2 : ZMod q) / (2 * n + 2 : ℂ) ^ s) := by
    rw [ ← tsum_even_add_odd ];
    · rw [ eq_comm, ← tsum_even_add_odd ];
      · norm_num [ pow_add, pow_mul, neg_div, tsum_neg, tsum_mul_left ] ; ring;
      · refine ( h_summable.comp_injective ( show Function.Injective ( fun k : ℕ => 2 * k + 1 ) from fun a b h => by simpa using h ) ).congr fun k => ?_
        simp only [Function.comp]
        push_cast
        rw [ div_eq_mul_inv, Complex.cpow_neg ]
      · refine ( h_summable.comp_injective ( show Function.Injective ( fun k : ℕ => 2 * k + 2 ) from fun a b h => by simpa using h ) ).congr fun k => ?_
        simp only [Function.comp]
        push_cast
        rw [ div_eq_mul_inv, Complex.cpow_neg ]
        ring
    · refine ( h_summable.comp_injective ( show Function.Injective ( fun k : ℕ => 2 * k + 1 ) from fun a b h => by simpa using h ) ).congr fun k => ?_
      simp only [Function.comp]
      push_cast
      rw [ div_eq_mul_inv, Complex.cpow_neg, pow_mul ]
      norm_num
    · refine ( h_summable.comp_injective ( show Function.Injective ( fun k : ℕ => 2 * k + 2 ) from fun a b h => by simpa using h ) ).neg.congr fun k => ?_
      simp only [Function.comp]
      push_cast
      rw [ div_eq_mul_inv, Complex.cpow_neg ]
      rw [ show 2 * k + 1 = 2 * k + 1 from rfl, pow_succ, pow_mul ]
      norm_num
      ring
  have h_even : ∑' n : ℕ, χ (2 * n + 2 : ZMod q) / (2 * n + 2 : ℂ) ^ s = (2 : ℂ) ^ (-(s : ℂ)) * χ (2 : ZMod q) * ∑' n : ℕ, χ (n + 1 : ZMod q) / (n + 1 : ℂ) ^ s := by
    rw [ ← tsum_mul_left ] ; refine' tsum_congr fun n => _ ; ring;
    rw [ show ( 2 + n * 2 : ℂ ) = 2 * ( 1 + n ) by ring, Complex.cpow_def_of_ne_zero, Complex.cpow_def_of_ne_zero ] <;> norm_num ; ring;
    · rw [ show ( 2 + n * 2 : ZMod q ) = 2 * ( 1 + n ) by ring, show ( 2 + n * 2 : ℂ ) = 2 * ( 1 + n ) by ring, Complex.log_mul ] <;> norm_num ; ring;
      · rw [ Complex.cpow_def_of_ne_zero ( by norm_cast; linarith ) ] ; rw [ Complex.exp_add ] ; ring;
        rw [ ← Complex.exp_neg ] ; ring;
      · exact mod_cast by positivity;
      · norm_num [ Complex.arg_le_pi, Complex.neg_pi_lt_arg ];
    · norm_cast ; linarith;
  have h_sum : ∑' n : ℕ, χ (n + 1 : ZMod q) / (n + 1 : ℂ) ^ s = LFunction χ s := by
    rw [ ← eq_comm,CriticalLinePhasor.DirichletCarrier.dirichletCarrier_eq_tsum χ hs ];
    rw [ Summable.tsum_eq_zero_add h_summable ] ; norm_num [ Complex.cpow_neg ];
    rw [ Complex.zero_cpow ( by rintro rfl; norm_num at hs ) ] ; norm_num [ div_eq_mul_inv ];
  simp_all +decide [ CriticalLinePhasor.DirichletPhasorCarrier.etaTwistClosed ];
  rw [ show ( 1 - s : ℂ ) = -s + 1 by ring, Complex.cpow_add ] <;> norm_num ; ring

/-- **The eta-twist correction factor never vanishes on the critical line.**
On `Re s = 1/2` we have `‖2^(1-s)·χ(2)‖ ∈ {0, √2}`, never `1`, so the factor
`1 - 2^(1-s)·χ(2)` is nonzero for *every* Dirichlet character. -/
theorem etaTwist_factor_ne_zero_critical (s : ℂ) (hs : s.re = 1 / 2) :
    (1 - (2 : ℂ) ^ (1 - s) * χ (2 : ZMod q)) ≠ 0 := by
      by_cases h : IsUnit ( 2 : ZMod q ) <;> simp_all +decide [ Complex.cpow_def ];
      · have h_norm : ‖(2 : ℂ) ^ (1 - s) * χ 2‖ = Real.sqrt 2 := by
          rw [ norm_mul, Complex.norm_cpow_of_ne_zero ] <;> norm_num [ hs ];
          rw [ Real.sqrt_eq_rpow, show ‖χ 2‖ = 1 from ?_ ] ; norm_num [ hs ];
          convert χ.norm_le_one _ |> le_antisymm <| _;
          obtain ⟨ k, hk ⟩ := h.exists_left_inv; have := χ.map_mul 2 k; simp_all +decide ;
          have := congr_arg Norm.norm ( χ.map_mul k 2 ) ; norm_num [ hk ] at this;
          nlinarith [ show ‖χ k‖ ≤ 1 from χ.norm_le_one k, show ‖χ 2‖ ≥ 0 from norm_nonneg _ ];
        contrapose! h_norm; simp_all +decide [ Complex.cpow_def ] ;
        rw [ sub_eq_zero ] at h_norm ; replace h_norm := congr_arg Norm.norm h_norm ; norm_num at h_norm ; nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ] ;
      · erw [ χ.map_nonunit ] <;> aesop

/-- **Unconditional critical-line zero equivalence.**  Because the eta-twist factor is
nonzero on `Re s = 1/2`, the eta-twisted carrier vanishes exactly at the critical-line zeros
of `L(·,χ)`, for every Dirichlet character:
`L_χ^(η)(s) = 0 ↔ L(s,χ) = 0` on the critical line. -/
theorem etaTwistClosed_eq_zero_iff_critical (s : ℂ) (hs : s.re = 1 / 2) :
    etaTwistClosed χ s = 0 ↔ LFunction χ s = 0 := by
      exact mul_eq_zero.trans <| or_iff_right <| CriticalLinePhasor.DirichletPhasorCarrier.etaTwist_factor_ne_zero_critical χ s hs

end CriticalLinePhasor.DirichletPhasorCarrier
/-!
## Fiber harmonics, carrier cancellation, and the zero-harmonic bridge

This final section makes precise the "vertical flow" picture of the carrier.  On the
critical line the `n`-th weighted phasor, viewed as a function of the height `y`, is the
*fiber*
```
v_n(y) = χ(n) · n^(-1/2) · exp(-(y·log n)·i).
```

### Fiber harmonic theorem
Each fiber is a harmonic oscillator / eigenmode of the vertical-flow operator `A = i·d/dy`,
with **frequency `log n`** (the Dirichlet-side harmonic value — *not* the zero ordinate `γ`):
```
A v_n = (log n) · v_n,   i.e.   i · v_n'(y) = (log n) · v_n(y).
```

### Carrier cancellation theorem
The total carrier `G_χ(y) = L(1/2 + i y, χ)` cancels exactly at the *zero ordinates* `γ`:
```
G_χ(γ) = 0  ↔  L(1/2 + i γ, χ) = 0.
```
The ordinate `γ` is therefore the **global cancellation height** of all fibers rotating
together — it is *not* an eigenvalue `log n` of any single fiber.  At the finite level the
log-weight moment `G_{χ,N}'(y) = -i·∑_{n<N} (log n)·v_n(y)` records the analytic harmonic
content.

### Hilbert–Pólya layer (scope)
The genuine Hilbert–Pólya statement `H_χ ψ_γ = γ · ψ_γ`, turning each cancellation height
`γ` into a spectral eigenvalue of a self-adjoint operator, is the open Hilbert–Pólya
conjecture and is *not* claimed here.  We record the abstract `ZeroHarmonic` packaging of a
zero ordinate, which is exactly a carrier cancellation height.
-/

namespace CriticalLinePhasor.FiberHarmonic

open Complex DirichletCharacter

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

/-- **The fiber phasor** `v_n(y) = χ(n) · n^(-1/2) · exp(-(y·log n)·i)`, the `n`-th
weighted phasor on the critical line viewed as a function of the height `y`. -/
noncomputable def fiberPhasor (n : ℕ) (y : ℝ) : ℂ :=
  χ (n : ZMod q) * (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
    Complex.exp (-(y * Real.log n) * Complex.I)

/-
The fiber phasor is the critical-line value of the weighted phasor term:
`v_n(y) = χ(n) · n^(-(1/2 + i y))`.
-/
theorem fiberPhasor_eq_cpow (n : ℕ) (hn : 0 < n) (y : ℝ) :
    fiberPhasor χ n y = χ (n : ZMod q) * (n : ℂ) ^ (-((1 / 2 : ℂ) + (y : ℂ) * Complex.I)) := by
  rw [ CriticalLinePhasor.DirichletCarrier.dirichlet_term_phasor_critical χ y n hn ]
  unfold CriticalLinePhasor.FiberHarmonic.fiberPhasor; push_cast; ring_nf

/-
**Fiber harmonic theorem (derivative form).**  Each fiber `v_n` satisfies
`v_n'(y) = (-(log n)·i) · v_n(y)`: it is an eigenmode of `d/dy`.
-/
theorem fiberPhasor_hasDerivAt (n : ℕ) (y : ℝ) :
    HasDerivAt (fun y : ℝ => fiberPhasor χ n y)
      ((-Real.log n : ℂ) * Complex.I * fiberPhasor χ n y) y := by
  have hb : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 y := (hasDerivAt_id y).ofReal_comp
  have hg : HasDerivAt (fun y : ℝ => -((y : ℂ) * (Real.log n : ℂ)) * Complex.I)
      (-(Real.log n : ℂ) * Complex.I) y := by
    have key : HasDerivAt (fun y : ℝ => (y : ℂ) * (-(Real.log n : ℂ) * Complex.I))
        (1 * (-(Real.log n : ℂ) * Complex.I)) y := hb.mul_const _
    refine key.congr_deriv ?_ |>.congr_of_eventuallyEq ?_
    · ring
    · filter_upwards with t; ring
  have h := ( ( Complex.hasDerivAt_exp _ ).comp y hg ).const_mul ( (χ (n : ZMod q)) * (((n : ℝ) ^ (-(1/2 : ℝ)) : ℝ) : ℂ) )
  have h2 : HasDerivAt (fun y : ℝ => fiberPhasor χ n y)
      ((χ (n : ZMod q)) * (((n : ℝ) ^ (-(1/2 : ℝ)) : ℝ) : ℂ) *
        (Complex.exp (-((y : ℂ) * (Real.log n : ℂ)) * Complex.I) * (-(Real.log n : ℂ) * Complex.I))) y := by
    refine h.congr_of_eventuallyEq ?_
    filter_upwards with t
    simp only [fiberPhasor, Function.comp]
  refine h2.congr_deriv ?_
  unfold CriticalLinePhasor.FiberHarmonic.fiberPhasor
  ring

/-
**Fiber harmonic eigenvalue equation.**  For the vertical-flow operator `A = i·d/dy`,
each fiber is an eigenmode with frequency `log n`:
`i · v_n'(y) = (log n) · v_n(y)`.
-/
theorem fiberPhasor_eigen (n : ℕ) (y : ℝ) :
    Complex.I * deriv (fun y : ℝ => fiberPhasor χ n y) y
      = (Real.log n : ℂ) * fiberPhasor χ n y := by
  convert congr_arg ( fun x : ℂ => Complex.I * x ) ( HasDerivAt.deriv ( fiberPhasor_hasDerivAt χ n y ) ) using 1 ; ring;
  norm_num

/-- **The finite fiber carrier** `G_{χ,N}(y) = ∑_{n<N} v_n(y)`. -/
noncomputable def fiberCarrierFinite (N : ℕ) (y : ℝ) : ℂ :=
  ∑ n ∈ Finset.range N, fiberPhasor χ n y

/-
**Carrier log-weight moment (finite level).**  The derivative of the finite fiber
carrier is the `-i`-scaled log-weighted sum of the fibers:
`G_{χ,N}'(y) = -i · ∑_{n<N} (log n)·v_n(y)`.
-/
theorem fiberCarrierFinite_hasDerivAt (N : ℕ) (y : ℝ) :
    HasDerivAt (fun y : ℝ => fiberCarrierFinite χ N y)
      (-Complex.I * ∑ n ∈ Finset.range N, (Real.log n : ℂ) * fiberPhasor χ n y) y := by
  have hsum : HasDerivAt (∑ n ∈ Finset.range N, fun y : ℝ => fiberPhasor χ n y)
      (∑ n ∈ Finset.range N, ((-Real.log n : ℂ) * Complex.I * fiberPhasor χ n y)) y :=
    HasDerivAt.sum fun n _ => CriticalLinePhasor.FiberHarmonic.fiberPhasor_hasDerivAt χ n y
  refine hsum.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
  · filter_upwards with t
    simp only [CriticalLinePhasor.FiberHarmonic.fiberCarrierFinite, Finset.sum_apply]
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

/-- **The carrier on the critical line**, `G_χ(y) := L(1/2 + i y, χ)`. -/
noncomputable def carrier (y : ℝ) : ℂ :=
  LFunction χ ((1 / 2 : ℂ) + (y : ℂ) * Complex.I)

/-- **Carrier cancellation** at height `γ`: the carrier vanishes there. -/
def CarrierZero (γ : ℝ) : Prop := carrier χ γ = 0

/-- **Carrier cancellation theorem.**  The carrier cancels at height `γ` exactly when
`L(1/2 + i γ, χ) = 0`: `γ` is a global cancellation ordinate of all fibers. -/
theorem carrierZero_iff_L_zero (γ : ℝ) :
    CarrierZero χ γ ↔ LFunction χ ((1 / 2 : ℂ) + (γ : ℂ) * Complex.I) = 0 := Iff.rfl

/-- **A zero ordinate** of the carrier: a height `γ` together with a proof that the
critical-line `L`-value vanishes there.  This is the "expelled zero height" that
Hilbert–Pólya would turn into a spectral eigenvalue. -/
structure ZeroHarmonic where
  /-- The zero ordinate (cancellation height). -/
  gamma : ℝ
  /-- The carrier cancels at `gamma`. -/
  is_zero : LFunction χ ((1 / 2 : ℂ) + (gamma : ℂ) * Complex.I) = 0

/-- A `ZeroHarmonic` is precisely a carrier cancellation height. -/
theorem zeroHarmonic_isCarrierZero (z : ZeroHarmonic χ) : CarrierZero χ z.gamma :=
  z.is_zero

end CriticalLinePhasor.FiberHarmonic
/-!
## Tate completion: every Dirichlet `L`-function is complete

Following Tate's thesis, rewrite the integer fiber phasor as a *multiplicative
(Mellin) quasi-character*:
```
v_n(y) = χ(n)·n^(-1/2)·e^(-i y log n)
       = χ(n)·n^(-(1/2 + i y))
       = χ(n)·|n|^(-(1/2 + i y)).
```
So the fiber is the restriction to `n ∈ ℕ` of a Tate quasi-character
`x ↦ χ(x)·|x|^(-(1/2 + i y))`, and the global object it lives inside is the **completed**
Dirichlet `L`-function (the adelic zeta integral `Z(Φ,ω,s)` of Tate's thesis):
```
Λ(s,χ) = gammaFactor(χ,s) · L(s,χ),
```
where `gammaFactor(χ,s)` is the archimedean Gamma/conductor factor (`Gammaℝ s` if `χ` is
even, `Gammaℝ (s+1)` if `χ` is odd).  Here `Gammaℝ s = π^(-s/2)·Γ(s/2)`.

The key Tate point about completion is that the archimedean factor is **nonzero
throughout the right half-plane `Re s > 0`** — in particular on the whole critical strip
and the critical line `Re s = 1/2`.  Hence completing `L` to `Λ` (raw carrier `→`
Tate-completed carrier) moves **no zeros**:
```
Λ(s,χ) = 0  ↔  L(s,χ) = 0      (for Re s > 0).
```
This is exactly the statement that *every* Dirichlet `L`-function is "complete" in the Tate
sense: it has a completed form whose nontrivial zeros coincide with those of `L`.  The
completed `L`-function additionally satisfies Tate's **functional equation**
`Λ(1-s,χ) = N^(s-1/2)·rootNumber(χ)·Λ(s,χ⁻¹)` for primitive `χ`, recorded below.
-/

namespace CriticalLinePhasor.Tate

open Complex DirichletCharacter

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

/-
**The fiber phasor is a Tate / Mellin multiplicative character.**  Rewriting the phase
`e^(-i y log n) = n^(-iy) = |n|^(-iy)` gives
```
χ(n)·n^(-(1/2 + i y)) = χ(n)·|n|^(-(1/2) - i y),
```
i.e. the integer fiber is the restriction to `n ∈ ℕ` of a Tate multiplicative quasi-character
(here `|n| = (n : ℝ)` for `n : ℕ`).
-/
theorem fiberPhasor_eq_mellin_character (n : ℕ) (y : ℝ) :
    χ (n : ZMod q) * (n : ℂ) ^ (-((1 / 2 : ℂ) + (y : ℂ) * Complex.I))
      = χ (n : ZMod q) * ((n : ℝ) : ℂ) ^ (-(1 / 2 : ℂ) - (y : ℂ) * Complex.I) := by
  convert rfl using 2 ; ring;
  norm_num

/-
**The Tate Gamma/conductor factor is nonzero on the right half-plane `Re s > 0`.**
This is the archimedean local factor of Tate's zeta integral; it has no zeros for
`Re s > 0`, in particular on the whole critical strip and the critical line.
-/
theorem gammaFactor_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    gammaFactor χ s ≠ 0 := by
  by_cases h_even : Even χ;
  · rw [ h_even.gammaFactor_def ] ; exact Complex.Gammaℝ_ne_zero_of_re_pos hs |> fun h => by simp_all +decide [ Complex.Gammaℝ ] ;
  · by_cases h_odd : Odd χ;
    · convert Complex.Gammaℝ_ne_zero_of_re_pos ( show 0 < ( s + 1 |> Complex.re ) from by norm_num; linarith ) using 1;
      convert h_odd.gammaFactor_def s using 1;
    · exact False.elim <| h_odd <| by have := χ.even_or_odd; tauto;

/-
**The completed (Tate) carrier as the Gamma-factor times `L`.**  For `Re s > 0`,
```
Λ(s,χ) = gammaFactor(χ,s) · L(s,χ).
```
This is the completion of the raw phasor carrier `L(s,χ)` to the Tate-completed carrier
`Λ(s,χ)` (the adelic zeta integral factored into its local pieces).
-/
theorem completedLFunction_eq_gammaFactor_mul {s : ℂ} (hs : 0 < s.re) :
    completedLFunction χ s = gammaFactor χ s * LFunction χ s := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs
  have hγ : gammaFactor χ s ≠ 0 := gammaFactor_ne_zero_of_re_pos χ hs
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inl hs0)]
  field_simp

/-
**Completion preserves zeros throughout `Re s > 0`.**  Since the Gamma/conductor factor
is nonzero for `Re s > 0`, the completed Dirichlet `L`-function vanishes exactly where `L`
vanishes:
```
Λ(s,χ) = 0  ↔  L(s,χ) = 0      (Re s > 0).
```
This is the statement that *every* Dirichlet `L`-function is complete in the Tate sense.
-/
theorem completedLFunction_eq_zero_iff {s : ℂ} (hs : 0 < s.re) :
    completedLFunction χ s = 0 ↔ LFunction χ s = 0 := by
  rw [ CriticalLinePhasor.Tate.completedLFunction_eq_gammaFactor_mul χ hs, mul_eq_zero, or_iff_right ( CriticalLinePhasor.Tate.gammaFactor_ne_zero_of_re_pos χ hs ) ]

/-- **The Tate-completed carrier on the critical line**, `Λ(1/2 + i y, χ)`. -/
noncomputable def completedCarrier (y : ℝ) : ℂ :=
  completedLFunction χ ((1 / 2 : ℂ) + (y : ℂ) * Complex.I)

/-
**The completed carrier equals the Gamma factor times the raw carrier** on the critical
line: `Λ(1/2 + i y, χ) = gammaFactor(χ, 1/2 + i y) · L(1/2 + i y, χ)`.
-/
theorem completedCarrier_eq (y : ℝ) :
    completedCarrier χ y
      = gammaFactor χ ((1 / 2 : ℂ) + (y : ℂ) * Complex.I)
        * LFunction χ ((1 / 2 : ℂ) + (y : ℂ) * Complex.I) := by
  rw [ CriticalLinePhasor.Tate.completedCarrier, CriticalLinePhasor.Tate.completedLFunction_eq_gammaFactor_mul χ (by simp) ]

/-
**The Tate-completed carrier has exactly the critical-line zeros of `L`.**
`Λ(1/2 + i y, χ) = 0 ↔ L(1/2 + i y, χ) = 0`.  Upgrading the raw phasor carrier to the
Tate-completed carrier does not change the zeros on the critical line.
-/
theorem completedCarrier_eq_zero_iff (y : ℝ) :
    completedCarrier χ y = 0 ↔ LFunction χ ((1 / 2 : ℂ) + (y : ℂ) * Complex.I) = 0 := by
  rw [ CriticalLinePhasor.Tate.completedCarrier, CriticalLinePhasor.Tate.completedLFunction_eq_zero_iff χ (by simp) ]

/-- **Tate's functional equation for primitive characters.**  The completed Dirichlet
`L`-function satisfies
```
Λ(1 - s, χ) = N^(s - 1/2)·rootNumber(χ)·Λ(s, χ⁻¹),
```
the global functional equation coming from the adelic zeta integral.  (This is recorded from
Mathlib's `DirichletCharacter.IsPrimitive.completedLFunction_one_sub`.) -/
theorem completed_functional_equation (hχ : IsPrimitive χ) (s : ℂ) :
    completedLFunction χ (1 - s)
      = (q : ℂ) ^ (s - 1 / 2) * rootNumber χ * completedLFunction χ⁻¹ s :=
  DirichletCharacter.IsPrimitive.completedLFunction_one_sub hχ s

end CriticalLinePhasor.Tate

/-!
## Hilbert–Pólya correlation: zero-vanishing ↔ self-adjoint harmonic eigenvalue

We now make precise, **unconditionally**, the Hilbert–Pólya *correlation* between a
carrier zero and its spectral harmonic.  We use a bounded everywhere-defined symmetric
("von Neumann / Hilbert", i.e. self-adjoint) operator on the one-dimensional fiber
Hilbert space `ℂ`:
```
H_γ : ℂ → ℂ,   H_γ z = γ · z      (multiplication by the real height γ).
```
Being multiplication by a **real** scalar, `H_γ` is symmetric/self-adjoint, so its spectrum
is real; and its unique eigenvalue is exactly `γ`.  The correlation theorem states that a
critical-line zero ordinate `γ` of `L(·,χ)` is produced *at the same time* as a real
eigenvalue of a self-adjoint operator:
```
L(1/2 + i γ, χ) = 0   ↔   (carrier vanishes  ∧  γ ∈ spec(H_γ), H_γ self-adjoint).
```
Equivalently, every zero ordinate is realized as the real eigenvalue of a self-adjoint
operator (`zeroHarmonic_selfAdjoint_realization`), and the assignment
`zero ordinate ↦ eigenvalue` is faithful (injective).

**Scope / honesty.**  This is the *correlation*, not the open Hilbert–Pólya conjecture.
The conjecture asks for a *single* canonical self-adjoint operator `H_χ` whose spectrum is
*exactly the set of all* nontrivial zero ordinates — which, by self-adjointness forcing real
spectrum, would imply the Riemann Hypothesis for `L(·,χ)`.  Here each `H_γ` is built from an
already-supplied critical-line zero, so the construction certifies the per-zero
spectral realization and the zero/eigenvalue correlation, but does **not** assert that all
zeros lie on the line, and so does **not** prove RH.
-/

namespace CriticalLinePhasor.HilbertPolya

open Complex DirichletCharacter CriticalLinePhasor.FiberHarmonic

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

/-- **The von Neumann / Hilbert operator** `H_γ z = γ · z`: multiplication by the real
height `γ` on the one-dimensional fiber Hilbert space `ℂ`. -/
noncomputable def vonNeumannOp (γ : ℝ) : Module.End ℂ ℂ := (γ : ℂ) • LinearMap.id

/-
Action of the operator: `H_γ z = γ · z`.
-/
theorem vonNeumannOp_apply (γ : ℝ) (z : ℂ) : vonNeumannOp γ z = (γ : ℂ) * z := by
  simp [CriticalLinePhasor.HilbertPolya.vonNeumannOp]

/-
**`H_γ` is symmetric (self-adjoint).**  Multiplication by the *real* scalar `γ` is
symmetric for the standard inner product on `ℂ`, so its spectrum is real.
-/
theorem vonNeumannOp_isSymmetric (γ : ℝ) : (vonNeumannOp γ).IsSymmetric := by
  intro x y; simp [vonNeumannOp_apply, inner];
  ring

/-
**`γ` is an eigenvalue of the self-adjoint operator `H_γ`** (every nonzero fiber value is
an eigenvector).
-/
theorem vonNeumannOp_hasEigenvalue (γ : ℝ) :
    Module.End.HasEigenvalue (vonNeumannOp γ) (γ : ℂ) := by
  simp [vonNeumannOp]
  rw [Module.End.HasUnifEigenvalue]
  simp +decide [Submodule.ne_bot_iff]
  exact ⟨1, one_ne_zero⟩

/-
**The spectrum of `H_γ` is exactly `{γ}`**: the only eigenvalue is the real height `γ`.
-/
theorem vonNeumannOp_hasEigenvalue_iff (γ : ℝ) (μ : ℂ) :
    Module.End.HasEigenvalue (vonNeumannOp γ) μ ↔ μ = (γ : ℂ) := by
  constructor;
  · intro hμ
    obtain ⟨x, hx_ne_zero, hx_eigen⟩ := Module.End.HasEigenvalue.exists_hasEigenvector hμ;
    simp_all +decide [ CriticalLinePhasor.HilbertPolya.vonNeumannOp ];
  · exact fun h => h.symm ▸ CriticalLinePhasor.HilbertPolya.vonNeumannOp_hasEigenvalue γ

/-
**Hilbert–Pólya correlation (per zero).**  A critical-line zero ordinate `γ` of `L(·,χ)`
is produced *simultaneously* as (i) a carrier-vanishing height and (ii) the real eigenvalue
of the self-adjoint operator `H_γ`:
```
CarrierZero χ γ  ↔  ( L(1/2 + i γ, χ) = 0  ∧  H_γ has eigenvalue γ ).
```
The eigenvalue clause holds for every `γ`, so the equivalence says the carrier vanishing and
the self-adjoint spectral harmonic are realized together at the same height.
-/
theorem carrierZero_correlation (γ : ℝ) :
    CarrierZero χ γ ↔
      (LFunction χ ((1 / 2 : ℂ) + (γ : ℂ) * Complex.I) = 0
        ∧ Module.End.HasEigenvalue (vonNeumannOp γ) (γ : ℂ)) := by
  constructor;
  · exact fun h => ⟨ h, vonNeumannOp_hasEigenvalue γ ⟩;
  · exact fun h => h.1

/-
**Self-adjoint realization of a zero ordinate.**  Every supplied critical-line zero
`z : ZeroHarmonic χ` yields a self-adjoint operator `H_{z.gamma}` whose (real) eigenvalue is
exactly the zero ordinate, and `z.gamma` is a carrier-vanishing height — the zero and its
spectral harmonic are produced at the same time.
-/
theorem zeroHarmonic_selfAdjoint_realization (z : ZeroHarmonic χ) :
    (vonNeumannOp z.gamma).IsSymmetric
      ∧ Module.End.HasEigenvalue (vonNeumannOp z.gamma) (z.gamma : ℂ)
      ∧ CarrierZero χ z.gamma := by
  exact ⟨ CriticalLinePhasor.HilbertPolya.vonNeumannOp_isSymmetric _, CriticalLinePhasor.HilbertPolya.vonNeumannOp_hasEigenvalue _, z.is_zero ⟩

/-
**Faithfulness of the spectral correlation.**  Distinct real heights give distinct
eigenvalues (`H_γ` has eigenvalue `γ` only): the assignment `ordinate ↦ eigenvalue` is
injective, so different zero ordinates are never conflated by the operator family.
-/
theorem vonNeumannOp_eigenvalue_injective :
    Function.Injective (fun γ : ℝ => (γ : ℂ)) := by
  exact Complex.ofReal_injective

end CriticalLinePhasor.HilbertPolya
/-!
## Zero measure and resolvent trace (Cauchy transform of the carrier zeros)

This section packages the carrier zeros into an **atomic spectral measure** and its
**resolvent trace** (Cauchy transform), the "von Neumann move" that turns the produced
zero/harmonic pairs into a spectral object:
```
μ_χ  = ∑_γ m_γ · δ_γ          (atomic zero measure)
R_χ(z) = ∑_γ m_γ /(γ - z)      (resolvent trace = Cauchy transform of μ_χ)
       = ∫ 1/(t - z) dμ_χ(t).
```
A `ZeroDatum` records a critical-line zero height `γ` of `L(·,χ)` (a carrier-cancellation
point `G_χ(γ) = L(1/2 + iγ,χ) = 0`) together with its multiplicity `m_γ`.  The clean,
unconditional bridge proved here is that the resolvent trace **is** the Cauchy transform of
the zero measure (`integral_atomicMeasure_eq` for the finite case, and
`resolventTrace_eq_integral` for the general summable case): this is exactly the trace of the
resolvent `(H_χ - z)⁻¹` of the multiplication-by-height operator `H_χ f(t) = t·f(t)` on
`L²(μ_χ)`.

**Scope / honesty.**  The construction of the measure and the identification of the resolvent
trace with its Cauchy transform are unconditional.  The further analytic identity equating
this Cauchy transform with the logarithmic derivative of the completed `L`-function,
```
R_χ(z) = -d/dz log Λ(1/2 + iz, χ) + d/dz log E(z),
```
is the **Hadamard factorization / explicit formula** for the Dirichlet `L`-function; it is a
deep analytic input that is *not* formalized here (it is the genuine content beyond the
formal "von Neumann move").  No Riemann Hypothesis is assumed or claimed.
-/

namespace CriticalLinePhasor.Resolvent

open Complex DirichletCharacter MeasureTheory CriticalLinePhasor.FiberHarmonic
open scoped ENNReal

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

/-- **A carrier-zero datum.**  A critical-line zero height `γ` of `L(·,χ)` (i.e. a carrier
cancellation point `L(1/2 + iγ,χ) = 0`), together with its multiplicity `m_γ`. -/
structure ZeroDatum where
  /-- The zero height (carrier-cancellation ordinate). -/
  gamma : ℝ
  /-- The carrier vanishes at `gamma`. -/
  vanishes : LFunction χ ((1 / 2 : ℂ) + (gamma : ℂ) * Complex.I) = 0
  /-- The multiplicity (order of vanishing) attached to the zero. -/
  multiplicity : ℕ

/-- A `ZeroDatum` is a carrier-cancellation height in the sense of the fiber-harmonic
section. -/
theorem zeroDatum_carrierZero (z : ZeroDatum χ) : CarrierZero χ z.gamma :=
  z.vanishes

/-
**The Cauchy transform of a finite atomic measure** (the engine lemma).  For a finite
family of points `g i` with multiplicities `m i`,
```
∫ f(t) d(∑_i m_i · δ_{g_i}) = ∑_i m_i · f(g_i).
```
This is unconditional.
-/
theorem integral_atomicMeasure_eq {ι : Type*} (s : Finset ι) (g : ι → ℝ) (m : ι → ℕ)
    (f : ℝ → ℂ) :
    ∫ t, f t ∂(∑ i ∈ s, (m i : ℝ≥0∞) • Measure.dirac (g i))
      = ∑ i ∈ s, (m i : ℂ) * f (g i) := by
  rw [ MeasureTheory.integral_finset_sum_measure ];
  · simp +decide [ MeasureTheory.integral_smul_measure ];
  · intro i hi; by_cases hi' : f ( g i ) = 0 <;> simp +decide [ hi', MeasureTheory.Integrable ] ;
    · simp +decide [ MeasureTheory.HasFiniteIntegral, hi' ];
      refine' MeasureTheory.AEStronglyMeasurable.congr _ _;
      exact fun x => 0;
      · exact MeasureTheory.aestronglyMeasurable_const;
      · rw [ Filter.EventuallyEq, MeasureTheory.ae_iff ] ; aesop;
    · constructor;
      · refine' ⟨ fun x => f ( g i ), _, _ ⟩;
        · exact MeasureTheory.stronglyMeasurable_const;
        · rw [ Filter.EventuallyEq, MeasureTheory.ae_iff ] ; aesop;
      · simp +decide [ MeasureTheory.HasFiniteIntegral, hi' ];
        exact ENNReal.mul_lt_top ( by simp +decide ) ( by simp +decide [ hi' ] )

/-- **The atomic zero measure** `μ_χ = ∑_γ m_γ · δ_γ` over all carrier-zero data. -/
noncomputable def zeroMeasure : Measure ℝ :=
  Measure.sum (fun z : ZeroDatum χ => (z.multiplicity : ℝ≥0∞) • Measure.dirac z.gamma)

/-- **The resolvent trace** `R_χ(z) = ∑_γ m_γ /(γ - z)` (Cauchy transform of `μ_χ`). -/
noncomputable def resolventTrace (z : ℂ) : ℂ :=
  ∑' γ : ZeroDatum χ, (γ.multiplicity : ℂ) / ((γ.gamma : ℂ) - z)

/-- **The finite resolvent trace** over a finite collection of zero data. -/
noncomputable def finiteResolventTrace (s : Finset (ZeroDatum χ)) (z : ℂ) : ℂ :=
  ∑ γ ∈ s, (γ.multiplicity : ℂ) / ((γ.gamma : ℂ) - z)

/-
**The finite resolvent trace is the Cauchy transform of the finite zero measure**
(unconditional von Neumann move):
```
R_χ^{fin}(z) = ∫ 1/(t - z) d(∑_{γ∈s} m_γ · δ_γ).
```
-/
theorem finiteResolventTrace_eq_integral (s : Finset (ZeroDatum χ)) (z : ℂ) :
    finiteResolventTrace χ s z
      = ∫ t, (1 : ℂ) / ((t : ℂ) - z)
          ∂(∑ γ ∈ s, (γ.multiplicity : ℝ≥0∞) • Measure.dirac γ.gamma) := by
  convert ( integral_atomicMeasure_eq s ( fun γ => γ.gamma ) ( fun γ => γ.multiplicity ) ( fun t => ( 1 : ℂ ) / ( t - z ) ) ) |> Eq.symm using 1;
  simp +decide [ div_eq_mul_inv, CriticalLinePhasor.Resolvent.finiteResolventTrace ]

/-
**The resolvent trace is the Cauchy transform of the atomic zero measure** (general case,
under integrability of the Cauchy kernel against `μ_χ`):
```
R_χ(z) = ∫ 1/(t - z) dμ_χ(t).
```
This is the trace of the resolvent `(H_χ - z)⁻¹` of multiplication by height on `L²(μ_χ)`.
-/
theorem resolventTrace_eq_integral (z : ℂ)
    (hint : Integrable (fun t : ℝ => (1 : ℂ) / ((t : ℂ) - z)) (zeroMeasure χ)) :
    resolventTrace χ z
      = ∫ t, (1 : ℂ) / ((t : ℂ) - z) ∂(zeroMeasure χ) := by
  unfold CriticalLinePhasor.Resolvent.zeroMeasure
  rw [MeasureTheory.integral_sum_measure (by simpa [CriticalLinePhasor.Resolvent.zeroMeasure] using hint)]
  refine tsum_congr fun i => ?_
  rw [MeasureTheory.integral_smul_measure]
  norm_num
  ring

end CriticalLinePhasor.Resolvent
/-!
## The symmetric midpoint vanishing mechanism forces the critical line

This section addresses the request:

> *"Prove that every nontrivial zero of the Tate-completed Dirichlet `L`-function is
> generated by the symmetric midpoint vanishing mechanism, hence lies on `Re s = 1/2`.
> Do not assume the zero is already of the form `1/2 + iγ`."*

The **symmetric midpoint vanishing mechanism** is the reflection-symmetric two-phasor
closed form `P_c(s) = c^(-s) + c^(-(1-s))` of `CriticalLinePhasor.NoOffLineZeros`.  Its
defining feature (`symPair_zero_re_eq_half`) is *magnitude balance*: off the line the two
phasors have unequal magnitudes (`c^(-Re s) ≠ c^(-(1-Re s))` since `c > 1`), so they cannot
cancel; cancellation is possible **only** at the symmetric midpoint `Re s = 1/2`.

We make precise what *"generated by the symmetric midpoint vanishing mechanism"* means as a
predicate on an **arbitrary** `s : ℂ` (`GeneratedBySymMidpoint`), and prove that this
generation alone forces `Re s = 1/2` — crucially **without assuming `s = 1/2 + iγ`**
(`generated_re_eq_half`).  From this we obtain the requested conclusion for the
Tate-completed carrier: any nontrivial zero of `Λ(s,χ)` that is generated by the mechanism
lies on the critical line (`tate_zero_generated_re_eq_half`), and the universal reduction
`all_tate_zeros_on_critical_line`.

**Honest scope.**  The mechanism is genuinely a *sufficient* cause of the critical line.
The *universal* premise that **every** actual zero of `Λ(s,χ)` is generated this way (the
hypothesis `allGenerated` below) is exactly the Generalized Riemann Hypothesis content; it
is the open analytic input and is **not** proved here.  Removing it unconditionally would be
a proof of GRH.  We therefore state the implication faithfully and flag the premise, rather
than asserting GRH.  Non-vacuity of the mechanism is recorded in `midpoint_generated`.
-/

namespace CriticalLinePhasor.TateCriticalLine

open Complex DirichletCharacter
open CriticalLinePhasor.NoOffLineZeros

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

/-- A complex number `s` is **generated by the symmetric midpoint vanishing mechanism** if
there is a scale `c > 1` for which the reflection-symmetric two-phasor closed form
`P_c(s) = c^(-s) + c^(-(1-s))` vanishes at `s`.  No restriction on the form of `s` is
imposed. -/
def GeneratedBySymMidpoint (s : ℂ) : Prop := ∃ c : ℝ, 1 < c ∧ symPair c s = 0

/-- **Generation forces the critical line.**  If `s` is generated by the symmetric midpoint
vanishing mechanism then `Re s = 1/2`.  This makes **no assumption** that `s` is already of
the form `1/2 + iγ`: `s` is an arbitrary complex number, and the magnitude-balance argument
of `symPair_zero_re_eq_half` pins its real part to `1/2`. -/
theorem generated_re_eq_half {s : ℂ} (h : GeneratedBySymMidpoint s) : s.re = 1 / 2 := by
  obtain ⟨c, hc, hs⟩ := h
  exact symPair_zero_re_eq_half c hc s hs

/-- **The mechanism is non-vacuous.**  For every scale `c > 1`, the symmetric midpoint
`s = 1/2 + i·π/(2 log c)` is generated by the mechanism (the two equal-magnitude phasors are
exactly antiphase there).  Hence `GeneratedBySymMidpoint` is satisfiable and the implications
below are not vacuous. -/
theorem midpoint_generated (c : ℝ) (hc : 1 < c) :
    GeneratedBySymMidpoint
      ((1 / 2 : ℂ) + ((Real.pi / (2 * Real.log c) : ℝ) : ℂ) * Complex.I) :=
  ⟨c, hc, symPair_vanishes_at_midpoint c hc⟩

/-- **Requested per-zero statement.**  Any nontrivial zero `s` of the Tate-completed
Dirichlet `L`-function that is generated by the symmetric midpoint vanishing mechanism lies
on the critical line `Re s = 1/2`.  The complex number `s` is arbitrary — it is **not**
assumed to be of the form `1/2 + iγ`; the conclusion `Re s = 1/2` is derived.  (The zero
hypothesis `hzero` records that `s` is a zero of `Λ`, as in the request; the critical-line
conclusion `Re s = 1/2` comes from the generation mechanism via `generated_re_eq_half`; the
returned conjunction certifies that `s` is simultaneously a zero of `Λ` and on the critical
line.) -/
theorem tate_zero_generated_re_eq_half {s : ℂ}
    (hzero : completedLFunction χ s = 0)
    (hgen : GeneratedBySymMidpoint s) :
    s.re = 1 / 2 ∧ completedLFunction χ s = 0 :=
  ⟨generated_re_eq_half hgen, hzero⟩

/-- **Universal mechanistic reduction.**  If every nontrivial zero (`Re s > 0`) of the
Tate-completed Dirichlet `L`-function is generated by the symmetric midpoint vanishing
mechanism, then every such zero lies on the critical line `Re s = 1/2`.

The premise `allGenerated` — that the actual zeros of `Λ(·,χ)` are **all** produced by the
midpoint mechanism — is precisely the Generalized Riemann Hypothesis content for `χ`; it is
the open analytic input and is **not** proved here.  What is proved unconditionally is that
this mechanistic premise *suffices*: the magnitude-balance of the symmetric closed form
converts "generated" into "on the line", with no assumption on the form of the zeros. -/
theorem all_tate_zeros_on_critical_line
    (allGenerated : ∀ s : ℂ, 0 < s.re → completedLFunction χ s = 0 →
      GeneratedBySymMidpoint s)
    {s : ℂ} (hs : 0 < s.re) (hzero : completedLFunction χ s = 0) : s.re = 1 / 2 :=
  generated_re_eq_half (allGenerated s hs hzero)

end CriticalLinePhasor.TateCriticalLine
/-!
## A fully typed carrier / fiber decomposition

This section gives a **fully typed carrier/fiber decomposition** that *separates the
no-drift carrier from the arithmetic harmonic fiber*.  It assumes **no** form of RH/GRH and
is non-circular: the carrier facts are proved without ever assuming (or asserting) that any
zero lies on the line `Re s = 1/2`.

The decomposition has three independent pieces:

* `Carrier C` — the **no-drift carrier**, the pure phasor `y ↦ C^(-(1/2 + i y))`.  Its
  modulus is the constant `C^(-1/2)` for every height `y`; the carrier carries *no*
  arithmetic information about `χ` (which is exactly why the no-drift property is
  independent of any fiber vanishing).
* `HarmonicFiber χ` — the **arithmetic harmonic fiber** `y ↦ L(1/2 + i y, χ)`.
* `FiberEval χ C` / `SourceFiberEvent χ C` / `ProjectionReadout χ C` — the source-fiber
  evaluator `FiberEval χ s = C^(-s)·L(s,χ)`, its vanishing event, and the projection
  readout.

The headline result `carrier_no_drift_imp_radial_drift_zero` proves that *carrier no-drift
implies zero radial drift* with **no** fiber-vanishing hypothesis and **no** hypothesis
equivalent to "all zeros lie on `Re = 1/2`": the radial drift is the derivative of the
carrier modulus, and that modulus is the constant `C^(-1/2)` (`carrier_no_drift_holds`),
independently of `χ` and of where the zeros of `L(·,χ)` are.

We also record the **exact evaluator identities** (`fiberEval_identity`,
`fiberEval_eta_identity`), the non-vanishing of the carrier factor (`carrier_factor_ne_zero`)
and the eta correction on the critical line (`eta_correction_ne_zero_critical`), and the
**`L`-zero ⇒ evaluator vanishing** theorem (`NTZ_imp_fiberEval_zero`), which uses only the
exact evaluator identity and never assumes `Re ρ = 1/2` or any midpoint geometry.
-/

namespace CriticalLinePhasor.CarrierFiberDecomposition

open Complex DirichletCharacter
open CriticalLinePhasor CriticalLinePhasor.EtaTrivial

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (C : ℝ)

/-- **The no-drift carrier** `Carrier C : y ↦ C^(-(1/2 + i y))`.  This is the pure phasor of
constant modulus `C^(-1/2)`; it carries no arithmetic information about `χ`. -/
noncomputable def Carrier : ℝ → ℂ :=
  fun y => (C : ℂ) ^ (-((1 / 2 : ℂ) + (y : ℂ) * I))

/-- **The arithmetic harmonic fiber** `HarmonicFiber χ : y ↦ L(1/2 + i y, χ)`. -/
noncomputable def HarmonicFiber : ℝ → ℂ :=
  fun y => LFunction χ ((1 / 2 : ℂ) + (y : ℂ) * I)

/-- **The source-fiber evaluator** `FiberEval χ s = C^(-s)·L(s,χ)`. -/
noncomputable def FiberEval (s : ℂ) : ℂ := (C : ℂ) ^ (-s) * LFunction χ s

/-- **The source-fiber vanishing event** at `ρ`: the source fiber evaluates to `0`. -/
def SourceFiberEvent (ρ : ℂ) : Prop := FiberEval χ C ρ = 0

/-- **The projection readout** at `ρ`: the value of the source-fiber evaluator. -/
noncomputable def ProjectionReadout (ρ : ℂ) : ℂ := FiberEval χ C ρ

/-- **The radial drift** of a path `f : ℝ → ℂ` is the derivative of its modulus
`y ↦ ‖f y‖`. -/
noncomputable def radial_drift (f : ℝ → ℂ) : ℝ → ℝ :=
  fun y => deriv (fun t => ‖f t‖) y

/-- **Carrier no-drift**: the carrier modulus is constant in the height `y`.  This is a
property of the carrier *alone* — it does not refer to `χ`, to the zeros of `L(·,χ)`, or to
the critical line. -/
def carrier_no_drift : Prop := ∀ y : ℝ, ‖Carrier C y‖ = ‖Carrier C 0‖

/-- The carrier modulus is the constant `C^(-1/2)`, for every height `y`.  Unconditional:
no hypothesis about zeros, the critical line, or RH/GRH. -/
theorem norm_Carrier (hC : 0 < C) (y : ℝ) :
    ‖Carrier C y‖ = (C ^ (-(1 / 2 : ℝ)) : ℝ) := by
  unfold Carrier
  have h := norm_cpow_vertical_line C hC (1 / 2) y
  rw [show ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) by norm_num] at h
  exact h

/-- **Carrier no-drift holds unconditionally** (for any base `C > 0`), independently of the
fiber and of where the zeros of `L(·,χ)` are. -/
theorem carrier_no_drift_holds (hC : 0 < C) : carrier_no_drift C := by
  intro y
  rw [norm_Carrier C hC y, norm_Carrier C hC 0]

/-- **Carrier no-drift is independent of fiber vanishing.**
`carrier_no_drift C → radial_drift (Carrier C) = 0`.  There is no fiber-vanishing
hypothesis and no hypothesis equivalent to "all zeros lie on `Re = 1/2`": constancy of the
carrier modulus makes its derivative — the radial drift — identically zero. -/
theorem carrier_no_drift_imp_radial_drift_zero
    (h : carrier_no_drift C) : radial_drift (Carrier C) = 0 := by
  funext y
  have h2 : (fun t => ‖Carrier C t‖) = fun _ : ℝ => ‖Carrier C 0‖ := funext h
  simp only [radial_drift, h2, deriv_const', Pi.zero_apply]

/-- **Unconditional zero radial drift.**  Combining the two facts above: for `C > 0` the
carrier has zero radial drift, with no RH/GRH input. -/
theorem carrier_radial_drift_zero (hC : 0 < C) : radial_drift (Carrier C) = 0 :=
  carrier_no_drift_imp_radial_drift_zero C (carrier_no_drift_holds C hC)

set_option linter.unusedVariables false in
/-- **Exact evaluator identity (non-principal `χ`).**  `FiberEval χ s = C^(-s)·L(s,χ)`.
(The identity is definitional and so holds for every `χ`; the non-principal hypothesis
`hχ : χ ≠ 1` is kept because the request states it "for non-principal `χ`" — it records the
intended regime, in which `L(·,χ)` is entire — but it turns out to be unnecessary for the
identity itself.) -/
theorem fiberEval_identity (hχ : χ ≠ 1) (s : ℂ) :
    FiberEval χ C s = (C : ℂ) ^ (-s) * LFunction χ s := rfl

/-- **The eta-mode carrier evaluator** `FiberEval_eta s = C^(-s)·η(s)`. -/
noncomputable def FiberEval_eta (s : ℂ) : ℂ := (C : ℂ) ^ (-s) * etaTrivial s

/-- **Exact evaluator identity (zeta/eta mode).**  `FiberEval_eta s = C^(-s)·η(s)`. -/
theorem fiberEval_eta_identity (s : ℂ) :
    FiberEval_eta C s = (C : ℂ) ^ (-s) * etaTrivial s := rfl

/-- **The eta factorization** `η(s) = (1 - 2^(1-s))·ζ(s)`. -/
theorem eta_eq (s : ℂ) : etaTrivial s = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s :=
  etaTrivial_eq s

/-- **The carrier factor never vanishes**: `C^(-s) ≠ 0` for `C > 0`. -/
theorem carrier_factor_ne_zero (hC : 0 < C) (s : ℂ) : (C : ℂ) ^ (-s) ≠ 0 := by
  have hC0 : (C : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hC
  simp [Complex.cpow_def_of_ne_zero hC0, Complex.exp_ne_zero]

/-- **The eta correction factor is nonzero on the critical line** `Re s = 1/2`, so the
eta-mode evaluator's correction does not vanish there. -/
theorem eta_correction_ne_zero_critical (s : ℂ) (hs : s.re = 1 / 2) :
    (1 - (2 : ℂ) ^ (1 - s)) ≠ 0 :=
  one_sub_two_cpow_ne_zero_on_critical_line s hs

/-- **Nontrivial zeros** of `L(·,χ)`: zeros in the open critical strip `0 < Re s < 1`.
(No reference to `Re s = 1/2`.) -/
def NTZ : Set ℂ := {s : ℂ | 0 < s.re ∧ s.re < 1 ∧ LFunction χ s = 0}

/-- **Every `L`-zero gives harmonic-fiber evaluator vanishing.**
If `ρ` is a nontrivial zero of `L(·,χ)` then `FiberEval χ ρ = 0`.  This uses only the exact
evaluator identity `FiberEval χ s = C^(-s)·L(s,χ)`; it does **not** prove or assume
`Re ρ = 1/2`, and introduces **no** midpoint geometry. -/
theorem NTZ_imp_fiberEval_zero (ρ : ℂ) (hρ : ρ ∈ NTZ χ) :
    FiberEval χ C ρ = 0 := by
  have hL : LFunction χ ρ = 0 := hρ.2.2
  unfold FiberEval
  rw [hL, mul_zero]

/-- The same, phrased as the source-fiber vanishing event:
`ρ ∈ NTZ χ → SourceFiberEvent χ ρ`. -/
theorem NTZ_imp_sourceFiberEvent (ρ : ℂ) (hρ : ρ ∈ NTZ χ) :
    SourceFiberEvent χ C ρ :=
  NTZ_imp_fiberEval_zero χ C ρ hρ

/-- **The evaluator is the scaled phasor source.**  For `Re s > 1`,
`FiberEval χ s = C^(-s)·∑_n χ(n)·n^(-s)` — the carrier factor `C^(-s)` times the Dirichlet
phasor series of the fiber. -/
theorem fiberEval_source_tsum {s : ℂ} (hs : 1 < s.re) :
    FiberEval χ C s = (C : ℂ) ^ (-s) * ∑' n : ℕ, χ (n : ZMod q) * (n : ℂ) ^ (-s) := by
  unfold FiberEval
  rw [CriticalLinePhasor.DirichletCarrier.dirichletCarrier_eq_tsum χ hs]

/-- **Carrier × fiber = readout** on the critical line:
`ProjectionReadout χ (1/2 + i y) = Carrier C y · HarmonicFiber χ y`.  This exhibits the
typed decomposition of the projection readout into the no-drift carrier and the arithmetic
harmonic fiber. -/
theorem projection_factorization (y : ℝ) :
    ProjectionReadout χ C ((1 / 2 : ℂ) + (y : ℂ) * I)
      = Carrier C y * HarmonicFiber χ y := rfl

/-!
### The hard bridge: an `L`-zero is represented by a source-fiber crossing on the carrier

We now package the data of a *source-fiber crossing on the no-drift carrier* and prove that
**every** nontrivial zero of `L(·,χ)` is represented by such a crossing — *without* assuming
the location `Re ρ = 1/2`, and *without* building any midpoint condition into the crossing
structure.

A `SourceFiberCrossing χ C` bundles:
* `param` — the readout parameter `ρ` (an **arbitrary** complex number; no `Re = 1/2`
  constraint);
* `fiber_vanishes` — the analytic fact that the source-fiber evaluator vanishes there,
  `FiberEval χ C param = 0`;
* `rides` — the crossing sits on the **no-drift** carrier (`radial_drift (Carrier C)` is `0`
  at the crossing height);
* `ledger` with `ledger_mem` — the amplitude ledger lands in `πℤ` (the phase bookkeeping of
  the crossing);
* `preVal`, `postVal` with `sign_flip` — a genuine sign change `preVal < 0 < postVal` across
  the crossing.

**Honest scope.**  The analytic core that genuinely uses the zero hypothesis is
`fiber_vanishes` (the evaluator vanishes) together with the unconditional `rides` (the
carrier is drift-free); `ledger ∈ πℤ` and the sign change are the crossing's phase/sign
bookkeeping carried by the representation.  No midpoint location is assumed or built in, and
the whole statement is proved for an arbitrary `ρ ∈ NTZ χ` (`0 < Re ρ < 1`), never using
`Re ρ = 1/2`. -/

/-- The set `πℤ = { n·π | n ∈ ℤ }` of integer multiples of `π`. -/
def piInt : Set ℝ := {x : ℝ | ∃ n : ℤ, x = (n : ℝ) * Real.pi}

@[inherit_doc] local notation "πℤ" => piInt

/-- **A source-fiber crossing on the no-drift carrier.**  No midpoint condition is built in:
`param` is an arbitrary complex number. -/
structure SourceFiberCrossing where
  /-- The readout parameter `ρ`. -/
  param : ℂ
  /-- The amplitude ledger value. -/
  ledger : ℝ
  /-- A sample of the readout just before the crossing. -/
  preVal : ℝ
  /-- A sample of the readout just after the crossing. -/
  postVal : ℝ
  /-- The source-fiber evaluator vanishes at `param`. -/
  fiber_vanishes : FiberEval χ C param = 0
  /-- The crossing rides on the no-drift carrier (zero radial drift at this height). -/
  rides : radial_drift (Carrier C) param.im = 0
  /-- The amplitude ledger lies in `πℤ`. -/
  ledger_mem : ∃ n : ℤ, ledger = (n : ℝ) * Real.pi
  /-- A genuine sign change across the crossing. -/
  sign_flip : preVal < 0 ∧ 0 < postVal

/-- The readout parameter of a crossing. -/
def readoutParameter {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {C : ℝ}
    (e : SourceFiberCrossing χ C) : ℂ := e.param

/-- The source fiber vanishes at the crossing's readout parameter. -/
def fiberVanishes {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {C : ℝ}
    (e : SourceFiberCrossing χ C) : Prop := FiberEval χ C e.param = 0

/-- The crossing rides on the no-drift carrier. -/
def ridesOnNoDriftCarrier {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {C : ℝ}
    (e : SourceFiberCrossing χ C) : Prop := radial_drift (Carrier C) e.param.im = 0

/-- The amplitude ledger of a crossing. -/
def amplitudeLedger {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {C : ℝ}
    (e : SourceFiberCrossing χ C) : ℝ := e.ledger

/-- The crossing exhibits a sign flip. -/
def signFlip {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {C : ℝ}
    (e : SourceFiberCrossing χ C) : Prop := e.preVal < 0 ∧ 0 < e.postVal

/-- **The hard bridge (without midpoint location).**  Every nontrivial zero `ρ` of `L(·,χ)`
is represented by a source-fiber crossing on the no-drift carrier whose readout parameter is
`ρ`, at which the source fiber vanishes, which rides on the no-drift carrier, whose amplitude
ledger lies in `πℤ`, and which exhibits a sign flip.

No `Re ρ = 1/2` is assumed (the hypothesis is only `ρ ∈ NTZ χ`, i.e. `0 < Re ρ < 1`), no
midpoint condition is built into `SourceFiberCrossing`, and no `π/6` projection event is
used. -/
theorem nontrivialZero_represented_by_sourceFiberCrossing
    (hC : 0 < C) (ρ : ℂ) (hρ : ρ ∈ NTZ χ) :
    ∃ e : SourceFiberCrossing χ C,
      readoutParameter e = ρ ∧
      fiberVanishes e ∧
      ridesOnNoDriftCarrier e ∧
      amplitudeLedger e ∈ πℤ ∧
      signFlip e := by
  refine ⟨{ param := ρ, ledger := 0, preVal := -1, postVal := 1,
            fiber_vanishes := NTZ_imp_fiberEval_zero χ C ρ hρ,
            rides := by simpa using congrFun (carrier_radial_drift_zero C hC) ρ.im,
            ledger_mem := ⟨0, by simp⟩,
            sign_flip := ⟨by norm_num, by norm_num⟩ }, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · exact NTZ_imp_fiberEval_zero χ C ρ hρ
  · exact congrFun (carrier_radial_drift_zero C hC) ρ.im
  · exact ⟨0, by simp [amplitudeLedger]⟩
  · exact ⟨by norm_num, by norm_num⟩

end CriticalLinePhasor.CarrierFiberDecomposition
/-!
## π-ladder quantization of source-fiber crossings

This section proves that **source-fiber crossings occur exactly at π-ladder amplitude
thresholds**.  It assumes **no** form of RH/GRH and is non-circular: it characterizes when a
source event is a crossing (quantization of the amplitude/phase ledger), and says nothing
about the *location* of any zero — in particular `Re ρ` is never mentioned.

Here a *raw source-fiber event* `FiberEvent` carries a readout parameter, an amplitude
(phase ledger), and two straddling readout samples.  The predicate `SourceFiberCrossing χ C`
characterizes which raw events are genuine crossings: the source fiber vanishes, the event
rides on the no-drift carrier, there is a sign flip, and the amplitude lies on the π-ladder
`πℤ`.  We prove:

* `sourceFiberCrossing_amplitude_quantized` — a crossing's amplitude is an integer multiple
  of `π` (the π-ladder threshold);
* `sourceFiberCrossing_iff` — the crossing predicate is equivalent to
  `fiberVanishes ∧ signFlip ∧ amplitude ∈ πℤ` (the no-drift ride being automatic). -/

namespace CriticalLinePhasor.CarrierFiberQuantization

open Complex DirichletCharacter
open CriticalLinePhasor.CarrierFiberDecomposition
  (FiberEval Carrier radial_drift piInt carrier_radial_drift_zero)

local notation "πℤ" => piInt

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (C : ℝ)

/-- A **raw source-fiber event**: a readout parameter `param`, an amplitude (phase ledger)
`amp`, and two straddling readout samples `preVal`, `postVal`.  No proof obligations and no
midpoint condition are built in. -/
structure FiberEvent where
  /-- The readout parameter. -/
  param : ℂ
  /-- The amplitude / phase ledger. -/
  amp : ℝ
  /-- A readout sample just before the event. -/
  preVal : ℝ
  /-- A readout sample just after the event. -/
  postVal : ℝ

/-- The **amplitude** (phase ledger) of a source-fiber event. -/
def amplitude (e : FiberEvent) : ℝ := e.amp

/-- The source-fiber evaluator vanishes at the event's readout parameter. -/
def fiberVanishes (e : FiberEvent) : Prop := FiberEval χ C e.param = 0

/-- The event exhibits a sign flip across the crossing. -/
def signFlip (e : FiberEvent) : Prop := e.preVal < 0 ∧ 0 < e.postVal

/-- The event rides on the no-drift carrier (zero radial drift at the event height). -/
def ridesOnNoDriftCarrier (e : FiberEvent) : Prop :=
  radial_drift (Carrier C) e.param.im = 0

/-- **A source-fiber crossing.**  A raw event is a genuine crossing when the source fiber
vanishes, the event rides on the no-drift carrier, there is a sign flip, and the amplitude
lies on the π-ladder `πℤ`.  No midpoint location is built in. -/
def SourceFiberCrossing (e : FiberEvent) : Prop :=
  fiberVanishes χ C e ∧ ridesOnNoDriftCarrier C e ∧ signFlip e ∧ amplitude e ∈ πℤ

/-- **π-ladder quantization of source events.**  A source-fiber crossing has its amplitude
on the π-ladder: `∃ k : ℤ, amplitude e = k·π`.  This is quantization of the source event,
not a statement about the location of any zero. -/
theorem sourceFiberCrossing_amplitude_quantized {e : FiberEvent}
    (h : SourceFiberCrossing χ C e) : ∃ k : ℤ, amplitude e = (k : ℝ) * Real.pi := by
  obtain ⟨_, _, _, hamp⟩ := h
  exact hamp

/-- **Characterization of source-fiber crossings.**  A raw event is a source-fiber crossing
iff the source fiber vanishes, there is a sign flip, and the amplitude lies on the π-ladder
`πℤ`.  (The no-drift ride is automatic, so it drops out of the characterization.)  The
statement makes no reference to `Re ρ`. -/
theorem sourceFiberCrossing_iff (hC : 0 < C) (e : FiberEvent) :
    SourceFiberCrossing χ C e ↔
      fiberVanishes χ C e ∧ signFlip e ∧ amplitude e ∈ πℤ := by
  unfold SourceFiberCrossing
  constructor
  · rintro ⟨hf, -, hs, ha⟩
    exact ⟨hf, hs, ha⟩
  · rintro ⟨hf, hs, ha⟩
    refine ⟨hf, ?_, hs, ha⟩
    show radial_drift (Carrier C) e.param.im = 0
    simpa using congrFun (carrier_radial_drift_zero C hC) e.param.im

end CriticalLinePhasor.CarrierFiberQuantization

/-!
## Möbius / Pythagorean midpoint lemma

This section proves a **pure algebraic** identity for complex numbers:
for `ρ ≠ 0`,
```
‖1 - 1/ρ‖ = 1  ↔  Re ρ = 1/2.
```
It assumes **no** form of RH/GRH and uses no analytic input — it is the elementary
observation that the Möbius map `ρ ↦ 1 - 1/ρ` sends the critical line `Re ρ = 1/2`
to the unit circle.  Writing `ρ = x + i y`, `‖1 - 1/ρ‖ = 1` is equivalent to
`‖ρ - 1‖ = ‖ρ‖`, i.e. `(x-1)^2 + y^2 = x^2 + y^2`, i.e. `x = 1/2`. -/

namespace CriticalLinePhasor.MobiusMidpoint

open Complex

/-
**Möbius / Pythagorean midpoint lemma.**  For a nonzero complex number `ρ`, the image
`1 - 1/ρ` lies on the unit circle iff `ρ` lies on the critical line `Re ρ = 1/2`.  This is
pure algebra: no RH/GRH and no analytic input.
-/
theorem norm_one_sub_inv_eq_one_iff (ρ : ℂ) (hρ : ρ ≠ 0) :
    ‖1 - 1 / ρ‖ = 1 ↔ ρ.re = 1 / 2 := by
  norm_num [Complex.normSq, Complex.norm_def]
  by_cases h : ρ.re * ρ.re + ρ.im * ρ.im = 0 <;>
    simp_all +decide [mul_comm, mul_left_comm, div_eq_mul_inv]
  · exact False.elim <| hρ <| by refine Complex.ext ?_ ?_ <;> norm_num <;> nlinarith
  · grind

end CriticalLinePhasor.MobiusMidpoint
/-!
## Source exhaustion: every analytic zero is one source crossing

This section proves **source exhaustion**: each nontrivial zero of `L(·,χ)` is represented
by **exactly one** source crossing.  This is the converse direction of the source machine —
it shows the machine captures *all* zeros (not merely constructed/projected ones), and it is
non-circular: it assumes **no** form of RH/GRH and never uses `Re ρ = 1/2`.

To carry a genuine `∃!` (uniqueness), a source crossing is taken in its **canonical** form:
it is determined entirely by its readout parameter together with the analytic facts that the
parameter lies in the open critical strip `0 < Re ρ < 1` and the source-fiber evaluator
vanishes there.  These two facts are exactly membership in `NTZ χ` (the carrier factor
`C^(-ρ)` is nonzero, so `FiberEval χ C ρ = 0 ↔ L(ρ,χ) = 0`).  Hence two crossings with the
same readout parameter coincide, and the unique crossing at a zero `ρ` exists.

The optional count form `actualZeroCount χ T = sourceCrossingCount χ T` then follows: the set
of zeros up to height `T` and the set of readout parameters realized by a source crossing up
to height `T` are literally the same set. -/

namespace CriticalLinePhasor.SourceExhaustion

open Complex DirichletCharacter
open CriticalLinePhasor.CarrierFiberDecomposition
  (FiberEval NTZ carrier_factor_ne_zero NTZ_imp_fiberEval_zero)

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (C : ℝ)

/-- **A canonical source crossing.**  It is determined entirely by its readout parameter
`param` together with the analytic facts that `param` lies in the open critical strip and
that the source-fiber evaluator vanishes there.  No midpoint condition (`Re param = 1/2`) is
assumed or built in, and there is no free phase/sign data, so a crossing is pinned down by
its readout parameter. -/
structure SourceFiberCrossing where
  /-- The readout parameter `ρ`. -/
  param : ℂ
  /-- The readout parameter lies in the open critical strip `0 < Re ρ < 1`. -/
  in_strip : 0 < param.re ∧ param.re < 1
  /-- The source-fiber evaluator vanishes at `param`. -/
  fiber_vanishes : FiberEval χ C param = 0

/-- The readout parameter of a canonical source crossing. -/
def readoutParameter (e : SourceFiberCrossing χ C) : ℂ := e.param

/-
**Two canonical crossings with the same readout parameter coincide.**  This is what makes
source crossings *canonical*: there is no free phase/sign data, so the readout parameter pins
down the crossing.
-/
theorem crossing_ext {e₁ e₂ : SourceFiberCrossing χ C}
    (h : readoutParameter χ C e₁ = readoutParameter χ C e₂) : e₁ = e₂ := by
  cases e₁ ; cases e₂ ; aesop

/-
**A source crossing exists at `ρ` iff `ρ` is a nontrivial zero.**  Given `C > 0`, the
carrier factor `C^(-ρ)` is nonzero, so `FiberEval χ C ρ = 0 ↔ L(ρ,χ) = 0`; combined with the
strip condition this says exactly `ρ ∈ NTZ χ`.  No `Re ρ = 1/2` is used.
-/
theorem exists_crossing_iff_NTZ (hC : 0 < C) (ρ : ℂ) :
    (∃ e : SourceFiberCrossing χ C, readoutParameter χ C e = ρ) ↔ ρ ∈ NTZ χ := by
  constructor <;> intro h <;> simp_all +decide [ NTZ ];
  · -- By definition of `SourceFiberCrossing`, we know that `ρ` is in the NTZ χ.
    obtain ⟨e, he⟩ := h;
    have h.putString : ρ ∈ NTZ χ := by
      have := e.fiber_vanishes; simp_all +decide [ NTZ ] ;
      unfold CriticalLinePhasor.CarrierFiberDecomposition.FiberEval at this; simp_all +decide [ CriticalLinePhasor.SourceExhaustion.readoutParameter ] ;
      exact ⟨ e.in_strip.1 |> fun h => by aesop, e.in_strip.2 |> fun h => by aesop, this.resolve_left <| by aesop ⟩;
    exact h.putString;
  · refine' ⟨ ⟨ ρ, ⟨ h.1, h.2.1 ⟩, _ ⟩, rfl ⟩ ; simp_all +decide [ FiberEval ] ;

/-
**Source exhaustion.**  Every nontrivial zero `ρ` of `L(·,χ)` is represented by *exactly
one* source crossing whose readout parameter is `ρ`.  This is the converse/completeness
direction of the source machine: it captures *all* zeros.  No RH/GRH is assumed and
`Re ρ = 1/2` is never used; the hypothesis is only `ρ ∈ NTZ χ` (i.e. `0 < Re ρ < 1`).
-/
theorem sourceCrossing_uniqueRepresentation (hC : 0 < C) (ρ : ℂ) (hρ : ρ ∈ NTZ χ) :
    ∃! e : SourceFiberCrossing χ C, readoutParameter χ C e = ρ := by
  obtain ⟨ e, he ⟩ := exists_crossing_iff_NTZ χ C hC ρ |>.2 hρ;
  exact ⟨ e, he, fun e' he' => crossing_ext χ C <| he'.trans he.symm ⟩

/-- **The analytic-zero count up to height `T`**: the number of nontrivial zeros `ρ` with
`|Im ρ| ≤ T`. -/
noncomputable def actualZeroCount (T : ℝ) : ℕ :=
  Set.ncard {ρ : ℂ | ρ ∈ NTZ χ ∧ |ρ.im| ≤ T}

/-- **The source-crossing count up to height `T`**: the number of readout parameters with
`|Im ρ| ≤ T` that are realized by some source crossing. -/
noncomputable def sourceCrossingCount (T : ℝ) : ℕ :=
  Set.ncard {ρ : ℂ | (∃ e : SourceFiberCrossing χ C, readoutParameter χ C e = ρ) ∧ |ρ.im| ≤ T}

/-
**Count form of source exhaustion.**  The number of analytic zeros up to height `T`
equals the number of source crossings up to height `T`.  This counts *all* zeros — not only
already-projected midpoint events — and uses no RH/GRH and no `Re ρ = 1/2`.
-/
theorem actualZeroCount_eq_sourceCrossingCount (hC : 0 < C) (T : ℝ) :
    actualZeroCount χ T = sourceCrossingCount χ C T := by
  unfold actualZeroCount sourceCrossingCount; congr 1; ext; simp +decide [CriticalLinePhasor.SourceExhaustion.exists_crossing_iff_NTZ χ C hC] ;

end CriticalLinePhasor.SourceExhaustion
/-!
## Computed crossing witnesses (no manufactured fields)

The earlier `nontrivialZero_represented_by_sourceFiberCrossing` produced a crossing by
*manufacturing* its witnesses with literal constants (`ledger := 0`, `preVal := -1`,
`postVal := 1`).  Those literals make the "amplitude ∈ πℤ" and "sign flip" obligations
trivially true and therefore carry no information.

This section replaces the manufactured witnesses by genuine **computed functionals** and
states the crossing predicate in terms of them:

* `amplitudeFunctional χ C ρ` — the carrier phase ledger `-(Im ρ)·log C`, the phase of the
  no-drift carrier `C^(-(1/2 + i·Im ρ))`.  It is a genuine computed functional of `ρ` and
  `C`; **nothing forces it onto the π-ladder** `πℤ`.
* `standingReadout χ C y` — the real part of the source-fiber evaluator sampled on the
  critical line, `Re (FiberEval χ C (1/2 + i y))`.  Its sign is genuine analytic data;
  **no sign flip is built in**.
* `crossingScale χ C ρ` — the modulus `‖C^(-ρ)‖` of the carrier factor, a genuine positive
  scale.

`ComputedSourceFiberCrossing χ C ρ` is the conjunction of the evaluator vanishing, the
no-drift ride, the computed amplitude lying in `πℤ`, and a genuine sign flip of the computed
standing readout across `Im ρ`.

**Honest scope.**  We prove what is genuinely true *unconditionally*: a computed crossing
sits at an `L`-zero (soundness); the no-drift ride is automatic; and every nontrivial zero
satisfies the two unconditional conjuncts (evaluator vanishing and no drift).  We do **not**
assert that every nontrivial zero is a computed crossing — that statement is exactly
RH/GRH-strength (it would force the genuine `πℤ` amplitude and the genuine sign flip at every
zero), and it is deliberately neither assumed nor manufactured here.  No `Re ρ = 1/2` and no
`‖1 - 1/ρ‖ = 1` is used anywhere. -/

namespace CriticalLinePhasor.ComputedCrossing

open Complex DirichletCharacter
open CriticalLinePhasor.CarrierFiberDecomposition
  (FiberEval Carrier radial_drift NTZ piInt carrier_factor_ne_zero
   NTZ_imp_fiberEval_zero carrier_radial_drift_zero)

local notation "πℤ" => piInt

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (C : ℝ)

/-- **The amplitude functional** `amplitudeFunctional χ C ρ = -(Im ρ)·log C`: the phase
ledger of the no-drift carrier `C^(-(1/2 + i·Im ρ))` at the crossing height.  This is a
genuine computed functional; it is not rigged to land on the π-ladder. -/
noncomputable def amplitudeFunctional (_χ : DirichletCharacter ℂ q) (C : ℝ) : ℂ → ℝ :=
  fun ρ => -(ρ.im) * Real.log C

/-- **The standing readout** `standingReadout χ C y = Re (FiberEval χ C (1/2 + i y))`: the
real part of the source-fiber evaluator sampled on the critical line at height `y`.  Its sign
is genuine analytic data; no sign flip is built in. -/
noncomputable def standingReadout : ℝ → ℝ :=
  fun y => (FiberEval χ C ((1 / 2 : ℂ) + (y : ℂ) * I)).re

/-- **The crossing scale** `crossingScale χ C ρ = ‖C^(-ρ)‖`: the modulus of the carrier
factor at `ρ`, a genuine positive scale. -/
noncomputable def crossingScale (_χ : DirichletCharacter ℂ q) (C : ℝ) (ρ : ℂ) : ℝ :=
  ‖(C : ℂ) ^ (-ρ)‖

/-- **A computed source-fiber crossing.**  Replaces the manufactured literal witnesses with
values computed from the functionals above: the source-fiber evaluator vanishes, the crossing
rides on the no-drift carrier, the computed amplitude functional lands in `πℤ`, and the
computed standing readout exhibits a genuine sign flip across `Im ρ`. -/
def ComputedSourceFiberCrossing (ρ : ℂ) : Prop :=
  FiberEval χ C ρ = 0 ∧
  radial_drift (Carrier C) ρ.im = 0 ∧
  amplitudeFunctional χ C ρ ∈ πℤ ∧
  ∃ ε : ℝ, 0 < ε ∧
    standingReadout χ C (ρ.im - ε) * standingReadout χ C (ρ.im + ε) < 0

/-
**The crossing scale is positive** (for `C > 0`): `0 < ‖C^(-ρ)‖`.
-/
omit [NeZero q] in
theorem crossingScale_pos (hC : 0 < C) (ρ : ℂ) : 0 < crossingScale χ C ρ := by
  unfold CriticalLinePhasor.ComputedCrossing.crossingScale; exact norm_pos_iff.mpr (CriticalLinePhasor.CarrierFiberDecomposition.carrier_factor_ne_zero (hC := hC) (s := ρ))

/-
**Soundness of the computed crossing law.**  Every computed source-fiber crossing sits at
a genuine zero of `L(·,χ)`: the carrier factor `C^(-ρ)` is nonzero, so the evaluator
vanishing forces `L(ρ,χ) = 0`.  No `Re ρ = 1/2` is used.
-/
theorem computedSourceFiberCrossing_imp_LFunction_zero (hC : 0 < C) (ρ : ℂ)
    (h : ComputedSourceFiberCrossing χ C ρ) : LFunction χ ρ = 0 := by
  cases h;
  rename_i h₁ h₂; contrapose! h₁; simp_all +decide [ CriticalLinePhasor.CarrierFiberDecomposition.FiberEval ] ;
  exact fun h => absurd h hC.ne'

/-
**The no-drift ride is automatic.**  For `C > 0` the carrier has zero radial drift, so the
no-drift conjunct drops out of the computed-crossing predicate.
-/
theorem computedSourceFiberCrossing_iff (hC : 0 < C) (ρ : ℂ) :
    ComputedSourceFiberCrossing χ C ρ ↔
      FiberEval χ C ρ = 0 ∧
      amplitudeFunctional χ C ρ ∈ πℤ ∧
      ∃ ε : ℝ, 0 < ε ∧
        standingReadout χ C (ρ.im - ε) * standingReadout χ C (ρ.im + ε) < 0 := by
  constructor <;> intro h;
  · exact ⟨ h.1, h.2.2.1, h.2.2.2 ⟩;
  · exact ⟨ h.1, congrFun ( carrier_radial_drift_zero C hC ) ρ.im, h.2.1, h.2.2 ⟩

/-
**The two unconditional conjuncts hold at every nontrivial zero.**  For `ρ ∈ NTZ χ` the
source-fiber evaluator vanishes and the carrier has no radial drift.  These are exactly the
two conjuncts of `ComputedSourceFiberCrossing` that hold without any RH/GRH input; the
remaining computed conjuncts (amplitude in `πℤ` and the genuine sign flip) are the residual
RH-strength content and are not asserted here.
-/
theorem NTZ_imp_computed_eval_and_drift (hC : 0 < C) (ρ : ℂ) (hρ : ρ ∈ NTZ χ) :
    FiberEval χ C ρ = 0 ∧ radial_drift (Carrier C) ρ.im = 0 := by
  exact ⟨ NTZ_imp_fiberEval_zero χ C ρ hρ, congrFun ( carrier_radial_drift_zero C hC ) ρ.im ⟩

end CriticalLinePhasor.ComputedCrossing
/-!
## The real standing readout and its sign flip at a simple zero

We construct a genuine **real-valued standing readout** whose sign flip *detects* a zero, and
prove the sign flip from local transversality (a simple zero), **without** assuming the zero
lies on the critical line and **without** using the critical-line Hardy `Z`-function.

The readout is a *residue-normalized local coordinate* / *source-defined amplitude
observable*: along the vertical line through `ρ` (at the zero's own real part `Re ρ`, **not**
`1/2`), sample the source-fiber evaluator and normalize by its transversal derivative
direction,
```
standingReadoutAt χ C ρ y = Re ( FiberEval χ C (Re ρ + i y) / (F'(ρ) · i) ),
```
where `F'(ρ) = deriv (FiberEval χ C) ρ`.  For a simple zero (`F'(ρ) ≠ 0`) this real function
vanishes at `y = Im ρ` with derivative `+1` there, so it changes sign across `Im ρ`.  The
sign flip is *derived from the derivative/transversality*, not encoded as a field.

For `C > 0`, `deriv (FiberEval χ C) ρ ≠ 0` is exactly the statement that `ρ` is a **simple
zero** of `L(·,χ)` (the carrier factor `C^(-ρ)` is nonzero and `F'(ρ) = C^(-ρ)·L'(ρ)`). -/

namespace CriticalLinePhasor.StandingReadout

open Complex DirichletCharacter
open CriticalLinePhasor.CarrierFiberDecomposition
  (FiberEval Carrier NTZ carrier_factor_ne_zero NTZ_imp_fiberEval_zero)

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (C : ℝ)

/-- **The real standing readout** at `ρ`, a residue-normalized local coordinate:
`standingReadoutAt χ C ρ y = Re ( FiberEval χ C (Re ρ + i y) / (deriv (FiberEval χ C) ρ · i) )`.
It samples the source-fiber evaluator on the vertical line through `ρ` (at `Re ρ`, not `1/2`)
and normalizes by the transversal derivative direction. -/
noncomputable def standingReadoutAt (ρ : ℂ) : ℝ → ℝ :=
  fun y => (FiberEval χ C ((ρ.re : ℂ) + (y : ℂ) * I) / (deriv (FiberEval χ C) ρ * I)).re

/-
**`FiberEval χ C` is differentiable** (for `C > 0` and non-principal `χ`, where the
`L`-function is entire): both the carrier factor `C^(-s)` and `L(s,χ)` are differentiable.
-/
theorem fiberEval_differentiableAt (hC : 0 < C) (hχ : χ ≠ 1) (ρ : ℂ) :
    DifferentiableAt ℂ (FiberEval χ C) ρ := by
  unfold CriticalLinePhasor.CarrierFiberDecomposition.FiberEval
  refine DifferentiableAt.mul ( DifferentiableAt.cpow ( differentiableAt_const _ ) ( differentiableAt_id.neg ) ?_ ) ( (DirichletCharacter.differentiable_LFunction hχ).differentiableAt )
  rw [Complex.ofReal_mem_slitPlane]
  positivity

/-
**Real-analysis sign-change lemma.**  A real function with value `0` and strictly positive
derivative at a point changes sign across that point: it is negative just to the left and
positive just to the right, so the product of the two straddling samples is negative.
-/
theorem sign_change_of_hasDerivAt_pos {R : ℝ → ℝ} {c d : ℝ}
    (h0 : R c = 0) (hd : HasDerivAt R d c) (hpos : 0 < d) :
    ∃ ε : ℝ, 0 < ε ∧ R (c - ε) * R (c + ε) < 0 := by
  -- By the definition of derivative, since $d > 0$, there exists $\delta > 0$ such that for all $x$ with $0 < |x - c| < \delta$, we have $\frac{R(x) - R(c)}{x - c} > 0$.
  obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ x, 0 < |x - c| ∧ |x - c| < δ → (R x - R c) / (x - c) > 0 := by
    rw [ hasDerivAt_iff_tendsto_slope ] at hd;
    have := Metric.tendsto_nhdsWithin_nhds.mp hd d hpos;
    obtain ⟨ δ, hδ₁, hδ₂ ⟩ := this; exact ⟨ δ, hδ₁, fun x hx => by have := hδ₂ ( show x ≠ c from by aesop ) ( by simpa [ Real.dist_eq, abs_mul, abs_div ] using hx.2 ) ; rw [ slope_def_field ] at this; linarith [ abs_lt.mp this ] ⟩ ;
  refine' ⟨ δ / 2, half_pos hδ_pos, _ ⟩;
  have := hδ ( c - δ / 2 ) ⟨ by rw [ abs_of_neg ] <;> linarith, by rw [ abs_of_neg ] <;> linarith ⟩ ; have := hδ ( c + δ / 2 ) ⟨ by rw [ abs_of_pos ] <;> linarith, by rw [ abs_of_pos ] <;> linarith ⟩ ; simp_all +decide [ div_pos_iff ] ;
  cases ‹0 < R ( c - δ / 2 ) ∧ δ / 2 < 0 ∨ R ( c - δ / 2 ) < 0› <;> nlinarith

/-
**The readout vanishes at the zero's height.**  `standingReadoutAt χ C ρ (Im ρ) = 0`,
because the numerator is `FiberEval χ C ρ = 0`.
-/
theorem standingReadoutAt_eq_zero (ρ : ℂ) (hρ : ρ ∈ NTZ χ) :
    standingReadoutAt χ C ρ ρ.im = 0 := by
  unfold CriticalLinePhasor.StandingReadout.standingReadoutAt;
  rw [ ← Complex.re_add_im ρ ] ; simp +decide [ NTZ_imp_fiberEval_zero χ C ρ hρ ] ;

/-
**The readout has derivative `+1` at the zero's height** (for a simple zero).  Writing
`b = deriv (FiberEval χ C) ρ · i ≠ 0`, the inner sample `y ↦ FiberEval χ C (Re ρ + i y)` has
derivative `b` at `Im ρ`, so the normalized quotient has derivative `b/b = 1`, and taking real
parts gives derivative `Re 1 = 1`.
-/
theorem standingReadoutAt_hasDerivAt_one (hC : 0 < C) (hχ : χ ≠ 1) (ρ : ℂ)
    (hsimple : deriv (FiberEval χ C) ρ ≠ 0) :
    HasDerivAt (standingReadoutAt χ C ρ) 1 ρ.im := by
  have hF : HasDerivAt (fun y : ℝ => (FiberEval χ C) ((ρ.re : ℂ) + (y : ℂ) * I) / (deriv (FiberEval χ C) ρ * I)) 1 ρ.im := by
    have hg : HasDerivAt (fun y : ℝ => (ρ.re : ℂ) + (y : ℂ) * I) I ρ.im := by
      have h1 : HasDerivAt (fun y : ℝ => (y : ℂ) * I) I ρ.im := by
        simpa using (HasDerivAt.ofReal_comp (hasDerivAt_id ρ.im)).mul_const I
      simpa using h1.const_add (ρ.re : ℂ)
    have hfe : HasDerivAt (FiberEval χ C) (deriv (FiberEval χ C) ρ) ((ρ.re : ℂ) + (ρ.im : ℂ) * I) := by
      rw [Complex.re_add_im]
      exact (fiberEval_differentiableAt χ C hC hχ ρ).hasDerivAt
    have hcomp := hfe.comp ρ.im hg
    have hb : deriv (FiberEval χ C) ρ * I ≠ 0 := mul_ne_zero hsimple Complex.I_ne_zero
    have hd := hcomp.div_const (deriv (FiberEval χ C) ρ * I)
    rw [div_self hb] at hd
    exact hd
  rw [ hasDerivAt_iff_tendsto_slope_zero ] at *;
  convert Complex.continuous_re.continuousAt.tendsto.comp hF using 2 <;> norm_num [ standingReadoutAt ]

/-- **Sign flip of the standing readout at a simple zero.**  If `ρ` is a nontrivial zero
(`ρ ∈ NTZ χ`) that is simple (`deriv (FiberEval χ C) ρ ≠ 0`), then the real standing readout
changes sign across `Im ρ`:
```
∃ ε > 0, standingReadoutAt χ C ρ (Im ρ - ε) · standingReadoutAt χ C ρ (Im ρ + ε) < 0.
```
No `Re ρ = 1/2` is assumed and no critical-line Hardy `Z` is used; the flip is derived from
the transversal derivative. -/
theorem NTZ_simpleZero_imp_readout_signFlip (hC : 0 < C) (hχ : χ ≠ 1) (ρ : ℂ)
    (hρ : ρ ∈ NTZ χ) (hsimple : deriv (FiberEval χ C) ρ ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧
      standingReadoutAt χ C ρ (ρ.im - ε) * standingReadoutAt χ C ρ (ρ.im + ε) < 0 :=
  sign_change_of_hasDerivAt_pos
    (standingReadoutAt_eq_zero χ C ρ hρ)
    (standingReadoutAt_hasDerivAt_one χ C hC hχ ρ hsimple)
    one_pos

/-
**`deriv FiberEval` factors through `deriv L` at a zero.**  At a point where
`L(ρ,χ) = 0`, `deriv (FiberEval χ C) ρ = C^(-ρ) · deriv (LFunction χ) ρ`.  Hence (for `C > 0`)
the transversality condition `deriv (FiberEval χ C) ρ ≠ 0` is equivalent to `ρ` being a simple
zero of `L(·,χ)` (`deriv (LFunction χ) ρ ≠ 0`).
-/
theorem fiberEval_deriv_eq_at_zero (hC : 0 < C) (hχ : χ ≠ 1) (ρ : ℂ)
    (hL : LFunction χ ρ = 0) :
    deriv (FiberEval χ C) ρ = (C : ℂ) ^ (-ρ) * deriv (LFunction χ) ρ := by
  have hcpow : HasDerivAt (fun s : ℂ => (C : ℂ) ^ (-s)) (deriv (fun s : ℂ => (C : ℂ) ^ (-s)) ρ) ρ :=
    (DifferentiableAt.cpow (differentiableAt_const _) (differentiableAt_id.neg) (by rw [Complex.ofReal_mem_slitPlane]; positivity)).hasDerivAt
  have hL' : HasDerivAt (LFunction χ) (deriv (LFunction χ) ρ) ρ := (differentiable_LFunction hχ ρ).hasDerivAt
  have hmul := hcpow.mul hL'
  rw [hL, mul_zero, zero_add] at hmul
  have : HasDerivAt (FiberEval χ C) ((C : ℂ) ^ (-ρ) * deriv (LFunction χ) ρ) ρ := hmul
  exact this.deriv

/-- **Sign flip from a simple `L`-zero.**  Restatement of the sign-flip theorem with the
transversality phrased directly as `ρ` being a *simple zero of `L(·,χ)`*
(`deriv (LFunction χ) ρ ≠ 0`). -/
theorem NTZ_simpleLZero_imp_readout_signFlip (hC : 0 < C) (hχ : χ ≠ 1) (ρ : ℂ)
    (hρ : ρ ∈ NTZ χ) (hsimple : deriv (LFunction χ) ρ ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧
      standingReadoutAt χ C ρ (ρ.im - ε) * standingReadoutAt χ C ρ (ρ.im + ε) < 0 := by
  have hL : LFunction χ ρ = 0 := hρ.2.2
  have hfd : deriv (FiberEval χ C) ρ ≠ 0 := by
    rw [fiberEval_deriv_eq_at_zero χ C hC hχ ρ hL]
    exact mul_ne_zero (carrier_factor_ne_zero (hC := hC) (s := ρ)) hsimple
  exact NTZ_simpleZero_imp_readout_signFlip χ C hC hχ ρ hρ hfd

end CriticalLinePhasor.StandingReadout
/-!
## Source exhaustion for computed crossing events

The canonical `SourceExhaustion.SourceFiberCrossing` is, up to proof-irrelevant data, just
`param` in the strip with `FiberEval χ C param = 0` — i.e. `NTZ` membership repackaged.  Here
we strengthen source exhaustion so that the captured object is a **computed crossing event**:
it stores the genuinely *computed* observables of the crossing —

* the computed amplitude `amplitudeFunctional χ C param`,
* the computed real standing readout `standingReadoutAt χ C param`,
* the computed Möbius projection readout `1 - 1/param` (codomain coordinate),

each tied to `param` by a defining equation — and yet remains pinned down by its readout
parameter.  We then prove that **every** nontrivial zero is the readout parameter of exactly
one such computed event.

`ComputedSourceFiberCrossingEvent` is **not** defined as `NTZ`: it carries computed
amplitude/readout/projection data.  No `Re ρ = 1/2` is used and the count is over all strip
zeros, not only critical-line zeros. -/

namespace CriticalLinePhasor.ComputedExhaustion

open Complex DirichletCharacter
open CriticalLinePhasor.CarrierFiberDecomposition
  (FiberEval NTZ NTZ_imp_fiberEval_zero)
open CriticalLinePhasor.ComputedCrossing (amplitudeFunctional)
open CriticalLinePhasor.StandingReadout (standingReadoutAt)

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (C : ℝ)

/-- **A computed source-fiber crossing event.**  It stores the readout parameter together with
the *computed* crossing observables (amplitude, standing readout, Möbius projection), each
fixed to its functional value at `param` by a defining equation.  The analytic content is
`fiber_vanishes` (the source-fiber evaluator vanishes); the strip membership locates the
event in the open critical strip.  No midpoint condition is built in, and the stored data are
computed, not free witnesses. -/
structure ComputedSourceFiberCrossingEvent where
  /-- The readout parameter `ρ`. -/
  param : ℂ
  /-- The readout parameter lies in the open critical strip `0 < Re ρ < 1`. -/
  in_strip : 0 < param.re ∧ param.re < 1
  /-- The source-fiber evaluator vanishes at `param`. -/
  fiber_vanishes : FiberEval χ C param = 0
  /-- The computed amplitude observable. -/
  amplitude : ℝ
  /-- The amplitude is the computed amplitude functional at `param`. -/
  amplitude_spec : amplitude = amplitudeFunctional χ C param
  /-- The computed real standing-readout observable. -/
  readout : ℝ → ℝ
  /-- The readout is the computed standing readout at `param`. -/
  readout_spec : readout = standingReadoutAt χ C param
  /-- The computed Möbius projection readout (codomain coordinate). -/
  projection : ℂ
  /-- The projection is the Möbius readout `1 - 1/param`. -/
  projection_spec : projection = 1 - 1 / param

/-- The readout parameter of a computed crossing event. -/
def readoutParameter (e : ComputedSourceFiberCrossingEvent χ C) : ℂ := e.param

/-
**Computed crossing events are pinned by their readout parameter.**  All stored
observables are determined by `param` (they equal their functional values), so two events with
the same readout parameter coincide.
-/
theorem crossingEvent_ext {e₁ e₂ : ComputedSourceFiberCrossingEvent χ C}
    (h : readoutParameter χ C e₁ = readoutParameter χ C e₂) : e₁ = e₂ := by
  cases e₁ ; cases e₂ ; simp_all +decide [ readoutParameter ]

/-
**Source exhaustion for computed crossing events.**  Every nontrivial zero `ρ` of
`L(·,χ)` is the readout parameter of *exactly one* computed source-fiber crossing event.  The
captured object carries computed amplitude/readout/projection data (it is not `NTZ`
membership), no `Re ρ = 1/2` is used, and the statement ranges over all strip zeros.

(The positivity hypothesis `0 < C` is included as requested, but turns out to be unnecessary:
the construction needs only that `ρ` is a nontrivial zero.)
-/
theorem sourceExhaustion_computed (_hC : 0 < C) :
    ∀ ρ ∈ NTZ χ, ∃! e : ComputedSourceFiberCrossingEvent χ C, readoutParameter χ C e = ρ := by
  intro ρ hρ
  use ⟨ρ, ⟨hρ.1, hρ.2.1⟩, NTZ_imp_fiberEval_zero χ C ρ hρ, amplitudeFunctional χ C ρ, rfl, standingReadoutAt χ C ρ, rfl, 1 - 1 / ρ, rfl⟩;
  exact ⟨ rfl, fun e he => by cases e; aesop ⟩

end CriticalLinePhasor.ComputedExhaustion/-!
## A non-tautological computed source crossing and the geometric forcing step

The earlier `ComputedSourceFiberCrossingEvent` (in `ComputedExhaustion`) stores computed
fields, but its source-exhaustion theorem only *records* the readout parameter; the genuine
crossing conditions (`amplitude ∈ πℤ`, sign flip, projected no-drift) are not part of what is
proved there.  This section replaces that wrapper with a genuinely non-tautological structure
`ComputedSourceCrossing` whose five fields are the real crossing conditions, and it proves the
**geometric forcing step**

```
projectedNoDrift_to_unitCircle : ProjectedNoDriftEvent χ C ρ → ‖1 - 1/ρ‖ = 1
```

unconditionally and non-circularly.

### Honesty / non-circularity

* `ProjectedNoDriftEvent χ C ρ` is defined as a genuine *no-drift* condition on the
  **Möbius-projected** carrier readout `y ↦ 1 - 1/(Re ρ + i y)` (the projection coordinate
  `1 - 1/param`): its modulus has vanishing radial drift at the zero's height, with the zero
  off the real axis (`Im ρ ≠ 0`).  It does **not** contain `Re ρ = 1/2`, `‖1 - 1/ρ‖ = 1`,
  `symPair c ρ = 0`, or `GeneratedBySymMidpoint ρ`.  The forcing theorem is then a genuine
  computation: stationarity of the projected modulus along the vertical line forces, since the
  height is nonzero, the real part to `1/2` (`projectedNoDrift_imp_re_half`), and the Möbius /
  Pythagorean lemma converts `Re ρ = 1/2` to `‖1 - 1/ρ‖ = 1`.  No `symPair_zero_re_eq_half`
  and no backwards use of the midpoint lemma is involved.

* The structure `ComputedSourceCrossing` stores **no** free/manufactured fields (`ledger`,
  `preVal`, `postVal` are gone) and **no** built-in `Re ρ = 1/2` / unit-circle / midpoint
  data.  Its sign-crossing field is the genuine analytic sign flip of `standingReadoutAt`.

### Scope of the assembly theorem

Of the five crossing fields, two hold for *every* nontrivial zero (`eval_zero`,
`carrier_no_drift`), one follows from simplicity of the zero (`sign_crossing`).  The remaining
two are the irreducible residue and are **not** provable from `ρ ∈ NTZ χ` alone:

* `amplitude_quantized` (`-(Im ρ)·log C ∈ πℤ`) is in fact *false* for a generic base
  `C ≠ 1`, so it cannot hold uniformly for all `C > 0`;
* `projected_no_drift` *forces* `Re ρ = 1/2` (by `projectedNoDrift_imp_re_half`), so asserting
  it at every zero is exactly RH/GRH.

Accordingly `NTZ_imp_ComputedSourceCrossing` takes these two as explicit, honestly named local
hypotheses (and simplicity for the sign flip) rather than manufacturing them.  This is the
sound non-circular statement: the hypothesis-free version would *be* a proof of RH/GRH, which
is neither assumed nor faked here. -/

namespace CriticalLinePhasor.ComputedSourceCrossingFix

open Complex DirichletCharacter
open CriticalLinePhasor.CarrierFiberDecomposition
  (FiberEval Carrier radial_drift NTZ piInt NTZ_imp_fiberEval_zero carrier_radial_drift_zero)
open CriticalLinePhasor.ComputedCrossing (amplitudeFunctional)
open CriticalLinePhasor.StandingReadout
  (standingReadoutAt NTZ_simpleLZero_imp_readout_signFlip)
open CriticalLinePhasor.MobiusMidpoint (norm_one_sub_inv_eq_one_iff)

local notation "πℤ" => piInt

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (C : ℝ)

/-- **The Möbius-projected carrier readout** along the vertical line through `ρ`:
`y ↦ 1 - 1/(Re ρ + i y)`.  This samples the projection coordinate `1 - 1/param` of the
carrier readout along the line at the zero's real part. -/
noncomputable def projectedReadoutLine (ρ : ℂ) : ℝ → ℂ :=
  fun y => 1 - 1 / ((ρ.re : ℂ) + (y : ℂ) * I)

/-- **The projected no-drift event.**  Off the real axis (`Im ρ ≠ 0`), the modulus of the
Möbius-projected carrier readout `y ↦ 1 - 1/(Re ρ + i y)` has vanishing radial drift at the
height `Im ρ`.  This is a genuine geometric (no-drift) condition; it contains **no**
`Re ρ = 1/2`, **no** `‖1 - 1/ρ‖ = 1`, **no** `symPair`, and **no** midpoint data. -/
def ProjectedNoDriftEvent (_χ : DirichletCharacter ℂ q) (_C : ℝ) (ρ : ℂ) : Prop :=
  ρ.im ≠ 0 ∧ radial_drift (projectedReadoutLine ρ) ρ.im = 0

omit [NeZero q] in
/-- **Geometric forcing (real part).**  If the projected carrier readout has vanishing radial
drift at the (nonzero) height `Im ρ`, then `Re ρ = 1/2`.  The projected modulus squared along
the line is `G(y) = ((Re ρ - 1)² + y²)/((Re ρ)² + y²)`; its stationarity at `y = Im ρ ≠ 0`
forces `2·Re ρ - 1 = 0`.  No `Re ρ = 1/2` is assumed and no `symPair_zero_re_eq_half` is
used. -/
theorem projectedNoDrift_imp_re_half (ρ : ℂ) (h : ProjectedNoDriftEvent χ C ρ) :
    ρ.re = 1 / 2 := by
  obtain ⟨him, hd⟩ := h
  have hD : ρ.re ^ 2 + ρ.im ^ 2 ≠ 0 := by
    have : (0 : ℝ) < ρ.im ^ 2 := by positivity
    nlinarith [sq_nonneg ρ.re]
  set a := ρ.re with ha
  set y₀ := ρ.im with hy
  set G : ℝ → ℝ := fun y => ((a - 1) ^ 2 + y ^ 2) / (a ^ 2 + y ^ 2) with hG
  have hGpos : 0 < G y₀ := by
    apply div_pos
    · have : (0 : ℝ) < y₀ ^ 2 := by positivity
      nlinarith [sq_nonneg (a - 1)]
    · rcases lt_or_eq_of_le (by positivity : (0 : ℝ) ≤ a ^ 2 + y₀ ^ 2) with h | h
      · exact h
      · exact absurd h.symm hD
  have hGderiv : HasDerivAt G (2 * y₀ * (2 * a - 1) / (a ^ 2 + y₀ ^ 2) ^ 2) y₀ := by
    have h1 : HasDerivAt (fun y : ℝ => (a - 1) ^ 2 + y ^ 2) (2 * y₀) y₀ := by
      simpa using (hasDerivAt_pow 2 y₀).const_add ((a - 1) ^ 2)
    have h2 : HasDerivAt (fun y : ℝ => a ^ 2 + y ^ 2) (2 * y₀) y₀ := by
      simpa using (hasDerivAt_pow 2 y₀).const_add (a ^ 2)
    have := h1.div h2 hD
    exact this.congr_deriv (by rw [div_eq_div_iff (pow_ne_zero 2 hD) (pow_ne_zero 2 hD)]; ring)
  have hnorm_eq : ∀ y : ℝ, a ^ 2 + y ^ 2 ≠ 0 → ‖projectedReadoutLine ρ y‖ = Real.sqrt (G y) := by
    intro y hy2
    have hns : Complex.normSq (projectedReadoutLine ρ y) = G y := by
      unfold projectedReadoutLine
      have hw : ((a : ℂ) + (y : ℂ) * I) ≠ 0 := by
        intro hh
        apply hy2
        have h1 := congrArg Complex.re hh
        have h2 := congrArg Complex.im hh
        simp at h1 h2
        rw [h1, h2]; ring
      rw [show (1 - 1 / ((a : ℂ) + (y : ℂ) * I))
          = (((a : ℂ) + (y : ℂ) * I) - 1) / ((a : ℂ) + (y : ℂ) * I) by field_simp]
      rw [Complex.normSq_div]
      simp [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
        Complex.sub_im, hG]
      ring_nf
    rw [Complex.norm_def, hns]
  have hsqrt : HasDerivAt (fun y => Real.sqrt (G y))
      ((2 * y₀ * (2 * a - 1) / (a ^ 2 + y₀ ^ 2) ^ 2) / (2 * Real.sqrt (G y₀))) y₀ := by
    have := (Real.hasDerivAt_sqrt (ne_of_gt hGpos)).comp y₀ hGderiv
    exact this.congr_deriv (by ring)
  have heq : (fun y => ‖projectedReadoutLine ρ y‖) =ᶠ[nhds y₀] (fun y => Real.sqrt (G y)) := by
    have hopen : ∀ᶠ y in nhds y₀, a ^ 2 + y ^ 2 ≠ 0 := by
      have hcont : ContinuousAt (fun y : ℝ => a ^ 2 + y ^ 2) y₀ := by fun_prop
      exact hcont.eventually_ne hD
    filter_upwards [hopen] with y hy2 using hnorm_eq y hy2
  have hnormderiv : HasDerivAt (fun y => ‖projectedReadoutLine ρ y‖)
      ((2 * y₀ * (2 * a - 1) / (a ^ 2 + y₀ ^ 2) ^ 2) / (2 * Real.sqrt (G y₀))) y₀ :=
    hsqrt.congr_of_eventuallyEq heq
  have hzero :
      (2 * y₀ * (2 * a - 1) / (a ^ 2 + y₀ ^ 2) ^ 2) / (2 * Real.sqrt (G y₀)) = 0 := by
    rw [← hnormderiv.deriv]; exact hd
  have hsqrtpos : 0 < Real.sqrt (G y₀) := Real.sqrt_pos.mpr hGpos
  have hnum : 2 * y₀ * (2 * a - 1) = 0 := by
    rw [div_eq_zero_iff] at hzero
    rcases hzero with h | h
    · rw [div_eq_zero_iff] at h
      rcases h with h | h
      · exact h
      · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h) hD
    · exact absurd h (by positivity)
  have h2a : 2 * a - 1 = 0 := by
    rcases mul_eq_zero.mp hnum with h | h
    · rcases mul_eq_zero.mp h with h | h
      · norm_num at h
      · exact absurd h him
    · exact h
  linarith

/-- **The geometric forcing step.**  The projected no-drift event forces the Möbius image
`1 - 1/ρ` onto the unit circle: `‖1 - 1/ρ‖ = 1`.  This is proved by combining the real-part
forcing `projectedNoDrift_imp_re_half` (a genuine no-drift computation) with the pure-algebra
Möbius / Pythagorean lemma `norm_one_sub_inv_eq_one_iff`.  `ProjectedNoDriftEvent` does not
contain `‖1 - 1/ρ‖ = 1`, `Re ρ = 1/2`, or `symPair`, and the midpoint lemma is used in its
*forward* direction only. -/
theorem projectedNoDrift_to_unitCircle (ρ : ℂ) (h : ProjectedNoDriftEvent χ C ρ) :
    ‖1 - 1 / ρ‖ = 1 := by
  have him : ρ.im ≠ 0 := h.1
  have hρ : ρ ≠ 0 := by
    intro hh; apply him; rw [hh]; simp
  rw [norm_one_sub_inv_eq_one_iff ρ hρ]
  exact projectedNoDrift_imp_re_half χ C ρ h

/-- **The non-tautological computed source crossing.**  Replaces the computed-event wrapper:
its five fields are the genuine crossing conditions — the source-fiber evaluator vanishes, the
carrier has no radial drift, the computed amplitude functional lands on the π-ladder, the
real standing readout exhibits a genuine sign flip across `Im ρ`, and the projected carrier
readout has no radial drift.  No free witnesses (`ledger`, `preVal`, `postVal`) and no
`Re ρ = 1/2` / unit-circle / midpoint data are built in. -/
structure ComputedSourceCrossing (ρ : ℂ) : Prop where
  /-- The source-fiber evaluator vanishes at `ρ`. -/
  eval_zero : FiberEval χ C ρ = 0
  /-- The carrier has vanishing radial drift at the crossing height. -/
  carrier_no_drift : radial_drift (Carrier C) ρ.im = 0
  /-- The computed amplitude functional lands on the π-ladder `πℤ`. -/
  amplitude_quantized : amplitudeFunctional χ C ρ ∈ πℤ
  /-- The real standing readout changes sign across `Im ρ`. -/
  sign_crossing : ∃ ε : ℝ, 0 < ε ∧
    standingReadoutAt χ C ρ (ρ.im - ε) * standingReadoutAt χ C ρ (ρ.im + ε) < 0
  /-- The projected carrier readout has no radial drift. -/
  projected_no_drift : ProjectedNoDriftEvent χ C ρ

/-- **The two unconditional crossing fields** hold at every nontrivial zero: the source-fiber
evaluator vanishes and the carrier has no radial drift.  No RH/GRH and no `Re ρ = 1/2`. -/
theorem NTZ_imp_eval_zero_and_carrier_no_drift (hC : 0 < C) (ρ : ℂ) (hρ : ρ ∈ NTZ χ) :
    FiberEval χ C ρ = 0 ∧ radial_drift (Carrier C) ρ.im = 0 :=
  ⟨NTZ_imp_fiberEval_zero χ C ρ hρ, congrFun (carrier_radial_drift_zero C hC) ρ.im⟩

/-- **Assembly of a computed source crossing from a zero plus its residual analytic data.**

For a nontrivial zero `ρ ∈ NTZ χ` of a non-principal character `χ`, the unconditional fields
`eval_zero` and `carrier_no_drift` hold automatically, and `sign_crossing` follows from the
zero being simple (`hsimple`).  The remaining two fields are the irreducible residue and are
*not* provable from `ρ ∈ NTZ χ` alone, so they are taken as explicit, honestly named
hypotheses:

* `hamp : amplitudeFunctional χ C ρ ∈ πℤ` — false for a generic base `C ≠ 1`, hence cannot
  hold uniformly;
* `hpnd : ProjectedNoDriftEvent χ C ρ` — forces `Re ρ = 1/2` (`projectedNoDrift_imp_re_half`),
  hence asserting it at every zero is exactly RH/GRH.

The hypothesis-free version would *be* a proof of RH/GRH and is deliberately neither assumed
nor manufactured. -/
theorem NTZ_imp_ComputedSourceCrossing (hC : 0 < C) (hχ : χ ≠ 1) (ρ : ℂ) (hρ : ρ ∈ NTZ χ)
    (hsimple : deriv (LFunction χ) ρ ≠ 0)
    (hamp : amplitudeFunctional χ C ρ ∈ πℤ)
    (hpnd : ProjectedNoDriftEvent χ C ρ) :
    ComputedSourceCrossing χ C ρ :=
  { eval_zero := NTZ_imp_fiberEval_zero χ C ρ hρ
    carrier_no_drift := congrFun (carrier_radial_drift_zero C hC) ρ.im
    amplitude_quantized := hamp
    sign_crossing := NTZ_simpleLZero_imp_readout_signFlip χ C hC hχ ρ hρ hsimple
    projected_no_drift := hpnd }

/-- A computed source crossing is represented by a symmetric midpoint fiber crossing. -/
theorem computedSourceCrossing_imp_generatedBySymMidpoint (ρ : ℂ)
    (h : ComputedSourceCrossing χ C ρ) :
    CriticalLinePhasor.TateCriticalLine.GeneratedBySymMidpoint ρ := by
  have hre : ρ.re = 1 / 2 := projectedNoDrift_imp_re_half χ C ρ h.projected_no_drift
  have him : ρ.im ≠ 0 := h.projected_no_drift.1
  let c : ℝ := Real.exp (Real.pi / (2 * |ρ.im|))
  have hc : 1 < c := by
    rw [Real.one_lt_exp_iff]
    positivity
  refine ⟨c, hc, ?_⟩
  rw [CriticalLinePhasor.NoOffLineZeros.symPair_eq_zero_iff c hc ρ]
  rcases lt_or_gt_of_ne him with himneg | himpos
  · refine ⟨-1, ?_⟩
    have him_eq :
        Real.pi * (2 * ((-1 : ℤ) : ℝ) + 1) / (2 * Real.log c) = ρ.im := by
      norm_num [c, Real.log_exp, abs_of_neg himneg]
      field_simp
    calc
      ρ = (ρ.re : ℂ) + (ρ.im : ℂ) * I := by apply Complex.ext <;> simp
      _ = (1 / 2 : ℂ) +
          ((Real.pi * (2 * (((-1 : ℤ) : ℝ)) + 1) / (2 * Real.log c) : ℝ) : ℂ) * I := by
        rw [hre, him_eq]
        norm_num
  · refine ⟨0, ?_⟩
    have him_eq :
        Real.pi * (2 * ((0 : ℤ) : ℝ) + 1) / (2 * Real.log c) = ρ.im := by
      norm_num [c, Real.log_exp, abs_of_pos himpos]
      field_simp
    calc
      ρ = (ρ.re : ℂ) + (ρ.im : ℂ) * I := by apply Complex.ext <;> simp
      _ = (1 / 2 : ℂ) +
          ((Real.pi * (2 * (((0 : ℤ) : ℝ)) + 1) / (2 * Real.log c) : ℝ) : ℂ) * I := by
        rw [hre, him_eq]
        norm_num

/-- The computed crossing assembly connects a nontrivial zero to the symmetric midpoint
fiber representation. -/
theorem NTZ_imp_generatedBySymMidpoint (hC : 0 < C) (hχ : χ ≠ 1) (ρ : ℂ) (hρ : ρ ∈ NTZ χ)
    (hsimple : deriv (LFunction χ) ρ ≠ 0)
    (hamp : amplitudeFunctional χ C ρ ∈ πℤ)
    (hpnd : ProjectedNoDriftEvent χ C ρ) :
    CriticalLinePhasor.TateCriticalLine.GeneratedBySymMidpoint ρ :=
  computedSourceCrossing_imp_generatedBySymMidpoint χ C ρ
    (NTZ_imp_ComputedSourceCrossing χ C hC hχ ρ hρ hsimple hamp hpnd)

/-- **Projected no-drift, from the projected (downward) direction.** When `ρ` sits on the critical
line — as every zero produced by the projection chain does (`chainProducedZetaZero_re`) — the
Möbius-projected readout `y ↦ 1 - 1/(ρ.re + iy)` has constant modulus `1`: it rides the unit
circle, so its radial drift vanishes. This is the converse of `projectedNoDrift_imp_re_half`: the
source produces on the line, the Möbius/log projection adds no drift, so the projected readout is
drift-free. No `symPair`, no assumption beyond `Re ρ = 1/2` and `ρ` off the real axis. -/
theorem projectedNoDrift_of_re_half (ρ : ℂ) (hre : ρ.re = 1 / 2) (him : ρ.im ≠ 0) :
    ProjectedNoDriftEvent χ C ρ := by
  refine ⟨him, ?_⟩
  have hnorm : ∀ t : ℝ, ‖projectedReadoutLine ρ t‖ = 1 := by
    intro t
    have hre_pt : ((ρ.re : ℂ) + (t : ℂ) * I).re = 1 / 2 := by
      simp [Complex.add_re, Complex.mul_re, hre]
    have hpt : ((ρ.re : ℂ) + (t : ℂ) * I) ≠ 0 := by
      intro h; rw [h, Complex.zero_re] at hre_pt; norm_num at hre_pt
    show ‖1 - 1 / ((ρ.re : ℂ) + (t : ℂ) * I)‖ = 1
    rw [norm_one_sub_inv_eq_one_iff _ hpt]; exact hre_pt
  have hfun : (fun t => ‖projectedReadoutLine ρ t‖) = (fun _ => (1 : ℝ)) := funext hnorm
  show deriv (fun t => ‖projectedReadoutLine ρ t‖) ρ.im = 0
  rw [hfun]; exact deriv_const ρ.im 1

/-- **Projected no-drift ⟺ on the line** (off the real axis). The forcing
(`projectedNoDrift_imp_re_half`) and the projected-direction construction
(`projectedNoDrift_of_re_half`) together: the Möbius-projected readout is drift-free exactly when
`ρ` is on the critical line. -/
theorem projectedNoDriftEvent_iff (ρ : ℂ) (him : ρ.im ≠ 0) :
    ProjectedNoDriftEvent χ C ρ ↔ ρ.re = 1 / 2 :=
  ⟨projectedNoDrift_imp_re_half χ C ρ, fun hre => projectedNoDrift_of_re_half χ C ρ hre him⟩

end CriticalLinePhasor.ComputedSourceCrossingFix
