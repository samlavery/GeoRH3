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
  convert HasDerivAt.prodMk ( HasDerivAt.mul ( HasDerivAt.mul ( hasDerivAt_const _ _ ) ( hasDerivAt_id k ) ) ( HasDerivAt.cos ( HasDerivAt.const_mul ( 2 * Real.pi ) ( hasDerivAt_id k ) ) ) ) ( HasDerivAt.prodMk ( HasDerivAt.mul ( HasDerivAt.mul ( hasDerivAt_const _ _ ) ( hasDerivAt_id k ) ) ( HasDerivAt.sin ( HasDerivAt.const_mul ( 2 * Real.pi ) ( hasDerivAt_id k ) ) ) ) ( HasDerivAt.const_mul p ( hasDerivAt_id k ) ) ) using 1;
  unfold CriticalLinePhasor.Geometry.helixVel; norm_num; ring;
  norm_num

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
  convert HasDerivAt.add ( HasDerivAt.mul ( HasDerivAt.div_const ( hasDerivAt_id t ) _ ) ( HasDerivAt.sqrt ( HasDerivAt.add ( hasDerivAt_const _ _ ) ( HasDerivAt.mul ( hasDerivAt_const _ _ ) ( hasDerivAt_pow 2 t ) ) ) _ ) ) ( HasDerivAt.mul ( hasDerivAt_const _ _ ) ( HasDerivAt.arsinh ( HasDerivAt.div_const ( HasDerivAt.mul ( hasDerivAt_const _ _ ) ( hasDerivAt_id t ) ) _ ) ) ) using 1 <;> norm_num ; ring;
  · field_simp;
    rw [ Real.sq_sqrt <| by positivity, Real.sq_sqrt <| by positivity ] ; ring;
    rw [ show p ^ 2 + r ^ 2 + r ^ 2 * Real.pi ^ 2 * t ^ 2 * 4 = ( p ^ 2 + r ^ 2 ) * ( ( p ^ 2 + r ^ 2 * Real.pi ^ 2 * t ^ 2 * 4 + r ^ 2 ) / ( p ^ 2 + r ^ 2 ) ) by rw [ mul_div_cancel₀ _ ( by positivity ) ] ; ring ] ; rw [ Real.sqrt_mul ( by positivity ) ] ; ring;
  · positivity

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
      simpa [ div_eq_inv_mul ] using hf;
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

end CriticalLinePhasor.NoOffLineZeros
