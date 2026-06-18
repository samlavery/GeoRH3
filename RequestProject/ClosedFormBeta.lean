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
  have hpos : (0:ℝ) < p ^ 2 + r ^ 2 + 4 * π ^ 2 * r ^ 2 * t ^ 2 := by positivity
  convert HasDerivAt.add ( HasDerivAt.mul ( HasDerivAt.div_const ( hasDerivAt_id t ) 2 ) ( HasDerivAt.sqrt ( HasDerivAt.add ( hasDerivAt_const t (p^2+r^2) ) ( HasDerivAt.mul ( hasDerivAt_const t (4*π^2*r^2) ) ( hasDerivAt_pow 2 t ) ) ) hpos.ne' ) ) ( HasDerivAt.mul ( hasDerivAt_const t ((p^2+r^2)/(4*π*r)) ) ( HasDerivAt.arsinh ( HasDerivAt.div_const ( HasDerivAt.mul ( hasDerivAt_const t (2*π*r) ) ( hasDerivAt_id t ) ) (√(p^2+r^2)) ) ) ) using 1
  · rfl
  · rfl
  · funext x
    simp only [Pi.add_apply, Pi.mul_apply, id_eq]
  · norm_num
    have hB : (0:ℝ) < p ^ 2 + r ^ 2 := by positivity
    have hA : √(p ^ 2 + r ^ 2 + 4 * π ^ 2 * r ^ 2 * t ^ 2) > 0 := Real.sqrt_pos.mpr hpos
    have hinner : √(1 + (2 * π * r * t / √(p ^ 2 + r ^ 2)) ^ 2) = √(p ^ 2 + r ^ 2 + 4 * π ^ 2 * r ^ 2 * t ^ 2) / √(p ^ 2 + r ^ 2) := by
      rw [← Real.sqrt_div' _ (by positivity)]
      congr 1
      rw [div_pow, Real.sq_sqrt hB.le]
      field_simp
      ring
    rw [hinner]
    have hBp : (0:ℝ) < √(p ^ 2 + r ^ 2) := Real.sqrt_pos.mpr hB
    have hA2 : √(p ^ 2 + r ^ 2 + 4 * π ^ 2 * r ^ 2 * t ^ 2) ^ 2 = p ^ 2 + r ^ 2 + 4 * π ^ 2 * r ^ 2 * t ^ 2 := Real.sq_sqrt hpos.le
    have hB2 : √(p ^ 2 + r ^ 2) ^ 2 = p ^ 2 + r ^ 2 := Real.sq_sqrt hB.le
    set A := √(p ^ 2 + r ^ 2 + 4 * π ^ 2 * r ^ 2 * t ^ 2) with hAdef
    set B := √(p ^ 2 + r ^ 2) with hBdef
    rw [inv_div]
    field_simp
    nlinarith [hA2, hB2, hA, hBp, Real.sqrt_nonneg (p ^ 2 + r ^ 2 + r ^ 2 * 2 ^ 2 * π ^ 2 * t ^ 2), Real.sq_sqrt (show (0:ℝ) ≤ p ^ 2 + r ^ 2 + r ^ 2 * 2 ^ 2 * π ^ 2 * t ^ 2 by positivity)]
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
  rw [← Complex.ofReal_natCast ell, CriticalLinePhasor.cpow_vertical_line_phasor ( ell : ℝ ) ( by positivity ) σ y]
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
      simpa only [ slope_fun_def_field, div_eq_inv_mul ] using hf;
  refine ⟨δ, hδ_pos, fun y hy z hz => ?_⟩
  obtain ⟨hy1, hy2⟩ := hy
  obtain ⟨hz1, hz2⟩ := hz
  have hsy : (f y - f x₀) / (y - x₀) * L > 0 := hδ y (by rw [abs_lt]; constructor <;> linarith) (by intro h; rw [h] at hy2; linarith)
  have hsz : (f z - f x₀) / (z - x₀) * L > 0 := hδ z (by rw [abs_lt]; constructor <;> linarith) (by intro h; rw [h] at hz1; linarith)
  rw [h0, sub_zero] at hsy hsz
  have hyL : f y * L < 0 := by
    have := mul_neg_of_pos_of_neg hsy (by linarith : y - x₀ < 0)
    rw [div_mul_eq_mul_div, div_mul_cancel₀] at this
    · exact this
    · linarith
  have hzL : f z * L > 0 := by
    have := mul_pos hsz (by linarith : (0:ℝ) < z - x₀)
    rw [div_mul_eq_mul_div, div_mul_cancel₀] at this
    · exact this
    · linarith
  nlinarith [mul_self_pos.2 hL, hyL, hzL]
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
/-!
## Operator / readout realization of the phasor cancellation observable
The cancellation condition of the model,
```
C(y) = Σ χ(n) · A(n) · e^{-i y log n},   A(n) = n^{-1/2},
```
is here given a precise **operator / readout realization** on a finite truncation
`Fin N` (the first `N` integers `1, …, N`).  There are three ingredients:
* the **spin generator** `genMatrix N`, the diagonal (self-adjoint / Hermitian) operator
  whose eigenvalues are the value-dependent spin rates `log n` (`genMatrix_isHermitian`);
* the **evolution / spin operator** `evolMatrix y N`, the diagonal *unitary* operator with
  entries `e^{-i y log n}` (`evolMatrix_mem_unitaryGroup`), realizing the spin
  `φ_n(y) = -(y log n)` as honest unit-modulus eigenvalues
  (`evolMatrix_mulVec_single`);
* the **readout** `readout N`, the magnitude-weighted linear functional
  `a ↦ Σ A(n) · a n` (a genuine `LinearMap`).
The realization theorem `cancellation_eq_phasor_sum` states that reading out the
spin-evolved coefficient/character vector reproduces *exactly* the phasor sum
`Σ χ(n) A(n) e^{-i y log n}`, and `cancellation_eq_cpow_sum` re-expresses it as the
Dirichlet partial sum `Σ χ(n) · n^{-(1/2 + i y)}`.  Thus the abstract cancellation
observable is realized concretely as `readout ∘ (unitary spin evolution)`.
-/
namespace CriticalLinePhasor.OperatorReadout
open Complex Matrix
/-- The unit-modulus **spin phasor** attached to `n`: `e^{-i y log n}`. -/
noncomputable def spin (y : ℝ) (n : ℕ) : ℂ := Complex.exp (-(y * Real.log n) * I)
/-- The critical-line **magnitude weight** `A(n) = n^{-1/2}`. -/
noncomputable def weight (n : ℕ) : ℝ := (n : ℝ) ^ (-(1 / 2 : ℝ))
/-- The full critical-line **phasor** `A(n)·e^{-i y log n} = n^{-1/2} e^{-i y log n}`. -/
noncomputable def phasor (y : ℝ) (n : ℕ) : ℂ := (weight n : ℂ) * spin y n
/-
The spin phasor has unit modulus (its exponent is purely imaginary).
-/
theorem spin_norm (y : ℝ) (n : ℕ) : ‖spin y n‖ = 1 := by
  unfold CriticalLinePhasor.OperatorReadout.spin;
  norm_num [ Complex.norm_exp ];
  norm_num [ Complex.log_im ]
/-
The phasor equals the critical-line Dirichlet term `n^{-(1/2 + i y)}`.
-/
theorem phasor_eq_cpow (y : ℝ) (n : ℕ) (hn : 0 < n) :
    phasor y n = (n : ℂ) ^ (-((1 / 2 : ℂ) + (y : ℂ) * I)) := by
      rw [CriticalLinePhasor.cpow_critical_line y n hn]
      unfold CriticalLinePhasor.OperatorReadout.phasor CriticalLinePhasor.OperatorReadout.weight CriticalLinePhasor.OperatorReadout.spin
      push_cast
      ring
/-- **Spin generator.**  The diagonal operator on `Fin N → ℂ` whose eigenvalues are the
value-dependent spin rates `log n` (here `n = i + 1`). -/
noncomputable def genMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal (fun i => (Real.log ((i : ℕ) + 1) : ℂ))
/-
The spin generator is **Hermitian** (self-adjoint): its eigenvalues `log n` are real.
-/
theorem genMatrix_isHermitian (N : ℕ) : (genMatrix N).IsHermitian := by
  unfold CriticalLinePhasor.OperatorReadout.genMatrix;
  simp +decide [ Matrix.IsHermitian ]
/-- **Evolution / spin operator.**  The diagonal operator with entries the spin phasors
`e^{-i y log n}` (`n = i + 1`).  This is the realization of the spin `φ_n(y) = -(y log n)`. -/
noncomputable def evolMatrix (y : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal (fun i => spin y ((i : ℕ) + 1))
/-
The evolution operator is **unitary**: it preserves norms, since every diagonal entry
`e^{-i y log n}` has unit modulus.
-/
theorem evolMatrix_mem_unitaryGroup (y : ℝ) (N : ℕ) :
    evolMatrix y N ∈ Matrix.unitaryGroup (Fin N) ℂ := by
      simp +decide [ CriticalLinePhasor.OperatorReadout.evolMatrix ];
      constructor <;> ext i j <;> by_cases hi : i = j <;> simp_all +decide;
      · simp_all +decide [ Complex.ext_iff, spin ];
        norm_num [ Complex.exp_re, Complex.exp_im, Matrix.one_apply ];
        norm_cast ; norm_num [ ← sq, hi ] ; ring;
      · exact Or.inl <| if_neg <| Ne.symm hi;
      · simp +decide [ Matrix.one_apply, hi, Complex.mul_conj, Complex.normSq_eq_norm_sq, spin_norm ];
      · exact Or.inr ( if_neg ( Ne.symm hi ) )
/-
**Eigen-action of the evolution operator.**  The standard basis vector `e_j` is an
eigenvector of `evolMatrix y N` with eigenvalue the spin phasor `e^{-i y log (j+1)}`.
-/
theorem evolMatrix_mulVec_single (y : ℝ) (N : ℕ) (j : Fin N) :
    evolMatrix y N *ᵥ (Pi.single j (1 : ℂ) : Fin N → ℂ)
      = spin y ((j : ℕ) + 1) • (Pi.single j (1 : ℂ) : Fin N → ℂ) := by
        ext i; by_cases hi : i = j <;> simp +decide [ * ] ;
        · exact if_pos rfl;
        · exact if_neg hi
/-- **Readout functional.**  The magnitude-weighted linear functional
`a ↦ Σ_i A(i+1) · a i`, realized as a genuine `LinearMap`. -/
noncomputable def readout (N : ℕ) : (Fin N → ℂ) →ₗ[ℂ] ℂ :=
  ∑ i : Fin N, (weight ((i : ℕ) + 1) : ℂ) • LinearMap.proj i
/-
Readout evaluates to the magnitude-weighted sum of coefficients.
-/
theorem readout_apply (N : ℕ) (a : Fin N → ℂ) :
    readout N a = ∑ i : Fin N, (weight ((i : ℕ) + 1) : ℂ) * a i := by
      unfold CriticalLinePhasor.OperatorReadout.readout;
      simp +decide [ Finset.sum_apply, LinearMap.proj ]
/-- **The cancellation observable**, realized as readout of the spin-evolved coefficient
vector: `C_N(y) = readout (evolMatrix y N *ᵥ χ)`. -/
noncomputable def cancellation (y : ℝ) (N : ℕ) (χ : Fin N → ℂ) : ℂ :=
  readout N (evolMatrix y N *ᵥ χ)
/-
**Operator/readout realization.**  Reading out the spin-evolved coefficient vector
reproduces exactly the phasor sum `Σ χ(n) A(n) e^{-i y log n}` (with `n = i + 1`).
-/
theorem cancellation_eq_phasor_sum (y : ℝ) (N : ℕ) (χ : Fin N → ℂ) :
    cancellation y N χ = ∑ i : Fin N, χ i * phasor y ((i : ℕ) + 1) := by
      unfold CriticalLinePhasor.OperatorReadout.cancellation;
      rw [ CriticalLinePhasor.OperatorReadout.readout_apply ];
      simp +decide [CriticalLinePhasor.OperatorReadout.evolMatrix, Matrix.mulVec, CriticalLinePhasor.OperatorReadout.phasor, mul_comm, mul_assoc]
/-
The cancellation observable as the **Dirichlet partial sum**
`Σ χ(n) · n^{-(1/2 + i y)}`.
-/
theorem cancellation_eq_cpow_sum (y : ℝ) (N : ℕ) (χ : Fin N → ℂ) :
    cancellation y N χ
      = ∑ i : Fin N, χ i * ((((i : ℕ) + 1 : ℕ) : ℂ) ^ (-((1 / 2 : ℂ) + (y : ℂ) * I))) := by
  convert CriticalLinePhasor.OperatorReadout.cancellation_eq_phasor_sum y N χ using 1;
  exact Finset.sum_congr rfl fun _ _ => by rw [ CriticalLinePhasor.OperatorReadout.phasor_eq_cpow ] ; norm_num;
end CriticalLinePhasor.OperatorReadout
/-!
## Exhaustion and receiver membership (mod-6 buckets)
The mod-6 "bucket" geometry (`s_n = n·π/3`, `6`-periodic) partitions the integers into six
**receivers**, the residue classes mod `6` indexed by `a : ZMod 6`.  We prove the two
defining structural facts:
* **Receiver membership** (`receiver_membership_unique`): every integer `n` belongs to
  *exactly one* receiver — namely `a = (n : ZMod 6)` — and distinct receivers are disjoint
  (`receiver_pairwise_disjoint`);
* **Exhaustion** (`receiver_exhaustion`): the receivers cover all of `ℕ`, and the finite
  observation windows `[0, 6N)` exhaust `ℕ` as `N → ∞` (`window_exhaustion`).
Together these say the receivers form a partition of `ℕ` that the truncated phasor sums
exhaust.
-/
namespace CriticalLinePhasor.Receiver
/-- The residue-class **receiver** mod `6`, indexed by `a : ZMod 6`. -/
def receiver (a : ZMod 6) : Set ℕ := {n : ℕ | (n : ZMod 6) = a}
/-- Membership in a receiver is exactly the residue condition. -/
theorem mem_receiver_iff (a : ZMod 6) (n : ℕ) : n ∈ receiver a ↔ (n : ZMod 6) = a := Iff.rfl
/-
**Receiver membership.**  Every integer lies in exactly one receiver.
-/
theorem receiver_membership_unique (n : ℕ) : ∃! a : ZMod 6, n ∈ receiver a := by
  refine' ⟨ n, _, _ ⟩ <;> simp +decide [ CriticalLinePhasor.Receiver.receiver ]
/-
Distinct receivers are disjoint.
-/
theorem receiver_pairwise_disjoint :
    Pairwise (Function.onFun Disjoint receiver) := by
      intros a b hab; rw [ Function.onFun, Set.disjoint_left ] ; intro n hna hnb; simp_all +decide [ CriticalLinePhasor.Receiver.mem_receiver_iff ] ;
/-
**Exhaustion (receivers).**  The receivers cover all of `ℕ`.
-/
theorem receiver_exhaustion : (⋃ a : ZMod 6, receiver a) = Set.univ := by
  ext n
  simp [mem_receiver_iff]
/-
**Exhaustion (windows).**  The finite observation windows `[0, 6N)` exhaust `ℕ`.
-/
theorem window_exhaustion (n : ℕ) : ∃ N : ℕ, n ∈ Finset.range (6 * N) := by
  exact ⟨ n + 1, Finset.mem_range.mpr ( by linarith ) ⟩
end CriticalLinePhasor.Receiver
/-!
## Counting zeros by winding number:  `N₀(T) = N(T)`
The winding of the phasor is *literally an angle*, so the natural, convergence-free way to
count zeros is the **argument principle / winding number** of the accumulated phase `Θ`.
On the helix the spin rate is `log n`, and — as the informal note puts it —
*multiplication becomes addition on the helix*: the phase is additive in `log`, so a
product of phasors winds by the **sum** of their argument increments.  This section makes
that counting precise.
We define the standard zero-counting functions for any candidate `L`-function `f`:
* `N f T`  — the number of zeros of `f` in the critical strip `0 ≤ Re s ≤ 1` with
  `0 < Im s ≤ T`;
* `N₀ f T` — the number of those zeros that lie on the **critical line** `Re s = 1/2`.
The clean unconditional content is:
* `N₀_eq_N_of_critical_line` — `N₀(T) = N(T)` **holds for every `T`** as soon as `f`
  satisfies the *critical-line property* (every strip zero has `Re s = 1/2`).  Indeed the two
  zero-sets are then literally equal (`stripZeros_eq_of_critical_line`).  This is the exact
  sense in which `N₀ = N` is equivalent to the Riemann Hypothesis.
* `symPair_N₀_eq_N` — for the exactly-soluble symmetric phasor closed form `P_c` the
  critical-line property is an unconditional theorem (`symPair_zero_re_eq_half`), so
  `N₀(T) = N(T)` holds **unconditionally** for the model.
The winding/argument-principle realization of the count is the **Hardy-type real angle
function** on the line: `symPair_on_line_eq` shows
```
P_c(1/2 + i y) = 2 · c^(-1/2) · cos(y · log c),
```
a *real* function whose modulus is `c^(-1/2)` and whose phase is `Θ(y) = y · log c`
(the winding angle).  Its zeros are exactly the points where `Θ` crosses an odd multiple of
`π/2` (`symPair_on_line_zero_iff`): each half-turn of the winding angle produces exactly one
zero, so counting zeros *is* counting half-turns of `Θ` — the convergence-free winding
count.  The abstract winding number `windingCount Θ a b = (Θ b - Θ a)/(2π)` is integer-valued
on loops (`windingCount_int_of_loop`), the defining property of a genuine winding number.
(For the full Dirichlet-`L` / Riemann `ζ` series, `N₀(T) = N(T)` for all `T` is the Riemann
Hypothesis, which is open; what is proved here unconditionally is the equivalence with the
critical-line property and its realization in the exactly-soluble phasor model.)
-/
namespace CriticalLinePhasor.ZeroCounting
open Complex CriticalLinePhasor.NoOffLineZeros
/-- Zeros of `f` in the critical strip `0 ≤ Re s ≤ 1` with imaginary part in `(0, T]`. -/
def stripZeros (f : ℂ → ℂ) (T : ℝ) : Set ℂ :=
  {s : ℂ | f s = 0 ∧ 0 < s.im ∧ s.im ≤ T ∧ 0 ≤ s.re ∧ s.re ≤ 1}
/-- `N(T)`: the number of zeros of `f` in the critical strip up to height `T`. -/
noncomputable def N (f : ℂ → ℂ) (T : ℝ) : ℕ := (stripZeros f T).ncard
/-- The strip zeros of `f` that additionally lie on the critical line `Re s = 1/2`. -/
def onLineStripZeros (f : ℂ → ℂ) (T : ℝ) : Set ℂ :=
  {s ∈ stripZeros f T | s.re = 1 / 2}
/-- `N₀(T)`: the number of strip zeros of `f` up to height `T` on the critical line. -/
noncomputable def N₀ (f : ℂ → ℂ) (T : ℝ) : ℕ := (onLineStripZeros f T).ncard
/-
The on-line zeros are always a subset of all strip zeros.
-/
theorem onLineStripZeros_subset (f : ℂ → ℂ) (T : ℝ) :
    onLineStripZeros f T ⊆ stripZeros f T := by
      exact fun x hx => hx.1
/-
**Critical-line property ⟹ equality of zero-sets.**  If every strip zero of `f` lies on
the critical line, then the two zero-sets coincide.
-/
theorem stripZeros_eq_of_critical_line (f : ℂ → ℂ) (T : ℝ)
    (h : ∀ s : ℂ, f s = 0 → 0 ≤ s.re → s.re ≤ 1 → s.re = 1 / 2) :
    onLineStripZeros f T = stripZeros f T := by
      exact Set.ext fun x => ⟨ fun hx => hx.1, fun hx => ⟨ hx, h x hx.1 hx.2.2.2.1 hx.2.2.2.2 ⟩ ⟩
/-
**`N₀(T) = N(T)` under the critical-line property.**  This is the precise unconditional
content of `N₀ = N`: it is equivalent to all strip zeros lying on the critical line.
-/
theorem N₀_eq_N_of_critical_line (f : ℂ → ℂ) (T : ℝ)
    (h : ∀ s : ℂ, f s = 0 → 0 ≤ s.re → s.re ≤ 1 → s.re = 1 / 2) :
    N₀ f T = N f T := by
      unfold CriticalLinePhasor.ZeroCounting.N₀ CriticalLinePhasor.ZeroCounting.N;
      rw [ stripZeros_eq_of_critical_line f T h ]
/-
`N₀(T) ≤ N(T)` whenever the strip zeros form a finite set.
-/
theorem N₀_le_N (f : ℂ → ℂ) (T : ℝ) (hfin : (stripZeros f T).Finite) :
    N₀ f T ≤ N f T := by
      exact Set.ncard_le_ncard ( onLineStripZeros_subset f T ) hfin
/-
**Hardy-type real angle function on the critical line.**  On the line `s = 1/2 + i y`
the symmetric phasor closed form is the *real* function
`2 · c^(-1/2) · cos(y · log c)`: modulus `c^(-1/2)`, winding phase `Θ(y) = y · log c`.
-/
theorem symPair_on_line_eq (c : ℝ) (hc : 1 < c) (y : ℝ) :
    symPair c ((1 / 2 : ℂ) + (y : ℂ) * I)
      = ((2 * c ^ (-(1 / 2 : ℝ)) * Real.cos (y * Real.log c) : ℝ) : ℂ) := by
        unfold CriticalLinePhasor.NoOffLineZeros.symPair;
        norm_num [ Complex.cpow_def_of_ne_zero, show c ≠ 0 by positivity ] ; ring;
        norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im, Real.rpow_def_of_pos ( zero_lt_one.trans hc ) ] ; ring;
        norm_num [ Complex.cos, Complex.exp_re, Complex.exp_im, Complex.arg_ofReal_of_nonneg ( by positivity : 0 ≤ c ) ] ; ring
/-
**Winding/argument-principle zero condition.**  On the critical line the model vanishes
exactly when the winding phase `Θ(y) = y · log c` crosses an odd multiple of `π/2`,
equivalently `2 · y · log c = (2k+1)·π`.  Each half-turn of `Θ` yields one zero.
-/
theorem symPair_on_line_zero_iff (c : ℝ) (hc : 1 < c) (y : ℝ) :
    symPair c ((1 / 2 : ℂ) + (y : ℂ) * I) = 0
      ↔ ∃ k : ℤ, 2 * y * Real.log c = (2 * k + 1) * Real.pi := by
        rw [ CriticalLinePhasor.ZeroCounting.symPair_on_line_eq c hc y ];
        norm_cast; norm_num [ Complex.cos, Complex.exp_re, Complex.exp_im ] ;
        rw [ Real.cos_eq_zero_iff ] ; exact or_iff_right ( by positivity ) |> Iff.trans <| by constructor <;> rintro ⟨ k, hk ⟩ <;> use k <;> linarith;
/-
**`N₀(T) = N(T)` for the model, unconditionally.**  The symmetric phasor closed form
`P_c` satisfies the critical-line property (`symPair_zero_re_eq_half`), so its winding count
of on-line zeros equals its total strip-zero count for every height `T`.
-/
theorem symPair_N₀_eq_N (c : ℝ) (hc : 1 < c) (T : ℝ) :
    N₀ (symPair c) T = N (symPair c) T := by
      apply N₀_eq_N_of_critical_line;
      exact fun s hs _ _ => CriticalLinePhasor.NoOffLineZeros.symPair_zero_re_eq_half c hc s hs
/-
The model's zero count is non-vacuous: for `T` at least the first zero ordinate
`π/(2 log c)` the strip contains a zero.
-/
theorem symPair_stripZeros_nonempty (c : ℝ) (hc : 1 < c) (T : ℝ)
    (hT : Real.pi / (2 * Real.log c) ≤ T) :
    (stripZeros (symPair c) T).Nonempty := by
      refine' ⟨ 1 / 2 + ( Real.pi / ( 2 * Real.log c ) ) * Complex.I, _, _, _, _, _ ⟩ <;> norm_num [ Complex.ext_iff ];
      · convert CriticalLinePhasor.NoOffLineZeros.symPair_vanishes_at_midpoint c hc using 1;
        norm_num [ Complex.ext_iff ];
      · norm_cast ; exact div_pos Real.pi_pos ( mul_pos zero_lt_two ( Real.log_pos hc ) );
      · norm_cast;
      · norm_num [ div_eq_mul_inv ];
      · norm_cast ; norm_num
/-- A continuous real argument-lift `Θ` of a path `g`:  `g t = ‖g t‖ · exp(i·Θ t)`.
The phase `Θ` is the accumulated winding angle. -/
def IsArgLift (g : ℝ → ℂ) (Θ : ℝ → ℝ) : Prop :=
  Continuous Θ ∧ ∀ t : ℝ, g t = (‖g t‖ : ℂ) * Complex.exp ((Θ t : ℂ) * I)
/-- The **winding number** of a path over `[a, b]` read off from its argument-lift `Θ`:
the net change of angle measured in turns. -/
noncomputable def windingCount (Θ : ℝ → ℝ) (a b : ℝ) : ℝ := (Θ b - Θ a) / (2 * Real.pi)
/-
**Winding number is an integer on loops.**  If `g` is a loop (`g a = g b`) that does not
pass through the origin and `Θ` is an argument-lift of `g`, then the winding number
`windingCount Θ a b` is an integer — the defining property of a genuine winding number, and
the integer the argument principle equates with a zero count.
-/
theorem windingCount_int_of_loop (g : ℝ → ℂ) (Θ : ℝ → ℝ) (h : IsArgLift g Θ)
    (a b : ℝ) (hloop : g a = g b) (hne : g a ≠ 0) :
    ∃ k : ℤ, windingCount Θ a b = (k : ℝ) := by
      unfold CriticalLinePhasor.ZeroCounting.windingCount;
      have h_exp : Complex.exp ((Θ b : ℂ) * Complex.I) = Complex.exp ((Θ a : ℂ) * Complex.I) := by
        obtain ⟨ h₁, h₂ ⟩ := h;
        grind;
      rw [ Complex.exp_eq_exp_iff_exists_int ] at h_exp ; obtain ⟨ k, hk ⟩ := h_exp ; exact ⟨ k, by rw [ div_eq_iff ( by positivity ) ] ; norm_num [ Complex.ext_iff ] at * ; linarith ⟩
end CriticalLinePhasor.ZeroCounting
/-!
## Carrier / fiber decomposition and the mediated midpoint claim
The model splits into two layers:
* **The carrier** — the no-drift unitary transport.  Its generator is the *real* operator
  `H(n) = log n` (Hermitian, `genMatrix_isHermitian`), its flow `U(t,n) = exp(i t log n)` is
  *unitary* (`evolMatrix_mem_unitaryGroup`), and the area law `R_n² = C·n` feeds the scale
  into each Dirichlet term as `(C·n)^(-s) = C^(-s) · n^(-s)` (`carrier_scale_factorization`).
  The carrier preserves radial placement and carries phase **without injecting drift**: the
  scale factor `C^(-s)` is never zero (`carrier_scale_ne_zero`) and on the critical line its
  modulus `C^(-1/2)` is independent of the ordinate `y` (`carrier_norm_no_drift`).
* **The harmonic fiber** — the channel-dependent payload `F_χ^C(s) = Σ χ(n)(C n)^(-s)
  = C^(-s) L(s, χ)` riding on the carrier.  Its job is to vanish.
Accordingly the midpoint claim is **mediated**, not direct.  Rather than "the zero is on the
carrier", the proof says: the fiber vanishes while transported by the carrier, and because
the carrier is no-drift/unitary, the projection of that vanishing event cannot acquire any
radial information that would move the readout off the midpoint.  Concretely, for the
exactly-soluble fiber `symPair`, the carrier-scaled observable
`F_C(s) = C^(-s) · P_c(s)` (the model instance of `F_χ^C`) vanishes **iff** the fiber `P_c`
vanishes (the carrier factor is nonzero), so:
```
fiber vanishes on carrier  ⟹  carrier no-drift ⟹  Re ρ = 1/2.
```
This is `scaledSymPair_zero_re_eq_half`, and the carrier scaling leaves the winding count
unchanged: `scaledSymPair_N₀_eq_N`.
-/
namespace CriticalLinePhasor.CarrierFiber
open Complex CriticalLinePhasor.NoOffLineZeros CriticalLinePhasor.ZeroCounting
/-
**Area-law per-term factorization.**  The carrier scale `R_n² = C·n` enters each
Dirichlet term multiplicatively: `(C·n)^(-s) = C^(-s) · n^(-s)`.  Multiplication of scales
becomes addition of phases ("multiplication becomes addition on the helix").
-/
theorem carrier_scale_factorization (C n : ℝ) (hC : 0 < C) (hn : 0 < n) (s : ℂ) :
    ((C * n : ℝ) : ℂ) ^ (-s) = (C : ℂ) ^ (-s) * (n : ℂ) ^ (-s) := by
      convert Complex.mul_cpow_ofReal_nonneg hC.le hn.le ( -s ) using 1 ; push_cast ; ring_nf
/-
**No-drift: the carrier scale is never zero.**  The transport factor `C^(-s)` cannot
vanish, so it can neither create nor destroy zeros of the fiber.
-/
theorem carrier_scale_ne_zero (C : ℝ) (hC : 0 < C) (s : ℂ) :
    (C : ℂ) ^ (-s) ≠ 0 := by
      simp_all +decide [ Complex.ofReal_cpow, hC.le, Complex.cpow_def ];
      split_ifs <;> simp_all +decide [ Complex.exp_ne_zero ]
/-
**No-drift on the critical line.**  On `s = 1/2 + i y` the carrier factor has modulus
`C^(-1/2)`, independent of the ordinate `y`: the carrier carries phase without radial drift.
-/
theorem carrier_norm_no_drift (C : ℝ) (hC : 0 < C) (y : ℝ) :
    ‖(C : ℂ) ^ (-((1 / 2 : ℂ) + (y : ℂ) * I))‖ = (C ^ (-(1 / 2 : ℝ)) : ℝ) := by
      rw [ Complex.norm_cpow_eq_rpow_re_of_pos ] <;> norm_num [ hC ]
/-- The **carrier-scaled fiber** `F_C(s) = C^(-s) · P_c(s)`, the model instance of the
harmonic fiber `F_χ^C = C^(-s) L(s, χ)` transported by the carrier. -/
noncomputable def scaledSymPair (C c : ℝ) (s : ℂ) : ℂ := (C : ℂ) ^ (-s) * symPair c s
/-
**Mediated midpoint claim.**  Every zero of the carrier-scaled fiber lies on the critical
line.  The carrier factor `C^(-s)` is nonzero (no drift), so a vanishing of `F_C` is exactly
a vanishing of the fiber `P_c`, which forces `Re s = 1/2` by phasor balance. This is the
mediated chain: fiber-vanishing-on-carrier ⟹ no-drift ⟹ midpoint.
-/
theorem scaledSymPair_zero_re_eq_half (C c : ℝ) (hC : 0 < C) (hc : 1 < c) (s : ℂ)
    (h : scaledSymPair C c s = 0) : s.re = 1 / 2 := by
      convert CriticalLinePhasor.NoOffLineZeros.symPair_zero_re_eq_half c hc s _;
      exact eq_zero_of_ne_zero_of_mul_left_eq_zero ( CriticalLinePhasor.CarrierFiber.carrier_scale_ne_zero C hC s ) h
/-
**Carrier scaling preserves the winding count.**  Since the carrier injects no drift,
the scaled fiber satisfies the same `N₀(T) = N(T)` as the bare fiber.
-/
theorem scaledSymPair_N₀_eq_N (C c : ℝ) (hC : 0 < C) (hc : 1 < c) (T : ℝ) :
    N₀ (scaledSymPair C c) T = N (scaledSymPair C c) T := by
      apply CriticalLinePhasor.ZeroCounting.N₀_eq_N_of_critical_line;
      exact fun s hs _ _ => CriticalLinePhasor.CarrierFiber.scaledSymPair_zero_re_eq_half C c hC hc s hs
end CriticalLinePhasor.CarrierFiber
/-!
## `ζ`/`L` and `symPair`: the same object in two representations
What is the precise, *true* sense in which the `ζ`/`L` object and the phasor closed form
`symPair` are "the same thing, just in different representations"?
**Honest scope.**  They are emphatically **not** the same analytic function: the Riemann
`ζ`/Dirichlet `L` functions have infinitely many, irregularly spaced nontrivial zeros, while
`symPair c` has equally spaced zeros (`symPair_on_line_zero_iff`).  `symPair` is the
exactly-soluble two-term *model* of the cancellation mechanism, not `L` itself.  So the
"sameness" cannot be literal function equality; it is **structural** and **representational**:
1. **Same structural identity (functional equation).**  The fingerprint of an `L`-function is
   its reflection symmetry across the critical line `s ↦ 1-s`.  The completed Riemann zeta
   satisfies `completedRiemannZeta (1-s) = completedRiemannZeta s` (Mathlib), and `symPair`
   satisfies the *identical* identity `symPair c (1-s) = symPair c s`.  This is proved,
   side by side, in `zeta_and_symPair_share_functional_equation`.  In this exact sense the two
   objects are the same kind of object: reflection-symmetric about the midpoint.
2. **Same data, 1D ⇄ 3D representations.**  The "1D representation" is the complex phasor
   value; the "3D representation" is the helix point.  These are related by an explicit
   bijection `ℂ × ℝ ≃ ℝ³`: the planar part of the helix point *is* the phasor and the third
   coordinate is the height (`helixToPhasor_phasorToHelix`, `phasorToHelix_helixToPhasor`),
   and it is norm-preserving on the plane (`helixToPhasor_norm`).  Concretely the helix point
   `γ(y)` projects to exactly the geometric phasor `R(y)·exp(i·2π e^y/p)`
   (`helixToPhasor_gammaY`): radius = magnitude, winding = phase.  The 3D helix is just the
   height-lifted picture of the 1D phasor — the same data in two representations.
Together: the phasor model and the `ζ`/`L` object share the defining functional-equation
symmetry, and the helix (3D) and phasor (1D) are interchangeable representations of one and
the same phasor datum.
-/
namespace CriticalLinePhasor.Representation
open Complex CriticalLinePhasor.NoOffLineZeros CriticalLinePhasor.Geometry
/-
**Shared functional-equation symmetry.**  `symPair` is reflection-symmetric about the
critical line, exactly like the completed `L`-function: `P_c(1-s) = P_c(s)`.
-/
theorem symPair_functional_symmetry (c : ℝ) (s : ℂ) :
    symPair c (1 - s) = symPair c s := by
      unfold CriticalLinePhasor.NoOffLineZeros.symPair; norm_num; ring;
/-
**`ζ` and `symPair` satisfy the same functional equation.**  Side by side: the completed
Riemann zeta and the phasor closed form obey the *identical* reflection identity `s ↦ 1-s`.
This is the precise machine-checked sense in which they are the same structural object.
-/
theorem zeta_and_symPair_share_functional_equation (c : ℝ) (s : ℂ) :
    completedRiemannZeta (1 - s) = completedRiemannZeta s ∧ symPair c (1 - s) = symPair c s := by
  exact ⟨ completedRiemannZeta_one_sub s, CriticalLinePhasor.Representation.symPair_functional_symmetry c s ⟩
/-- **1D → 3D.**  Lift a planar phasor `z : ℂ` to the helix at height `h`. -/
def phasorToHelix (z : ℂ) (h : ℝ) : ℝ × ℝ × ℝ := (z.re, z.im, h)
/-- **3D → 1D.**  Project a helix point to its planar phasor (the first two coordinates as a
complex number), discarding the height. -/
def helixToPhasor (v : ℝ × ℝ × ℝ) : ℂ := ⟨v.1, v.2.1⟩
/-
Round-trip 1D → 3D → 1D recovers the phasor.
-/
theorem helixToPhasor_phasorToHelix (z : ℂ) (h : ℝ) :
    helixToPhasor (phasorToHelix z h) = z := by
      exact Complex.ext rfl rfl
/-
Round-trip 3D → 1D → 3D recovers the helix point (the height is carried by the third
coordinate).
-/
theorem phasorToHelix_helixToPhasor (v : ℝ × ℝ × ℝ) :
    phasorToHelix (helixToPhasor v) v.2.2 = v := by
      exact Prod.ext rfl ( Prod.ext rfl rfl )
/-
The 1D ⇄ 3D correspondence is norm-preserving on the plane: the modulus of the phasor is
the cylindrical (planar) radius of the helix point.
-/
theorem helixToPhasor_norm (v : ℝ × ℝ × ℝ) :
    ‖helixToPhasor v‖ = Real.sqrt (v.1 ^ 2 + v.2.1 ^ 2) := by
      unfold CriticalLinePhasor.Representation.helixToPhasor; rw [ Complex.norm_def ] ; norm_num [ Complex.normSq ] ; ring;
/-
**The helix point is the phasor, lifted.**  The planar projection of the boxed helix
point `γ(y)` is exactly the geometric phasor `R(y)·exp(i·2π e^y/p)`: its modulus is the
radius `R(y)` and its phase is the winding angle `2π e^y / p`.  The 3D and 1D pictures carry
the same datum.
-/
theorem helixToPhasor_gammaY (p r y : ℝ) :
    helixToPhasor (gammaY p r y)
      = (radius p r y : ℂ) * Complex.exp (((2 * Real.pi * Real.exp y / p : ℝ)) * I) := by
        unfold CriticalLinePhasor.Geometry.gammaY CriticalLinePhasor.Geometry.radius; norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ] ; ring;
        unfold CriticalLinePhasor.Representation.helixToPhasor; unfold CriticalLinePhasor.Geometry.helix; unfold CriticalLinePhasor.Geometry.kClimb; norm_num [ Complex.exp_re, Complex.exp_im ] ; ring;
        norm_num
end CriticalLinePhasor.Representation
/-!
## Projection faithfulness: bijection, loss ledger, and unique reconstruction
This section makes precise the "projection faithfulness" argument with an explicit
**bijection** (`Equiv`), a **loss ledger**, and **unique reconstruction**.
**Representation faithfulness (1D ⇄ 3D).**  The projection `helixToPhasor : ℝ³ → ℂ` discards
the height.  That lost coordinate is *ledgered* and the projection is *faithful*: the pairing
`ℂ × ℝ ≃ ℝ³` (`reprEquiv`) is a genuine bijection whose inverse reconstructs the 3D point
**uniquely** from the 1D phasor together with the ledgered height
(`reprEquiv`, `phasorToHelix_helixToPhasor`).  So the 3D helix and the 1D phasor are literally
the same object presented in two representations — no information is lost, only ledgered.
**Shared zero-symmetry with Mathlib's actual `riemannZeta`.**  We use Mathlib's *actual*
`riemannZeta` and its set of nontrivial zeros `zetaNontrivialZeros`.  The reflection
`s ↦ 1-s` is an **involutive bijection** of that set (`zetaReflectionEquiv`), proved
**unconditionally** from Mathlib's functional equation `riemannZeta_one_sub` (a zero is
preserved because the reflected value is a *multiple* of `riemannZeta s = 0`).  The *identical*
involution is a bijection of the phasor model's zeros (`symPairReflectionEquiv`).  Thus the
actual zeta zeros and the model's zeros carry one and the same reflection-symmetry structure.
**Honest scope.**  This is a faithful identification of *representations* (1D ⇄ 3D, an
isomorphism) and a genuine *shared symmetry structure* of the two zero sets — it is **not** a
claim that `symPair` equals `riemannZeta`/`L` as functions, nor that their zero sets are equal
(they are not: `symPair`'s zeros are equally spaced).  What is unconditionally true and proved
is exactly the bijections above and the reconstruction identities.
-/
namespace CriticalLinePhasor.Faithful
open Complex CriticalLinePhasor.NoOffLineZeros CriticalLinePhasor.Representation
/-
Reflection across the critical line is an involution: `1 - (1 - a) = a`.
-/
theorem one_sub_one_sub (a : ℂ) : 1 - (1 - a) = a := by
  ring
/-
**Faithful 1D → 3D leg.**  Reconstructing the phasor and the ledgered height from the
3D → 1D projection returns the original input.
-/
theorem reprEquiv_left_inv (zh : ℂ × ℝ) :
    (helixToPhasor (phasorToHelix zh.1 zh.2), (phasorToHelix zh.1 zh.2).2.2) = zh := by
      unfold CriticalLinePhasor.Representation.helixToPhasor CriticalLinePhasor.Representation.phasorToHelix; aesop;
/-- **The faithful representation bijection** `ℂ × ℝ ≃ ℝ³`.  The 1D phasor plus the ledgered
height is the same datum as the 3D helix point; the inverse is unique reconstruction. -/
def reprEquiv : ℂ × ℝ ≃ (ℝ × ℝ × ℝ) where
  toFun zh := phasorToHelix zh.1 zh.2
  invFun v := (helixToPhasor v, v.2.2)
  left_inv zh := reprEquiv_left_inv zh
  right_inv v := phasorToHelix_helixToPhasor v
/-- The set of nontrivial zeros of Mathlib's *actual* Riemann zeta function (critical strip
`0 < Re s < 1`). -/
def zetaNontrivialZeros : Set ℂ := {s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1}
/-- The zero set of the phasor model `symPair c`. -/
def symPairZeros (c : ℝ) : Set ℂ := {s : ℂ | symPair c s = 0}
/-
**Reflection preserves Mathlib's actual zeta nontrivial zeros (unconditional).**  If `s`
is a nontrivial zero of `riemannZeta`, so is `1 - s`.  The functional equation
`riemannZeta_one_sub` writes `riemannZeta (1-s)` as a multiple of `riemannZeta s = 0`.
-/
theorem reflection_mem_zetaNontrivialZeros (s : ℂ) (hs : s ∈ zetaNontrivialZeros) :
    (1 - s) ∈ zetaNontrivialZeros := by
      refine' ⟨ _, _, _ ⟩;
      · convert riemannZeta_one_sub ( show ∀ n : ℕ, s ≠ -↑n from ?_ ) ( show s ≠ 1 from ?_ ) using 1;
        · rw [ hs.1, MulZeroClass.mul_zero ];
        · intro n hn; have := hs.2.1; simp_all +decide [ Complex.ext_iff ] ;
          linarith;
        · exact fun h => by have := hs.2.2; norm_num [ h ] at this;
      · norm_num +zetaDelta at *;
        exact hs.2.2;
      · simpa using hs.2.1
/-
**Reflection preserves the model's zeros.**  Follows from the shared functional-equation
symmetry `symPair c (1-s) = symPair c s`.
-/
theorem reflection_mem_symPairZeros (c : ℝ) (s : ℂ) (hs : s ∈ symPairZeros c) :
    (1 - s) ∈ symPairZeros c := by
      exact Eq.trans ( CriticalLinePhasor.Representation.symPair_functional_symmetry c s ) hs
/-- **Reflection involution bijection on Mathlib's actual zeta nontrivial zeros.**  The map
`s ↦ 1-s` is a bijection (involution) of `zetaNontrivialZeros`, unconditionally. -/
def zetaReflectionEquiv : zetaNontrivialZeros ≃ zetaNontrivialZeros where
  toFun s := ⟨1 - s.1, reflection_mem_zetaNontrivialZeros s.1 s.2⟩
  invFun s := ⟨1 - s.1, reflection_mem_zetaNontrivialZeros s.1 s.2⟩
  left_inv s := Subtype.ext (one_sub_one_sub s.1)
  right_inv s := Subtype.ext (one_sub_one_sub s.1)
/-- **The identical reflection involution bijection on the model's zeros.**  The same
`s ↦ 1-s` is a bijection of `symPairZeros c`. -/
def symPairReflectionEquiv (c : ℝ) : symPairZeros c ≃ symPairZeros c where
  toFun s := ⟨1 - s.1, reflection_mem_symPairZeros c s.1 s.2⟩
  invFun s := ⟨1 - s.1, reflection_mem_symPairZeros c s.1 s.2⟩
  left_inv s := Subtype.ext (one_sub_one_sub s.1)
  right_inv s := Subtype.ext (one_sub_one_sub s.1)
/-- The **helix-lifted** copy of Mathlib's actual zeta nontrivial zeros: each zero `s` is
placed on the helix as the 3D point `phasorToHelix s (Im s)` (planar part `s`, ledgered
height `Im s`). -/
def zetaZerosHelix : Set (ℝ × ℝ × ℝ) :=
  (fun s : ℂ => phasorToHelix s s.im) '' zetaNontrivialZeros
/-
**The helix zeros project to `ζ`.**  The projection `helixToPhasor` restricts to a
*bijection* from the helix-lifted zeros `zetaZerosHelix` onto Mathlib's *actual* `riemannZeta`
nontrivial zeros `zetaNontrivialZeros` — unconditionally.  This is the projection-faithfulness
statement with codomain the genuine zeta zeros: every helix zero projects to a zeta zero, the
projection is injective on the helix zeros, and every zeta zero is hit.
-/
theorem helix_projects_to_zeta :
    Set.BijOn helixToPhasor zetaZerosHelix zetaNontrivialZeros := by
      refine' ⟨ _, _, _ ⟩;
      · intro;
        rintro ⟨ s, hs, rfl ⟩ ; exact hs;
      · -- Injectivity follows directly from the definition of `helixToPhasor`.
        intro v hv w hw h_eq
        obtain ⟨s, hs, rfl⟩ := hv
        obtain ⟨t, ht, rfl⟩ := hw
        simp [helixToPhasor] at h_eq
        aesop;
      · exact fun s hs => ⟨ _, ⟨ s, hs, rfl ⟩, by simp +decide [ phasorToHelix, helixToPhasor ] ⟩
/-
**`ζ` zeros lift up to the helix.**  Conversely, lifting `s ↦ phasorToHelix s (Im s)` is a
*bijection* from Mathlib's actual `riemannZeta` nontrivial zeros onto their helix copy
`zetaZerosHelix` — the inverse of `helix_projects_to_zeta`.  So the up (lift) and down
(projection) trips are mutually inverse bijections: zeta zeros and their helix copies are the
same data.
-/
theorem zeta_lifts_to_helix :
    Set.BijOn (fun s : ℂ => phasorToHelix s s.im) zetaNontrivialZeros zetaZerosHelix := by
      refine' ⟨ fun s hs => _, fun s hs => _, fun s hs => _ ⟩;
      · exact Set.mem_image_of_mem _ hs;
      · simp +decide [ Complex.ext_iff, CriticalLinePhasor.Representation.phasorToHelix ];
      · obtain ⟨ s, hs, rfl ⟩ := hs; exact ⟨ s, hs, rfl ⟩ ;
/-- The **critical-line axis** in the 3D helix picture: lifted points whose planar real part
is `1/2`.  On-line zeros lift exactly to this axis. -/
def criticalAxis : Set (ℝ × ℝ × ℝ) := {v : ℝ × ℝ × ℝ | v.1 = 1 / 2}
/-
**An off-line 1D zero lifts off the axis and forces an off-axis pair.**  If `s` is a
nontrivial `riemannZeta` zero with `Re s ≠ 1/2`, then its helix lift lies *off* the
critical-line axis (`criticalAxis`), and the reflection `1 - s` is a *distinct* nontrivial
zero, also off the line, on the opposite side of the axis (the two real parts sum to `1`, i.e.
are mirror images about `1/2`).  So an off-line zero can never sit solitarily on the axis: it
projects to a genuine off-axis pair straddling the midpoint.
-/
theorem offline_zero_projects_off_axis (s : ℂ) (hs : s ∈ zetaNontrivialZeros)
    (hoff : s.re ≠ 1 / 2) :
    phasorToHelix s s.im ∉ criticalAxis ∧ (1 - s) ∈ zetaNontrivialZeros ∧
      (1 - s).re ≠ 1 / 2 ∧ (1 - s) ≠ s ∧ s.re + (1 - s).re = 1 := by
        refine' ⟨ _, _, _, _, _ ⟩;
        · exact fun h => hoff <| h.symm ▸ rfl;
        · grind +suggestions;
        · contrapose! hoff; norm_num at *; linarith;
        · exact fun h => hoff <| by norm_num [ Complex.ext_iff ] at *; linarith;
        · norm_num
end CriticalLinePhasor.Faithful
/-!
## Unconditional Riemann-Hypothesis equivalences (valid, non-circular proof targets)
The point of this section is methodological as much as mathematical.  "This statement is
*equivalent to* the Riemann Hypothesis" is **not** a reason to abandon a proof attempt.  An
equivalence `X ↔ RiemannHypothesis` is itself a fully **unconditional** theorem: it neither
assumes RH nor is circular.  Proving such equivalences is a legitimate goal — it turns RH into
a concrete, transferable target rather than a conversation-ending label.  What is *not*
acceptable is a proof of `X` that secretly assumes RH (or is circular); those are discarded.
"Equivalent to RH" alone is not grounds to discard.
Here we prove, against Mathlib's **actual** `RiemannHypothesis` and `riemannZeta`:
* `zeta_nontrivial_zeros_in_strip` — every nontrivial zero of `ζ` lies in the open critical
  strip `0 < Re s < 1` (fully unconditional, this is *not* RH);
* `riemannHypothesis_iff_zeros_on_line` — `RiemannHypothesis ↔` every nontrivial-strip zero
  has `Re = 1/2` (matching `CriticalLinePhasor.Faithful.zetaNontrivialZeros`);
* `riemannHypothesis_iff_no_offaxis_zero` — `RiemannHypothesis ↔` there is no off-axis zero,
  i.e. the off-axis reflected pair of `offline_zero_projects_off_axis` never occurs;
* `N₀_eq_N_iff_upper_strip_on_line` — the precise unconditional content of `N₀ = N`: the
  on-line strip-zero set equals the full strip-zero set for `ζ` at every height **iff** every
  upper-strip zero lies on the critical line; and `riemannHypothesis_imp_N₀_eq_N` — RH forces
  `N₀ = N` at every height (the `N₀ = N` framing).  The converse of the latter is *not* a
  theorem: `N₀ = N` only constrains zeros with `Im > 0`, so it cannot rule out a hypothetical
  off-line *real* zero in `(0,1)`, which RH also forbids.  This is documented honestly rather
  than overclaimed.
The *hard* direction of each equivalence is exactly the open content of RH.  That is the whole
point: these are RH-strength but non-circular targets, stated honestly and proved as far as the
equivalences themselves (which is unconditional) without smuggling in RH.
-/
namespace CriticalLinePhasor.RHEquivalences
open Complex CriticalLinePhasor.Faithful CriticalLinePhasor.ZeroCounting
/-
**Bernoulli numbers at even positive indices are nonzero.**  Because `ζ(2m) ≠ 0` (it lies
in the zero-free region `Re ≥ 1`) and `ζ(2m)` is a nonzero rational multiple of
`bernoulli (2m)` (`riemannZeta_two_mul_nat`).
-/
theorem bernoulli_even_ne_zero (m : ℕ) (hm : m ≠ 0) : bernoulli (2 * m) ≠ 0 := by
  have h_nonzero : riemannZeta (2 * (m : ℂ)) ≠ 0 := by
    exact riemannZeta_ne_zero_of_one_le_re ( by norm_num; linarith [ show ( m : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr ( Nat.pos_of_ne_zero hm ) ] );
  have := @riemannZeta_two_mul_nat m ‹_›; simp_all +decide [ Nat.factorial_ne_zero, Complex.exp_ne_zero ] ;
/-
**Nontrivial zeros have real part `< 1`** (zero-free region `Re ≥ 1`).
-/
theorem zeta_zero_re_lt_one {s : ℂ} (h0 : riemannZeta s = 0) : s.re < 1 := by
  exact lt_of_not_ge fun h => riemannZeta_ne_zero_of_one_le_re h h0
/-
**Nontrivial zeros have real part `> 0`.**  If `Re s ≤ 0` and `s` is not a non-positive
integer, the functional equation `riemannZeta_one_sub` forces `ζ(1-s) = 0` with `Re(1-s) ≥ 1`,
impossible.  If `s = -k` is a non-positive integer, `riemannZeta_neg_nat_eq_bernoulli` shows
`ζ(-k) = 0` forces `bernoulli (k+1) = 0`, i.e. `k+1` odd `> 1` (using `bernoulli_even_ne_zero`
and `riemannZeta_zero` for `k = 0`), hence `s = -2j` is a trivial zero.
-/
theorem zeta_nontrivial_zero_re_pos {s : ℂ} (h0 : riemannZeta s = 0)
    (htriv : ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) (h1 : s ≠ 1) : 0 < s.re := by
  by_cases h : ∃ k : ℕ, s = -k;
  · obtain ⟨ k, rfl ⟩ := h;
    rcases Nat.even_or_odd' k with ⟨ c, rfl | rfl ⟩ <;> norm_num at *;
    · rcases c with ( _ | c ) <;> norm_num at *;
      exact absurd h0 ( by rw [ riemannZeta_zero ] ; norm_num );
    · have := @riemannZeta_neg_nat_eq_bernoulli ( 1 + 2 * c ) ; simp_all +decide [ Nat.add_comm 1, Nat.mul_succ ];
      rw [ eq_comm ] at this ; norm_cast at this ; simp_all +decide [ Nat.even_add_one ];
      exact absurd ( this.resolve_right ( by linarith ) ) ( bernoulli_even_ne_zero _ ( Nat.succ_ne_zero _ ) );
  · -- Since $s$ is not a non-positive integer, we can apply the functional equation to get $\zeta(1-s) = 0$.
    have hzeta1s : riemannZeta (1 - s) = 0 := by
      grind +suggestions;
    exact not_le.mp fun hle => absurd ( zeta_zero_re_lt_one hzeta1s ) ( by norm_num; linarith )
/-- **Nontrivial zeros lie in the open critical strip `0 < Re s < 1`** (unconditional). -/
theorem zeta_nontrivial_zeros_in_strip {s : ℂ} (h0 : riemannZeta s = 0)
    (htriv : ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) (h1 : s ≠ 1) :
    s ∈ zetaNontrivialZeros :=
  ⟨h0, zeta_nontrivial_zero_re_pos h0 htriv h1, zeta_zero_re_lt_one h0⟩
/-
**RH ⟺ every nontrivial-strip zero lies on the critical line.**  Unconditional
equivalence with Mathlib's actual `RiemannHypothesis`; the hard direction is the open content
of RH.
-/
theorem riemannHypothesis_iff_zeros_on_line :
    RiemannHypothesis ↔ ∀ s ∈ zetaNontrivialZeros, s.re = 1 / 2 := by
  constructor <;> intro h;
  · intro s hs; exact h s hs.1 (by
    rintro ⟨ n, rfl ⟩ ; norm_num [ Complex.ext_iff ] at hs;
    exact absurd hs.2.1 ( by norm_num [ Complex.ext_iff ] ; linarith )) (by
    exact fun h => by have := hs.2.2; norm_num [ h ] at this;);
  · intro s hs htriv h1
    have hs' : s ∈ zetaNontrivialZeros := by
      apply zeta_nontrivial_zeros_in_strip hs htriv h1
    exact h s hs'
/-- **RH ⟺ there is no off-axis nontrivial zero.**  Equivalently, the off-axis reflected pair
of `offline_zero_projects_off_axis` never occurs. -/
theorem riemannHypothesis_iff_no_offaxis_zero :
    RiemannHypothesis ↔ ¬ ∃ s ∈ zetaNontrivialZeros, s.re ≠ 1 / 2 := by
  rw [riemannHypothesis_iff_zeros_on_line]
  constructor
  · intro h ⟨s, hs, hne⟩; exact hne (h s hs)
  · intro h s hs; by_contra hne; exact h ⟨s, hs, hne⟩
/-
**The precise unconditional content of `N₀ = N`.**  The on-line strip-zero set equals the
full strip-zero set of `ζ` for every height `T` **iff** every zero in the (upper) closed strip
`0 ≤ Re s ≤ 1`, `Im s > 0`, lies on the critical line.  No RH is assumed; this is the exact
meaning of the counting identity `N₀(T) = N(T)`.
-/
theorem N₀_eq_N_iff_upper_strip_on_line :
    (∀ T : ℝ, onLineStripZeros riemannZeta T = stripZeros riemannZeta T) ↔
      ∀ s : ℂ, riemannZeta s = 0 → 0 < s.im → 0 ≤ s.re → s.re ≤ 1 → s.re = 1 / 2 := by
  constructor;
  · unfold CriticalLinePhasor.ZeroCounting.onLineStripZeros CriticalLinePhasor.ZeroCounting.stripZeros;
    intro h s hs hs' hs'' hs'''; specialize h s.im; rw [ Set.ext_iff ] at h; specialize h s; aesop;
  · intro h T;
    exact Set.ext fun x => ⟨ fun hx => hx.1, fun hx => ⟨ hx, h x hx.1 hx.2.1 hx.2.2.2.1 hx.2.2.2.2 ⟩ ⟩
/-
**RH forces `N₀ = N` at every height.**  Under the Riemann Hypothesis, the on-line
strip-zero set of `ζ` equals the full strip-zero set for all `T`.  (The converse fails as an
implication, since `N₀ = N` cannot see a hypothetical off-line real zero in `(0,1)`; see the
section docstring.)
-/
theorem riemannHypothesis_imp_N₀_eq_N (h : RiemannHypothesis) :
    ∀ T : ℝ, onLineStripZeros riemannZeta T = stripZeros riemannZeta T := by
  intro T; ext s; simp [CriticalLinePhasor.ZeroCounting.onLineStripZeros, CriticalLinePhasor.ZeroCounting.stripZeros]; (
  intro h₀ h₁ h₂ h₃ h₄; specialize h s; simp_all +decide [ Complex.ext_iff ] ;
  exact h ( fun n hn => by linarith ) ( fun hn => by linarith ));
end CriticalLinePhasor.RHEquivalences
/-!
## The helix + fiber as a geometric/coefficient realization of the GL(1) automorphic L-function
This section makes precise the claim "the helix plus fiber is a geometric/coefficient
realization of the automorphic representation's L-packet / readout."
**Honest scope.**  Mathlib does not have a general theory of automorphic representations or
their L-packets, and a literal identification of the heuristic helix with a `GL(n)` automorphic
form for `n ≥ 2` is not a well-defined mathematical statement.  What *is* well-defined — and is
exactly the level at which "automorphic representation" is formalizable here — is the **`GL(1)`
/ abelian case**: an automorphic representation of `GL(1)/ℚ` is a Hecke character, realized by a
Dirichlet character `χ`, its **L-packet is a singleton** `{χ}` (abelian groups have singleton
packets), and its standard L-function is the Dirichlet L-function
`L(s, χ) = Σ χ(n) n^{-s} = LSeries (fun n ↦ χ n) s` (Mathlib's `DirichletCharacter.LFunction`,
equal to the `LSeries` for `Re s > 1`).
In this `GL(1)` setting we prove that the **fiber** (the value-dependent coefficient `n^{-s}`)
and the **helix** (the faithful geometric encoding `ℂ ⇄ ℝ³`) together realize the L-function's
coefficient/readout:
* `LSeries_term_eq_char_mul_fiber` — the L-series coefficient (Mathlib's `LSeries.term`) factors
  as character × fiber: `χ(n) · n^{-s}`;
* `carrier_fiber_factorization` — the carrier/fiber split `(C·n)^{-s} = C^{-s} · n^{-s}`
  (re-export of `CarrierFiber.carrier_scale_factorization` in L-function language);
* `LSeries_term_on_critical_line` — on `s = 1/2 + i y` the coefficient equals
  `χ(n) · phasor`, the magnitude-`n^{-1/2}` spin phasor of `OperatorReadout`;
* `LSeries_term_realized_on_helix` — the coefficient, as a complex phasor, is faithfully carried
  by the helix: projecting its helix lift recovers it exactly (the geometric realization);
* `LFunction_partialSum_eq_readout` — the finite L-function partial sum equals the operator
  `readout ∘ (unitary spin evolution)` cancellation observable of `OperatorReadout`, i.e. the
  helix/operator "readout" reproduces the truncated automorphic L-function;
* `LFunction_eq_readout_limit_term` — at the analytic level (`Re s > 1`) the `GL(1)` L-function
  `DirichletCharacter.LFunction χ` is the sum of exactly these character×fiber coefficients.
-/
namespace CriticalLinePhasor.AutomorphicRealization
open Complex CriticalLinePhasor.OperatorReadout CriticalLinePhasor.Representation
/-- **Coefficient = character × fiber.**  The `GL(1)` L-function coefficient (`LSeries.term`)
attached to the Dirichlet character `χ` factors as the character value times the fiber
`n^{-s}`. -/
theorem LSeries_term_eq_char_mul_fiber {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (s : ℂ) (n : ℕ) (hn : n ≠ 0) :
    LSeries.term (fun k => χ k) s n = (χ n) * (n : ℂ) ^ (-s) := by
  rw [LSeries.term_def, if_neg hn, Complex.cpow_neg]
  ring
/-- **Carrier/fiber factorization in L-function language.**  Rescaling the integer index by the
carrier scale `C` splits the fiber multiplicatively: `(C·n)^{-s} = C^{-s} · n^{-s}`. -/
theorem carrier_fiber_factorization (C : ℝ) (n : ℝ) (hC : 0 < C) (hn : 0 < n) (s : ℂ) :
    ((C * n : ℝ) : ℂ) ^ (-s) = (C : ℂ) ^ (-s) * (n : ℂ) ^ (-s) :=
  CriticalLinePhasor.CarrierFiber.carrier_scale_factorization C n hC hn s
/-- **Coefficient on the critical line = character × spin phasor.**  On `s = 1/2 + i y` the
`GL(1)` coefficient is `χ(n) · A(n) · e^{-i y log n}` with `A(n) = n^{-1/2}` — the operator
`phasor` of `OperatorReadout`. -/
theorem LSeries_term_on_critical_line {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (y : ℝ) (n : ℕ) (hn : 0 < n) :
    LSeries.term (fun k => χ k) ((1 / 2 : ℂ) + (y : ℂ) * I) n
      = (χ n) * phasor y n := by
  rw [LSeries_term_eq_char_mul_fiber χ _ n hn.ne', phasor_eq_cpow y n hn]
/-- **The coefficient is faithfully realized on the helix.**  Lifting the `GL(1)` coefficient
(a complex phasor) to the helix at any height `h` and projecting back recovers it exactly: the
helix is a faithful geometric carrier of the L-function coefficient/readout. -/
theorem LSeries_term_realized_on_helix {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (s : ℂ) (n : ℕ) (h : ℝ) :
    helixToPhasor (phasorToHelix (LSeries.term (fun k => χ k) s n) h)
      = LSeries.term (fun k => χ k) s n :=
  helixToPhasor_phasorToHelix _ h
/-- **The finite L-function partial sum is the operator readout.**  Summing the `GL(1)`
coefficients over `n = 1,…,N` on the critical line equals the `OperatorReadout` cancellation
observable `readout ∘ (unitary spin evolution)` applied to the character vector — the
helix/operator "readout" reproduces the truncated automorphic L-function. -/
theorem LFunction_partialSum_eq_readout {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (y : ℝ) (M : ℕ) :
    ∑ i : Fin M, LSeries.term (fun k => χ k) ((1 / 2 : ℂ) + (y : ℂ) * I) ((i : ℕ) + 1)
      = cancellation y M (fun i : Fin M => χ ((i : ℕ) + 1)) := by
  rw [cancellation_eq_phasor_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [LSeries_term_on_critical_line χ y ((i : ℕ) + 1) (Nat.succ_pos _)]
  push_cast
  ring
/-- **The analytic `GL(1)` L-function is the sum of character×fiber coefficients.**  For
`Re s > 1`, `DirichletCharacter.LFunction χ s` equals `∑' n, χ(n) · n^{-s}` — the L-packet's
standard L-function is exactly the readout of the fiber coefficients. -/
theorem LFunction_eq_readout_limit_term {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.LFunction χ s = ∑' n : ℕ, LSeries.term (fun k => χ k) s n := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  rfl
end CriticalLinePhasor.AutomorphicRealization
/-!
## The spin/helix operator as a Frobenius eigenphase system
This section makes precise the claim "the helix is a Frobenius eigenphase system."
In the Euler-product picture, the `GL(1)` L-function factors as
`L(s, χ) = ∏_p (1 - χ(p) p^{-s})^{-1}`, and the local factor at a prime `p` is governed by the
**Frobenius eigenvalue** `χ(p) p^{-s}`.  On the critical line `s = 1/2 + i y` the value-dependent
part is the **eigenphase** `p^{-i y} = e^{-i y log p}`, a unit-modulus complex number.  The
operator/helix realization of `OperatorReadout` is exactly a system whose diagonal spectrum is
these eigenphases:
* `frobEigenphase` (`= spin`) is the Frobenius eigenphase `e^{-i y log n}`;
* `frobEigenphase_unit_modulus` — every eigenphase has modulus `1`;
* `frobEigenphase_mul` — eigenphases multiply by adding log-spins:
  `(e^{-i y log a})(e^{-i y log b}) = e^{-i y log (a b)}` (the Euler-product / Frobenius
  multiplicativity, "multiplication of indices = addition of phases");
* `spin_operator_eigenvector` — the standard basis vector `e_j` is an eigenvector of the
  diagonal spin (Frobenius) operator `evolMatrix` with eigenvalue the eigenphase
  `e^{-i y log (j+1)}` (the operator is *diagonalized* by the index basis);
* `spin_operator_det_eq_prod_eigenphase` — the determinant of the spin operator is the product
  of all eigenphases (the joint Frobenius phase of a window of indices);
* `euler_factor_eq_one_sub_eigenphase` — the local Euler factor on the line is
  `1 - χ(p) · p^{-1/2} · (Frobenius eigenphase)`, exhibiting the eigenphase inside the
  L-function's local factor.
-/
namespace CriticalLinePhasor.FrobeniusEigenphase
open Complex Matrix CriticalLinePhasor.OperatorReadout
/-- The **Frobenius eigenphase** attached to index `n`: the unit-modulus phase
`p^{-i y} = e^{-i y log n}` (the value-dependent part of the Frobenius eigenvalue
`χ(p) p^{-s}` on the critical line). -/
noncomputable def frobEigenphase (y : ℝ) (n : ℕ) : ℂ := spin y n
/-- Every Frobenius eigenphase has unit modulus. -/
theorem frobEigenphase_unit_modulus (y : ℝ) (n : ℕ) : ‖frobEigenphase y n‖ = 1 :=
  spin_norm y n
/-
**Frobenius multiplicativity of eigenphases.**  The eigenphases multiply by adding their
log-spins: `e^{-i y log a} · e^{-i y log b} = e^{-i y log (a·b)}` for positive indices.
-/
theorem frobEigenphase_mul (y : ℝ) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    frobEigenphase y a * frobEigenphase y b = frobEigenphase y (a * b) := by
  unfold frobEigenphase spin; norm_num [ ← Complex.exp_add ] ; ring;
  rw [ Real.log_mul ( by positivity ) ( by positivity ) ] ; push_cast ; ring;
/-- **The index basis diagonalizes the spin (Frobenius) operator.**  The standard basis vector
`e_j` is an eigenvector of `evolMatrix y N` with eigenvalue the Frobenius eigenphase
`e^{-i y log (j+1)}`. -/
theorem spin_operator_eigenvector (y : ℝ) (N : ℕ) (j : Fin N) :
    evolMatrix y N *ᵥ (Pi.single j (1 : ℂ) : Fin N → ℂ)
      = frobEigenphase y ((j : ℕ) + 1) • (Pi.single j (1 : ℂ) : Fin N → ℂ) :=
  evolMatrix_mulVec_single y N j
/-
**Joint Frobenius phase of a window.**  The determinant of the spin operator is the product
of all Frobenius eigenphases in the window — the combined phase of indices `1,…,N`.
-/
theorem spin_operator_det_eq_prod_eigenphase (y : ℝ) (N : ℕ) :
    (evolMatrix y N).det = ∏ i : Fin N, frobEigenphase y ((i : ℕ) + 1) := by
  -- By definition of $evolMatrix$, we know that its determinant is the product of its diagonal entries.
  simp [CriticalLinePhasor.OperatorReadout.evolMatrix];
  rfl
/-
**The eigenphase inside the local Euler factor.**  On the line `s = 1/2 + i y`, the local
Euler factor of the `GL(1)` L-function at a prime `p` is
`1 - χ(p) · p^{-1/2} · (Frobenius eigenphase)`.
-/
theorem euler_factor_eq_one_sub_eigenphase (χ : ℕ → ℂ) (p : ℕ) (hp : 0 < p) (y : ℝ) :
    1 - χ p * (p : ℂ) ^ (-((1 / 2 : ℂ) + (y : ℂ) * I))
      = 1 - χ p * ((p : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) * frobEigenphase y p := by
  unfold CriticalLinePhasor.FrobeniusEigenphase.frobEigenphase; ring;
  convert congr_arg ( fun x : ℂ => 1 - χ p * x ) ( cpow_vertical_line_phasor ( p : ℝ ) ( Nat.cast_pos.mpr hp ) ( 1 / 2 ) y ) using 1 <;> norm_num ; ring;
  · norm_num;
  · unfold CriticalLinePhasor.OperatorReadout.spin; ring;
    norm_num [ mul_assoc, mul_comm, mul_left_comm, Complex.ofReal_log ( Nat.cast_nonneg _ ) ]
end CriticalLinePhasor.FrobeniusEigenphase
/-!
## The helix carrier as "Frobenius/cohomology" for `ζ` (function-field dictionary)
This section makes precise the analogy "the helix source carrier is to `ζ` what
Frobenius/cohomology is to the function-field zeta function."
In the function-field case (a smooth projective curve `C/𝔽_q`), the Weil/Grothendieck picture
gives the zeta function as a **determinant of Frobenius acting on cohomology**:
```
Z(C, T) = det(1 - T · Frob | H¹) / ((1 - T)(1 - qT)) = ∏ᵢ (1 - αᵢ T) / ((1-T)(1-qT)),
```
where the `αᵢ` are the Frobenius eigenvalues, the reciprocal zeros of the numerator, and the
Weil RH is the statement `|αᵢ| = q^{1/2}` — the eigenvalues lie on a fixed circle.
The honest, fully provable transcription of this dictionary in our setting: the spin/helix
operator `evolMatrix` plays the role of (normalized) **Frobenius**, its **characteristic
determinant** `det(1 - T · evolMatrix)` plays the role of the cohomological zeta numerator, and
its reciprocal zeros are exactly the eigenphases — which, by unitarity, all lie on the unit
circle (the exact analog of the Weil bound after the `n^{-1/2}` normalization):
* `localZeta` — the determinant `det(1 - T · evolMatrix y N)`, the "cohomological" zeta numerator
  of the helix carrier operator;
* `localZeta_eq_prod` — `localZeta = ∏ᵢ (1 - T · αᵢ)` with `αᵢ` the Frobenius eigenphases
  (`= det(1 - T·Frob)`, the Weil determinant formula);
* `localZeta_zero_iff` — its zeros are exactly the reciprocals `T = αᵢ⁻¹` of the Frobenius
  eigenphases (the reciprocal-zero / spectral interpretation);
* `frobEigenphase_on_unit_circle` — every Frobenius eigenphase has modulus `1` (the normalized
  Weil bound: eigenvalues on a fixed circle), so every reciprocal zero of `localZeta` also lies
  on the unit circle.
This is the precise sense in which the helix carrier's spin operator *is* a Frobenius and its
characteristic determinant *is* the cohomological zeta — non-circular and assuming nothing about
RH; it is a theorem of linear algebra plus the unitarity already proven.
-/
namespace CriticalLinePhasor.FunctionFieldAnalogy
open Complex Matrix CriticalLinePhasor.OperatorReadout CriticalLinePhasor.FrobeniusEigenphase
/-- **Cohomological zeta numerator of the helix carrier operator.**  The characteristic
determinant `det(1 - T · evolMatrix y N)`, the analog of `det(1 - T·Frob | H¹)`. -/
noncomputable def localZeta (y : ℝ) (N : ℕ) (T : ℂ) : ℂ :=
  (1 - T • evolMatrix y N).det
/-
**Weil determinant formula.**  The cohomological zeta numerator factors as a product over
the Frobenius eigenphases: `det(1 - T·Frob) = ∏ᵢ (1 - T·αᵢ)`.
-/
theorem localZeta_eq_prod (y : ℝ) (N : ℕ) (T : ℂ) :
    localZeta y N T = ∏ i : Fin N, (1 - T * frobEigenphase y ((i : ℕ) + 1)) := by
  unfold CriticalLinePhasor.FunctionFieldAnalogy.localZeta CriticalLinePhasor.FrobeniusEigenphase.frobEigenphase CriticalLinePhasor.OperatorReadout.evolMatrix;
  rw [ show ( 1 - T • Matrix.diagonal fun i : Fin N => spin y ( i + 1 ) : Matrix ( Fin N ) ( Fin N ) ℂ ) = Matrix.diagonal ( fun i : Fin N => 1 - T * spin y ( i + 1 ) ) by ext i j; by_cases hi : i = j <;> aesop ] ; rw [ Matrix.det_diagonal ] ;
/-
**Reciprocal-zero / spectral interpretation.**  The zeros of the cohomological zeta
numerator are exactly the reciprocals of the Frobenius eigenphases.
-/
theorem localZeta_zero_iff (y : ℝ) (N : ℕ) (T : ℂ) :
    localZeta y N T = 0 ↔ ∃ i : Fin N, T * frobEigenphase y ((i : ℕ) + 1) = 1 := by
  rw [ localZeta_eq_prod, Finset.prod_eq_zero_iff ];
  grind +splitImp
/-- **Normalized Weil bound.**  Every Frobenius eigenphase lies on the unit circle, so every
reciprocal zero of `localZeta` does too — the exact analog of `|αᵢ| = q^{1/2}` after the
`n^{-1/2}` normalization. -/
theorem frobEigenphase_on_unit_circle (y : ℝ) (n : ℕ) : ‖frobEigenphase y n‖ = 1 :=
  frobEigenphase_unit_modulus y n
end CriticalLinePhasor.FunctionFieldAnalogy
/-!
## Frobenius-purity analogue: fiber-crossing representation forces `Re ρ = 1/2`
This section formalizes the program: *the analogue of Frobenius purity is the theorem that every
analytic zero of `ζ` is represented by a harmonic-fiber crossing on the no-drift carrier; once
that representation holds, the fixed-radius carrier forces the unit-circle readout and the
Möbius/Pythagorean balance gives `Re ρ = 1/2`.*
Concretely:
* The **no-drift carrier** is the factor `C^{-s}`, whose modulus is `y`-independent
  (`CarrierFiber.carrier_norm_no_drift`) and which never vanishes
  (`CarrierFiber.carrier_scale_ne_zero`) — fixed radius, no radial drift.
* The **harmonic fiber** is the reflection-symmetric two-phasor closed form `symPair c`
  (equivalently the carrier-scaled `scaledSymPair`), whose vanishing is the phasor-balance /
  unit-circle readout condition.
* The **purity mechanism** is `NoOffLineZeros.symPair_zero_re_eq_half`: a fiber crossing forces
  the two equal-radius phasors to be antiphase, i.e. `Re = 1/2` (the Möbius/Pythagorean balance).
The representation hypothesis `FiberRepresentation` — "every nontrivial-strip zero of the actual
`riemannZeta` is a crossing of some harmonic fiber `symPair c`" — is the Frobenius-purity
analogue.  We prove **unconditionally** that it *forces* RH (`fiberRepresentation_forces_RH`).
Conversely, under RH every nontrivial-strip zero with nonzero ordinate is realized as such a
fiber crossing (`riemannHypothesis_imp_fiberRepresentation_of_im_ne_zero`), so the hypothesis is
RH-strength (it implies RH and is supplied by RH on the non-real zeros).
**Honest scope.**  Establishing `FiberRepresentation` for the actual `ζ` is the open, RH-strength
step; we do not assume it and the implication proved here is non-circular.  The point — exactly as
the user states — is that "RH-strength / RH-equivalent" is *not* grounds to refuse the attempt:
the mechanism (carrier no-drift ⟹ unit circle ⟹ `Re = 1/2`) is a theorem, and the only missing
ingredient is the representation of `ζ`'s zeros as fiber crossings, which is here isolated as a
single precise target rather than dismissed.
-/
namespace CriticalLinePhasor.PurityProgram
open Complex CriticalLinePhasor.NoOffLineZeros CriticalLinePhasor.Faithful
  CriticalLinePhasor.RHEquivalences
/-- **The Frobenius-purity analogue (representation hypothesis).**  Every nontrivial-strip zero
of the actual `riemannZeta` is a crossing of some harmonic fiber `symPair c` (`c > 1`) on the
no-drift carrier. -/
def FiberRepresentation : Prop :=
  ∀ s ∈ zetaNontrivialZeros, ∃ c : ℝ, 1 < c ∧ symPair c s = 0
/-- **Purity forces the critical line.**  If every nontrivial-strip zero is a fiber crossing,
then every such zero has `Re = 1/2` — the no-drift/unit-circle readout mechanism
(`symPair_zero_re_eq_half`) applied to the representing fiber. -/
theorem fiberRepresentation_forces_critical_line (h : FiberRepresentation) :
    ∀ s ∈ zetaNontrivialZeros, s.re = 1 / 2 := by
  intro s hs
  obtain ⟨c, hc, hzero⟩ := h s hs
  exact symPair_zero_re_eq_half c hc s hzero
/-- **Purity forces RH.**  The representation hypothesis implies the Riemann Hypothesis
(unconditional, non-circular). -/
theorem fiberRepresentation_forces_RH (h : FiberRepresentation) : RiemannHypothesis :=
  riemannHypothesis_iff_zeros_on_line.mpr (fiberRepresentation_forces_critical_line h)
/-
**RH supplies the representation on non-real zeros.**  Under RH, a nontrivial-strip zero
`s` with `Im s ≠ 0` has `Re s = 1/2`, hence (writing `s = 1/2 + i y`, `y = Im s ≠ 0`) it is a
crossing of the explicit fiber `symPair (exp (π / (2 |y|)))`, via `symPair_on_line_zero_iff`
with `k = 0` (for `y > 0`) or `k = -1` (for `y < 0`).  Together with
`fiberRepresentation_forces_RH` this exhibits the representation hypothesis as RH-strength.
-/
theorem riemannHypothesis_imp_fiberRepresentation_of_im_ne_zero (h : RiemannHypothesis)
    (s : ℂ) (hs : s ∈ zetaNontrivialZeros) (him : s.im ≠ 0) :
    ∃ c : ℝ, 1 < c ∧ symPair c s = 0 := by
  refine' ⟨ Real.exp ( Real.pi / ( 2 * |s.im| ) ), _, _ ⟩ <;> norm_num [ Real.exp_pos ];
  · positivity;
  · convert CriticalLinePhasor.ZeroCounting.symPair_on_line_zero_iff ( Real.exp ( Real.pi / ( 2 * |s.im| ) ) ) ( Real.one_lt_exp_iff.mpr <| by positivity ) s.im |>.2 _ using 1
    generalize_proofs at *;
    · convert rfl using 2 ; norm_num [ Complex.ext_iff, hs.2.1, hs.2.2 ];
      exact Eq.symm ( CriticalLinePhasor.RHEquivalences.riemannHypothesis_iff_zeros_on_line.mp h s hs );
    · cases abs_cases s.im <;> simp +decide [ * ];
      · exact ⟨ 0, by rw [ mul_div_cancel₀ _ ( mul_ne_zero two_ne_zero him ) ] ; ring ⟩;
      · exact ⟨ -1, by push_cast; nlinarith [ Real.pi_pos, mul_div_cancel₀ Real.pi ( by linarith : ( - ( 2 * s.im ) ) ≠ 0 ) ] ⟩
/-- **Audit conclusion: the fiber representation is exactly RH, with no slack.**  For any `s`
with nonzero ordinate, `s` is a crossing of *some* harmonic fiber `symPair c` (`c > 1`) **iff**
`Re s = 1/2`.
This is the precise outcome of auditing the program for circularity.  The forward direction is
the no-drift/unit-circle forcing mechanism (`symPair_zero_re_eq_half`); the backward direction
is the explicit construction `c = exp(π / (2|Im s|))`.  Together they show that representing a
point as a fiber crossing **already requires** `Re s = 1/2`: the construction of the representing
fiber is only possible once the point is known to lie on the line.  Hence, for the actual `ζ`,
`FiberRepresentation` neither smuggles in RH nor is circular as an *implication* — but it cannot
be *established* through this helix/fiber construction without first proving `Re ρ = 1/2` for
`ζ`'s zeros by independent means.  The helix/fiber apparatus is therefore a sound RH-*forcing*
mechanism whose remaining input (`Re ρ = 1/2` for `ζ`) is exactly RH itself; this development
proves the mechanism unconditionally and isolates that input as the single open target, without
asserting RH and without circularity. -/
theorem fiber_crossing_iff_on_line (s : ℂ) (him : s.im ≠ 0) :
    (∃ c : ℝ, 1 < c ∧ symPair c s = 0) ↔ s.re = 1 / 2 := by
  constructor
  · rintro ⟨c, hc, hz⟩
    exact symPair_zero_re_eq_half c hc s hz
  · intro hre
    refine' ⟨ Real.exp ( Real.pi / ( 2 * |s.im| ) ), _, _ ⟩ <;> norm_num [ Real.exp_pos ];
    · positivity;
    · convert CriticalLinePhasor.ZeroCounting.symPair_on_line_zero_iff ( Real.exp ( Real.pi / ( 2 * |s.im| ) ) ) ( Real.one_lt_exp_iff.mpr <| by positivity ) s.im |>.2 _ using 1
      generalize_proofs at *;
      · convert rfl using 2 ; norm_num [ Complex.ext_iff, hre ];
      · cases abs_cases s.im <;> simp +decide [ * ];
        · exact ⟨ 0, by rw [ mul_div_cancel₀ _ ( mul_ne_zero two_ne_zero him ) ] ; ring ⟩;
        · exact ⟨ -1, by push_cast; nlinarith [ Real.pi_pos, mul_div_cancel₀ Real.pi ( by linarith : ( - ( 2 * s.im ) ) ≠ 0 ) ] ⟩
end CriticalLinePhasor.PurityProgram
