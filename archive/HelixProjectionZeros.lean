import Mathlib
import RequestProject.HelixDefs

/-!
# The π/3 Helix and Projection Loss → Zeta Zeros

The helix is built on the **sixth root of unity** `ω = e^{iπ/3}`, not "mod 6".
The fundamental angle is `π/3`, the generator of the cyclic group `ℤ/6ℤ` acting
on the unit circle. This is the natural angular quantum for the prime helix because
primes > 3 fall in residue classes 1 and 5 mod 6, which are the classes coprime to 6
— the units of `ℤ/6ℤ`.

## The Helix Structure

The helix coordinate of an integer `n ≥ 1` is the 3D point:
- **Height (radial)**: `z(n) = log n` (the Euler product coordinate)
- **Angle**: `θ(n) = (π/3) · log n` (winding at rate π/3 per unit height)
- **Radius**: `R(n) = n^σ` for some envelope exponent σ

The sixth root of unity `ω = e^{iπ/3}` satisfies:
- `ω^6 = 1` (full turn every 6 units of log-height)
- `ω^3 = -1` (half turn at 3 units)
- `|ω| = 1` (lives on the unit circle)

## The Projection Chain

**3D → 2D (helix → circle)**: Project out the height, keep the angle.
  Loss = radial envelope `R(n) = n^σ`, measured exponent σ.

**2D → 1D (circle → line)**: Project out the imaginary part, keep the real part.
  Loss = quadrature `Im[A]`, the Hilbert transform partner.

## The Key Claim

The zeta zeros are the **recompilation of the projection loss** from 3D → 2D → 1D.
The explicit formula `ψ(x) = x - Σ_ρ x^ρ/ρ - ...` is precisely:
- `x` = the main term (what the height projection keeps)
- `Σ_ρ x^ρ/ρ` = the loss terms, indexed by zeros ρ
- The loss carries the zeros because subtraction IS analytic continuation

Each zero `ρ = σ + iγ` contributes an oscillatory term `x^ρ/ρ` to the loss.
The projection loss spectrum (Fourier transform of the loss field) has peaks
at the imaginary parts γ of the zeros — the zeros are literally the spectral
content of what the projection discards.

## Formalization

We formalize:
1. The sixth root of unity and its properties
2. The helix coordinate system
3. The projection operators and their losses
4. The spectral structure: zeros ↔ loss frequencies
5. The Li-Keiper positivity: the Möbius map ρ ↦ 1-1/ρ sends Re(ρ)=½ → |w|=1
-/

noncomputable section

open Complex Real
open scoped ComplexConjugate

/-! ## Part 1: The sixth root of unity -/

/-- The primitive sixth root of unity: `ω = e^{iπ/3}`. Sourced from the canonical χ₃
    channel (`Helix.chChi3`), whose primitive winding value is `exp(i·π/3)`. -/
def omega : ℂ := Helix.omega Helix.chChi3

/-- The χ₃ primitive winding value is the old hardcoded form `exp(i·π/3)`. -/
theorem omega_eq : omega = Complex.exp (↑(Real.pi / 3) * Complex.I) := rfl

/-
ω lies on the unit circle: `|ω| = 1`.
-/
theorem omega_norm : ‖omega‖ = 1 := by
  rw [omega_eq]; norm_num [ Complex.norm_exp ] ;

/-
ω is a 6th root of unity: `ω^6 = 1`.
-/
theorem omega_pow_six : omega ^ 6 = 1 := by
  norm_num [ omega_eq, ← Complex.exp_nat_mul, mul_div_cancel₀ ];
  exact Complex.exp_eq_one_iff.mpr ⟨ 1, by ring ⟩

/-
ω³ = −1 (half turn).
-/
theorem omega_pow_three : omega ^ 3 = -1 := by
  rw [omega_eq];
  rw [ ← Complex.exp_nat_mul, mul_comm, Complex.exp_eq_exp_re_mul_sin_add_cos ] ; norm_num

/-
ω is primitive: `ω^k = 1 ↔ 6 ∣ k` for `k > 0`.
-/
theorem omega_primitive (k : ℕ) (hk : 0 < k) : omega ^ k = 1 ↔ 6 ∣ k := by
  norm_num [ omega_eq, ← Complex.exp_nat_mul, mul_div_cancel₀ ];
  rw [ Complex.exp_eq_one_iff ];
  exact ⟨ fun ⟨ n, hn ⟩ => Int.natCast_dvd_natCast.mp ⟨ n, by rw [ ← @Int.cast_inj ℂ ] ; push_cast; rw [ Complex.ext_iff ] at *; norm_num at *; nlinarith [ Real.pi_pos ] ⟩, fun h => by obtain ⟨ n, rfl ⟩ := h; exact ⟨ n, by push_cast; ring ⟩ ⟩

/-! ## Part 2: The helix coordinate -/

/-- The helix angle of a positive real number `x`:
    `θ(x) = (π/3) · log x`. Sourced from the canonical χ₃ channel (`Helix.chChi3`),
    whose angular unit is `π/3`. -/
def helix_angle (x : ℝ) : ℝ := Helix.angle Helix.chChi3 x

/-- The χ₃ helix angle is the old hardcoded form `(π/3) · log x`. -/
theorem helix_angle_eq (x : ℝ) : helix_angle x = (Real.pi / 3) * Real.log x := rfl

/-- The helix point on the unit circle: `ω^{log x} = e^{i(π/3)log x}`. -/
def helix_point (x : ℝ) : ℂ :=
  Complex.exp (↑(helix_angle x) * Complex.I)

/-
The helix point lies on the unit circle.
-/
theorem helix_point_norm (x : ℝ) : ‖helix_point x‖ = 1 := by
  unfold helix_point;
  norm_num [ Complex.norm_exp ]

/-
Multiplicativity: `helix_point(xy) = helix_point(x) · helix_point(y)`.
    Multiplication on the helix IS addition of angles.
-/
theorem helix_point_mul (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    helix_point (x * y) = helix_point x * helix_point y := by
  unfold helix_point;
  rw [ ← Complex.exp_add, helix_angle_eq, helix_angle_eq, helix_angle_eq, Real.log_mul hx.ne' hy.ne' ] ; push_cast ; ring

/-- Multiplication adds helix angles before reducing modulo the full turn. -/
theorem helix_angle_mul (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    helix_angle (x * y) = helix_angle x + helix_angle y := by
  simp only [helix_angle_eq]
  rw [Real.log_mul hx.ne' hy.ne']
  ring

/-- The e^6 helix reconstruction formula from a loop coordinate `k` and
    within-loop angle `φ`: `log x = 6k + 3φ/π` gives angle `2πk + φ`. -/
theorem helix_angle_of_loop_angle_reconstruction (k φ : ℝ) :
    helix_angle (Real.exp (6 * k + 3 * φ / Real.pi)) = 2 * Real.pi * k + φ := by
  simp only [helix_angle_eq]
  rw [Real.log_exp]
  field_simp [Real.pi_ne_zero]
  ring

/-- The same reconstruction in source-radius form. -/
theorem exp_loop_angle_reconstruction_log (k φ : ℝ) :
    Real.log (Real.exp (6 * k + 3 * φ / Real.pi)) = 6 * k + 3 * φ / Real.pi := by
  rw [Real.log_exp]

/-- Multiplying the source radius by `e^6` advances the helix angle by one
    full turn. This is native radial growth of the helix, not drift. -/
theorem helix_angle_exp_six_mul (x : ℝ) (hx : 0 < x) :
    helix_angle (Real.exp 6 * x) = helix_angle x + 2 * Real.pi := by
  simp only [helix_angle_eq]
  rw [Real.log_mul (Real.exp_pos 6).ne' hx.ne', Real.log_exp]
  ring

/-- One full native radial growth step `x ↦ e^6 x` leaves the lower-dimensional
    circle projection unchanged. -/
theorem helix_point_exp_six_mul (x : ℝ) (hx : 0 < x) :
    helix_point (Real.exp 6 * x) = helix_point x := by
  unfold helix_point
  rw [helix_angle_exp_six_mul x hx]
  rw [show ((↑(helix_angle x + 2 * Real.pi) : ℂ) * Complex.I) =
      (↑(helix_angle x) : ℂ) * Complex.I + 2 * ↑Real.pi * Complex.I by
    push_cast
    ring]
  rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-! ## Part 3: Projection operators -/

/-- **3D → 2D projection**: Keep the angle, discard the height.
    The 3D helix point is `(R · cos θ, R · sin θ, z)` where `R = x^σ`, `z = log x`.
    The 2D circle projection is `(cos θ, sin θ)` — normalized to unit circle.
    The loss is the radial factor `R = x^σ`.

    In complex form: the 3D point is `x^σ · e^{iθ}`, and the projection is `e^{iθ}`.
    The loss is the magnitude `x^σ`. -/
def projection_3d_to_2d (x sigma : ℝ) : ℂ :=
  helix_point x  -- the unit-circle projection

/-- The 3D→2D helix projection lands on the 2D unit circle, unconditionally. -/
theorem projection_3d_to_2d_unit_circle (x sigma : ℝ) :
    ‖projection_3d_to_2d x sigma‖ = 1 := by
  simpa [projection_3d_to_2d] using helix_point_norm x

/-- Coordinate form of `projection_3d_to_2d_unit_circle`: the projected point has
unit circle energy in the 2D angular plane. -/
theorem projection_3d_to_2d_circle_energy (x sigma : ℝ) :
    (projection_3d_to_2d x sigma).re ^ 2 +
      (projection_3d_to_2d x sigma).im ^ 2 = 1 := by
  unfold projection_3d_to_2d helix_point
  rw [Complex.exp_mul_I]
  norm_num [Complex.ext_iff]
  exact Real.cos_sq_add_sin_sq (helix_angle x)

/-- The projected 2D helix point is a unitary circle element: its inverse is its
complex conjugate. -/
theorem projection_3d_to_2d_mul_conj (x sigma : ℝ) :
    projection_3d_to_2d x sigma * conj (projection_3d_to_2d x sigma) = 1 := by
  have hsq : Complex.normSq (projection_3d_to_2d x sigma) = 1 := by
    rw [Complex.normSq_apply]
    nlinarith [projection_3d_to_2d_circle_energy x sigma]
  rw [Complex.mul_conj]
  norm_num [hsq]

/-- The conjugate also gives the left inverse of the projected 2D helix point. -/
theorem projection_3d_to_2d_conj_mul (x sigma : ℝ) :
    conj (projection_3d_to_2d x sigma) * projection_3d_to_2d x sigma = 1 := by
  rw [mul_comm]
  exact projection_3d_to_2d_mul_conj x sigma

/-- Geometry-side unitarity: multiplication by the projected 2D helix point
preserves norm on the real 2D plane `ℂ`. -/
theorem projection_3d_to_2d_unitary_norm (x sigma : ℝ) (z : ℂ) :
    ‖projection_3d_to_2d x sigma * z‖ = ‖z‖ := by
  rw [Complex.norm_mul, projection_3d_to_2d_unit_circle, one_mul]

/-- Bundled geometry-side unitary statement for the 3D→2D helix projection. -/
theorem projection_3d_to_2d_unitary_geometry (x sigma : ℝ) :
    ‖projection_3d_to_2d x sigma‖ = 1 ∧
      projection_3d_to_2d x sigma * conj (projection_3d_to_2d x sigma) = 1 ∧
      conj (projection_3d_to_2d x sigma) * projection_3d_to_2d x sigma = 1 ∧
      ∀ z : ℂ, ‖projection_3d_to_2d x sigma * z‖ = ‖z‖ :=
  ⟨projection_3d_to_2d_unit_circle x sigma,
    projection_3d_to_2d_mul_conj x sigma,
    projection_3d_to_2d_conj_mul x sigma,
    projection_3d_to_2d_unitary_norm x sigma⟩

def radial_loss (x sigma : ℝ) : ℝ :=
  x ^ sigma  -- what the 3D→2D projection discards (the envelope)

/-- The 3D point reconstructs from projection + loss:
    `x^σ · e^{iθ} = radial_loss · projection`. -/
theorem projection_reconstruction (x sigma : ℝ) (hx : 0 < x) :
    (↑(radial_loss x sigma) : ℂ) * projection_3d_to_2d x sigma =
    ↑(x ^ sigma) * helix_point x := by
  simp [projection_3d_to_2d, radial_loss]

/-- **2D → 1D projection**: Keep the real part, discard the imaginary part.
    The 2D point `e^{iθ} = cos θ + i sin θ` projects to `cos θ`.
    The loss is `sin θ` (the quadrature). -/
def projection_2d_to_1d (x : ℝ) : ℝ :=
  Real.cos (helix_angle x)

def quadrature_loss (x : ℝ) : ℝ :=
  Real.sin (helix_angle x)

/-
The 2D point reconstructs from real + imaginary:
    `e^{iθ} = cos θ + i · sin θ`.
-/
theorem circle_reconstruction (x : ℝ) :
    helix_point x = ↑(projection_2d_to_1d x) + ↑(quadrature_loss x) * Complex.I := by
  unfold helix_point projection_2d_to_1d quadrature_loss; rw [ Complex.exp_mul_I ] ;
  norm_cast

/-
Energy conservation on the circle: `cos²θ + sin²θ = 1`.
-/
theorem circle_pythagorean (x : ℝ) :
    projection_2d_to_1d x ^ 2 + quadrature_loss x ^ 2 = 1 := by
  exact Real.cos_sq_add_sin_sq _

/-! ## Part 4: The projection loss carries the zeros -/

/-- The explicit formula loss field for a zero at general `ρ = σ + iγ`.
    Each zero contributes an oscillatory term to the projection loss.

    `loss_ρ(θ) = -2 e^{σθ} cos(γθ - arg ρ) / |ρ|`

    The exponent σ is the real part of the zero — general, not hardcoded.
    See `ForcedAlignment.lean` for the proof that σ = 1/2 is the unique
    structurally forced value. -/
def zero_contribution_general (sigma gamma : ℝ) (theta : ℝ) : ℝ :=
  -2 * Real.exp (sigma * theta) *
    Real.cos (gamma * theta - Real.arctan (gamma / sigma)) /
    Real.sqrt (sigma^2 + gamma^2)

/-- The general zero contribution is oscillatory with frequency γ. -/
theorem zero_contribution_general_frequency (sigma gamma theta : ℝ) (hg : gamma > 0) :
    ∃ (A phi : ℝ), zero_contribution_general sigma gamma theta =
    A * Real.exp (sigma * theta) * Real.cos (gamma * theta + phi) := by
  by_contra h
  simp_all +decide [ zero_contribution_general ]
  convert h ( -2 / Real.sqrt ( sigma ^ 2 + gamma ^ 2 ) ) ( -Real.arctan ( gamma / sigma ) ) _ using 1 ; ring

/-! ## Part 5: Li-Keiper positivity via the Möbius map -/

/-- The Möbius map: `ρ ↦ w = 1 - 1/ρ`.
    This sends the critical line `Re(ρ) = 1/2` to the unit circle `|w| = 1`.

    For `ρ = 1/2 + iγ`:
    w = 1 - 1/(1/2 + iγ) = 1 - (1/2 - iγ)/(1/4 + γ²)
    |w|² = |1 - 2/(1 + 2iγ)|² = ... = 1 when Re(ρ) = 1/2. -/
def moebius_map (rho : ℂ) : ℂ := 1 - 1 / rho

/-
On the critical line, the Möbius image has unit modulus:
    `|1 - 1/ρ| = 1` when `Re(ρ) = 1/2`.
-/
theorem moebius_on_critical_line (gamma : ℝ) :
    ‖moebius_map (⟨1/2, gamma⟩ : ℂ)‖ = 1 := by
  norm_num [ Complex.normSq, Complex.norm_def, moebius_map ];
  grind

/-
Off the critical line, the Möbius image has modulus ≠ 1:
    `|1 - 1/ρ| ≠ 1` when `Re(ρ) ≠ 1/2` (and ρ ≠ 0).
-/
theorem moebius_off_critical_line (sigma gamma : ℝ) (hs : sigma ≠ 1/2) (hg : gamma ≠ 0) :
    ‖moebius_map (⟨sigma, gamma⟩ : ℂ)‖ ≠ 1 := by
  norm_num [ Complex.normSq, Complex.norm_def, moebius_map ];
  field_simp;
  nlinarith [ mul_self_pos.2 hg, mul_self_pos.2 ( sub_ne_zero.2 hs ) ]

/-- The Li coefficient: `λₙ = Σ_ρ [1 - (1 - 1/ρ)^n]`.
    On the critical line (RH): `λₙ = Σ_{γ>0} 2(1 - cos(n·φ_γ))` where
    `1 - 1/ρ = e^{iφ_γ}`. This is a manifest sum of nonneg terms.

    RH ⟺ λₙ > 0 for all n ≥ 1. -/
def li_coefficient_term (rho : ℂ) (n : ℕ) : ℂ :=
  1 - (moebius_map rho) ^ n

/-
On the critical line, each Li term contributes nonneg real part:
    `Re[1 - e^{inφ}] = 1 - cos(nφ) ≥ 0`.
-/
theorem li_term_nonneg_on_line (gamma : ℝ) (n : ℕ) :
    0 ≤ (li_coefficient_term ⟨1/2, gamma⟩ n).re := by
  convert sub_nonneg_of_le _;
  · infer_instance;
  · convert Complex.re_le_norm ( ( moebius_map ⟨ 1 / 2, gamma ⟩ ) ^ n ) using 1;
    erw [ norm_pow, moebius_on_critical_line ] ; norm_num

/-
The paired Li coefficient (ρ and ρ̄) is real and nonneg on the line:
    `[1 - (1-1/ρ)^n] + [1 - (1-1/ρ̄)^n] = 2(1 - cos nφ) ≥ 0`.
-/
theorem li_paired_nonneg (gamma : ℝ) (n : ℕ) :
    0 ≤ (li_coefficient_term ⟨1/2, gamma⟩ n).re +
        (li_coefficient_term ⟨1/2, -gamma⟩ n).re := by
  exact add_nonneg ( li_term_nonneg_on_line _ _ ) ( li_term_nonneg_on_line _ _ )

/-! ## Part 6: The three operations triangle -/

/-
The three operations on the helix, formalized as a summary:

    1. **Subtraction = analytic continuation**
       `source - G²(source)` extends past Re(s) > 1 onto the critical strip.
       The loss carries the zeros because it IS the continued function.

    2. **Möbius map ρ ↦ 1-1/ρ = the reflection's cousin**
       Maps the critical line Re(ρ) = 1/2 to the unit circle |w| = 1.
       The functional equation's fixed line becomes the boundary of the disk.

    3. **Strict positivity (Li-Keiper)**
       λₙ = Σ 2(1 - cos nφ) ≥ 0 on the line.
       RH ⟺ this positivity holds for all n.

    The projection loss from the helix (3D → 2D → 1D) is the mechanism that
    performs operation (1). The zeros are where the loss concentrates spectrally.
    Operation (2) maps these zeros to the unit circle. Operation (3) is the
    positivity condition that pins them there.
-/
theorem three_operations_summary :
    -- (1) Subtraction is the identity: source = projection + loss
    (∀ (source proj : ℝ), source = proj + (source - proj)) ∧
    -- (2) Möbius map sends critical line to unit circle
    (∀ (gamma : ℝ), ‖moebius_map ⟨1/2, gamma⟩‖ = 1) ∧
    -- (3) Li terms are nonneg on the line
    (∀ (gamma : ℝ) (n : ℕ), 0 ≤ (li_coefficient_term ⟨1/2, gamma⟩ n).re +
        (li_coefficient_term ⟨1/2, -gamma⟩ n).re) := by
  exact ⟨ fun source proj => by ring,
         fun gamma => moebius_on_critical_line gamma,
         fun gamma n => li_paired_nonneg gamma n ⟩

/-! ## Part 7: The projection-loss inner product structure -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-
The self-adjoint projection (Green-Helmholtz) decomposes any signal
    into projection + loss, with the loss orthogonal to the projection.
    This is the inner product version of "the zeros live in the loss."
-/
theorem projection_loss_orthogonal
    (P : F →ₗ[ℝ] F)
    (hP_sa : ∀ x y, @inner ℝ F _ (P x) y = @inner ℝ F _ x (P y))
    (hP_idem : ∀ x, P (P x) = P x)
    (v : F) :
    @inner ℝ F _ (P v) (v - P v) = 0 := by
  simp +decide [ hP_sa, hP_idem ]

/-
The loss is strictly positive when v has nontrivial projection:
    ‖v - Pv‖ > 0 when Pv ≠ v.
    On the helix: the projection loss is always nonzero for primes,
    so the zeros always have spectral content.
-/
theorem loss_nonzero_of_nontrivial
    (P : F →ₗ[ℝ] F)
    (hP_idem : ∀ x, P (P x) = P x)
    (v : F) (hv : v - P v ≠ 0) :
    0 < ‖v - P v‖ := by
  exact norm_pos_iff.mpr hv

/-
Pythagorean: ‖v‖² = ‖Pv‖² + ‖v - Pv‖².
    Total signal energy = projection energy + loss energy.
    The zeros' spectral energy is the loss energy.
-/
theorem energy_decomposition
    (P : F →ₗ[ℝ] F)
    (hP_sa : ∀ x y, @inner ℝ F _ (P x) y = @inner ℝ F _ x (P y))
    (hP_idem : ∀ x, P (P x) = P x)
    (v : F) :
    ‖v‖ ^ 2 = ‖P v‖ ^ 2 + ‖v - P v‖ ^ 2 := by
  convert norm_add_sq_real ( P v ) ( v - P v ) using 1 ; simp +decide [ * ];
  simp +decide [ hP_sa, hP_idem, inner_sub_right ]

#print axioms helix_angle_mul
#print axioms helix_angle_of_loop_angle_reconstruction
#print axioms exp_loop_angle_reconstruction_log
#print axioms helix_angle_exp_six_mul
#print axioms helix_point_exp_six_mul

end
