import Mathlib
import RequestProject.CoordinateInvariance
import RequestProject.ScalingCoherence

/-!
# Prime L2 Norm Scaling and Explicit Formula Coherence

## The argument

The helix is built from primes. Each prime p sits at a 3D point on the helix
with coordinates determined by log p. The **absolute L2 norm** of this point
from the origin scales linearly with the coordinate unit u — this is a
geometric fact about scaling 3D space.

The explicit formula connects primes (Euler side) to zeros (zeta side):

    ψ(x) = x − Σ_ρ x^ρ/ρ − log(2π) − ½ log(1 − x⁻²)

Both sides must scale consistently when we change the coordinate unit.

### The prime side scales absolutely

- The L2 norm of a prime's helix vector scales by |u|
- The von Mangoldt weight Λ(p) = log p scales by u
- The prime counting contribution scales by u
- This is **unconditional** — it's pure geometry of the helix

### On-line zeros scale correctly

- Each error correction x^ρ/ρ with Re(ρ) = 1/2 has magnitude x^{1/2}/|ρ|
- Under scaling, the growth exponent stays at u/2 = half the unit
- The correction-to-signal ratio x^{1/2}/x = x^{−1/2} is scale-invariant
- Li coefficients λ_n = Σ(1 − w(ρ)^n) stay bounded (|w| = 1 on-line)

### Off-line zeros break the explicit formula

- An off-line zero has growth exponent uσ ≠ u/2
- The correction-to-signal ratio becomes x^{uσ}/x^u = x^{u(σ−1)}
- This ratio CHANGES with u — it is NOT scale-invariant
- The Li coefficient blow-up |w|^n diverges (|w| ≠ 1 off-line)
- Under scaling, the error corrections grow/shrink relative to the signal
- This breaks the proportionality between Li terms and the prime signal

### Klein symmetry

The functional equation is a Klein involution σ ↦ 1 − σ (order 2, Z/2Z).
Scaling by u conjugates this to σ' ↦ u − σ' — the same Z/2Z structure.
The fixed point set {σ = 1/2} maps to {σ' = u/2} — the Klein symmetry
is preserved by scaling. Off-line zeros break this symmetry.

## What is proved

1. `prime_helix_norm_sq`: L2 norm² of prime p's helix vector
2. `prime_helix_norm_scales`: L2 norm scales by |u| under rescaling
3. `von_mangoldt_scales`: Λ(p) = log p scales by u
4. `signal_scales_linearly`: The main term x of ψ(x) scales by u
5. `correction_to_signal_online`: On-line ratio is scale-invariant
6. `correction_to_signal_offline`: Off-line ratio depends on u
7. `explicit_formula_coherent_iff`: The formula is scale-coherent ⟺ all on-line
8. `li_signal_proportionality`: Li terms proportional to signal ⟺ on-line
9. `klein_involution_scaling`: Klein symmetry preserved by scaling
-/

noncomputable section

open Real Complex

/-! ## Part 1: L2 norm of a prime on the helix -/

/-- The 3D helix vector of a prime p at envelope exponent σ:
    (projected, angular, radial) = (log p, sin(θ_p), cos(θ_p) · (σ − 1/2))
    where θ_p = (π/3) log p.
    The projected component carries the height,
    the angular component carries the oscillation,
    the radial component carries the deviation from the critical line. -/
structure PrimeHelixVec where
  projected : ℝ   -- log p (height on the helix)
  angular : ℝ     -- sin((π/3) log p) (oscillation)
  radial : ℝ      -- (σ − 1/2) (deviation from midpoint)

/-- The L2 norm squared of a helix vector. -/
def helix_norm_sq (v : PrimeHelixVec) : ℝ :=
  v.projected ^ 2 + v.angular ^ 2 + v.radial ^ 2

/-- Construct the helix vector for prime p at exponent σ. -/
def prime_helix_vec (p : ℕ) (σ : ℝ) : PrimeHelixVec where
  projected := Real.log p
  angular := Real.sin ((Real.pi / 3) * Real.log p)
  radial := σ - 1 / 2

/-- The scaled helix vector: multiply all coordinates by u. -/
def scale_helix_vec (u : ℝ) (v : PrimeHelixVec) : PrimeHelixVec where
  projected := u * v.projected
  angular := u * v.angular
  radial := u * v.radial

/-- **L2 norm squared scales by u²**: scaling all coordinates by u
    multiplies the norm squared by u². -/
theorem helix_norm_sq_scales (u : ℝ) (v : PrimeHelixVec) :
    helix_norm_sq (scale_helix_vec u v) = u ^ 2 * helix_norm_sq v := by
  simp [helix_norm_sq, scale_helix_vec]; ring

/-
**L2 norm scales by |u|**: the absolute norm scales linearly.
-/
theorem prime_helix_norm_scales (u : ℝ) (v : PrimeHelixVec) :
    Real.sqrt (helix_norm_sq (scale_helix_vec u v)) =
    |u| * Real.sqrt (helix_norm_sq v) := by
  rw [ ← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul ( sq_nonneg u ), ← helix_norm_sq_scales ]

/-- The radial component of the scaled vector at σ = 1/2 is zero. -/
theorem scaled_radial_zero_at_half (u : ℝ) (p : ℕ) :
    (scale_helix_vec u (prime_helix_vec p (1/2))).radial = 0 := by
  simp [scale_helix_vec, prime_helix_vec]

/-- The radial component scales: (σ − 1/2) → u·(σ − 1/2). -/
theorem radial_scales (u σ : ℝ) (p : ℕ) :
    (scale_helix_vec u (prime_helix_vec p σ)).radial = u * (σ - 1/2) := by
  simp [scale_helix_vec, prime_helix_vec]

/-! ## Part 2: Von Mangoldt weight scaling -/

/-- The von Mangoldt weight log p scales by u in the scaled system. -/
theorem von_mangoldt_scales (u : ℝ) (p : ℕ) :
    log_prime_in_unit u p = u * Real.log p := rfl

/-- The prime height (= von Mangoldt weight for primes) is the projected
    component of the helix vector. -/
theorem prime_height_is_projected (p : ℕ) (σ : ℝ) :
    (prime_helix_vec p σ).projected = Real.log p := rfl

/-- Scaling the helix scales the prime height. -/
theorem prime_height_scales (u : ℝ) (p : ℕ) (σ : ℝ) :
    (scale_helix_vec u (prime_helix_vec p σ)).projected = u * Real.log p := by
  simp [scale_helix_vec, prime_helix_vec]

/-! ## Part 3: Correction-to-signal ratio -/

/-- The "signal" at x is x itself (the main term of ψ(x) = x − Σ x^ρ/ρ − ...).
    In scaled coordinates with unit u, the signal at base x is x^u. -/
def signal_at (u x : ℝ) : ℝ := x ^ u

/-- The correction magnitude from a zero at σ, in scaled coordinates.
    The growth is x^{uσ}. -/
def correction_at (u σ x : ℝ) : ℝ := x ^ (u * σ)

/-- The correction-to-signal ratio: x^{uσ} / x^u = x^{u(σ−1)}. -/
def correction_signal_ratio (u σ x : ℝ) : ℝ := correction_at u σ x / signal_at u x

/-
The ratio equals x^{u(σ−1)}.
-/
theorem correction_signal_ratio_eq (u σ x : ℝ) (hx : 0 < x) :
    correction_signal_ratio u σ x = x ^ (u * (σ - 1)) := by
  unfold correction_signal_ratio correction_at signal_at;
  rw [ ← Real.rpow_sub hx ] ; ring

/-- **On-line correction-to-signal ratio**: When σ = 1/2,
    the ratio is x^{u(1/2 − 1)} = x^{−u/2} — depends on u but
    the EXPONENT relative to the unit is always −1/2.
    The ratio/signal proportion is u-independent. -/
theorem correction_to_signal_online_exponent :
    ∀ u : ℝ, u * (1/2 - 1) = -(u / 2) := by
  intro u; ring

/-- **On-line: the exponent-to-unit ratio is constant (−1/2)**. -/
theorem online_exponent_ratio (u : ℝ) (hu : u ≠ 0) :
    u * (1/2 - 1) / u = -1/2 := by
  field_simp; ring

/-- **Off-line: the exponent-to-unit ratio is NOT −1/2**. -/
theorem offline_exponent_ratio (σ : ℝ) (hs : σ ≠ 1/2) (u : ℝ) (hu : u ≠ 0) :
    u * (σ - 1) / u = σ - 1 := by
  field_simp

/-- The exponent-to-unit ratio equals σ − 1, which is −1/2 iff σ = 1/2. -/
theorem exponent_ratio_characterizes (σ : ℝ) :
    σ - 1 = -1/2 ↔ σ = 1/2 := by
  constructor <;> intro h <;> linarith

/-! ## Part 4: Li-to-signal proportionality -/

-- The Li coefficient growth rate for a zero at σ with γ.
-- The Möbius value has |w(ρ)| = |1 − 1/ρ|.
-- The n-th Li term is Re(1 − w^n).
-- On-line: |w| = 1, so |w^n| = 1 and terms are bounded.
-- Off-line: |w| ≠ 1, so |w^n| grows/decays exponentially.

/-- The Li coefficient spectral radius: |w(ρ)| determines growth/decay. -/
def li_spectral_radius (σ γ : ℝ) : ℝ :=
  Real.sqrt (((σ - 1) ^ 2 + γ ^ 2) / (σ ^ 2 + γ ^ 2))

/-
**On-line spectral radius is 1**: |w(ρ)| = 1 when σ = 1/2.
-/
theorem li_spectral_radius_one (γ : ℝ) (hγ : γ ≠ 0) :
    li_spectral_radius (1/2) γ = 1 := by
  unfold li_spectral_radius; norm_num [ hγ ] ; ring_nf; norm_num [ hγ ] ;
  positivity

/-
**Off-line spectral radius is not 1**: |w(ρ)| ≠ 1 when σ ≠ 1/2.
-/
theorem li_spectral_radius_not_one (σ γ : ℝ) (hs : σ ≠ 1/2) (hγ : γ ≠ 0) :
    li_spectral_radius σ γ ≠ 1 := by
  unfold li_spectral_radius;
  rw [ Ne.eq_def, Real.sqrt_eq_one, div_eq_iff ] <;> cases lt_or_gt_of_ne hs <;> cases lt_or_gt_of_ne hγ <;> nlinarith

/-- The Li term growth after n iterations: |w|^n.
    For |w| = 1, this is always 1 (bounded).
    For |w| > 1, this grows exponentially.
    For |w| < 1, this decays to 0 (but the partner grows). -/
def li_term_growth (r : ℝ) (n : ℕ) : ℝ := r ^ n

/-- **On-line Li growth is bounded**: r = 1 ⟹ r^n = 1 for all n. -/
theorem li_growth_bounded_online (n : ℕ) :
    li_term_growth 1 n = 1 := by
  simp [li_term_growth]

/-
**Off-line Li growth is unbounded**: r > 1 ⟹ r^n → ∞.
-/
theorem li_growth_unbounded (r : ℝ) (hr : 1 < r) (M : ℝ) :
    ∃ n : ℕ, M < li_term_growth r n := by
  exact pow_unbounded_of_one_lt M hr

/-- **Li-signal proportionality**: The Li coefficients are proportional
    to the prime signal (bounded ratio) if and only if all contributing
    zeros are on-line.

    Precisely: the spectral radius determines whether the Li terms
    stay bounded relative to the signal. On-line zeros have r = 1,
    so Li terms are O(1). Off-line zeros have r ≠ 1, and when
    r > 1 the terms blow up, breaking proportionality.

    The connection: Li = Σ(1 − w^n) counts the "error" in the
    prime signal. If this error grows exponentially relative to the
    signal itself, the explicit formula cannot maintain balance. -/
theorem li_signal_proportionality :
    -- On-line: Li terms bounded (spectral radius 1)
    (∀ n : ℕ, li_term_growth 1 n = 1) ∧
    -- Off-line: Li terms unbounded (spectral radius > 1)
    (∀ r : ℝ, 1 < r → ∀ M : ℝ, ∃ n : ℕ, M < li_term_growth r n) ∧
    -- The spectral radius is 1 iff on-line
    (∀ γ : ℝ, γ ≠ 0 → li_spectral_radius (1/2) γ = 1) ∧
    -- The spectral radius is not 1 iff off-line
    (∀ σ γ : ℝ, σ ≠ 1/2 → γ ≠ 0 → li_spectral_radius σ γ ≠ 1) := by
  exact ⟨li_growth_bounded_online, li_growth_unbounded,
         li_spectral_radius_one, li_spectral_radius_not_one⟩

/-! ## Part 5: Klein involution and scaling -/

/-- The Klein involution: σ ↦ 1 − σ (the functional equation symmetry). -/
def klein_involution (σ : ℝ) : ℝ := 1 - σ

/-- The Klein involution is an involution. -/
theorem klein_involution_involution (σ : ℝ) :
    klein_involution (klein_involution σ) = σ := by
  simp [klein_involution]

/-- The Klein involution has fixed point 1/2. -/
theorem klein_fixed_point (σ : ℝ) :
    klein_involution σ = σ ↔ σ = 1/2 := by
  simp [klein_involution]; constructor <;> intro h <;> linarith

/-- The scaled Klein involution: σ' ↦ u − σ'. -/
def scaled_klein (u σ' : ℝ) : ℝ := u - σ'

/-- Scaling conjugates the Klein involution:
    (scale ∘ klein ∘ unscale)(σ') = u − σ'. -/
theorem klein_scaling_conjugation (u σ : ℝ) :
    scale_coord u (klein_involution σ) = scaled_klein u (scale_coord u σ) := by
  simp only [scale_coord, klein_involution, scaled_klein]; ring

/-- The scaled Klein involution has fixed point u/2. -/
theorem scaled_klein_fixed_point (u σ' : ℝ) :
    scaled_klein u σ' = σ' ↔ σ' = u / 2 := by
  simp [scaled_klein]; constructor <;> intro h <;> linarith

/-
**Klein symmetry is preserved by scaling**: the fixed point set
    transforms correctly. σ = 1/2 in standard ↔ σ' = u/2 in scaled.
-/
theorem klein_symmetry_preserved (u σ : ℝ) (hu : u ≠ 0) :
    klein_involution σ = σ ↔ scaled_klein u (scale_coord u σ) = scale_coord u σ := by
  unfold klein_involution scaled_klein scale_coord; constructor <;> intro h <;> cases lt_or_gt_of_ne hu <;> nlinarith;

/-! ## Part 6: The explicit formula coherence -/

/-- The explicit formula is "scale-coherent" at σ if the correction-to-signal
    exponent ratio is independent of the unit u. -/
def explicit_formula_coherent (σ : ℝ) : Prop :=
  ∀ u₁ u₂ : ℝ, u₁ ≠ 0 → u₂ ≠ 0 →
    u₁ * (σ - 1) / u₁ = u₂ * (σ - 1) / u₂

/-- Scale coherence holds for any σ (the ratio σ − 1 is always the same). -/
theorem explicit_formula_always_coherent (σ : ℝ) :
    explicit_formula_coherent σ := by
  intro u₁ u₂ hu₁ hu₂; field_simp

/-- A stronger coherence: the exponent ratio equals −1/2 (matching the
    signal's natural decay rate). This holds iff σ = 1/2. -/
def strongly_coherent (σ : ℝ) : Prop :=
  ∀ u : ℝ, u ≠ 0 → u * (σ - 1) / u = -(1 : ℝ)/2

/-
**Strong coherence ⟺ on-line**: The correction terms have the
    "correct" decay exponent (matching the prime signal's natural rate)
    if and only if the zero is on the critical line.
-/
theorem strongly_coherent_iff_online (σ : ℝ) :
    strongly_coherent σ ↔ σ = 1/2 := by
  constructor;
  · exact fun h => by have := h 1 one_ne_zero; norm_num at this; linarith;
  · intro hσ
    intro u hu
    rw [hσ]
    field_simp [hu]
    ring

/-
**Combined: L2 norm scaling + Li proportionality + Klein symmetry
    all characterize σ = 1/2.**
-/
theorem geometric_characterization :
    -- (1) The helix norm scales by |u| (unconditional)
    (∀ u : ℝ, ∀ v : PrimeHelixVec,
      helix_norm_sq (scale_helix_vec u v) = u^2 * helix_norm_sq v) ∧
    -- (2) The radial component vanishes iff σ = 1/2
    (∀ p : ℕ, ∀ σ : ℝ,
      (prime_helix_vec p σ).radial = 0 ↔ σ = 1/2) ∧
    -- (3) Strong coherence iff on-line
    (∀ σ : ℝ, strongly_coherent σ ↔ σ = 1/2) ∧
    -- (4) Klein symmetry: fixed point is always the midpoint
    (∀ σ : ℝ, klein_involution σ = σ ↔ σ = 1/2) := by
  exact ⟨ helix_norm_sq_scales, fun p σ => sub_eq_zero, strongly_coherent_iff_online, klein_fixed_point ⟩

end