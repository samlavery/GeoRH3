import Mathlib

/-!
# Green–Helmholtz / Gram energy is non-negative (the von Neumann positive form)

The Green–Helmholtz kernel `K_μ(x,y) = (1/2μ)·e^{−μ|x−y|}` is the Green's function of
`A = −d²/dΘ² + μ²` (`(−d²/dx²+μ²)K_μ = δ`), so `G_μ = A⁻¹` is positive and the Gram energy

  `E = Σ_{i,j} a_i a_j K_μ(x_i, x_j) = ‖A^{−1/2}(Σ a_i δ_{x_i})‖² ≥ 0`.

We prove `E ≥ 0` directly from the **feature/integral representation**
`K_μ(x,y) = ∫_ℝ φ_x(t) φ_y(t) dt`, `φ_x(t) = e^{−μ(x−t)}·𝟙[t≤x]`, giving `E = ∫ (Σ_i a_i φ_{x_i})² ≥ 0`.

HONEST SCOPE (Rule Two / Rule Four). This positivity is **automatic**: it holds for *any* real
coefficients `a_i` and points `x_i` — it does not see the primes, the character, or the zeros, and an
off-line zero is invisible to it (its `−L′/L` pole lies off the real axis, contributing no real-axis
divergence). Specialising `a_i = Λ(qᵢ)χ(qᵢ)/√qᵢ`, `x_i = log qᵢ` gives the prime-trace Gram energy
`Eχ ≥ 0` (numerically `Eχ₃ ≪ E_random`, character-sensitive) — but this is the Weil-positivity
*machinery*, **not** a forcing of the critical line. The GRH content is the off-line *penalty*
(the zero-side sign change), which this prime-side `≥ 0` form does not carry. Do not dress this as GRH.
-/

open MeasureTheory Real

noncomputable section
namespace GHGram

variable (μ : ℝ)

/-- One-sided exponential feature `φ_x(t) = e^{−μ(x−t)}` for `t ≤ x`, else `0`. -/
def feat (x t : ℝ) : ℝ := if t ≤ x then Real.exp (μ * (t - x)) else 0

/-- The Green–Helmholtz kernel `K_μ(x,y) = (1/2μ)·e^{−μ|x−y|}`. -/
def K (x y : ℝ) : ℝ := (1 / (2 * μ)) * Real.exp (-μ * |x - y|)

theorem feat_nonneg (x t : ℝ) : 0 ≤ feat μ x t := by
  unfold feat; split
  · exact (Real.exp_pos _).le
  · rfl

/-- `φ_x · φ_y` is the `Iic`-indicator of a single exponential. -/
theorem feat_mul (x y t : ℝ) :
    feat μ x t * feat μ y t
      = (Set.Iic (min x y)).indicator (fun t => Real.exp (μ * (2 * t - x - y))) t := by
  unfold feat
  rw [Set.indicator_apply]
  simp only [Set.mem_Iic, le_min_iff]
  by_cases hx : t ≤ x
  · by_cases hy : t ≤ y
    · simp only [hx, hy, if_true, and_self]
      rw [← Real.exp_add]; congr 1; ring
    · simp [hx, hy]
  · simp [hx]

/-- `φ_x · φ_y` is integrable. -/
theorem feat_mul_integrable (hμ : 0 < μ) (x y : ℝ) :
    Integrable (fun t => feat μ x t * feat μ y t) := by
  simp_rw [feat_mul μ]
  rw [integrable_indicator_iff measurableSet_Iic]
  have h : (fun t : ℝ => Real.exp (μ * (2 * t - x - y)))
         = fun t => Real.exp (-(μ * (x + y))) * Real.exp ((2 * μ) * t) := by
    funext t; rw [← Real.exp_add]; congr 1; ring
  rw [h]
  exact (integrableOn_exp_mul_Iic (show (0:ℝ) < 2 * μ by positivity) _).const_mul _

/-- **Feature representation of the kernel:** `K_μ(x,y) = ∫ φ_x φ_y`. -/
theorem K_eq_integral (hμ : 0 < μ) (x y : ℝ) :
    K μ x y = ∫ t, feat μ x t * feat μ y t := by
  simp_rw [feat_mul μ]
  rw [MeasureTheory.integral_indicator measurableSet_Iic]
  have h : (fun t : ℝ => Real.exp (μ * (2 * t - x - y)))
         = fun t => Real.exp (-(μ * (x + y))) * Real.exp ((2 * μ) * t) := by
    funext t; rw [← Real.exp_add]; congr 1; ring
  simp_rw [h]
  rw [MeasureTheory.integral_const_mul, integral_exp_mul_Iic (show (0:ℝ) < 2 * μ by positivity)]
  have hmin : x + y - 2 * min x y = |x - y| := by
    rcases le_total x y with hle | hle
    · rw [min_eq_left hle, abs_of_nonpos (by linarith)]; ring
    · rw [min_eq_right hle, abs_of_nonneg (by linarith)]; ring
  rw [K, show -μ * |x - y| = -(μ * (x + y)) + 2 * μ * min x y by rw [← hmin]; ring,
      Real.exp_add]
  ring

/-- The Gram energy `Σ_{i,j} a_i a_j K_μ(x_i, x_j)`. -/
def gramEnergy {ι : Type*} (s : Finset ι) (a x : ι → ℝ) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s, a i * a j * K μ (x i) (x j)

/-- The Gram energy equals `∫ (Σ_i a_i φ_{x_i})²` — manifestly `≥ 0`. -/
theorem gramEnergy_eq_integral (hμ : 0 < μ) {ι : Type*} (s : Finset ι) (a x : ι → ℝ) :
    (∫ t, (∑ i ∈ s, a i * feat μ (x i) t) ^ 2) = gramEnergy μ s a x := by
  have key : ∀ t, (∑ i ∈ s, a i * feat μ (x i) t) ^ 2
      = ∑ i ∈ s, ∑ j ∈ s, a i * a j * (feat μ (x i) t * feat μ (x j) t) := by
    intro t
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  simp_rw [key]
  unfold gramEnergy
  rw [MeasureTheory.integral_finsetSum s
    (fun i _ => MeasureTheory.integrable_finsetSum s
      (fun j _ => (feat_mul_integrable μ hμ (x i) (x j)).const_mul _))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [MeasureTheory.integral_finsetSum s
    (fun j _ => (feat_mul_integrable μ hμ (x i) (x j)).const_mul _)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [MeasureTheory.integral_const_mul, ← K_eq_integral μ hμ]

/-- **The Green–Helmholtz / Gram energy is non-negative** (`gramEnergy_nonneg`). The von Neumann
    positive form: `A = −d²/dΘ²+μ²` self-adjoint positive ⟹ `A⁻¹` positive ⟹ `⟨T, A⁻¹ T⟩ ≥ 0`.
    Proven via the feature representation, so it is automatic (holds for any `a`, `x`). -/
theorem gramEnergy_nonneg (hμ : 0 < μ) {ι : Type*} (s : Finset ι) (a x : ι → ℝ) :
    0 ≤ gramEnergy μ s a x := by
  rw [← gramEnergy_eq_integral μ hμ]
  exact MeasureTheory.integral_nonneg (fun t => sq_nonneg _)

end GHGram
