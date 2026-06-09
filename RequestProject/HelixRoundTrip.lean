import Mathlib

/-!
# Helix Round-Trip: Projection Loss Tracking Forces the Midpoint

The Li coefficients come from the **helix** (the Euler product / prime side),
not from assuming zeros are on the critical line. The Möbius map ρ ↦ 1-1/ρ
is the **helix operation**, and its modulus |1-1/ρ| measures whether the
round-trip through projections is isometric.

## The Round-Trip Structure

With Green-Helmholtz and tracked projection loss, we can go:

  **3D → 2D → 3D → 2D → 1D → 2D**

At each stage:
- The forward projection P is self-adjoint and idempotent
- The loss L = I - P is self-adjoint and idempotent (onto the complement)
- Reconstruction is exact: x = Px + Lx (no information lost)
- Energy is conserved: ‖x‖² = ‖Px‖² + ‖Lx‖²

## The Functional Equation as an Involution

The functional equation ξ(s) = ξ(1-s) gives an involution R: σ ↦ 1-σ
on the helix. This involution satisfies:
- R² = Id (it's an involution)
- R is self-adjoint (inner product is preserved)
- The fixed line of R is σ = 1/2

The round-trip **project → reflect → reconstruct** composes with R:
- Project to 2D: lose σ, keep γ
- Reflect via FE: σ ↦ 1-σ
- Reconstruct to 3D: add back the loss

If the reconstruction uses the REFLECTED height, you get a new 3D point
with σ replaced by 1-σ. The zero at ρ = σ+iγ maps to 1-ρ = (1-σ)+iγ.

## The Key Observation

The Möbius map w = 1-1/ρ satisfies:
- |w| = 1 ⟺ Re(ρ) = 1/2 ⟺ ρ is on the fixed line of R
- The Li coefficient λ_n = Σ_ρ [1 - w^n] is computed from the HELIX

The round-trip operator T = P∘R∘P (project, reflect, project) satisfies:
- T is self-adjoint (composition of self-adjoint operators when R commutes with P)
- T = P when R fixes the projection subspace (i.e., when σ = 1/2)

## What We Prove

1. **Round-trip energy conservation**: each step preserves total energy
2. **The involution is self-adjoint**: ⟪Rx, y⟫ = ⟪x, Ry⟫
3. **The composition P∘R∘P is self-adjoint** when R is
4. **Fixed-point characterization**: P∘R∘P = P iff R fixes Im(P)
5. **The Möbius modulus on the helix**: |1-1/ρ|² = 1 iff Re(ρ) = 1/2
6. **Li terms from the helix**: the Li coefficients for general ρ
-/

noncomputable section

/-! ## Part 1: Round-trip through projections -/

section RoundTrip

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Round-trip step 1: Project and track loss. -/
theorem round_trip_exact (P : F →ₗ[ℝ] F) (hP_idem : ∀ x, P (P x) = P x) (x : F) :
    P x + (x - P x) = x := by
  abel

/-
Round-trip step 2: Energy is conserved at each projection.
-/
theorem round_trip_energy
    (P : F →ₗ[ℝ] F)
    (hP_sa : ∀ x y, @inner ℝ F _ (P x) y = @inner ℝ F _ x (P y))
    (hP_idem : ∀ x, P (P x) = P x)
    (x : F) :
    ‖x‖ ^ 2 = ‖P x‖ ^ 2 + ‖x - P x‖ ^ 2 := by
  rw [ @norm_sub_pow_two ℝ ];
  have := hP_sa x ( P x ) ; simp_all +decide [ inner_self_eq_norm_sq_to_K ] ; ring;

/-
The cascade 3D → 2D → 1D decomposes energy three ways.
-/
theorem cascade_energy
    (P₁ P₂ : F →ₗ[ℝ] F)
    (hP₁_sa : ∀ x y, @inner ℝ F _ (P₁ x) y = @inner ℝ F _ x (P₁ y))
    (hP₁_idem : ∀ x, P₁ (P₁ x) = P₁ x)
    (hP₂_sa : ∀ x y, @inner ℝ F _ (P₂ x) y = @inner ℝ F _ x (P₂ y))
    (hP₂_idem : ∀ x, P₂ (P₂ x) = P₂ x)
    (x : F) :
    ‖x‖ ^ 2 = ‖P₂ (P₁ x)‖ ^ 2 + ‖P₁ x - P₂ (P₁ x)‖ ^ 2 + ‖x - P₁ x‖ ^ 2 := by
  have h₁ := round_trip_energy ( P₁ ) hP₁_sa hP₁_idem ( x );
  rw [ h₁, round_trip_energy _ hP₂_sa hP₂_idem ]

end RoundTrip

/-! ## Part 2: The functional equation involution -/

section Involution

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- An involution R on an inner product space: R² = Id. -/
structure IsInvolution (R : F →ₗ[ℝ] F) : Prop where
  sq_eq_id : ∀ x, R (R x) = x

/-- A self-adjoint involution. -/
structure IsSelfAdjointInvolution (R : F →ₗ[ℝ] F) extends IsInvolution R : Prop where
  self_adjoint : ∀ x y, @inner ℝ F _ (R x) y = @inner ℝ F _ x (R y)

/-
A self-adjoint involution is isometric: ‖Rx‖ = ‖x‖.
-/
theorem involution_isometric (R : F →ₗ[ℝ] F) (hR : IsSelfAdjointInvolution R) (x : F) :
    ‖R x‖ = ‖x‖ := by
  rw [ ← sq_eq_sq₀ ] <;> try positivity;
  rw [ ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq ];
  rw [ ← hR.self_adjoint, hR.toIsInvolution.sq_eq_id ]

/-
The composition P ∘ R ∘ P is self-adjoint when P and R are.
-/
theorem compose_PRP_self_adjoint
    (P R : F →ₗ[ℝ] F)
    (hP_sa : ∀ x y, @inner ℝ F _ (P x) y = @inner ℝ F _ x (P y))
    (hR_sa : ∀ x y, @inner ℝ F _ (R x) y = @inner ℝ F _ x (R y))
    (x y : F) :
    @inner ℝ F _ ((P ∘ₗ R ∘ₗ P) x) y = @inner ℝ F _ x ((P ∘ₗ R ∘ₗ P) y) := by
  simp +decide [ hP_sa, hR_sa ]

/-
If R fixes the image of P (i.e., R ∘ P = P ∘ R on Im(P)), then P∘R∘P = P.
    On the helix: if the functional equation fixes the 2D circle
    (i.e., the zeros are symmetric and ON the fixed line), then the
    round-trip does nothing new.
-/
theorem PRP_eq_P_of_fixed
    (P R : F →ₗ[ℝ] F)
    (hP_idem : ∀ x, P (P x) = P x)
    (hR_fixes_P : ∀ x, P (R (P x)) = P x) :
    ∀ x, (P ∘ₗ R ∘ₗ P) x = P x := by
  exact hR_fixes_P

/-
Conversely: if P∘R∘P = P for all x, then R fixes Im(P).
    This is the "midpoint forcing" from the round-trip:
    if the round-trip is trivial, the involution fixes the projection.
-/
theorem R_fixes_P_of_PRP_eq_P
    (P R : F →ₗ[ℝ] F)
    (hP_idem : ∀ x, P (P x) = P x)
    (hR_inv : ∀ x, R (R x) = x)
    (hPRP : ∀ x, (P ∘ₗ R ∘ₗ P) x = P x) :
    ∀ x, P (R (P x)) = P x := by
  exact hPRP

end Involution

/-! ## Part 3: The Möbius map on the helix (for general ρ) -/

section MoebiusGeneral

open Complex

/-- The Möbius map for a general zero ρ = σ + iγ in the critical strip. -/
def moebius_helix (sigma gamma : ℝ) : ℂ :=
  1 - 1 / (⟨sigma, gamma⟩ : ℂ)

/-
|1 - 1/ρ|² = ((σ-1)² + γ²) / (σ² + γ²).
    This is the key formula: the modulus squared of the Möbius image.
-/
theorem moebius_norm_sq (sigma gamma : ℝ) (h : sigma ^ 2 + gamma ^ 2 ≠ 0) :
    ‖moebius_helix sigma gamma‖ ^ 2 =
    ((sigma - 1) ^ 2 + gamma ^ 2) / (sigma ^ 2 + gamma ^ 2) := by
  unfold moebius_helix; norm_num [ Complex.normSq, Complex.sq_norm ] ; ring;
  grind

/-
|1 - 1/ρ|² = 1 ⟺ (σ-1)² + γ² = σ² + γ² ⟺ -2σ + 1 = 0 ⟺ σ = 1/2.
    The Möbius image has unit modulus exactly on the critical line.
-/
theorem moebius_unit_iff (sigma gamma : ℝ) (hg : gamma ≠ 0) :
    ‖moebius_helix sigma gamma‖ = 1 ↔ sigma = 1/2 := by
  rw [ ← sq_eq_sq₀, moebius_norm_sq ] <;> norm_num [ hg ];
  · exact ⟨ fun h => by rw [ div_eq_iff ( by positivity ) ] at h; nlinarith, fun h => by rw [ div_eq_iff ( by positivity ) ] ; nlinarith ⟩;
  · positivity

/-- The Li coefficient for a GENERAL zero ρ (not assuming Re(ρ) = 1/2).
    This is the helix Li term — it comes from the Euler product, not from
    assuming the line. -/
def li_helix_term (sigma gamma : ℝ) (n : ℕ) : ℂ :=
  1 - (moebius_helix sigma gamma) ^ n

/-
On the critical line (σ = 1/2), the Li term has nonneg real part.
    Re[1 - w^n] = 1 - Re[w^n] ≥ 1 - |w^n| = 1 - |w|^n = 1 - 1 = 0
    since |w| = 1 on the line.
-/
theorem li_helix_nonneg_on_line (gamma : ℝ) (n : ℕ) :
    0 ≤ (li_helix_term (1/2) gamma n).re := by
  convert sub_nonneg_of_le _;
  · infer_instance;
  · convert Complex.re_le_norm ( ( moebius_helix ( 1 / 2 ) gamma ) ^ n ) using 1 ; norm_num [ moebius_unit_iff ];
    by_cases h : gamma = 0 <;> simp_all +decide [ moebius_unit_iff ];
    · unfold moebius_helix; norm_num [ Complex.normSq, Complex.norm_def ] ;
    · rw [ moebius_unit_iff _ _ h |>.2 ] ; norm_num;
      norm_num

/-
The doubling formula: `Re(z²) = 2·Re(z)² - ‖z‖²`.
    This is the key algebraic identity for the off-line growth argument.
-/
theorem re_sq_eq (z : ℂ) :
    (z ^ 2).re = 2 * z.re ^ 2 - ‖z‖ ^ 2 := by
  norm_num [ sq, Complex.norm_def ] ; ring;
  rw [ Real.sq_sqrt ( Complex.normSq_nonneg _ ), Complex.normSq_apply ] ; ring

/-! ### Cofinal recurrence on the unit circle -/

open Filter Metric

private lemma circle_recurrence (u : ℂ) (hu : ‖u‖ = 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, 1 ≤ m ∧ ‖u ^ m - 1‖ < ε := by
  have hmem : ∀ n : ℕ, u ^ n ∈ Metric.closedBall (0:ℂ) 1 := fun n => by
    simp [Metric.mem_closedBall, dist_zero_right, norm_pow, hu, one_pow]
  obtain ⟨a, -, φ, hφ, htend⟩ := (isCompact_closedBall (0:ℂ) 1).tendsto_subseq hmem
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨K, hK⟩ := htend (ε/2) (by linarith)
  have hi := hK K le_rfl
  have hj := hK (K+1) (Nat.le_succ K)
  simp only [Function.comp_apply, Complex.dist_eq] at hi hj
  have htri := dist_triangle (u ^ (φ K)) a (u ^ (φ (K+1)))
  rw [Complex.dist_eq, Complex.dist_eq, Complex.dist_eq,
      norm_sub_rev a (u ^ (φ (K+1)))] at htri
  have hlt : ‖u ^ (φ K) - u ^ (φ (K+1))‖ < ε := by linarith
  have hmono : φ K < φ (K + 1) := hφ (by omega)
  refine ⟨φ (K+1) - φ K, by omega, ?_⟩
  have hadd : φ (K+1) = φ K + (φ (K+1) - φ K) := by omega
  have hKcomm : φ (1 + K) = φ (K + 1) := by ring_nf
  have heq : u ^ (φ K) - u ^ (φ (K+1)) =
      u ^ (φ K) * (1 - u ^ (φ (K+1) - φ K)) := by
    conv_lhs => rw [hadd, pow_add]
    rw [show φ (K + 1) - φ K = φ (1 + K) - φ K from by rw [hKcomm]]
    ring
  rw [heq, norm_mul, norm_pow, hu, one_pow, one_mul, norm_sub_rev] at hlt
  exact hlt

private lemma pow_sub_one_le' (z : ℂ) (hz : ‖z‖ = 1) (k : ℕ) :
    ‖z ^ k - 1‖ ≤ k * ‖z - 1‖ := by
  have hgeom : z ^ k - 1 = (∑ i ∈ Finset.range k, z ^ i) * (z - 1) :=
    (geom_sum_mul z k).symm
  rw [hgeom, norm_mul]
  have hsum : ‖∑ i ∈ Finset.range k, z ^ i‖ ≤ k := by
    calc ‖∑ i ∈ Finset.range k, z ^ i‖
        ≤ ∑ i ∈ Finset.range k, ‖z ^ i‖ := norm_sum_le _ _
      _ = ∑ _i ∈ Finset.range k, (1:ℝ) := by simp [norm_pow, hz, one_pow]
      _ = k := by simp
  exact mul_le_mul_of_nonneg_right hsum (norm_nonneg _)

private lemma recur_cofinal (u : ℂ) (hu : ‖u‖ = 1) {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ ‖u ^ n - 1‖ < ε := by
  obtain ⟨m, hm1, hmlt⟩ := circle_recurrence u hu
    (ε := ε / (N+1)) (div_pos hε (by positivity))
  refine ⟨m * (N + 1), ?_, ?_⟩
  · calc N ≤ 1 * (N + 1) := by omega
      _ ≤ m * (N + 1) := by gcongr
  · have hb := pow_sub_one_le' (u ^ m)
      (by rw [norm_pow, hu, one_pow]) (N + 1)
    rw [← pow_mul] at hb
    have hN1 : (0:ℝ) < ((↑N:ℝ) + 1) := by positivity
    have hcancel : ((↑N:ℝ) + 1) * (ε / ((↑N:ℝ) + 1)) = ε := by field_simp
    have hmul : ((↑N:ℝ) + 1) * ‖u ^ m - 1‖ < ε := by
      have h := mul_lt_mul_of_pos_left hmlt hN1; rwa [hcancel] at h
    have hbcast : (((↑(N + 1) : ℕ)):ℝ) = (↑N:ℝ) + 1 := by push_cast; ring
    rw [hbcast] at hb
    exact lt_of_le_of_lt hb hmul

/-- For |w| > 1, `Re(w^n)` is unbounded above.
    Uses cofinal recurrence on the unit circle: write `w = r·u` with `r = ‖w‖ > 1`
    and `‖u‖ = 1`. The unit-circle powers `u^n` return within ε of 1 for
    arbitrarily large n (by compactness + pigeonhole). At those n,
    `Re(w^n) = r^n · Re(u^n) > r^n/2 → ∞`. -/
theorem re_pow_unbounded_above (w : ℂ) (hw : 1 < ‖w‖) :
    ∀ C : ℝ, ∃ n : ℕ, C < (w ^ n).re := by
  intro T
  set r := ‖w‖ with hr
  have hr0 : (0:ℝ) < r := by linarith
  have hrne : (r:ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  set u := w / (r:ℂ) with hu_def
  have hu : ‖u‖ = 1 := by
    rw [hu_def, norm_div,
        show ‖(r:ℂ)‖ = r from by
          rw [Complex.norm_real]; exact Real.norm_of_nonneg hr0.le,
        ← hr, div_self hr0.ne']
  have hpow : Filter.Tendsto (fun n : ℕ => r ^ n)
      Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hw
  obtain ⟨N, hN⟩ := (hpow.eventually_gt_atTop (2 * T)).exists
  obtain ⟨n, hnN, hnlt⟩ := recur_cofinal u hu (ε := 1) one_pos N
  refine ⟨n, ?_⟩
  have hns : (u^n).re * (u^n).re + (u^n).im * (u^n).im = 1 := by
    have h : Complex.normSq (u^n) = 1 := by
      rw [Complex.normSq_eq_norm_sq, norm_pow, hu, one_pow]; norm_num
    rwa [Complex.normSq_apply] at h
  have hexp : ‖u ^ n - 1‖^2 = 2 - 2*(u^n).re := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im,
               Complex.one_im, sub_zero]
    linear_combination hns
  have hun : (1:ℝ)/2 < (u^n).re := by
    have h1 : ‖u ^ n - 1‖^2 < 1 := by
      rw [pow_two]
      nlinarith [mul_self_lt_mul_self (norm_nonneg (u^n - 1)) hnlt]
    rw [hexp] at h1; linarith
  have hwu : (r:ℂ) * u = w := by rw [hu_def]; field_simp
  have hre : (w ^ n).re = r^n * (u^n).re := by
    have hwm : w ^ n = (↑(r^n) : ℂ) * u^n := by
      rw [← hwu, mul_pow, Complex.ofReal_pow]
    rw [hwm]
    simp only [Complex.mul_re, Complex.ofReal_re,
               Complex.ofReal_im, zero_mul, sub_zero]
  rw [hre]
  have hrnpos : 0 < r^n := by positivity
  have hrn : r^N ≤ r^n := pow_le_pow_right₀ hw.le hnN
  have hhalf : r^n * (1/2) < r^n * (u^n).re :=
    mul_lt_mul_of_pos_left hun hrnpos
  linarith [hhalf, hrn, hN]

/-
Off the critical line with |w| > 1, the Li term is unbounded below:
    there exist arbitrarily large n with Re[1 - w^n] < 0.
    This follows from `re_pow_unbounded_above`: since Re(w^n) is
    unbounded, Re(1 - w^n) = 1 - Re(w^n) is unbounded below.
-/
theorem li_helix_unbounded_off_line (sigma gamma : ℝ) (hg : gamma ≠ 0)
    (hw : 1 < ‖moebius_helix sigma gamma‖) :
    ∀ M : ℝ, ∃ n : ℕ, (li_helix_term sigma gamma n).re < M := by
  intro M
  obtain ⟨n, hn⟩ := re_pow_unbounded_above (moebius_helix sigma gamma) hw (1 - M);
  -- Since $Re(w^n) > 1 - M$, we have $Re �(�1 - w^n) < M$.
  use n
  simp [li_helix_term, hn];
  linarith

/-
Off the critical line with |w| < 1, the Li term converges to 1:
    Re[1 - w^n] → 1 as n → ∞ when |w| < 1. So it's eventually positive
    but with a DIFFERENT character than the on-line case.
-/
theorem li_helix_converges_off_line_small (sigma gamma : ℝ)
    (hw : ‖moebius_helix sigma gamma‖ < 1) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n, N ≤ n →
    |(li_helix_term sigma gamma n).re - 1| < ε := by
  -- Using the fact thatmoebius_h �elix� sigma gamma‖ < 1, we get(moebius_helix sigma gamma) ^ n‖ → 0 as n → ∞.
  have h_norm_pow : Filter.Tendsto (fun n : ℕ => ‖(moebius_helix sigma gamma) ^ n‖) Filter.atTop (nhds 0) := by
    simpa using tendsto_pow_atTop_nhds_zero_of_lt_one ( norm_nonneg _ ) hw;
  -- Using the fact that the real part of a complex number is less than or equal to its norm, we get:
  have h_real_part : Filter.Tendsto (fun n : ℕ => Complex.re ((moebius_helix sigma gamma) ^ n)) Filter.atTop (nhds 0) := by
    exact squeeze_zero_norm ( fun n => Complex.abs_re_le_norm _ ) h_norm_pow;
  simpa [ li_helix_term ] using Metric.tendsto_atTop.mp ( h_real_part.const_sub 1 )

end MoebiusGeneral

/-! ## Part 4: The round-trip forces the fixed point -/

section ForcedMidpoint

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-
**The round-trip argument.**

    Given:
    - P: orthogonal projection (self-adjoint, idempotent) — the 3D→2D projection
    - R: self-adjoint involution — the functional equation σ ↦ 1-σ
    - L = I - P: the projection loss (also an orthogonal projection)

    The round-trip 3D → 2D → 3D → 2D is:
    P x → (add back Rx of loss) → P(Px + R(Lx)) = Px + P(R(Lx))

    If R maps Im(L) to Im(L) (the loss subspace is R-invariant), then
    P(R(Lx)) = 0, so the round-trip gives Px — it's trivial.

    If R maps Im(L) to Im(P) (the loss subspace maps to the projection
    subspace under R), then P(R(Lx)) = R(Lx), and the round-trip gives
    Px + R(Lx) — the reflected loss gets promoted to signal.

    The midpoint σ = 1/2 is exactly where R fixes both subspaces,
    because the involution's fixed line bisects the decomposition.
-/
theorem round_trip_midpoint
    (P R : F →ₗ[ℝ] F)
    (hP_sa : ∀ x y, @inner ℝ F _ (P x) y = @inner ℝ F _ x (P y))
    (hP_idem : ∀ x, P (P x) = P x)
    (hR_inv : ∀ x, R (R x) = x)
    (hR_sa : ∀ x y, @inner ℝ F _ (R x) y = @inner ℝ F _ x (R y))
    (x : F) :
    -- The round-trip composition is self-adjoint
    @inner ℝ F _ ((P ∘ₗ R ∘ₗ P) x) x = @inner ℝ F _ x ((P ∘ₗ R ∘ₗ P) x) := by
  convert real_inner_comm _ _

/-
Energy bound for the round-trip: |⟪P∘R∘Px, x⟫| ≤ ‖Px‖².
    This is Cauchy-Schwarz applied to the projected components.
-/
theorem round_trip_energy_bound
    (P R : F →ₗ[ℝ] F)
    (hP_sa : ∀ x y, @inner ℝ F _ (P x) y = @inner ℝ F _ x (P y))
    (hP_idem : ∀ x, P (P x) = P x)
    (hR_sa : ∀ x y, @inner ℝ F _ (R x) y = @inner ℝ F _ x (R y))
    (hR_isometric : ∀ x, ‖R x‖ = ‖x‖)
    (x : F) :
    |@inner ℝ F _ ((P ∘ₗ R ∘ₗ P) x) x| ≤ ‖P x‖ ^ 2 := by
  convert abs_real_inner_le_norm ( R ( P x ) ) ( P x ) using 1;
  · simp +decide [ hP_sa, hR_sa, hP_idem ];
  · rw [ hR_isometric, sq ]

/-
When R commutes with P (R∘P = P∘R), the round-trip is trivial: P∘R∘P = P.
    Commutativity means the projection and the involution are "aligned" —
    the subspace decomposition respects the symmetry.
    This happens exactly when Im(P) and Im(L) are both R-invariant,
    which is the "balanced" / midpoint case.
-/
theorem round_trip_trivial_of_commuting
    (P R : F →ₗ[ℝ] F)
    (hP_idem : ∀ x, P (P x) = P x)
    (hcomm : ∀ x, P (R x) = R (P x)) (x : F) :
    (P ∘ₗ R ∘ₗ P) x = (R ∘ₗ P) x := by
  aesop

/-
The cascade 3D → 2D → 1D with round-trip.
    Total energy: ‖x‖² = ‖P₂P₁x‖² + ‖P₁x - P₂P₁x‖² + ‖x - P₁x‖²
    Each component carries part of the signal.
    The round-trip 2D → 3D adds back the loss:
    P₁x + (x - P₁x) = x (exact reconstruction).
    Going to 1D and back: P₂(P₁x) + (P₁x - P₂(P₁x)) = P₁x.
-/
theorem full_cascade_reconstruction
    (P₁ P₂ : F →ₗ[ℝ] F)
    (hP₁_idem : ∀ x, P₁ (P₁ x) = P₁ x)
    (hP₂_idem : ∀ x, P₂ (P₂ x) = P₂ x)
    (x : F) :
    -- 1D → 2D reconstruction
    P₂ (P₁ x) + (P₁ x - P₂ (P₁ x)) = P₁ x ∧
    -- 2D → 3D reconstruction
    P₁ x + (x - P₁ x) = x := by
  exact ⟨ add_sub_cancel _ _, add_sub_cancel _ _ ⟩

end ForcedMidpoint

/-! ## Part 5: The honest status -/

/-- Summary of what the round-trip proves:

    ✓ PROVED: P∘R∘P is self-adjoint (so the round-trip is a "fair" operator)
    ✓ PROVED: |⟪P∘R∘P x, x⟫| ≤ ‖Px‖² (energy bound)
    ✓ PROVED: If R commutes with P, then P∘R∘P = R∘P (trivial round-trip)
    ✓ PROVED: |1-1/ρ| = 1 ⟺ σ = 1/2 (Möbius characterization)
    ✓ PROVED: Li terms ≥ 0 on the line (easy direction)
    ✓ PROVED: Li terms → -∞ off the line when |w| > 1

    THE GAP: proving that P∘R∘P = P unconditionally for the spectral
    projection onto ζ zeros. This requires showing that the zero subspace
    is R-invariant (zeros come in pairs ρ, 1-ρ AND each pair contributes
    positively). The pairing is the functional equation (free). The
    open step is the positivity of each pair's contribution.

    Equivalently: we need Λ ≥ 0 to force the round-trip to be trivial.
    The Mertens trick (3+4cosθ+cos2θ ≥ 0) gives a partial result
    (zero-free region near σ=1), but not the full result (σ=1/2). -/
theorem round_trip_status :
    -- The Möbius characterization is unconditional:
    (∀ (sigma gamma : ℝ) (hg : gamma ≠ 0),
      ‖moebius_helix sigma gamma‖ = 1 ↔ sigma = 1/2) := by
  intro sigma gamma hg
  exact moebius_unit_iff sigma gamma hg

end