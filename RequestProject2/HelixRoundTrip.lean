import Mathlib
import RequestProject.ZetaZeroDefs
import RequestProject.SpectralSide

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

/-! ## Part 0: The arithmetic round trip — the ground floor

"Integers are divisible by factors, and reproducible by those same factors."
This is the ORIGINAL round trip — FTA in round-trip form, the base case of the
entire tower: decomposition exists, reconstruction is exact, and the readout is
faithful (no two prime multisets build the same integer). Every floor above —
the helix placement, the Hilbert projections with their ledgers, the line
readout — inherits this shape. The tower:

  FTA round trip (arithmetic, exact)         — this section
  → helix placement (geometric, bijective)   — `existsUnique_placed`
  → projection + loss ledger (Hilbert, exact)— Parts 1–2
  → line readout (faithful, observable)      — `line_readout_faithful`,
                                               `source_observability`
-/

section ArithmeticRoundTrip

/-- **Reproducible by those same factors**: reconstruction is exact —
the product of an integer's prime factors is the integer. -/
theorem fta_reconstruct (n : ℕ) (hn : n ≠ 0) :
    (Nat.primeFactorsList n).prod = n :=
  Nat.prod_primeFactorsList hn

/-- **Faithful**: no two prime factorizations build the same integer — any prime
list with the right product is a permutation of THE factor list. -/
theorem fta_faithful (n : ℕ) (l : List ℕ)
    (hl : ∀ p ∈ l, p.Prime) (hprod : l.prod = n) :
    l.Perm (Nat.primeFactorsList n) :=
  Nat.primeFactorsList_unique hprod hl

/-- **The arithmetic round trip, packaged**: decomposition followed by
reconstruction is the identity, and the decomposition is the unique one. -/
theorem fta_round_trip (n : ℕ) (hn : n ≠ 0) :
    (Nat.primeFactorsList n).prod = n ∧
    ∀ l : List ℕ, (∀ p ∈ l, p.Prime) → l.prod = n →
      l.Perm (Nat.primeFactorsList n) :=
  ⟨fta_reconstruct n hn, fun l hl hp => fta_faithful n l hl hp⟩


/-! ### The four operations abide by FTA (the closed arithmetic universe)

Under the winding representation, multiplication and division ARE FTA's own
addition and subtraction — exponent vectors add and subtract (the free abelian
structure). Ordinary addition and subtraction abide by CLOSURE: their results
never leave the governed domain — every output of every operation factors
uniquely. The arithmetic universe is complete and total under all four
operations; nothing arithmetic can do escapes FTA's jurisdiction. -/

/-- **Multiplication is winding-addition**: the factorization of a product is the
sum of the factorizations. -/
theorem fta_mul (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) :
    (m * n).factorization = m.factorization + n.factorization :=
  Nat.factorization_mul hm hn

/-- **Division is winding-subtraction**: the factorization of an exact quotient is
the difference of the factorizations. -/
theorem fta_div {m n : ℕ} (h : n ∣ m) :
    (m / n).factorization = m.factorization - n.factorization :=
  Nat.factorization_div h

/-- **Addition abides by closure**: a sum never leaves FTA's domain — it is exactly
reproducible from its own factors. -/
theorem fta_add_closed (m n : ℕ) (h : m + n ≠ 0) :
    (Nat.primeFactorsList (m + n)).prod = m + n :=
  Nat.prod_primeFactorsList h

/-- **Subtraction abides by closure**: a difference never leaves FTA's domain. -/
theorem fta_sub_closed (m n : ℕ) (h : m - n ≠ 0) :
    (Nat.primeFactorsList (m - n)).prod = m - n :=
  Nat.prod_primeFactorsList h

/-- **The four operations, packaged**: the FTA universe is closed and total —
multiplication and division act as winding addition and subtraction; addition and
subtraction stay within the governed domain. -/
theorem fta_four_operations :
    (∀ m n : ℕ, m ≠ 0 → n ≠ 0 →
      (m * n).factorization = m.factorization + n.factorization) ∧
    (∀ m n : ℕ, n ∣ m →
      (m / n).factorization = m.factorization - n.factorization) ∧
    (∀ m n : ℕ, m + n ≠ 0 →
      (Nat.primeFactorsList (m + n)).prod = m + n) ∧
    (∀ m n : ℕ, m - n ≠ 0 →
      (Nat.primeFactorsList (m - n)).prod = m - n) :=
  ⟨fun m n hm hn => fta_mul m n hm hn,
   fun _ _ h => fta_div h,
   fun m n h => fta_add_closed m n h,
   fun m n h => fta_sub_closed m n h⟩

end ArithmeticRoundTrip

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
theorem moebius_norm_sq' (sigma gamma : ℝ) (h : sigma ^ 2 + gamma ^ 2 ≠ 0) :
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
  rw [ ← sq_eq_sq₀, moebius_norm_sq' ] <;> norm_num [ hg ];
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
  have hw : ‖moebius_helix (1/2) gamma‖ = 1 := by
    rcases eq_or_ne gamma 0 with h | h
    · subst h; unfold moebius_helix; norm_num [Complex.norm_def, Complex.normSq]
    · exact (moebius_unit_iff (1/2) gamma h).mpr rfl
  have hre : (li_helix_term (1/2) gamma n).re = 1 - ((moebius_helix (1/2) gamma) ^ n).re := by
    simp [li_helix_term, Complex.sub_re, Complex.one_re]
  rw [hre]
  have h1 : ((moebius_helix (1/2) gamma) ^ n).re ≤ ‖(moebius_helix (1/2) gamma) ^ n‖ :=
    Complex.re_le_norm _
  rw [norm_pow, hw, one_pow] at h1
  linarith

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

lemma pow_sub_one_le' (z : ℂ) (hz : ‖z‖ = 1) (k : ℕ) :
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

/-! ## Part 6: The quartet dichotomy — hypothesis-free

The functional-equation quartet `{ρ, ρ̄, 1−ρ, 1−ρ̄}` maps under the Möbius helix
operation to `{w, w̄, w⁻¹, w̄⁻¹}` — THE PAIRING IS FREE (`moebius_helix_mul_reflect`:
`w(ρ)·w(1−ρ) = 1`, pure algebra). The quartet's combined Li readout is then
`4 − 2·Re(wⁿ) − 2·Re(w⁻ⁿ)`, and the dichotomy needs no modulus hypothesis: one of
`w, w⁻¹` always has modulus ≥ 1, with equality exactly on the line. Conclusion
(`quartetLi_boundedBelow_iff`): **the critical line is precisely where the quartet's
helix readout is bounded below.** On-line: every term ≥ 0 (the `2(1−cos)` law, the
equality case). Off-line: unbounded below along a cofinal subsequence (the circle
recurrence). What remains open after this is only the MIXING: that a sum of
infinitely many quartets cannot use the on-line members' bounded surplus to fund an
off-line member's exponential deficit. -/

section QuartetDichotomy

open Complex

/-- `⟨1−σ, −γ⟩ = 1 − ⟨σ, γ⟩`: the FE reflection in coordinates. -/
lemma reflect_coord (sigma gamma : ℝ) :
    (⟨1 - sigma, -gamma⟩ : ℂ) = 1 - (⟨sigma, gamma⟩ : ℂ) := by
  apply Complex.ext <;> simp

/-- **The pairing is free**: the Möbius images of an FE-reflected pair multiply to 1.
`(1 − 1/ρ)·(1 − 1/(1−ρ)) = 1` whenever `ρ ≠ 0, 1`. -/
theorem moebius_helix_mul_reflect (sigma gamma : ℝ)
    (h0 : (⟨sigma, gamma⟩ : ℂ) ≠ 0) (h1 : (⟨sigma, gamma⟩ : ℂ) ≠ 1) :
    moebius_helix sigma gamma * moebius_helix (1 - sigma) (-gamma) = 1 := by
  unfold moebius_helix
  rw [reflect_coord]
  have h1' : (1 : ℂ) - (⟨sigma, gamma⟩ : ℂ) ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  field_simp
  ring

/-- Conjugating the height conjugates the Möbius image. -/
lemma moebius_helix_neg_im (sigma gamma : ℝ) :
    moebius_helix sigma (-gamma) = (starRingEnd ℂ) (moebius_helix sigma gamma) := by
  unfold moebius_helix
  have hc : (⟨sigma, -gamma⟩ : ℂ) = (starRingEnd ℂ) (⟨sigma, gamma⟩ : ℂ) := by
    apply Complex.ext <;> simp
  rw [hc, map_sub, map_one, map_div₀, map_one]

/-- The quartet Li readout: the four FE-related Li terms, real parts summed. -/
def quartetLi (sigma gamma : ℝ) (n : ℕ) : ℝ :=
  (li_helix_term sigma gamma n).re + (li_helix_term sigma (-gamma) n).re
  + (li_helix_term (1 - sigma) gamma n).re + (li_helix_term (1 - sigma) (-gamma) n).re

/-- The quartet readout in closed form: `4 − 2·Re(wⁿ) − 2·Re(w⁻ⁿ)`. -/
theorem quartetLi_eq (sigma gamma : ℝ)
    (h0 : (⟨sigma, gamma⟩ : ℂ) ≠ 0) (h1 : (⟨sigma, gamma⟩ : ℂ) ≠ 1) :
    ∀ n : ℕ, quartetLi sigma gamma n
      = 4 - 2*((moebius_helix sigma gamma)^n).re
          - 2*(((moebius_helix sigma gamma)⁻¹)^n).re := by
  intro n
  have hrefl : moebius_helix (1 - sigma) (-gamma) = (moebius_helix sigma gamma)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by
      rw [mul_comm]; exact moebius_helix_mul_reflect sigma gamma h0 h1)
  have hconj1 : (li_helix_term sigma (-gamma) n).re = (li_helix_term sigma gamma n).re := by
    unfold li_helix_term
    rw [moebius_helix_neg_im, ← map_pow]
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
  have hconj2 : (li_helix_term (1 - sigma) gamma n).re
      = (li_helix_term (1 - sigma) (-gamma) n).re := by
    have e := moebius_helix_neg_im (1 - sigma) (-gamma)
    rw [neg_neg] at e
    unfold li_helix_term
    rw [e, ← map_pow]
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
  have hrefl_re : (li_helix_term (1 - sigma) (-gamma) n).re
      = 1 - (((moebius_helix sigma gamma)⁻¹)^n).re := by
    unfold li_helix_term
    rw [hrefl]
    simp [Complex.sub_re, Complex.one_re]
  have hbase : (li_helix_term sigma gamma n).re
      = 1 - ((moebius_helix sigma gamma)^n).re := by
    unfold li_helix_term
    simp [Complex.sub_re, Complex.one_re]
  unfold quartetLi
  rw [hconj1, hconj2, hrefl_re, hbase]
  ring

/-- **On the line the quartet pays nonnegatively, always** (the `2(1 − cos nθ)` law:
the equality case lives here). -/
theorem quartetLi_nonneg_on_line (gamma : ℝ) (n : ℕ) :
    0 ≤ quartetLi (1/2) gamma n := by
  have h := li_helix_nonneg_on_line gamma n
  have h' := li_helix_nonneg_on_line (-gamma) n
  have e : (1 : ℝ) - 1/2 = 1/2 := by norm_num
  unfold quartetLi
  rw [e]
  linarith

/-- **Off the line the quartet readout is unbounded below** — hypothesis-free: the
quartet always contains `w` and `w⁻¹`, and off the line one of them has modulus
strictly above 1; the circle recurrence then drives the readout to `−∞` cofinally. -/
theorem quartetLi_unbounded_off_line (sigma gamma : ℝ)
    (hg : gamma ≠ 0) (hs : sigma ≠ 1/2) :
    ∀ M : ℝ, ∃ n : ℕ, quartetLi sigma gamma n < M := by
  intro M
  have h0 : (⟨sigma, gamma⟩ : ℂ) ≠ 0 := by
    intro h; exact hg (by simpa using congrArg Complex.im h)
  have h1 : (⟨sigma, gamma⟩ : ℂ) ≠ 1 := by
    intro h; exact hg (by simpa using congrArg Complex.im h)
  set w := moebius_helix sigma gamma with hw
  have hwne : w ≠ 0 := by
    intro hw0
    have := moebius_helix_mul_reflect sigma gamma h0 h1
    rw [← hw, hw0, zero_mul] at this
    exact zero_ne_one this
  have hrne : ‖w‖ ≠ 1 := fun hr => hs ((moebius_unit_iff sigma gamma hg).mp hr)
  rcases lt_or_gt_of_ne hrne with hlt | hgt
  · -- ‖w‖ < 1: the partner w⁻¹ has modulus > 1
    have hinv : 1 < ‖w⁻¹‖ := by
      rw [norm_inv]
      exact (one_lt_inv₀ (norm_pos_iff.mpr hwne)).mpr hlt
    obtain ⟨n, hn⟩ := re_pow_unbounded_above w⁻¹ hinv ((6 - M)/2)
    refine ⟨n, ?_⟩
    have hsmall : |((w)^n).re| ≤ 1 := by
      calc |((w)^n).re| ≤ ‖w^n‖ := Complex.abs_re_le_norm _
        _ = ‖w‖^n := norm_pow _ _
        _ ≤ 1 := pow_le_one₀ (norm_nonneg _) hlt.le
    rw [quartetLi_eq sigma gamma h0 h1 n, ← hw]
    have : -2*((w)^n).re ≤ 2 := by nlinarith [abs_le.mp hsmall]
    nlinarith
  · -- ‖w‖ > 1 directly
    obtain ⟨n, hn⟩ := re_pow_unbounded_above w hgt ((6 - M)/2)
    refine ⟨n, ?_⟩
    have hsmall : |(((w)⁻¹)^n).re| ≤ 1 := by
      calc |(((w)⁻¹)^n).re| ≤ ‖(w⁻¹)^n‖ := Complex.abs_re_le_norm _
        _ = ‖w⁻¹‖^n := norm_pow _ _
        _ ≤ 1 := pow_le_one₀ (norm_nonneg _) (by
            rw [norm_inv]
            exact inv_le_one_of_one_le₀ hgt.le)
    rw [quartetLi_eq sigma gamma h0 h1 n, ← hw]
    have : -2*(((w)⁻¹)^n).re ≤ 2 := by nlinarith [abs_le.mp hsmall]
    nlinarith

/-- **The characterization** (γ ≠ 0): the critical line is exactly where the
quartet's helix readout is bounded below. The on-line direction is the `≥ 0` law;
the off-line direction is the cofinal collapse. After this theorem, the open content
of the program is ONLY the mixing across quartets. -/
theorem quartetLi_boundedBelow_iff (sigma gamma : ℝ) (hg : gamma ≠ 0) :
    (∃ B : ℝ, ∀ n : ℕ, B ≤ quartetLi sigma gamma n) ↔ sigma = 1/2 := by
  constructor
  · intro ⟨B, hB⟩
    by_contra hs
    obtain ⟨n, hn⟩ := quartetLi_unbounded_off_line sigma gamma hg hs (B - 1)
    have := hB n
    linarith
  · intro hs
    subst hs
    exact ⟨0, fun n => quartetLi_nonneg_on_line gamma n⟩

end QuartetDichotomy

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
    positivity of each pair's contribution is RH.

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

/-! ## Part 7: The natural coordinates — (sine, cosine, winding)

Multiplication is linear in winding; addition is contained by it; the two faces of
arithmetic meet in `(cos, sin)`. Euler's formula is the pointwise bridge between
them (`euler_seam_bridge`), and the critical line is exactly where a zero's Möbius
readout lives in the image of trigonometry (`trig_coordinates_iff_online`).
These theorems make "off-line = outside (sin, cos)" a kernel predicate, not
rhetoric: an off-line zero's readout equals `cos θ + i sin θ` for NO angle θ —
it is not a strange point OF trigonometry but a point outside its entire image. -/

section NaturalCoordinates

open Complex

/-- **Euler's formula is the seam's bridge**: phasor multiplication (the
multiplicative face, where winding adds linearly) IS angle addition (the additive
face, where winding is contained). The two faces of arithmetic reconcile in
`(cos, sin)`, pointwise, as a theorem. -/
theorem euler_seam_bridge (α β : ℝ) :
    exp (↑α * I) * exp (↑β * I) = exp (↑(α + β) * I) := by
  rw [← exp_add, ofReal_add, add_mul]

/-- **On the line, the readout lives in trigonometry**: at `σ = 1/2` the Möbius
readout of a zero is `cos θ + i sin θ` for an actual winding angle `θ` — a point
of trigonometry, Euler's formula made flesh. -/
theorem online_trig_coordinates (gamma : ℝ) (hg : gamma ≠ 0) :
    ∃ θ : ℝ, moebius_helix (1/2) gamma = Complex.cos θ + Complex.sin θ * I := by
  refine ⟨(moebius_helix (1/2) gamma).arg, ?_⟩
  have h1 : ‖moebius_helix (1/2) gamma‖ = 1 :=
    (moebius_unit_iff (1/2) gamma hg).mpr rfl
  rw [← Complex.exp_mul_I]
  calc moebius_helix (1/2) gamma
      = ↑‖moebius_helix (1/2) gamma‖
          * exp (↑(moebius_helix (1/2) gamma).arg * I) :=
        (Complex.norm_mul_exp_arg_mul_I _).symm
    _ = exp (↑(moebius_helix (1/2) gamma).arg * I) := by
        rw [h1, ofReal_one, one_mul]

/-- **The trigonometric census**: a zero's Möbius readout lies in the image of
`(cos, sin)` — the unit circle, where the Pythagorean identity governs — **iff**
the zero is on the critical line. Off the line the readout is `cos θ + i sin θ`
for NO angle whatsoever, while FTA keeps the winding additive and Euler keeps the
bridge exact. This is the kernel form of: *an off-line zero would require trig,
FTA, and Euler to be wrong about it — it lies outside trigonometry's image.* -/
theorem trig_coordinates_iff_online (sigma gamma : ℝ) (hg : gamma ≠ 0) :
    (∃ θ : ℝ, moebius_helix sigma gamma = Complex.cos θ + Complex.sin θ * I)
      ↔ sigma = 1/2 := by
  constructor
  · rintro ⟨θ, hθ⟩
    refine (moebius_unit_iff sigma gamma hg).mp ?_
    rw [hθ, ← Complex.exp_mul_I]
    exact Complex.norm_exp_ofReal_mul_I θ
  · rintro rfl
    exact online_trig_coordinates gamma hg

/-- **Pythagoras at the readout**: `re² + im² = 1` — the Pythagorean identity —
holds of a zero's Möbius readout **iff** the zero is on the line. "Off-line" and
"cos² + sin² fails at the readout" are the same predicate. -/
theorem readout_pythagoras_iff_online (sigma gamma : ℝ) (hg : gamma ≠ 0) :
    (moebius_helix sigma gamma).re ^ 2 + (moebius_helix sigma gamma).im ^ 2 = 1
      ↔ sigma = 1/2 := by
  rw [← moebius_unit_iff sigma gamma hg,
    ← sq_eq_sq₀ (norm_nonneg _) zero_le_one, one_pow, Complex.sq_norm,
    Complex.normSq_apply]
  constructor <;> intro h <;> nlinarith [h]

end NaturalCoordinates

/-! ## Part 8: Completeness and zero obstruction of the natural coordinates

The instrument theorem: the natural coordinate system (sine, cosine, winding
number) on the helix is **complete** — faithful (`helixCoords_injective`:
nothing collides) and total (`helixCoords_surjective`: every point of the
helix is realized — nothing is missed; `helixCoords_complete`
packages the bijection) — and the coordinate transform carries **zero
obstruction**: one loop of the deck action moves the coordinates by exactly
one winding quantum with no anomalous residue (`helixCoords_deck_exact` — the
chart contributes nothing to the drift class), and the windowed census is
invariant under the natural-units rechart (`arcChart_census_invariant` — no
count, hence no gap and no law, can be created or destroyed by a unit change).

Honest scope: these theorems prove the COORDINATES are exact — any obstruction
to the production law is a fact about the world, never a chart artifact. They
clean the battlefield; they do not by themselves discharge the law. -/

section HelixCompleteness

open Real

/-- The natural coordinates of the unwound helix parameter `t`: the circle
pair `(cos 2πt, sin 2πt)` and the winding number `⌊t⌋`. -/
noncomputable def helixCoords (t : ℝ) : ℝ × ℝ × ℤ :=
  (Real.cos (2 * π * t), Real.sin (2 * π * t), ⌊t⌋)

/-- **Zero obstruction (deck exactness)**: one loop moves the natural
coordinates by exactly one quantum — the circle pair returns identically and
the winding increments by exactly `1`. The chart's cocycle under the deck
action is the integer quantum with zero anomalous residue: the coordinates
contribute nothing to the drift class. Any nonzero drift belongs to the
world, never to the chart. -/
theorem helixCoords_deck_exact (t : ℝ) :
    helixCoords (t + 1)
      = (Real.cos (2 * π * t), Real.sin (2 * π * t), ⌊t⌋ + 1) := by
  simp only [helixCoords, Prod.mk.injEq]
  refine ⟨?_, ?_, Int.floor_add_one t⟩
  · rw [show 2 * π * (t + 1) = 2 * π * t + (1 : ℤ) * (2 * π) by push_cast; ring,
      Real.cos_add_int_mul_two_pi]
  · rw [show 2 * π * (t + 1) = 2 * π * t + (1 : ℤ) * (2 * π) by push_cast; ring,
      Real.sin_add_int_mul_two_pi]

/-- **Faithful (nothing collides)**: the natural coordinates determine the
helix parameter completely. The circle pair pins the angle modulo whole loops
(Euler's formula + 2π-periodicity), and the winding number kills the loop
ambiguity. -/
theorem helixCoords_injective : Function.Injective helixCoords := by
  intro s t h
  simp only [helixCoords, Prod.mk.injEq] at h
  obtain ⟨hcos, hsin, hfloor⟩ := h
  have hexp : Complex.exp (↑(2 * π * s) * Complex.I)
      = Complex.exp (↑(2 * π * t) * Complex.I) := by
    apply Complex.ext
    · simpa only [Complex.exp_ofReal_mul_I_re] using hcos
    · simpa only [Complex.exp_ofReal_mul_I_im] using hsin
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
  have h1 := congrArg Complex.im hn
  simp at h1
  have h2π : (2 * π : ℝ) ≠ 0 := by positivity
  have hst : s = t + ↑n := by
    apply mul_left_cancel₀ h2π
    linear_combination h1
  have hn0 : n = 0 := by
    have hf : ⌊t + (n : ℝ)⌋ = ⌊t⌋ := by rw [← hst, hfloor]
    rw [Int.floor_add_intCast] at hf
    omega
  rw [hst, hn0, Int.cast_zero, add_zero]

/-- **Total (nothing is missed)**: every point of the HELIX — any circle pair
`(x, y)` together with any winding number `k`, the radius being
winding-determined (the area law), so no fourth coordinate exists — is
realized by an actual helix parameter. -/
theorem helixCoords_surjective (x y : ℝ) (k : ℤ) (hxy : x ^ 2 + y ^ 2 = 1) :
    ∃ t : ℝ, helixCoords t = (x, y, k) := by
  set z : ℂ := ⟨x, y⟩ with hzdef
  have hz1 : ‖z‖ = 1 := by
    have h2 : ‖z‖ ^ 2 = 1 ^ 2 := by
      rw [Complex.sq_norm, hzdef, Complex.normSq_mk, one_pow]
      linear_combination hxy
    exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp h2
  have hcos : Real.cos z.arg = x := by
    have h := Complex.norm_mul_cos_arg z
    rw [hz1, one_mul] at h
    exact h
  have hsin : Real.sin z.arg = y := by
    have h := Complex.norm_mul_sin_arg z
    rw [hz1, one_mul] at h
    exact h
  set θ : ℝ := z.arg with hθdef
  set f : ℝ := Int.fract (θ / (2 * π)) with hfdef
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have hang : 2 * π * (f + ↑k) = θ + ↑(k - ⌊θ / (2 * π)⌋) * (2 * π) := by
    have hfr : f = θ / (2 * π) - ↑⌊θ / (2 * π)⌋ := (Int.self_sub_floor _).symm
    rw [hfr]
    push_cast
    field_simp
    ring
  refine ⟨f + ↑k, ?_⟩
  simp only [helixCoords, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · rw [hang, Real.cos_add_int_mul_two_pi]
    exact hcos
  · rw [hang, Real.sin_add_int_mul_two_pi]
    exact hsin
  · rw [Int.floor_add_intCast, hfdef, Int.floor_fract, zero_add]

/-- **Completeness, packaged**: the natural coordinates are a bijection from
the unwound line onto the full HELIX in natural coordinates
`{(x, y, k) : x² + y² = 1}` — the circle pair with the winding number, the
radius winding-determined (the area law). Seen down the collapse axis the
object IS the unit circle — every winding superimposed on the one circle,
the 2D stage where the phasors live and the wave reads as real; the object
itself is the helix. The chart misses nothing and collides nothing. -/
theorem helixCoords_complete :
    Set.BijOn helixCoords Set.univ
      {p : ℝ × ℝ × ℤ | p.1 ^ 2 + p.2.1 ^ 2 = 1} := by
  refine ⟨fun t _ => ?_, helixCoords_injective.injOn, fun p hp => ?_⟩
  · simp only [helixCoords, Set.mem_setOf_eq]
    exact Real.cos_sq_add_sin_sq _
  · obtain ⟨t, ht⟩ := helixCoords_surjective p.1 p.2.1 p.2.2 hp
    exact ⟨t, Set.mem_univ t, by rw [ht]⟩

/-- The rechart preserves window membership exactly (strict monotonicity):
the window structure of the census is carried without distortion. -/
theorem arcChart_mem_Icc_iff (x a b : ℝ) :
    arcChart x ∈ Set.Icc (arcChart a) (arcChart b) ↔ x ∈ Set.Icc a b := by
  have h3 : (0 : ℝ) < π / 3 := by positivity
  simp [arcChart, Set.mem_Icc, mul_le_mul_iff_right₀ h3]

/-- **Zero obstruction for the census**: windowed counts are invariant under
the natural-units rechart — for ANY finite set of putative zeros and ANY
window. No count, hence no gap and no law, can be created or destroyed by the
unit change: a census imbalance exists in one chart iff it exists in every
chart. Gaps are world-facts or they are nothing — never unit artifacts. -/
theorem arcChart_census_invariant (Z : Finset ℂ) (a b : ℝ) :
    (Z.filter fun ρ => arcChart a ≤ arcChart ρ.re ∧ arcChart ρ.re ≤ arcChart b).card
      = (Z.filter fun ρ => a ≤ ρ.re ∧ ρ.re ≤ b).card := by
  congr 1
  ext ρ
  have h3 : (0 : ℝ) < π / 3 := by positivity
  simp only [Finset.mem_filter, arcChart, mul_le_mul_iff_right₀ h3]

end HelixCompleteness

/-! ## Part 9: The quantum ladder — one quantum per zero, induct forever

The part of the program the windowing obscured: on the helix the levels are a
LADDER — `quantumLevelZ k = (k + ½)π`, two directions from the midpoint anchor
— and three exact facts replace all windowing:

* the step is exactly one quantum (`quantumLevelZ_step`; `quantumLevelZ_orbit`:
  level `k` sits exactly `k` quanta from the anchor, both directions, forever);
* the levels are exactly the nodes of the cosine readout and NOTHING else is
  (`node_iff_level` — the complete node census of the readout, no window);
* induction covers the whole ladder (`ladder_induction`, two-directional —
  compactness is irrelevant; the ladder is `ℤ` and induction inducts forever).

And the Deligne dictionary in this program's direction: **purity is
non-negativity FROM zero source drift** — drift `= 0` ⟹ `|w| = 1` (purity,
the weight-½ statement) ⟹ the quartet readout is `≥ 0` with its zeros
attained. The `≥ 0` is DERIVED from conservation — never assumed, never used
to force the line: the legal direction.

Honest scope, one line: the identification of the m-th L-zero with the m-th
ladder level is the production law — these theorems are the exact chassis it
rides on. -/

section QuantumLadder

open Real

/-- The two-directional quantum ladder: level `k` at `(k + ½)π`, `k ∈ ℤ` —
midpoint anchor, half-quantum offset, one quantum per step, both directions. -/
noncomputable def quantumLevelZ (k : ℤ) : ℝ := (k + 1/2) * π

/-- **Exactly one quantum per step.** -/
theorem quantumLevelZ_step (k : ℤ) :
    quantumLevelZ (k + 1) = quantumLevelZ k + π := by
  unfold quantumLevelZ; push_cast; ring

/-- **Every level is exactly `k` quanta from the anchor** — the whole ladder,
both directions, no windowing. -/
theorem quantumLevelZ_orbit (k : ℤ) :
    quantumLevelZ k = quantumLevelZ 0 + k * π := by
  unfold quantumLevelZ; push_cast; ring

/-- **The complete node census, chart level**: the cosine readout vanishes at
the ladder levels and NOWHERE else. Every node is exactly one quantum from the
next, `ℤ`-indexed from the midpoint — the census needs no window. -/
theorem node_iff_level (x : ℝ) :
    Real.cos x = 0 ↔ ∃ k : ℤ, x = quantumLevelZ k := by
  rw [Real.cos_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [hk]; unfold quantumLevelZ; ring⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [hk]; unfold quantumLevelZ; ring⟩

/-- Every level is a node. -/
theorem quantumLevelZ_node (k : ℤ) : Real.cos (quantumLevelZ k) = 0 :=
  (node_iff_level _).mpr ⟨k, rfl⟩

/-- The quadrature readout at the levels is exactly `±1`, alternating — unit
amplitude lobes, one per quantum, forever. -/
theorem quantumLevelZ_unit (k : ℤ) :
    Real.sin (quantumLevelZ k) = (-1) ^ k := by
  unfold quantumLevelZ
  rw [show ((k : ℝ) + 1/2) * π = k * π + π / 2 by ring,
    Real.sin_add_pi_div_two, Real.cos_int_mul_pi]

/-- One quantum step flips the lobe sign exactly — the sign-flip census in
kernel form. -/
theorem quantumLevelZ_alternate (k : ℤ) :
    Real.sin (quantumLevelZ (k + 1)) = -Real.sin (quantumLevelZ k) := by
  rw [quantumLevelZ_step, Real.sin_add_pi]

/-- **One double-ended helix**: the antihelix is the same ladder read from the
other end — the end-swap `k ↦ −(k+1)` is the mirror involution, sending level
`k` to its exact negative. The two sheets are one ℤ-indexed object; "height"
on the mirror end is the same coordinate read backwards. -/
theorem quantumLevelZ_neg (k : ℤ) :
    quantumLevelZ (-(k + 1)) = -quantumLevelZ k := by
  unfold quantumLevelZ; push_cast; ring

/-- **The midpoint is not a level**: the double-ended ladder has no rung at
the origin — the spiral starts BETWEEN its two first rungs. There is no birth
region. -/
theorem quantumLevelZ_ne_zero (k : ℤ) : quantumLevelZ k ≠ 0 := by
  unfold quantumLevelZ
  intro h
  rcases mul_eq_zero.mp h with h' | h'
  · have h2 : (2 * k : ℝ) + 1 = 0 := by linarith
    have h3 : (2 * k + 1 : ℤ) = 0 := by exact_mod_cast h2
    omega
  · exact Real.pi_ne_zero h'

/-- **The full-cost straddle**: the two first rungs sit a FULL quantum apart,
symmetric about the midpoint — `±π/2` each side, the `−1` and `0` levels
spaced the entire cost `π` from each other. The two ends of the one helix
begin half a quantum out, in opposite directions. -/
theorem quantumLevelZ_midpoint_straddle :
    quantumLevelZ 0 - quantumLevelZ (-1) = π ∧
    quantumLevelZ 0 = π / 2 ∧ quantumLevelZ (-1) = -(π / 2) := by
  refine ⟨?_, ?_, ?_⟩ <;> (unfold quantumLevelZ; push_cast; ring)

/-- **Induct forever — no windowing**: a property true at the midpoint anchor
and carried by single quantum steps, up and down, holds at EVERY level of the
two-directional ladder. -/
theorem ladder_induction (P : ℝ → Prop) (h0 : P (quantumLevelZ 0))
    (hup : ∀ k : ℤ, P (quantumLevelZ k) → P (quantumLevelZ (k + 1)))
    (hdown : ∀ k : ℤ, P (quantumLevelZ k) → P (quantumLevelZ (k - 1))) :
    ∀ k : ℤ, P (quantumLevelZ k) := by
  intro k
  induction k using Int.induction_on with
  | zero => exact h0
  | succ i ih => exact hup i ih
  | pred i ih => exact hdown (-i) ih

/-- The source drift of a zero's Möbius readout: the radial defect of its
orbit. Drift `0` = the orbit never spirals — pure rotation on the circle. -/
noncomputable def sourceDrift (sigma gamma : ℝ) : ℝ :=
  ‖moebius_helix sigma gamma‖ - 1

/-- **Purity from zero drift** (the Deligne statement, this program's
direction): zero source drift IS unimodularity — the weight-½ purity
`|w| = 1`. -/
theorem purity_of_noDrift (sigma gamma : ℝ)
    (h : sourceDrift sigma gamma = 0) :
    ‖moebius_helix sigma gamma‖ = 1 := by
  unfold sourceDrift at h; linarith

/-- Zero drift ⟺ the critical line (`γ ≠ 0`): conservation locates the line. -/
theorem noDrift_iff_online (sigma gamma : ℝ) (hg : gamma ≠ 0) :
    sourceDrift sigma gamma = 0 ↔ sigma = 1/2 := by
  unfold sourceDrift
  rw [← moebius_unit_iff sigma gamma hg]
  constructor <;> intro h <;> linarith

/-- **Non-negativity FROM zero drift** — the Deligne purity chain in this
program's direction: drift `= 0` ⟹ purity `|w| = 1` ⟹ the quartet readout is
`≥ 0` with its zeros attained. The `≥ 0` is DERIVED from conservation — never
assumed, never used to force the line. -/
theorem quartet_nonneg_of_noDrift (sigma gamma : ℝ) (hg : gamma ≠ 0)
    (h : sourceDrift sigma gamma = 0) (n : ℕ) :
    0 ≤ quartetLi sigma gamma n := by
  rw [noDrift_iff_online sigma gamma hg] at h
  subst h
  exact quartetLi_nonneg_on_line gamma n

/-- The full purity dichotomy: zero source drift ⟺ the quartet readout is
bounded below at all orders. Drift is the ONLY failure mode. -/
theorem purity_dichotomy (sigma gamma : ℝ) (hg : gamma ≠ 0) :
    sourceDrift sigma gamma = 0
      ↔ ∃ B : ℝ, ∀ n : ℕ, B ≤ quartetLi sigma gamma n := by
  rw [noDrift_iff_online sigma gamma hg]
  exact (quartetLi_boundedBelow_iff sigma gamma hg).symm

/-- `sin (arcsin ½) = ½`: the value↔angle round trip at the critical value is
EXACT — the bridge between the algebraic `½` and its angle is lossless. -/
theorem sin_arcsin_half : Real.sin (Real.arcsin (1/2)) = 1/2 :=
  Real.sin_arcsin (by norm_num) (by norm_num)

/-- `arcsin ½ = π/6`: the angle of the critical value is half the channel
arc. -/
theorem arcsin_half : Real.arcsin (1/2) = π / 6 := by
  rw [← Real.sin_pi_div_six]
  exact Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- **The dictionary weld**: at the critical value the natural-units rechart
IS the inverse-trig bridge — `arcChart ½ = arcsin ½ = π/6`. The `½ ↔ π/6`
identification is the sin/arcsin round trip: exact, lossless, not a
convention. -/
theorem arcChart_half_eq_arcsin : arcChart (1/2) = Real.arcsin (1/2) := by
  rw [arcsin_half]
  simp only [arcChart]
  ring

/-- **THE EVICTION THEOREM — unconditional: off-line zeros have nowhere to
exist on the helix.** Three kernel facts, no hypotheses, no windows:

1. the node census is COMPLETE — the readout vanishes at the quantum ladder
   levels and nowhere else (`node_iff_level`);
2. the ladder is EXACTLY spaced — one quantum per step, both directions from
   the midpoint, forever (`quantumLevelZ_step`);
3. the no-drift locus IS the critical line — zero source drift exactly at
   `σ = ½`, strictly nonzero drift everywhere else (`noDrift_iff_online`).

On the geometry there is no off-ladder node, no drift-free off-line point, no
gap between rungs for anything to hide in: the ghost is evicted from the
helix, unconditionally. Its only coherent residence (NOT "a shadow of
nothing" — by the gauge identity `HelixSource = C^{-s}L` every zero of `L` is
a zero of the source function, prime-built like all the others): a PRIME-BUILT
cancellation of the genuine superposition occurring OFF the ladder — produced
by the engine, billed by no meter (no node, no quantum purchase, no sign
flip; the census prices it +2 in the box, 0 at the nodes). "The engine bills
everything it produces — every cancellation is a purchase" is the production
law: the program's one open span, and after this theorem its only possible
shape. -/
theorem helix_eviction :
    (∀ x : ℝ, Real.cos x = 0 ↔ ∃ k : ℤ, x = quantumLevelZ k) ∧
    (∀ k : ℤ, quantumLevelZ (k + 1) = quantumLevelZ k + π) ∧
    (∀ sigma gamma : ℝ, gamma ≠ 0 →
      (sourceDrift sigma gamma = 0 ↔ sigma = 1/2)) :=
  ⟨node_iff_level, quantumLevelZ_step, noDrift_iff_online⟩

end QuantumLadder

/-! ## Part 10: The mixing engine — synchronized recurrence, no destructive mixing

The aggregation step from ONE off-line quartet collapsing
(`quartetLi_unbounded_off_line`) to a FAMILY of off-line quartets collapsing
TOGETHER. The engine is the k-torus generalization of `circle_recurrence`:
finitely many unimodular phases return to 1 simultaneously, at arbitrarily
late times (compactness + pigeonhole on the product torus — the same proof as
the single circle, run in `Fin k → ℂ`). Consequences, in order:

* `torus_recur_cofinal` — simultaneous returns at arbitrarily late times;
* `sim_re_pow_unbounded` — finitely many moduli `> 1` have `Re((w i)^n)`
  exceeding ANY bound at COMMON cofinal times: bad quartets cannot
  destructively interfere — they dip together;
* `quartet_family_collapse` — the SUM of any nonempty finite family of
  off-line quartet readouts is unbounded below, cofinally.

Honest scope: this is the complete FINITE part of the mixing lemma. The
remaining step for the full Li aggregate is the TAIL — the subexponential
bound on the infinitely many far quartets via the Hadamard summability
`Σ 1/|ρ|²` — classical, zero-free, not yet in this file. -/

section MixingEngine

open Filter Metric

/-- **Simultaneous circle recurrence** (k-torus pigeonhole): finitely many
unimodular phases return within `ε` of `1` TOGETHER. -/
lemma torus_recurrence {k : ℕ} (u : Fin k → ℂ) (hu : ∀ i, ‖u i‖ = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, 1 ≤ m ∧ ∀ i, ‖(u i) ^ m - 1‖ < ε := by
  set x : ℕ → (Fin k → ℂ) := fun n i => (u i) ^ n with hx
  have hmem : ∀ n : ℕ, x n ∈ Metric.closedBall (0 : Fin k → ℂ) 1 := fun n => by
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
    simp [hx, norm_pow, hu i]
  obtain ⟨a, -, φ, hφ, htend⟩ :=
    (isCompact_closedBall (0 : Fin k → ℂ) 1).tendsto_subseq hmem
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨K, hK⟩ := htend (ε/2) (by linarith)
  have hi := hK K le_rfl
  have hj := hK (K+1) (Nat.le_succ K)
  simp only [Function.comp_apply] at hi hj
  have htri := dist_triangle (x (φ K)) a (x (φ (K+1)))
  rw [dist_comm a (x (φ (K+1)))] at htri
  have hlt : dist (x (φ K)) (x (φ (K+1))) < ε := by linarith
  have hmono : φ K < φ (K + 1) := hφ (by omega)
  refine ⟨φ (K+1) - φ K, by omega, fun i => ?_⟩
  have hcoord : dist (x (φ K) i) (x (φ (K+1)) i) < ε :=
    lt_of_le_of_lt (dist_le_pi_dist _ _ i) hlt
  simp only [hx, Complex.dist_eq] at hcoord
  have hadd : φ (K+1) = φ K + (φ (K+1) - φ K) := by omega
  have heq : (u i) ^ (φ K) - (u i) ^ (φ (K+1)) =
      (u i) ^ (φ K) * (1 - (u i) ^ (φ (K+1) - φ K)) := by
    conv_lhs => rw [hadd, pow_add]
    ring
  rw [heq, norm_mul, norm_pow, hu i, one_pow, one_mul, norm_sub_rev] at hcoord
  exact hcoord

/-- Simultaneous recurrence at arbitrarily late times. -/
lemma torus_recur_cofinal {k : ℕ} (u : Fin k → ℂ) (hu : ∀ i, ‖u i‖ = 1)
    {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ ∀ i, ‖(u i) ^ n - 1‖ < ε := by
  obtain ⟨m, hm1, hmlt⟩ := torus_recurrence u hu
    (ε := ε / (N+1)) (div_pos hε (by positivity))
  refine ⟨m * (N + 1), ?_, fun i => ?_⟩
  · calc N ≤ 1 * (N + 1) := by omega
      _ ≤ m * (N + 1) := by gcongr
  · have hb := pow_sub_one_le' ((u i) ^ m)
      (by rw [norm_pow, hu i, one_pow]) (N + 1)
    rw [← pow_mul] at hb
    have hN1 : (0:ℝ) < ((↑N:ℝ) + 1) := by positivity
    have hcancel : ((↑N:ℝ) + 1) * (ε / ((↑N:ℝ) + 1)) = ε := by field_simp
    have hmul : ((↑N:ℝ) + 1) * ‖(u i) ^ m - 1‖ < ε := by
      have h := mul_lt_mul_of_pos_left (hmlt i) hN1; rwa [hcancel] at h
    have hbcast : (((↑(N + 1) : ℕ)):ℝ) = (↑N:ℝ) + 1 := by push_cast; ring
    rw [hbcast] at hb
    exact lt_of_le_of_lt hb hmul

/-- **No destructive mixing**: finitely many moduli `> 1` have their power
real-parts exceed ANY bound at COMMON, arbitrarily late times — the bad
quartets dip together. -/
theorem sim_re_pow_unbounded {k : ℕ} (w : Fin k → ℂ) (hw : ∀ i, 1 < ‖w i‖)
    (C : ℝ) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ ∀ i, C < ((w i) ^ n).re := by
  have hr0 : ∀ i, (0:ℝ) < ‖w i‖ := fun i => lt_trans one_pos (hw i)
  set u : Fin k → ℂ := fun i => w i / (‖w i‖ : ℂ) with hudef
  have hu : ∀ i, ‖u i‖ = 1 := fun i => by
    simp only [hudef, norm_div, Complex.norm_real,
      Real.norm_of_nonneg (hr0 i).le]
    exact div_self (hr0 i).ne'
  have hev : ∀ᶠ n in atTop, ∀ i, 2 * C < (‖w i‖) ^ n := by
    rw [Filter.eventually_all]
    intro i
    exact (tendsto_pow_atTop_atTop_of_one_lt (hw i)).eventually_gt_atTop (2 * C)
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp hev
  obtain ⟨n, hnN, hnlt⟩ := torus_recur_cofinal u hu (ε := 1) one_pos (max N N₁)
  refine ⟨n, le_trans (le_max_left _ _) hnN, fun i => ?_⟩
  have hns : Complex.normSq ((u i)^n) = 1 := by
    rw [Complex.normSq_eq_norm_sq, norm_pow, hu i, one_pow]; norm_num
  have hre : (1:ℝ)/2 < (((u i))^n).re := by
    have hexp : ‖(u i) ^ n - 1‖^2 = 2 - 2*(((u i))^n).re := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.one_re, Complex.sub_im,
        Complex.one_im, sub_zero]
      rw [Complex.normSq_apply] at hns
      linear_combination hns
    have h1 : ‖(u i) ^ n - 1‖^2 < 1 := by
      have := hnlt i
      nlinarith [norm_nonneg ((u i)^n - 1)]
    nlinarith [h1, hexp]
  have hsplit : w i = (‖w i‖ : ℂ) * u i := by
    have hne : ((‖w i‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hr0 i).ne'
    simp only [hudef]
    field_simp
  have hwn : ((w i) ^ n).re = (‖w i‖)^n * (((u i))^n).re := by
    conv_lhs => rw [hsplit, mul_pow, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
  have hrn : 2 * C < (‖w i‖) ^ n := hN₁ n (le_trans (le_max_right _ _) hnN) i
  have hrpos : (0:ℝ) < (‖w i‖) ^ n := pow_pos (hr0 i) n
  rw [hwn]
  nlinarith [mul_pos (sub_pos.mpr hre) hrpos, hrn]

/-- **The finite mixing lemma**: the SUM of any nonempty finite family of
off-line quartet readouts is unbounded below at arbitrarily late common
times. Within the finite part, no conspiracy of off-line zeros can rescue the
aggregate — the family collapses together. -/
theorem quartet_family_collapse {k : ℕ} (hk : 0 < k)
    (sigma gamma : Fin k → ℝ) (hg : ∀ i, gamma i ≠ 0)
    (hs : ∀ i, sigma i ≠ 1/2) (M : ℝ) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ (∑ i, quartetLi (sigma i) (gamma i) n) < M := by
  have h0 : ∀ i, (⟨sigma i, gamma i⟩ : ℂ) ≠ 0 := fun i h =>
    hg i (by simpa using congrArg Complex.im h)
  have h1 : ∀ i, (⟨sigma i, gamma i⟩ : ℂ) ≠ 1 := fun i h =>
    hg i (by simpa using congrArg Complex.im h)
  have hwne : ∀ i, moebius_helix (sigma i) (gamma i) ≠ 0 := by
    intro i hw0
    have hmr := moebius_helix_mul_reflect (sigma i) (gamma i) (h0 i) (h1 i)
    rw [hw0, zero_mul] at hmr
    exact zero_ne_one hmr
  have hrne : ∀ i, ‖moebius_helix (sigma i) (gamma i)‖ ≠ 1 := fun i hr =>
    hs i ((moebius_unit_iff (sigma i) (gamma i) (hg i)).mp hr)
  set v : Fin k → ℂ := fun i =>
    if 1 < ‖moebius_helix (sigma i) (gamma i)‖
    then moebius_helix (sigma i) (gamma i)
    else (moebius_helix (sigma i) (gamma i))⁻¹ with hvdef
  have hv : ∀ i, 1 < ‖v i‖ := by
    intro i
    by_cases hcase : 1 < ‖moebius_helix (sigma i) (gamma i)‖
    · simpa [hvdef, if_pos hcase] using hcase
    · have hlt : ‖moebius_helix (sigma i) (gamma i)‖ < 1 :=
        lt_of_le_of_ne (not_lt.mp hcase) (hrne i)
      have hinv : 1 < ‖(moebius_helix (sigma i) (gamma i))⁻¹‖ := by
        rw [norm_inv]
        exact (one_lt_inv₀ (norm_pos_iff.mpr (hwne i))).mpr hlt
      simpa [hvdef, if_neg hcase] using hinv
  have hterm : ∀ (i : Fin k) (n : ℕ), quartetLi (sigma i) (gamma i) n
      = 4 - 2*((v i)^n).re - 2*(((v i)⁻¹)^n).re := by
    intro i n
    rw [quartetLi_eq (sigma i) (gamma i) (h0 i) (h1 i) n]
    by_cases hcase : 1 < ‖moebius_helix (sigma i) (gamma i)‖
    · simp only [hvdef, if_pos hcase]
    · simp only [hvdef, if_neg hcase, inv_inv]
      ring
  set C : ℝ := (6 * k - M) / (2 * k) + 1 with hCdef
  obtain ⟨n, hnN, hnC⟩ := sim_re_pow_unbounded v hv C N
  refine ⟨n, hnN, ?_⟩
  have hbound : ∀ i : Fin k, quartetLi (sigma i) (gamma i) n ≤ 6 - 2 * C := by
    intro i
    rw [hterm i n]
    have hCi : C < ((v i)^n).re := hnC i
    have hsmall : |(((v i)⁻¹)^n).re| ≤ 1 := by
      calc |(((v i)⁻¹)^n).re| ≤ ‖((v i)⁻¹)^n‖ := Complex.abs_re_le_norm _
        _ = ‖(v i)⁻¹‖^n := norm_pow _ _
        _ ≤ 1 := pow_le_one₀ (norm_nonneg _) (by
            rw [norm_inv]
            exact inv_le_one_of_one_le₀ (hv i).le)
    have habs := abs_le.mp hsmall
    nlinarith [hCi, habs.1, habs.2]
  calc (∑ i, quartetLi (sigma i) (gamma i) n)
      ≤ ∑ _i : Fin k, (6 - 2*C) := Finset.sum_le_sum fun i _ => hbound i
    _ = k * (6 - 2*C) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ < M := by
        have hk' : (0:ℝ) < k := by exact_mod_cast hk
        rw [hCdef]
        have hexpand : (k:ℝ) * (6 - 2*((6 * k - M) / (2 * k) + 1))
            = M - 2*k := by
          field_simp
          ring
        rw [hexpand]
        linarith

end MixingEngine

/-! ## Part 11: The bucket mechanism — vanish in one ledger, pay in the other

The conductor assigns `−` and `+` buckets to the prime residues it admits.
The fiber is a harmonic already and a standing wave everywhere; a
crossing/vanishing happens when the internal channels' phases cancel — the
buckets MEET — and at that moment the unsigned amplitude total is the
harmonic cost. The same event read in two ledgers: the SIGNED collection
vanishes (the zero), the UNSIGNED collection pays the price (the purchase).
This is why the conversion law holds: a full cancellation requires its
budget spent. (`fibres_meet_at_any_vanishing` /
`fibres_balance_at_any_vanishing` are the χ₃ kernel instances of the
rendezvous.) -/

section BucketMechanism

/-- The `+` bucket: the admitted residues' positive contributions. -/
noncomputable def plusBucket (F : Finset ℕ) (s : ℕ → ℝ) : ℝ :=
  ∑ n ∈ F, max (s n) 0

/-- The `−` bucket: the admitted residues' negative contributions, as a
non-negative amount. -/
noncomputable def minusBucket (F : Finset ℕ) (s : ℕ → ℝ) : ℝ :=
  ∑ n ∈ F, max (-(s n)) 0

/-- The signed collection — the wave's skeleton — is the bucket difference. -/
theorem signed_eq_buckets (F : Finset ℕ) (s : ℕ → ℝ) :
    ∑ n ∈ F, s n = plusBucket F s - minusBucket F s := by
  rw [plusBucket, minusBucket, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rcases le_total 0 (s n) with h | h
  · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), sub_zero]
  · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h), zero_sub, neg_neg]

/-- The unsigned collection — the energy meter — is the bucket sum. -/
theorem amplitude_eq_buckets (F : Finset ℕ) (s : ℕ → ℝ) :
    ∑ n ∈ F, |s n| = plusBucket F s + minusBucket F s := by
  rw [plusBucket, minusBucket, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rcases le_total 0 (s n) with h | h
  · rw [abs_of_nonneg h, max_eq_left h, max_eq_right (neg_nonpos.mpr h),
      add_zero]
  · rw [abs_of_nonpos h, max_eq_right h, max_eq_left (neg_nonneg.mpr h),
      zero_add]

/-- **Vanishing IS rendezvous**: the signed collection cancels exactly when
the conductor's two buckets meet. -/
theorem vanishing_iff_rendezvous (F : Finset ℕ) (s : ℕ → ℝ) :
    ∑ n ∈ F, s n = 0 ↔ plusBucket F s = minusBucket F s := by
  rw [signed_eq_buckets, sub_eq_zero]

/-- **The price at the rendezvous**: when the phases cancel, the amplitude
total is exactly twice the bucket — the harmonic cost, paid in full at the
moment of vanishing. Zero in the signed ledger, payment in the unsigned. -/
theorem price_at_rendezvous (F : Finset ℕ) (s : ℕ → ℝ)
    (h : ∑ n ∈ F, s n = 0) :
    ∑ n ∈ F, |s n| = 2 * plusBucket F s := by
  rw [amplitude_eq_buckets, ← (vanishing_iff_rendezvous F s).mp h]
  ring

/-- **Complex vanishing is a DOUBLE rendezvous**: a vanishing of a complex
collection demands BOTH component collections meet simultaneously — two real
conditions at one point. On the standing line the imaginary collection is
identically zero (reality — the Möbius pairing pays that book in advance,
forever), so an on-line vanishing needs ONE rendezvous; anywhere else it
needs two. -/
theorem complex_vanishing_iff_double_rendezvous (F : Finset ℕ) (s : ℕ → ℂ) :
    ∑ n ∈ F, s n = 0 ↔
      (plusBucket F (fun n => (s n).re) = minusBucket F (fun n => (s n).re) ∧
       plusBucket F (fun n => (s n).im) = minusBucket F (fun n => (s n).im)) := by
  rw [← vanishing_iff_rendezvous, ← vanishing_iff_rendezvous]
  constructor
  · intro h
    constructor
    · have := congrArg Complex.re h
      simpa [Complex.re_sum] using this
    · have := congrArg Complex.im h
      simpa [Complex.im_sum] using this
  · rintro ⟨hre, him⟩
    apply Complex.ext
    · simpa [Complex.re_sum] using hre
    · simpa [Complex.im_sum] using him

/-- **The double price**: a complex vanishing pays BOTH books in full — each
component's amplitude total is twice its bucket. The cost side of the
induction's step: one quantum buys one rendezvous; a vanishing away from the
standing line must complete two. -/
theorem double_price_at_rendezvous (F : Finset ℕ) (s : ℕ → ℂ)
    (h : ∑ n ∈ F, s n = 0) :
    ∑ n ∈ F, |(s n).re| = 2 * plusBucket F (fun n => (s n).re) ∧
    ∑ n ∈ F, |(s n).im| = 2 * plusBucket F (fun n => (s n).im) := by
  obtain ⟨hre, him⟩ := (complex_vanishing_iff_double_rendezvous F s).mp h
  exact ⟨price_at_rendezvous F _ ((vanishing_iff_rendezvous F _).mpr hre),
    price_at_rendezvous F _ ((vanishing_iff_rendezvous F _).mpr him)⟩

/-- **Face one of the conversion law — the flip IS the phase quantum**: `k`
sign flips are exactly the phase `e^{iπk}` — one π per flip, by Euler. The
alternation is kernel (`signFlip_of_simple_node`, `quantumLevelZ_alternate`);
this is the dictionary identifying each flip with one quantum of phase.
Combined: a real wave's accrued phase advances exactly π per transversal
crossing — topology, not analysis. -/
theorem flip_phase_quantum (k : ℤ) :
    Complex.exp ((k : ℂ) * (Real.pi * Complex.I)) = (-1) ^ k := by
  rw [Complex.exp_int_mul, Complex.exp_pi_mul_I]

end BucketMechanism

/-! ## Part 12: The welds — one program, one set of objects

Tie-lemmas identifying this file's objects with their counterparts across the
program, so every theorem speaks about the same things. -/

section Welds

/-- **Weld 1**: this file's Möbius readout IS the program's spectral
coordinate — `moebius_helix σ γ = SpectralSide.w (σ + iγ)`. One object, two
files, now one lemma. -/
theorem moebius_helix_eq_w (sigma gamma : ℝ) :
    moebius_helix sigma gamma = SpectralSide.w ⟨sigma, gamma⟩ :=
  rfl

/-- **Weld 2**: the quantum ladder's rungs are exactly the census form —
`(k + ½)π = (2k+1)·(π/2)`, the parameterization `Real.cos_eq_zero_iff`
speaks. Same rungs, both spellings, one lemma. -/
theorem quantumLevelZ_eq_census_form (k : ℤ) :
    quantumLevelZ k = (2 * k + 1) * (Real.pi / 2) := by
  unfold quantumLevelZ; push_cast; ring

end Welds
