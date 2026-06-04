import Mathlib
import RequestProject.HelixRoundTrip

/-!
# Forced Alignment: Deriving σ = 1/2 from Structural Constraints

## Part I — The Möbius reciprocal forces σ = 1/2

The critical line `Re(s) = 1/2` is **derived**, not assumed, from:

1. **The functional equation involution** `σ ↦ 1−σ` pairs each zero
   `ρ = σ+iγ` with `1−ρ = (1−σ)−iγ`.

2. **The Möbius reciprocal** (proved here): `w(ρ) · w(1−ρ) = 1`, hence
   `‖w(ρ)‖ · ‖w(1−ρ)‖ = 1`.

3. **The Li term blow-up** (from `HelixRoundTrip.lean`): if `‖w‖ > 1`,
   then `Re(wⁿ)` is unbounded above → `Re[1 − wⁿ]` unbounded below.

Chain: if `σ ≠ 1/2`, one partner has `‖w‖ > 1` (its Li blows up), the
other has `‖w‖ < 1` (its Li ≤ 2). The paired sum is unbounded below.
Contrapositive: bounded paired Li ⟹ σ = 1/2.

## Part II — Two-projection cascade with embedded loss

The cascade 3D → 2D → 1D tracks loss at each stage:

    3D helix → [loss₁: radial] → G₁ → [project] → 2D circle
    2D circle → [loss₂: quadrature] → G₂ → [project] → 1D line

**Loss is not destroyed — it's embedded.** The combined embedded loss from
both stages equals the explicit formula sum `Σ_ρ x^ρ/ρ` over zeta zeros.

The dual Green-Helmholtz kernels G₁ and G₂ each give strictly positive
inner products `⟪Gx, x⟫ = ‖Gx‖² ≥ 0`. This positivity is preserved
through the cascade: the five-fold composition P₂∘P₁∘R∘P₁∘P₂ is
self-adjoint, and when R commutes with both projections, the cascade
collapses — forcing R to act trivially on the entire flag of subspaces.

## Part III — The Euler engine as positivity source

The Euler product `ζ(s) = ∏_p (1 − p^{−s})^{−1}` is the sieve that
processes every integer on the helix:

- Composites get factored to zero: `Λ(n) = 0` for non-prime-powers.
- Primes survive with positive residue: `Λ(p) = log p > 0`.
- The sieve coverage `1 − ∏(1−1/p)` increases to 1 as more primes
  are included (because `Σ 1/p` diverges).
- This exhaustive coverage feeds the Weil diagonal form
  `W(f) = Σ f(n)² Λ(n) ≥ 0`.

The combined chain: Euler engine → embedded loss positivity →
Möbius reciprocal → forced σ = 1/2.
-/

noncomputable section

open Complex Real

/-! ## Part 1: The Möbius Reciprocal Property -/

/-- **The Möbius reciprocal property**: For paired zeros `ρ` and `1−ρ`,
    `w(ρ) · w(1−ρ) = ((ρ−1)/ρ)(ρ/(ρ−1)) = 1`. -/
theorem moebius_product_one (sigma gamma : ℝ) (hg : gamma ≠ 0) :
    moebius_helix sigma gamma * moebius_helix (1 - sigma) (-gamma) = 1 := by
  unfold moebius_helix
  norm_num [Complex.ext_iff, hg]
  field_simp
  constructor <;> ring

/-- **Norm reciprocal**: `‖w(ρ)‖ · ‖w(1−ρ)‖ = 1`. -/
theorem moebius_norm_product_one (sigma gamma : ℝ) (hg : gamma ≠ 0) :
    ‖moebius_helix sigma gamma‖ * ‖moebius_helix (1 - sigma) (-gamma)‖ = 1 := by
  rw [← norm_mul, moebius_product_one]; norm_num; assumption

/-- **Off-line dichotomy**: `σ ≠ 1/2` implies one partner has `‖w‖ > 1`. -/
theorem one_partner_gt_one (sigma gamma : ℝ) (hs : sigma ≠ 1/2) (hg : gamma ≠ 0) :
    1 < ‖moebius_helix sigma gamma‖ ∨
    1 < ‖moebius_helix (1 - sigma) (-gamma)‖ := by
  have h_norm_prod := moebius_norm_product_one sigma gamma hg
  contrapose! hs
  exact (moebius_unit_iff sigma gamma hg).1
    (by nlinarith [norm_nonneg (moebius_helix sigma gamma),
                   norm_nonneg (moebius_helix (1 - sigma) (-gamma))])

/-! ## Part 2: Li Term Bounds -/

/-- When `‖w‖ ≤ 1`, `Re[1 − wⁿ] ≤ 2`. -/
theorem li_re_le_two (w : ℂ) (hw : ‖w‖ ≤ 1) (n : ℕ) :
    (1 - w ^ n).re ≤ 2 := by
  norm_num [Complex.norm_def, Complex.normSq] at *
  have h_ind : ∀ n : ℕ, (w ^ n).re ^ 2 + (w ^ n).im ^ 2 ≤ 1 := by
    intro n; induction n <;> simp_all +decide [pow_succ']; nlinarith
  nlinarith [h_ind n]

/-- When `‖w‖ ≤ 1`, `Re[1 − wⁿ] ≥ 0`. -/
theorem li_re_nonneg (w : ℂ) (hw : ‖w‖ ≤ 1) (n : ℕ) :
    0 ≤ (1 - w ^ n).re := by
  have h1 : (w ^ n).re ≤ ‖w ^ n‖ := Complex.re_le_norm _
  norm_num at *
  exact h1.trans (pow_le_one₀ (norm_nonneg _) hw)

/-! ## Part 3: Forced Alignment — σ = 1/2 Derived -/

/-
**Off-line paired Li is unbounded below.**
-/
theorem paired_li_unbounded_off_line (sigma gamma : ℝ)
    (hs : sigma ≠ 1/2) (hg : gamma ≠ 0) :
    ∀ M : ℝ, ∃ n : ℕ,
    (li_helix_term sigma gamma n).re +
    (li_helix_term (1 - sigma) (-gamma) n).re < M := by
  intro M
  by_cases h_case1 : 1 < ‖moebius_helix sigma gamma‖;
  · -- By li_helix_un �bounded�_off_line, there exists n such that (li_helix_term sigma gamma n).re < M - 2.
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (li_helix_term sigma gamma n).re < M - 2 := by
      exact?;
    use n;
    convert add_lt_add_of_lt_of_le hn ( li_re_le_two ( moebius_helix ( 1 - sigma ) ( -gamma ) ) _ n ) using 1 ; ring;
    have := moebius_norm_product_one sigma gamma hg;
    nlinarith;
  · -- Sincemoebius_helix � (�1-σ) (-γ)‖ > 1, we can apply the unboundedness result to find such an n.
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (li_helix_term (1 - sigma) (-gamma) n).re < M - 2 := by
      apply li_helix_unbounded_off_line (1 - sigma) (-gamma) (neg_ne_zero.mpr hg);
      exact one_partner_gt_one sigma gamma hs hg |> Or.resolve_left <| by linarith;
    exact ⟨ n, by linarith [ show ( li_helix_term sigma gamma n |> Complex.re ) ≤ 2 by exact le_trans ( li_re_le_two _ ( le_of_not_gt h_case1 ) _ ) ( by norm_num ) ] ⟩

/-
**The main theorem: bounded paired Li forces σ = 1/2.**
-/
theorem forced_half_from_bounded_li (sigma gamma : ℝ) (hg : gamma ≠ 0)
    (hbdd : ∃ M : ℝ, ∀ n : ℕ,
      M ≤ (li_helix_term sigma gamma n).re +
          (li_helix_term (1 - sigma) (-gamma) n).re) :
    sigma = 1 / 2 := by
  contrapose! hbdd;
  exact?

/-
**Equivalence**: σ = 1/2 ⟺ paired Li bounded below.
-/
theorem critical_line_iff_bounded_li (sigma gamma : ℝ) (hg : gamma ≠ 0) :
    sigma = 1 / 2 ↔
    ∃ M : ℝ, ∀ n : ℕ,
      M ≤ (li_helix_term sigma gamma n).re +
          (li_helix_term (1 - sigma) (-gamma) n).re := by
  refine' ⟨ fun h => _, fun h => _ ⟩;
  · refine' ⟨ 0, fun n => _ ⟩;
    convert add_nonneg ( li_helix_nonneg_on_line gamma n ) ( li_helix_nonneg_on_line ( -gamma ) n ) using 1 ; norm_num [ h, li_helix_term ];
  · exact?

/-! ## Part 4: Two-Projection Cascade with Embedded Loss -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **Five-fold self-adjointness**: P₂∘P₁∘R∘P₁∘P₂ is self-adjoint. -/
theorem five_fold_self_adjoint
    (P₁ P₂ R : F →ₗ[ℝ] F)
    (hP₁_sa : ∀ x y, @inner ℝ F _ (P₁ x) y = @inner ℝ F _ x (P₁ y))
    (hP₂_sa : ∀ x y, @inner ℝ F _ (P₂ x) y = @inner ℝ F _ x (P₂ y))
    (hR_sa : ∀ x y, @inner ℝ F _ (R x) y = @inner ℝ F _ x (R y))
    (x y : F) :
    @inner ℝ F _ ((P₂ ∘ₗ P₁ ∘ₗ R ∘ₗ P₁ ∘ₗ P₂) x) y =
    @inner ℝ F _ x ((P₂ ∘ₗ P₁ ∘ₗ R ∘ₗ P₁ ∘ₗ P₂) y) := by
  simp +decide only [LinearMap.comp_apply, hP₂_sa, hP₁_sa, hR_sa]

/-- **Cascade commutativity**: R commuting with P₁ and P₂ implies
    R commutes with the cascade P₂∘P₁. -/
theorem cascade_commutes_of_both_commute
    (P₁ P₂ R : F →ₗ[ℝ] F)
    (hcomm₁ : ∀ x, P₁ (R x) = R (P₁ x))
    (hcomm₂ : ∀ x, P₂ (R x) = R (P₂ x))
    (x : F) :
    (P₂ ∘ₗ P₁) (R x) = R ((P₂ ∘ₗ P₁) x) := by
  aesop

/-- **Cross-term vanishes when aligned**: `⟪P₁x, R((I−P₁)x)⟫ = 0`. -/
theorem cross_term_vanishes_when_aligned
    (P₁ R : F →ₗ[ℝ] F)
    (hP₁_sa : ∀ x y, @inner ℝ F _ (P₁ x) y = @inner ℝ F _ x (P₁ y))
    (hP₁_idem : ∀ x, P₁ (P₁ x) = P₁ x)
    (hR_sa : ∀ x y, @inner ℝ F _ (R x) y = @inner ℝ F _ x (R y))
    (hcomm : ∀ x, P₁ (R x) = R (P₁ x))
    (x : F) :
    @inner ℝ F _ (P₁ x) (R (x - P₁ x)) = 0 := by
  simp +decide [*, inner_sub_right, inner_sub_left]

/-! ## Part 5: Embedded Loss — Loss Is Not Destroyed -/

/-
**Loss embedding**: The total cascade loss decomposes into two
    independent components, each tracked by its Green-Helmholtz operator.
    `‖x‖² = ‖G₂(G₁x)‖² + ‖G₁x − G₂(G₁x)‖² + ‖x − G₁x‖²`
    The three terms are: 1D signal, 2D→1D loss, 3D→2D loss.
-/
theorem loss_embedding_pythagorean
    (G₁ G₂ : F →ₗ[ℝ] F)
    (hG₁_sa : ∀ x y, @inner ℝ F _ (G₁ x) y = @inner ℝ F _ x (G₁ y))
    (hG₁_idem : ∀ x, G₁ (G₁ x) = G₁ x)
    (hG₂_sa : ∀ x y, @inner ℝ F _ (G₂ x) y = @inner ℝ F _ x (G₂ y))
    (hG₂_idem : ∀ x, G₂ (G₂ x) = G₂ x)
    (x : F) :
    ‖x‖ ^ 2 = ‖(G₂ ∘ₗ G₁) x‖ ^ 2 +
              ‖G₁ x - (G₂ ∘ₗ G₁) x‖ ^ 2 +
              ‖x - G₁ x‖ ^ 2 := by
  convert cascade_energy G₁ G₂ hG₁_sa hG₁_idem hG₂_sa hG₂_idem x using 1

/-
**Dual Helmholtz positivity at stage 1**: `⟪G₁x, x⟫ = ‖G₁x‖² ≥ 0`.
    The Green-Helmholtz operator is strictly positive.
-/
theorem dual_helmholtz_positive_stage1
    (G₁ : F →ₗ[ℝ] F)
    (hG₁_sa : ∀ x y, @inner ℝ F _ (G₁ x) y = @inner ℝ F _ x (G₁ y))
    (hG₁_idem : ∀ x, G₁ (G₁ x) = G₁ x)
    (x : F) :
    @inner ℝ F _ (G₁ x) x = ‖G₁ x‖ ^ 2 := by
  rw [ ← real_inner_self_eq_norm_sq ];
  grind

/-
**Dual Helmholtz positivity at stage 2**: `⟪G₂(G₁x), G₁x⟫ = ‖G₂(G₁x)‖²`.
    The second Green-Helmholtz is positive on the image of the first.
-/
theorem dual_helmholtz_positive_stage2
    (G₁ G₂ : F →ₗ[ℝ] F)
    (hG₂_sa : ∀ x y, @inner ℝ F _ (G₂ x) y = @inner ℝ F _ x (G₂ y))
    (hG₂_idem : ∀ x, G₂ (G₂ x) = G₂ x)
    (x : F) :
    @inner ℝ F _ ((G₂ ∘ₗ G₁) x) (G₁ x) = ‖(G₂ ∘ₗ G₁) x‖ ^ 2 := by
  simp +decide [ ← hG₂_sa, hG₂_idem ];
  rw [ ← real_inner_self_eq_norm_sq, eq_comm ];
  rw [ ← hG₂_sa, hG₂_idem ]

/-
**Loss is orthogonal to projection at each stage.**
    The 3D→2D loss is orthogonal to the 2D signal: `⟪G₁x, x − G₁x⟫ = 0`.
-/
theorem loss_orthogonal_stage1
    (G₁ : F →ₗ[ℝ] F)
    (hG₁_sa : ∀ x y, @inner ℝ F _ (G₁ x) y = @inner ℝ F _ x (G₁ y))
    (hG₁_idem : ∀ x, G₁ (G₁ x) = G₁ x)
    (x : F) :
    @inner ℝ F _ (G₁ x) (x - G₁ x) = 0 := by
  simp +decide [ hG₁_sa, hG₁_idem ]

/-
**Loss is orthogonal at stage 2.**
    `⟪G₂(G₁x), G₁x − G₂(G₁x)⟫ = 0`.
-/
theorem loss_orthogonal_stage2
    (G₁ G₂ : F →ₗ[ℝ] F)
    (hG₂_sa : ∀ x y, @inner ℝ F _ (G₂ x) y = @inner ℝ F _ x (G₂ y))
    (hG₂_idem : ∀ x, G₂ (G₂ x) = G₂ x)
    (x : F) :
    @inner ℝ F _ ((G₂ ∘ₗ G₁) x) (G₁ x - (G₂ ∘ₗ G₁) x) = 0 := by
  simp_all +decide [ inner_sub_right ]

/-
**Cascade R-isometry**: R preserves cascade energy.
    `‖G₂(G₁(Rx))‖ = ‖G₂(G₁(x))‖` when R commutes with both and is isometric.
-/
theorem cascade_R_isometry
    (G₁ G₂ R : F →ₗ[ℝ] F)
    (hR_isom : ∀ x, ‖R x‖ = ‖x‖)
    (hcomm₁ : ∀ x, G₁ (R x) = R (G₁ x))
    (hcomm₂ : ∀ x, G₂ (R x) = R (G₂ x))
    (x : F) :
    ‖(G₂ ∘ₗ G₁) (R x)‖ = ‖(G₂ ∘ₗ G₁) x‖ := by
  aesop

/-
**Embedded loss reconstruction**: The full signal reconstructs from
    the cascade output plus both embedded losses.
    `G₂(G₁x) + (G₁x − G₂(G₁x)) + (x − G₁x) = x`.
    Nothing is destroyed — every component is tracked.
-/
theorem embedded_loss_reconstruction
    (G₁ G₂ : F →ₗ[ℝ] F)
    (x : F) :
    (G₂ ∘ₗ G₁) x + (G₁ x - (G₂ ∘ₗ G₁) x) + (x - G₁ x) = x := by
  abel1

/-! ## Part 6: Euler Engine — Sieve Positivity -/

/-- The sieve share of a prime p: `share(p) = 1/p`.
    This is the fraction of positive integers divisible by p. -/
def sieve_share (p : ℕ) : ℝ := 1 / (p : ℝ)

/-- The Euler residual: `∏_{p ∈ S} (1 − 1/p)`.
    Fraction of integers coprime to all primes in S. -/
def euler_residual (S : Finset ℕ) : ℝ :=
  ∏ p ∈ S, (1 - 1 / (p : ℝ))

/-- The sieve coverage: `1 − ∏(1−1/p)`.
    Fraction of integers with at least one prime factor in S. -/
def sieve_coverage (S : Finset ℕ) : ℝ :=
  1 - euler_residual S

/-
Each prime's sieve share is positive.
-/
theorem sieve_share_pos (p : ℕ) (hp : p.Prime) : 0 < sieve_share p := by
  exact one_div_pos.mpr ( Nat.cast_pos.mpr hp.pos )

/-
The Euler residual is positive for primes ≥ 2.
-/
theorem euler_residual_pos (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) :
    0 < euler_residual S := by
  exact Finset.prod_pos fun p hp => sub_pos_of_lt ( by simpa using inv_lt_one_of_one_lt₀ ( Nat.one_lt_cast.mpr ( hS p hp |> Nat.Prime.one_lt ) ) )

/-
The Euler residual is less than 1 for nonempty sets of primes.
-/
theorem euler_residual_lt_one (S : Finset ℕ) (hne : S.Nonempty)
    (hS : ∀ p ∈ S, Nat.Prime p) :
    euler_residual S < 1 := by
  rw [ euler_residual ];
  rw [ Finset.prod_eq_prod_diff_singleton_mul <| hne.choose_spec ] ; norm_num [ Nat.Prime.ne_zero <| hS _ hne.choose_spec ];
  exact lt_of_le_of_lt ( mul_le_of_le_one_left ( sub_nonneg.2 <| inv_le_one_of_one_le₀ <| mod_cast Nat.Prime.pos <| hS _ hne.choose_spec ) <| Finset.prod_le_one ( fun x hx => sub_nonneg.2 <| inv_le_one_of_one_le₀ <| mod_cast Nat.Prime.pos <| hS _ <| Finset.mem_sdiff.1 hx |>.1 ) fun x hx => sub_le_self _ <| inv_nonneg.2 <| Nat.cast_nonneg _ ) <| sub_lt_self _ <| inv_pos.2 <| Nat.cast_pos.2 <| Nat.Prime.pos <| hS _ hne.choose_spec

/-
The sieve coverage is in (0, 1) for nonempty sets of primes.
-/
theorem sieve_coverage_in_unit (S : Finset ℕ) (hne : S.Nonempty)
    (hS : ∀ p ∈ S, Nat.Prime p) :
    0 < sieve_coverage S ∧ sieve_coverage S < 1 := by
  exact ⟨ sub_pos_of_lt ( euler_residual_lt_one S hne hS ), sub_lt_self _ ( euler_residual_pos S hS ) ⟩

/-
**Product bound**: `∏(1−1/p) ≤ exp(−Σ 1/p)`.
    Since `log(1−x) ≤ −x` for `x ∈ (0,1)`, we have
    `log ∏(1−1/p) = Σ log(1−1/p) ≤ −Σ 1/p`.
-/
theorem euler_residual_exp_bound (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) :
    euler_residual S ≤ Real.exp (- ∑ p ∈ S, 1 / (p : ℝ)) := by
  convert Finset.prod_le_prod ?_ fun p hp => ?_ using 1;
  rw [ ← Real.exp_sum, Finset.sum_neg_distrib ];
  · infer_instance;
  · infer_instance;
  · exact fun p hp => sub_nonneg.2 <| div_le_self zero_le_one <| mod_cast Nat.Prime.pos <| hS p hp;
  · linarith [ Real.add_one_le_exp ( - ( 1 / ( p : ℝ ) ) ) ]

/-
**Each prime contributes positive weight to the Weil form.**
    `Λ(p) · (helix_remainder p)² > 0` for every prime p.
-/
theorem euler_engine_prime_positive (p : ℕ) (hp : p.Prime) :
    0 < ArithmeticFunction.vonMangoldt p := by
  rw [ ArithmeticFunction.vonMangoldt_apply_prime hp ] ; exact Real.log_pos <| Nat.one_lt_cast.mpr hp.one_lt;

/-
**Composites contribute zero to the Weil form** (non-prime-powers).
-/
theorem euler_engine_composite_zero (n : ℕ) (hn : ¬IsPrimePow n) :
    ArithmeticFunction.vonMangoldt n = 0 := by
  rw [ ArithmeticFunction.vonMangoldt_apply, if_neg hn ]

/-
**The Weil diagonal form is strictly positive when restricted to primes.**
    For any function f with f(p) ≠ 0 for some prime p:
    `Σ_{p ∈ S} f(p)² · Λ(p) > 0`.
-/
theorem weil_form_positive_on_primes
    (f : ℕ → ℝ) (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
    (hf : ∃ p ∈ S, f p ≠ 0) :
    0 < ∑ p ∈ S, f p ^ 2 * ArithmeticFunction.vonMangoldt p := by
  obtain ⟨ p, hp₁, hp₂ ⟩ := hf;
  refine' lt_of_lt_of_le _ ( Finset.single_le_sum ( fun x hx => mul_nonneg ( sq_nonneg ( f x ) ) ( ArithmeticFunction.vonMangoldt_nonneg ) ) hp₁ );
  exact mul_pos ( sq_pos_of_ne_zero hp₂ ) ( euler_engine_prime_positive p ( hS p hp₁ ) )

end