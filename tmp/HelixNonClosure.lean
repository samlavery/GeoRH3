import Mathlib

/-!
# Helix Non-Closure: Prime Irreducibility via Factor-by-Subtraction

On the mod-6 prime helix, multiplication is addition: `θ(mn) = θ(m) + θ(n)`
where `θ(n) = log n`. Factoring `N = m · k` becomes subtracting heights:
`log N = log m + log k`.

A node survives every proper subtraction iff N has no proper divisors — iff N is prime.
This is the **sieve rewritten as subtraction on log-heights**.

## The non-closure theorem

The angular coordinate is `φ(n) = (π/3) log n mod 2π`. One full turn = `2π/(π/3) = 6`
in log-height. Returning to the identity node (φ=0) means:

  `Σ c_p · log p = 6k` for integers `c_p, k`
  ⟺ `∏ p^{c_p} = e^{6k}`

- **k = 0**: `∏ p^{c_p} = 1` ⟹ all `c_p = 0` (unique factorization)
- **k ≠ 0**: `e^{6k}` is transcendental, a rational product of primes never equals it

So the only closure is trivial: **primes are irreducible nodes on the helix**.

## The greedy remainder

For each prime p, the "greedy factoring" tries to express `log p` as `k · log q`
for smaller primes q. The remainder `r(p) = min_q |log p - k · log q|` is always
strictly positive (since log p / log q is irrational for distinct primes p, q).

This remainder IS the projection loss: when you project the helix onto the circle
(3D → 2D), the angular position survives but the "height surplus" beyond full turns
is lost. For primes, this loss is always nonzero.

## Connection to Green-Helmholtz

The angular remainder, passed through the projection-loss framework:
- **3D → 2D loss**: The radial envelope `R = |A|` measures how far from a flat circle
  the helix point sits. For primes, `R > 0` always.
- **2D → 1D loss**: The quadrature `Im[A]` measures the angular component dropped
  by the real projection. Both losses are nonzero for primes.

The positivity of both losses is a consequence of Λ(n) ≥ 0 and the Euler product.
-/

noncomputable section

open Real

/-! ## Part 1: Log-ratios of distinct primes are irrational -/

/-
If `p` and `q` are distinct primes, then `log p / log q` is irrational.
    Proof: if `log p / log q = a/b` (rationals), then `p^b = q^a`,
    contradicting unique factorization.
-/
theorem log_ratio_irrational {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Irrational (Real.log p / Real.log q) := by
  by_contra h_rat;
  -- Then there exist integers $a$ and $b$ with $b � \�neq 0$ such that $\log p / \log q = a / b$.
  obtain ⟨a, b, hb, h_eq⟩ : ∃ a b : ℕ, b ≠ 0 ∧ Real.log p / Real.log q = a / b := by
    exact Exists.elim ( Classical.not_not.mp h_rat ) fun x hx => ⟨ x.num.natAbs, x.den, Nat.cast_ne_zero.mpr x.pos.ne', by simpa [ abs_of_nonneg ( Rat.num_nonneg.mpr ( show 0 ≤ x from by exact_mod_cast hx ▸ div_nonneg ( Real.log_natCast_nonneg _ ) ( Real.log_natCast_nonneg _ ) ) ), Rat.cast_def ] using hx.symm ⟩;
  -- Then we have $p^b = q^a$.
  have h_exp : (p : ℝ) ^ b = q ^ a := by
    rw [ div_eq_div_iff ] at h_eq;
    · rw [ ← Real.exp_log ( Nat.cast_pos.mpr hp.pos ), ← Real.exp_log ( Nat.cast_pos.mpr hq.pos ), ← Real.exp_nat_mul, ← Real.exp_nat_mul ] ; norm_num ; linarith;
    · exact ne_of_gt <| Real.log_pos <| Nat.one_lt_cast.mpr hq.one_lt;
    · positivity;
  norm_cast at h_exp; have := congr_arg ( ·.factorization q ) h_exp; norm_num at this; have := congr_arg ( ·.factorization p ) h_exp; norm_num at this; simp_all +decide ;
  aesop

/-
For distinct primes p ≠ q and any nonzero integer k,
    `k · log p ≠ log q`. No prime is a perfect power of another.
-/
theorem no_prime_power_relation {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (k : ℤ) (hk : k ≠ 0) :
    (k : ℝ) * Real.log p ≠ Real.log q := by
  rcases Int.eq_nat_or_neg k with ⟨ c, rfl | rfl ⟩ <;> norm_num at *;
  · intro H;
    apply_fun Real.exp at H ; rw [ mul_comm, Real.exp_mul, Real.exp_log, Real.exp_log ] at H <;> norm_cast at * <;> try linarith [ hp.pos, hq.pos ];
    subst H; have := Nat.prime_iff.mp hp; have := Nat.prime_iff.mp hq; simp_all +decide [ Nat.prime_mul_iff ] ;
  · nlinarith [ show 0 < Real.log p from Real.log_pos <| Nat.one_lt_cast.mpr hp.one_lt, show 0 < Real.log q from Real.log_pos <| Nat.one_lt_cast.mpr hq.one_lt ]

/-! ## Part 2: Unique factorization forces trivial closure (k = 0 case) -/

/-
If a product of prime powers equals 1, all exponents are zero.
    This is the k = 0 case of the non-closure theorem:
    `∏ p_i ^ c_i = 1 ⟹ ∀ i, c_i = 0`

    Formalized for a single prime: if `p^n = 1` and p is prime, then n = 0.
-/
theorem prime_pow_eq_one {p : ℕ} (hp : p.Prime) {n : ℕ} (h : p ^ n = 1) : n = 0 := by
  rw [ pow_eq_one_iff ] at h ; aesop

/-
Two-prime version: if `p^a = q^b` for distinct primes, then `a = 0` and `b = 0`.
-/
theorem distinct_prime_pow_eq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {a b : ℕ} (h : p ^ a = q ^ b) : a = 0 ∧ b = 0 := by
  have := congr_arg ( ·.factorization p ) h ; norm_num [ hp.ne_zero, hq.ne_zero ] at this;
  simp_all +decide [ hp.factorization, hq.factorization ];
  exact Nat.pow_right_injective hq.one_lt <| mod_cast h.symm

/-! ## Part 3: The transcendence barrier (k ≠ 0 case) -/

/-- **Lindemann's theorem** (stated as hypothesis):
    `exp(α)` is transcendental for any nonzero algebraic `α`.
    In particular, `e^(6k)` is transcendental for any nonzero integer `k`,
    so it cannot equal any rational number (let alone a product of prime powers).

    This is not yet in Mathlib, so we state it as a hypothesis. -/
def lindemann_hypothesis : Prop :=
  ∀ (q : ℤ), q ≠ 0 → Irrational (Real.exp (6 * q))

/-
Under Lindemann's theorem: no product of prime powers equals `e^{6k}` for `k ≠ 0`.
    This is because `∏ p_i^{c_i}` is rational (indeed a positive integer when all `c_i ≥ 0`),
    but `e^{6k}` is irrational.

    Stated for a single prime: `p^n ≠ e^{6k}` for `k ≠ 0`.
-/
theorem prime_pow_ne_exp (hl : lindemann_hypothesis) {p : ℕ} (hp : p.Prime)
    (n : ℕ) (k : ℤ) (hk : k ≠ 0) :
    (p ^ n : ℝ) ≠ Real.exp (6 * k) := by
  by_contra h_contra;
  exact hl k hk ⟨ p ^ n, by push_cast; linarith ⟩

/-! ## Part 4: The non-closure theorem -/

/-
**Non-closure theorem (k = 0 case, fully proved)**:
    If `n · log p = 0`, then `n = 0`. (The trivial closure is the only one within
    a single prime's contributions.)
-/
theorem helix_closure_trivial_single {p : ℕ} (hp : p.Prime) (n : ℤ)
    (h : (n : ℝ) * Real.log p = 0) : n = 0 := by
  exact_mod_cast eq_zero_of_ne_zero_of_mul_right_eq_zero ( ne_of_gt ( Real.log_pos ( Nat.one_lt_cast.mpr hp.one_lt ) ) ) h

/-
**Non-closure (angular version, k = 0)**:
    If `Σ cᵢ · log pᵢ = 0` where each pᵢ is prime and cᵢ ∈ ℤ,
    stated for two primes: `c₁ · log p + c₂ · log q = 0` with distinct primes
    implies `c₁ = 0` and `c₂ = 0`.
-/
theorem helix_closure_two_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (c₁ c₂ : ℤ)
    (h : (c₁ : ℝ) * Real.log p + (c₂ : ℝ) * Real.log q = 0) :
    c₁ = 0 ∧ c₂ = 0 := by
  by_cases hc₁ : c₁ = 0;
  · simp_all +decide [ hp.ne_zero, hq.ne_zero ];
    norm_cast at h; aesop;
  · -- If $c₁ \neq 0$, then $c₁ * \log p = -c₂ * \log q$, so $\log p / \log q = -c₂ / c₁ �$� is rational, � contradict�ing $\log_ratio_irrational$.
    have h_rat : ∃ r : ℚ, Real.log p / Real.log q = r := by
      exact ⟨ -c₂ / c₁, by push_cast; rw [ div_eq_div_iff ] <;> cases lt_or_gt_of_ne ( show ( c₁ : ℝ ) ≠ 0 by simpa ) <;> nlinarith [ Real.log_pos ( Nat.one_lt_cast.mpr hp.one_lt ), Real.log_pos ( Nat.one_lt_cast.mpr hq.one_lt ) ] ⟩;
    exact False.elim <| log_ratio_irrational hp hq hpq <| by aesop;

/-
**Non-closure (full angular version, k ≠ 0, uses Lindemann)**:
    Under the Lindemann hypothesis, `c · log p = 6k` for a prime `p`
    implies `c = 0` and `k = 0`.
-/
theorem helix_closure_full (hl : lindemann_hypothesis) {p : ℕ} (hp : p.Prime)
    (c : ℤ) (k : ℤ)
    (h : (c : ℝ) * Real.log p = 6 * k) :
    c = 0 ∧ k = 0 := by
  by_cases hc : c = 0;
  · aesop;
  · -- If $c \neq 0$, then $p^{|c|} = e^{6k}$ or $p^{|c|} = e^{-6k}$, depending on the sign of $c$.
    have h_exp : (p : ℝ) ^ c.natAbs = Real.exp (6 * k) ∨ (p : ℝ) ^ c.natAbs = Real.exp (-6 * k) := by
      cases' Int.eq_nat_or_neg c with hc hc ; simp_all +decide [ ← Real.rpow_natCast, Real.rpow_def_of_pos ];
      cases hc <;> simp_all +decide [ Real.rpow_def_of_pos, hp.pos ];
      · exact Or.inl <| by linarith;
      · grind;
    cases' h_exp with h_exp h_exp;
    · have := prime_pow_ne_exp hl hp c.natAbs k;
      by_cases hk : k = 0 <;> simp_all +decide;
    · have := prime_pow_ne_exp hl hp c.natAbs ( -k ) ?_ <;> aesop

/-! ## Part 5: Angular remainder is always positive for primes -/

/-- The angular remainder of a prime on the helix.
    `helix_remainder p = log p mod 6` (always in [0, 6)). -/
def helix_remainder (p : ℕ) : ℝ :=
  Real.log p - 6 * ⌊Real.log p / 6⌋

/-- The normalized angular remainder `r(p)/6 ∈ [0, 1)`. -/
def helix_remainder_normalized (p : ℕ) : ℝ :=
  helix_remainder p / 6

/-
The angular remainder is nonneg.
-/
theorem helix_remainder_nonneg (p : ℕ) (hp : p.Prime) :
    0 ≤ helix_remainder p := by
  exact sub_nonneg_of_le ( by linarith [ Int.floor_le ( Real.log p / 6 ) ] )

/-
The angular remainder is strictly positive for primes.
    (Because `log p = 6k` would mean `p = e^{6k}`, which is transcendental,
    contradicting p ∈ ℕ. For the k = 0 case: log p = 0 means p = 1, not prime.)
-/
theorem helix_remainder_pos (hl : lindemann_hypothesis) (p : ℕ) (hp : p.Prime) :
    0 < helix_remainder p := by
  by_contra! h_contra;
  -- By definition of $helix_remainder �$,� we know that � $�Real.log p = 6 *Real.log p / 6⌋$.
  have h_eq : Real.log p = 6 * ⌊Real.log p / 6⌋ := by
    exact le_antisymm ( le_of_sub_nonpos h_contra ) ( sub_nonneg.mp ( helix_remainder_nonneg p hp ) );
  -- From $Real.log p = 6 * �Real�.log� p / 6⌋$, we deduce that $Real.log p = 6k$ for some integer $k$.
  obtain ⟨k, hk⟩ : ∃ k : ℤ, Real.log p = 6 * k := by
    grind;
  convert helix_closure_full hl hp 1 k ?_ using 1 ; norm_num [ hk ];
  norm_num [ hk ]

/-
The normalized remainder is in (0, 1) for primes.
    This is the "positive remainder" — every prime leaves a nonzero angular residue
    on the helix. Composites (non-prime-powers) can be reduced to 0 by Möbius
    cancellation, but primes always survive with a positive remainder.
-/
theorem helix_remainder_in_unit_interval (hl : lindemann_hypothesis) (p : ℕ) (hp : p.Prime) :
    0 < helix_remainder_normalized p ∧ helix_remainder_normalized p < 1 := by
  constructor;
  · exact div_pos ( helix_remainder_pos hl p hp ) ( by norm_num );
  · exact div_lt_one ( by norm_num ) |>.2 <| sub_lt_iff_lt_add'.2 <| by linarith [ Int.lt_floor_add_one ( Real.log p / 6 ) ] ;

/-! ## Part 6: Connection to projection loss -/

/-
The angular remainder equals the projection loss in the Green-Helmholtz
    framework. When the 3D helix is projected onto the 2D circle (mod 2π),
    the lost information is precisely the number of full turns — the integer
    part ⌊log p / 6⌋. The remainder `log p mod 6` is what survives.

    For the inner product framework: the remainder `r(p)` determines the
    energy in the loss channel. Since `r(p) > 0` for all primes,
    the loss is always nonzero — the projection always discards information
    about primes. This is the "positive projection loss" property.

    The Weil form `W_Λ` weights each prime by `Λ(p) = log p > 0`.
    The total loss energy is `Σ_p Λ(p) · r(p)² > 0` — strictly positive
    because every prime contributes.
-/
theorem projection_loss_positive_primes (hl : lindemann_hypothesis) (p : ℕ) (hp : p.Prime) :
    0 < ArithmeticFunction.vonMangoldt p * helix_remainder p ^ 2 := by
  rw [ ArithmeticFunction.vonMangoldt_apply ];
  rw [ if_pos ];
  · exact mul_pos ( Real.log_pos <| Nat.one_lt_cast.mpr <| Nat.Prime.one_lt <| Nat.minFac_prime hp.ne_one ) ( sq_pos_of_pos <| helix_remainder_pos hl p hp );
  · exact hp.isPrimePow

/-! ## Part 7: The Euler product as inability to factor -/

/-
The Euler product identity in additive form:
    `Σ_{d | n} Λ(d) = log n`.
    Reinterpreted: the prime-power weights summed over divisors reconstruct
    the height on the helix. For a prime p, the only divisors contributing
    are 1 (with Λ(1) = 0) and p itself (with Λ(p) = log p).
    So `log p = Λ(p)` — the prime carries its own full weight.
    This is "inability to factor": the weight cannot be decomposed further.
-/
theorem euler_product_at_prime {p : ℕ} (hp : p.Prime) :
    ∑ d ∈ p.divisors, ArithmeticFunction.vonMangoldt d = Real.log p := by
  rw [ ArithmeticFunction.vonMangoldt_sum ]

/-
For a composite n = a · b (both > 1), the weight distributes:
    `log n = log a + log b`, and each factor carries its own divisor sum.
    The composite is "reduced" in the sense that its Λ value is 0
    (unless it's a prime power), while its constituents carry the weight.
-/
theorem composite_weight_zero (n : ℕ) (hn : 1 < n) (hn_not_pp : ¬IsPrimePow n) :
    ArithmeticFunction.vonMangoldt n = 0 := by
  rw [ ArithmeticFunction.vonMangoldt_apply, if_neg ] ; aesop

end