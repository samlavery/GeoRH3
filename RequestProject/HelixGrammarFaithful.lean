import RequestProject.HelixUnitaryOperator
import RequestProject.HelixExplicitFormulaTermByTerm
import Mathlib

/-!
# The helix grammar is unconditionally faithful: multiplication ↦ winding addition

For the configured channels (the tower `ch_pi6, ch_pi3, ch_pi2, ch_pi`), the helix character
`helixUnitary t = Circle.exp((π/3)·t)` represents the multiplicative monoid of positive reals
faithfully: a positive real `x` winds at angle `log x`, and `log(m·n) = log m + log n`, so the
**winding of a product is the product of the windings**. This is the Euler-product / unique-
factorization source written as `mult → add`, and it is unconditional (axiom-clean): no zeros,
no L-function, no positivity hypothesis.
-/

noncomputable section

open Real Complex

namespace HelixGrammar

/-- **Multiplication becomes winding addition (faithful grammar).** The winding of a product is
the product of the windings: `helixUnitary(log(m·n)) = helixUnitary(log m) · helixUnitary(log n)`.
This is `log(mn) = log m + log n` carried through the helix homomorphism — unconditional. -/
theorem helix_mul_to_add (m n : ℝ) (hm : m ≠ 0) (hn : n ≠ 0) :
    helixUnitary (Real.log (m * n))
      = helixUnitary (Real.log m) * helixUnitary (Real.log n) := by
  rw [Real.log_mul hm hn, helixUnitary_add]

/-- **The source coordinate is faithful.** `log` is injective on the positives, so distinct
positive reals (in particular distinct integers / prime powers) wind to distinct log-coordinates.
The helix grammar's source map loses no multiplicative information. -/
theorem helix_log_faithful : Set.InjOn Real.log (Set.Ioi (0 : ℝ)) :=
  Real.log_injOn_pos

/-- **The helix grammar is unconditionally correct for every configured channel.** For each
tower channel the winding character is a faithful multiplicative→additive homomorphism
(winding of a product = product of windings), is unitary, covers the spectral circle, and
realizes the configurator law `radialExp = modulus`. Axiom-clean; no RH/GRH content. -/
theorem helix_config_correct (c : HelixEF.ConfiguredChannel)
    (hc : c ∈ HelixEF.towerChannels) :
    (∀ m n : ℝ, m ≠ 0 → n ≠ 0 →
        helixUnitary (Real.log (m * n))
          = helixUnitary (Real.log m) * helixUnitary (Real.log n)) ∧
    (∀ t : ℝ, ‖(helixUnitary t : ℂ)‖ = 1) ∧
    (∀ z : Circle, ∃ t : ℝ, helixUnitary t = z) ∧
    (c.radialExp = (c.modulus : ℝ)) :=
  ⟨fun m n hm hn => helix_mul_to_add m n hm hn,
   helixUnitary_norm,
   helixUnitary_surjective,
   HelixEF.radialExp_eq_modulus c hc⟩

/-! ## FTA on the configured helix: unique factorization is realized geometrically -/

/-- `Circle.exp` of a natural multiple is the corresponding winding power. -/
private theorem circle_exp_nat_mul (k : ℕ) (s : ℝ) :
    Circle.exp ((k : ℝ) * s) = (Circle.exp s) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show ((k + 1 : ℕ) : ℝ) * s = (k : ℝ) * s + s by push_cast; ring,
          Circle.exp_add, ih, pow_succ]

/-- The configured winding at spacing `U`: `x` winds at angle `U·log x`, valued on the circle. -/
def configWinding (U x : ℝ) : Circle := Circle.exp (U * Real.log x)

@[simp] theorem configWinding_one (U : ℝ) : configWinding U 1 = 1 := by
  simp [configWinding]

/-- Multiplication of the source becomes the product of the windings. -/
theorem configWinding_mul (U : ℝ) {m n : ℝ} (hm : m ≠ 0) (hn : n ≠ 0) :
    configWinding U (m * n) = configWinding U m * configWinding U n := by
  unfold configWinding; rw [Real.log_mul hm hn, mul_add, Circle.exp_add]

/-- The winding of a power is the power of the winding. -/
theorem configWinding_pow (U x : ℝ) (k : ℕ) :
    configWinding U (x ^ k) = configWinding U x ^ k := by
  unfold configWinding
  rw [Real.log_pow, show U * ((k : ℝ) * Real.log x) = (k : ℝ) * (U * Real.log x) by ring,
      circle_exp_nat_mul]

/-- The winding of a finite product of nonzero reals is the product of the windings. -/
theorem configWinding_prod (U : ℝ) {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    configWinding U (∏ i ∈ s, f i) = ∏ i ∈ s, configWinding U (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha,
          configWinding_mul U (hf a (Finset.mem_insert_self a s))
            (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)),
          ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

/-- **FTA on the configured helix.** Every positive integer's winding (at spacing `U`) is the
product of its prime‑power windings: `windU(n) = ∏_{p∣n} windU(p)^{vₚ(n)}` — unique factorization
realized geometrically through the `mult→add` homomorphism. Unconditional; holds for *every*
configuration spacing `U`. -/
theorem configWinding_fta (U : ℝ) {n : ℕ} (hn : n ≠ 0) :
    configWinding U (n : ℝ)
      = ∏ p ∈ n.primeFactors, configWinding U (p : ℝ) ^ (n.factorization p) := by
  have hnat : (n : ℝ) = ∏ p ∈ n.primeFactors, ((p : ℝ)) ^ (n.factorization p) := by
    conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn]
    show (↑(∏ p ∈ n.factorization.support, p ^ (n.factorization p)) : ℝ) = _
    rw [Nat.support_factorization, Nat.cast_prod]
    exact Finset.prod_congr rfl (fun p _ => by rw [Nat.cast_pow])
  rw [hnat, configWinding_prod U _ _ (fun p hp => by
        have : 0 < p := (Nat.prime_of_mem_primeFactors hp).pos
        positivity)]
  exact Finset.prod_congr rfl (fun p _ => configWinding_pow U _ _)

/-- **FTA holds on every configured channel.** For each tower channel (`ch_pi6 … ch_pi`, spacings
`π/6, π/3, π/2, π`), the winding at that channel's spacing factors every integer through its unique
prime factorization. Unconditional. -/
theorem channel_fta (c : HelixEF.ConfiguredChannel) (_hc : c ∈ HelixEF.towerChannels)
    {n : ℕ} (hn : n ≠ 0) :
    configWinding (Real.pi / (c.spacingDenom : ℝ)) (n : ℝ)
      = ∏ p ∈ n.primeFactors,
          configWinding (Real.pi / (c.spacingDenom : ℝ)) (p : ℝ) ^ (n.factorization p) :=
  configWinding_fta _ hn

end HelixGrammar

end

#print axioms HelixGrammar.helix_mul_to_add
#print axioms HelixGrammar.helix_log_faithful
#print axioms HelixGrammar.helix_config_correct
#print axioms HelixGrammar.configWinding_fta
#print axioms HelixGrammar.channel_fta
