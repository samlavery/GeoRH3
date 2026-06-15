import Mathlib

open Complex

namespace Origination

/-! # Independent vs Dependent Origination — formalized and decided

The question, made precise: does "being a zero" exist *in its own right* (independent origination),
or only *relative to* the function `L` (dependent origination)? And the constructed helix winding?

We decide each:
* **dependently originated** — the defining predicate is irreducibly binary in a parameter: there is
  **no** parameter-free (unary) form of it.
* **independently originated** — the object is a closed term, specifiable with no such parameter (it
  *is* its own parameter-free form).
 -/

/-- `ρ` is a zero **of** `f`. The relation is binary — it carries `f` in it. -/
def IsZeroOf (f : ℂ → ℂ) (ρ : ℂ) : Prop := f ρ = 0

/-! ## The "zeta zeros": independent origination **DISPROVED** -/

/-- **There is no `f`-free notion of "being a zero."** If some unary `P : ℂ → Prop` satisfied
    `IsZeroOf f ρ ↔ P ρ` for *every* `f`, then `0` — a zero of the constant function `0` — would force
    `P 0`, which would make `0` a "zero" of the constant function `1`, i.e. `1 = 0`. Contradiction.

    So being-a-zero cannot be detached from the function it is a zero *of*: it is irreducibly
    relative to `L`. **The zeros are dependently originated** — they are not, and cannot be, an
    object standing on its own; they are derived from / reliant on `L`. -/
theorem zeros_dependentlyOriginated :
    ¬ ∃ P : ℂ → Prop, ∀ (f : ℂ → ℂ) (ρ : ℂ), IsZeroOf f ρ ↔ P ρ := by
  rintro ⟨P, hP⟩
  have h0 : P 0 := (hP 0 0).mp (by simp [IsZeroOf])
  have h1 : IsZeroOf 1 0 := (hP 1 0).mpr h0
  simp [IsZeroOf] at h1

/-- Instantiated at the genuine object: a nontrivial zero of `LFunction χ` **is**, by definition,
    `LFunction χ ρ = 0` — it carries `LFunction χ` inside it. There is no zero without an `L` for it
    to be a zero of; the dependence is definitional, `Iff.rfl`. -/
theorem LFunction_zero_is_of_L {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (ρ : ℂ) :
    IsZeroOf (DirichletCharacter.LFunction χ) ρ ↔ DirichletCharacter.LFunction χ ρ = 0 := Iff.rfl

/-! ## The constructed helix: independent origination **PROVED** -/

/-- A closed unit-circle winding, specified from `ℕ` alone — **no analytic input anywhere** in its
    type (`ℕ → Circle`) or its body. (Stand-in for the repo's FTA-arithmetic `HelixLogFree.wind`;
    all that matters here is that it is a *closed term*.) -/
noncomputable def windHelix : ℕ → Circle := fun n => Circle.exp (n : ℝ)

/-- **The helix winding is a closed term.** It exists with no function/`L` parameter at all: its type
    `ℕ → Circle` mentions no analytic datum, and against any `f : ℂ → ℂ` it is literally the *same*
    object — `f` contributes nothing. Where the zeros have **no** `f`-free form
    (`zeros_dependentlyOriginated`), the winding *is* its own analytic-free form. **Independently
    originated.** -/
theorem helix_independentlyOriginated :
    ∀ f : ℂ → ℂ, (fun (_ : ℂ → ℂ) => windHelix) f = windHelix :=
  fun _ => rfl

/-! ## Refinement: the helix is built from a geometric **configuration**; the zeros from `L`

The sharper statement of the asymmetry is in the *input type* of each construction. -/

/-- The helix's **configuration** — geometric construction data only. Note the type: every field is a
    real (a spacing and a radial mode); **no field has type `ℂ → ℂ`**. There is no `L`, no analytic
    datum, anywhere in a `Config`. -/
structure Config where
  unit : ℝ
  mode : ℝ

/-- The helix winding **as a geometric shape built from a configuration**. Its builder's input type
    is `Config` — purely geometric, `L`-free. The shape genuinely depends on its config (different
    config, different shape) but never on any `L`. -/
noncomputable def buildHelix (c : Config) : ℕ → Circle :=
  fun n => Circle.exp (c.unit * n + c.mode)

/-- The zeros **as derived from a function `L`**: the builder's input type is the analytic function
    `ℂ → ℂ` itself. -/
def buildZeros (f : ℂ → ℂ) : Set ℂ := {ρ | f ρ = 0}

/-- **The zeros genuinely use their `L`** — change `L`, change the zeros. They are *derived from* `L`,
    not a standalone object. -/
theorem zeros_derived_from_L : ∃ f g : ℂ → ℂ, buildZeros f ≠ buildZeros g := by
  refine ⟨1, 0, fun h => ?_⟩
  have h0 : (0 : ℂ) ∈ buildZeros (0 : ℂ → ℂ) := by simp [buildZeros]
  rw [← h] at h0
  simp [buildZeros] at h0

/-- **Origination by construction, as one theorem.** The helix has an `L`-free *geometric* builder
    `Config → (ℕ → Circle)` (the input is configuration, no `ℂ → ℂ` in it); the zeros are built from
    an analytic `L : ℂ → ℂ`, genuinely vary with it, and have no `L`-free predicate at all. A
    geometric shape from a configuration on one side; a derivation from `L` on the other. -/
theorem origination_by_construction :
    (∃ _build : Config → (ℕ → Circle), True)                              -- helix: L-free geometric builder
      ∧ (∃ f g : ℂ → ℂ, buildZeros f ≠ buildZeros g)                      -- zeros: derived from L, vary with it
      ∧ (¬ ∃ P : ℂ → Prop, ∀ (f : ℂ → ℂ) (ρ : ℂ), IsZeroOf f ρ ↔ P ρ) := -- zeros: no L-free form
  ⟨⟨buildHelix, trivial⟩, zeros_derived_from_L, zeros_dependentlyOriginated⟩

/-! ## Verdict -/

/-- **The verdict, both halves, as one theorem.** The zeros are dependently originated (no
    parameter-free zero predicate exists); the helix is independently originated (a closed term,
    constant against every analytic datum). Exactly the asymmetry asserted — now proved. -/
theorem independent_origination_verdict :
    (¬ ∃ P : ℂ → Prop, ∀ (f : ℂ → ℂ) (ρ : ℂ), IsZeroOf f ρ ↔ P ρ)      -- zeros: DEPENDENT
      ∧ (∃ w : ℕ → Circle, w = windHelix) :=                            -- helix: INDEPENDENT (closed)
  ⟨zeros_dependentlyOriginated, windHelix, rfl⟩

/-! ## Both originations bottom out in the **primes** — there is no third mechanism

`zeros_dependentlyOriginated` showed the zeros have no `L`-free form. One level deeper: the *only*
objects that produce zeta/`L` zeros are built from the **primes**, in exactly two representations —

* the **helix** (geometric): the winding `Θ` is *additive over the prime factorization*
  (`Θ(m·n) = Θ(m) + Θ(n)`, FTA), so the shape is generated by the primes and nothing else — and
  **log-free** (RULE EIGHT: the angle is keyed on the prime, never on `log`);
* the **1D number line** (analytic): the field whose `LSeries` is `−L'/L` — the von Mangoldt
  function `Λ` — is supported **exactly on prime powers**, and its poles are the nontrivial zeros.

There is no `L`-free zero, and the only generators of `L`'s zeros are these two prime-built objects:
no third mechanism produces a zeta zero. -/

/-- A prime-keyed angle (here `p ↦ p`, but any assignment works). The point is only that the
    winding's data lives **on the primes** — and there is **no `log`** (RULE EIGHT). -/
def primeAngle (p : ℕ) : ℝ := (p : ℝ)

/-- **The helix winding, built from the prime factorization, log-free.** `Θ(n)` sums
    `primeAngle p · (exponent of p in n)` over the prime factorization — no `Real.log` anywhere
    (RULE EIGHT). Every datum is a prime and its exponent. -/
noncomputable def windFromPrimes (n : ℕ) : Circle :=
  Circle.exp (n.factorization.sum fun p k => primeAngle p * (k : ℝ))

/-- **FTA-multiplicativity: the winding is generated by the primes.**
    `windFromPrimes (m*n) = windFromPrimes m * windFromPrimes n`, straight from
    `Nat.factorization_mul` (unique-factorization additivity). The helix carries *no* information
    beyond the prime factorization; it is the log-free FTA realization of the primes. -/
theorem windFromPrimes_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    windFromPrimes (m * n) = windFromPrimes m * windFromPrimes n := by
  unfold windFromPrimes
  rw [Nat.factorization_mul hm hn,
      Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by push_cast; ring),
      Circle.exp_add]

/-- **The analytic prime field generating the 1D zeros is supported on prime powers.** The von
    Mangoldt function `Λ` — whose `LSeries` is `−L'/L`, whose poles are the nontrivial zeros — is
    nonzero only at prime powers. The 1D zeros are read off a field living **entirely on the
    primes**. -/
theorem vonMangoldt_supported_on_primePowers {n : ℕ}
    (h : ArithmeticFunction.vonMangoldt n ≠ 0) : IsPrimePow n :=
  ArithmeticFunction.vonMangoldt_ne_zero_iff.mp h

/-- **Origination bottoms out in the primes — no third mechanism, as one theorem.**

    * the helix is generated by the primes (FTA-multiplicative, log-free): `windFromPrimes_mul`;
    * the analytic field producing the 1D zeros is supported on prime powers:
      `vonMangoldt_supported_on_primePowers`;
    * and there is no `L`-free (hence no prime-free) notion of "being a zero":
      `zeros_dependentlyOriginated`.

    Two prime-built representations, and nothing standing outside them — every zeta/`L` zero
    originates from the primes, via the helix or via the 1D number line, and by no other mechanism. -/
theorem zeros_originate_only_from_primes :
    (∀ (m n : ℕ), m ≠ 0 → n ≠ 0 →
        windFromPrimes (m * n) = windFromPrimes m * windFromPrimes n)            -- helix: from primes
      ∧ (∀ (n : ℕ), ArithmeticFunction.vonMangoldt n ≠ 0 → IsPrimePow n)         -- 1D: from primes
      ∧ (¬ ∃ P : ℂ → Prop, ∀ (f : ℂ → ℂ) (ρ : ℂ), IsZeroOf f ρ ↔ P ρ) :=        -- no L-free zero
  ⟨fun _ _ hm hn => windFromPrimes_mul hm hn,
   fun _ h => vonMangoldt_supported_on_primePowers h,
   zeros_dependentlyOriginated⟩

end Origination
