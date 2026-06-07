import Mathlib
import RequestProject.HelixSurrogate

/-!
# The log-free helix coordinate: factorization-additive winding

The source coordinate is **not** `log n`. It is the factorization-additive winding angle

```
Θ_F(n) = Σ_{p^a ∥ n} a · Θ_F(p)
```

for which multiplication becomes addition **by the Fundamental Theorem of Arithmetic**, not by
`log`: `Θ_F(m·n) = Θ_F(m) + Θ_F(n)` (`factorAngle_mul`). Primes carry per-channel directions
(the fibre); composites inherit by factorization sum. The radial shell is the loop count `k`
with `R = e^m·k` and area law `n ≈ k²` (so `R ≈ √n`, the critical ½ frame).

The `lossMatrix` atom then reads its phase from this factorization geometry —
`exp(i · ⟨rowDir_j, Θ_F(n)⟩)` — never from the analytic Mellin phase `exp(-i u_j log n)`.
This feeds the same verified scaffold (`HelixSurrogate`): PSD boundary Gram, self-adjoint Dirac
operator, real spectrum — now on a genuinely log-free construction.
-/

open scoped BigOperators ComplexOrder

namespace HelixFactor

/-- A channel: helix geometry (`m`, `radialUnit = e^m`, `angleUnit`, `pitch`), the arithmetic
    fibre `chi`, and the per-prime winding direction `primeAngle`. -/
structure Channel where
  m : ℕ
  radialUnit : ℝ
  angleUnit : ℝ
  pitch : ℝ
  chi : ℕ → ℂ
  primeAngle : ℕ → ℝ

/-- **The factorization-additive winding angle** `Θ_F(n) = Σ_{p^a ∥ n} a · Θ_F(p)`,
    as a sum over the prime factorization (`Nat.factorization`). No `log`. -/
noncomputable def factorAngle (F : Channel) (n : ℕ) : ℝ :=
  n.factorization.sum fun p e => (e : ℝ) * F.primeAngle p

@[simp] theorem factorAngle_one (F : Channel) : factorAngle F 1 = 0 := by
  simp [factorAngle]

/-- **Multiplication becomes addition — the FTA doing the job usually outsourced to `log`.**
    `Θ_F(m·n) = Θ_F(m) + Θ_F(n)` for nonzero `m, n`. This is the log-free primitive. -/
theorem factorAngle_mul (F : Channel) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    factorAngle F (m * n) = factorAngle F m + factorAngle F n := by
  unfold factorAngle
  rw [Nat.factorization_mul hm hn,
    Finsupp.sum_add_index' (fun p => by simp) (fun p a b => by push_cast; ring)]

/-! ## The three channels (geometry + fibre + prime directions) -/

/-- ζ — helix unit `π/6`, radial `e³`, trivial fibre (every prime the same direction). -/
noncomputable def zeta : Channel where
  m := 3; radialUnit := Real.exp 3; angleUnit := Real.pi / 6; pitch := Real.pi / 6
  chi := fun _ => 1
  primeAngle := fun _ => 1

/-- χ₃ (mod 6) — `p ≡ 1 → +`, `p ≡ 5 → −`, `p = 3` conductor-null. -/
noncomputable def chi3 : Channel where
  m := 6; radialUnit := Real.exp 6; angleUnit := Real.pi / 3; pitch := Real.pi / 3
  chi := fun n => if n % 3 = 1 then 1 else if n % 3 = 2 then -1 else 0
  primeAngle := fun p => if p % 6 = 1 then 1 else if p % 6 = 5 then -1 else 0

/-- χ₈ (mod 8) — `p ≡ 1,7 → +`, `p ≡ 3,5 → −`, even conductor-null. -/
noncomputable def chi8 : Channel where
  m := 8; radialUnit := Real.exp 8; angleUnit := Real.pi / 2; pitch := Real.pi / 2
  chi := fun n => if n % 8 = 1 ∨ n % 8 = 7 then 1 else if n % 8 = 3 ∨ n % 8 = 5 then -1 else 0
  primeAngle := fun p => if p % 8 = 1 ∨ p % 8 = 7 then 1 else if p % 8 = 3 ∨ p % 8 = 5 then -1 else 0

/-! ## The log-free `lossMatrix` atom -/

/-- **The log-free sampled analysis operator.** Entry `(j, n)`: amplitude × fibre ×
    `exp(i · rowPhase_j · Θ_F(n))` × √(projection-loss) — the phase read from factorization
    geometry, never from `exp(-i u_j log n)`. -/
noncomputable def lossMatrix (F : Channel) {M N : ℕ} (rowPhase : Fin M → ℝ)
    (amp : ℕ → ℝ) (ploss : Fin M → ℕ → ℝ) : Matrix (Fin M) (Fin N) ℂ :=
  fun j n =>
    (amp (n.val + 1) : ℂ) * F.chi (n.val + 1)
      * Complex.exp (Complex.I * (rowPhase j : ℂ) * (factorAngle F (n.val + 1) : ℂ))
      * (Real.sqrt (ploss j (n.val + 1)) : ℂ)

/-- The completed-boundary Gram of the log-free construction is PSD (scaffold instance). -/
theorem completedBoundary_posSemidef (F : Channel) {M N : ℕ} (rowPhase : Fin M → ℝ)
    (amp : ℕ → ℝ) (ploss : Fin M → ℕ → ℝ) :
    (HelixSurrogate.boundaryMatrix (lossMatrix F rowPhase amp ploss (N := N))).PosSemidef :=
  HelixSurrogate.completedBoundary_posSemidef _

end HelixFactor
