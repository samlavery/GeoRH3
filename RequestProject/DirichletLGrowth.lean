import Mathlib
import RequestProject.DirichletLHadamard

/-!
# Step 4 (the hard brick): growth of `L(χ,·)` toward the order-1 Hadamard product

The character `χ ≠ 1` is *more* tractable than ζ here: its partial sums over a full period cancel
(`∑_{a : ZMod N} χ a = 0`), so the partial-sum function is **bounded**, which (via Abel summation)
gives an entire continuation with a polynomial vertical-strip bound and **no pole** — avoiding ζ's
Euler–Maclaurin-with-pole. This file builds the foundational χ-fact: **bounded partial sums.**
The remaining growth chain (Abel bound, Γ-Stirling, functional equation ⇒ order-1, then the
χ-agnostic Jensen scaffold ⇒ `∑ ord(ρ)/‖ρ‖² < ∞`) is staged.
-/

open Complex

namespace DirichletLHadamard

variable {N : ℕ} [NeZero N]

/-- Summing a function over `Finset.range N` via the `ℕ → ZMod N` cast is the full sum over
    `ZMod N` (the cast is a bijection on a complete residue block). -/
theorem sum_range_eq_sum_zmod (g : ZMod N → ℂ) :
    ∑ j ∈ Finset.range N, g (j : ZMod N) = ∑ a : ZMod N, g a := by
  refine Finset.sum_nbij' (fun j => (j : ZMod N)) (fun a => a.val) ?_ ?_ ?_ ?_ ?_
  · intro j _; exact Finset.mem_univ _
  · intro a _; exact Finset.mem_range.mpr a.val_lt
  · intro j hj; exact ZMod.val_natCast_of_lt (Finset.mem_range.mp hj)
  · intro a _; exact ZMod.natCast_rightInverse a
  · intro j _; rfl

/-- **A full block of `N` consecutive character values cancels** (for `χ ≠ 1`): the translation
    invariance of the complete-residue sum plus `∑_{a} χ a = 0`. -/
theorem chi_block_sum_zero {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (M : ℕ) :
    ∑ j ∈ Finset.range N, χ ((M + j : ℕ) : ZMod N) = 0 := by
  have e1 : ∑ j ∈ Finset.range N, χ ((M + j : ℕ) : ZMod N)
      = ∑ j ∈ Finset.range N, χ ((M : ZMod N) + (j : ZMod N)) :=
    Finset.sum_congr rfl (fun j _ => by congr 1; push_cast; ring)
  have e2 : ∑ j ∈ Finset.range N, χ ((M : ZMod N) + (j : ZMod N))
      = ∑ a : ZMod N, χ ((M : ZMod N) + a) :=
    sum_range_eq_sum_zmod (fun a => χ ((M : ZMod N) + a))
  have e3 : ∑ a : ZMod N, χ ((M : ZMod N) + a) = ∑ a : ZMod N, χ a :=
    Equiv.sum_comp (Equiv.addLeft (M : ZMod N)) χ
  rw [e1, e2, e3]
  exact MulChar.sum_eq_zero_of_ne_one hχ

/-- **The character partial-sum function is `N`-periodic** (each added block cancels). -/
theorem chiPartialSum_periodic {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (M : ℕ) :
    ∑ n ∈ Finset.range (M + N), χ (n : ZMod N) = ∑ n ∈ Finset.range M, χ (n : ZMod N) := by
  have hblock : ∑ n ∈ Finset.Ico M (M + N), χ (n : ZMod N) = 0 := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_left]
    exact chi_block_sum_zero hχ M
  have hsub := Finset.sum_Ico_eq_sub (fun n => χ ((n : ℕ) : ZMod N)) (Nat.le_add_right M N)
  rw [hblock] at hsub
  exact sub_eq_zero.mp hsub.symm

/-- **Bounded character partial sums** — the key fact making `L(χ,·)` (for `χ ≠ 1`) tractable: the
    partial sums of `χ` are bounded uniformly in `M`, by `∑_{j<N} ‖χ(j)‖ ≤ N`. (This is what drives
    the Abel-summation polynomial strip bound, with no pole — unlike ζ.) -/
theorem chiPartialSum_bounded {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    ∃ B : ℝ, ∀ M : ℕ, ‖∑ n ∈ Finset.range M, χ (n : ZMod N)‖ ≤ B := by
  refine ⟨∑ j ∈ Finset.range N, ‖χ (j : ZMod N)‖, fun M => ?_⟩
  have hkr : ∀ (k r : ℕ),
      ∑ n ∈ Finset.range (N * k + r), χ (n : ZMod N)
        = ∑ n ∈ Finset.range r, χ (n : ZMod N) := by
    intro k
    induction k with
    | zero => intro r; simp
    | succ k ih =>
        intro r
        have he : N * (k + 1) + r = (N * k + r) + N := by ring
        rw [he, chiPartialSum_periodic hχ, ih]
  have hM : ∑ n ∈ Finset.range M, χ (n : ZMod N)
      = ∑ n ∈ Finset.range (M % N), χ (n : ZMod N) := by
    have h := hkr (M / N) (M % N)
    rwa [Nat.div_add_mod] at h
  rw [hM]
  have hNpos : 0 < N := Nat.pos_of_ne_zero (‹NeZero N›.out)
  calc ‖∑ n ∈ Finset.range (M % N), χ (n : ZMod N)‖
      ≤ ∑ n ∈ Finset.range (M % N), ‖χ (n : ZMod N)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range N, ‖χ (j : ZMod N)‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun x hx => Finset.mem_range.mpr
            (lt_of_lt_of_le (Finset.mem_range.mp hx) (le_of_lt (Nat.mod_lt M hNpos))))
          (fun _ _ _ => norm_nonneg _)

/-- Bounded partial sums over `Icc 1 m` (the form appearing in the Abel integrand). -/
theorem chiPartialSum_Icc_bounded {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ m : ℕ, ‖∑ k ∈ Finset.Icc 1 m, χ (k : ZMod N)‖ ≤ B := by
  obtain ⟨B, hB⟩ := chiPartialSum_bounded hχ
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  refine ⟨B + ‖χ (0 : ZMod N)‖, add_nonneg hB0 (norm_nonneg _), fun m => ?_⟩
  have hset : Finset.range (m + 1) = insert 0 (Finset.Icc 1 m) := by
    ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  have hsplit : ∑ k ∈ Finset.Icc 1 m, χ (k : ZMod N)
      = (∑ k ∈ Finset.range (m + 1), χ (k : ZMod N)) - χ (0 : ZMod N) := by
    rw [hset, Finset.sum_insert (by simp)]; simp only [Nat.cast_zero]; ring
  rw [hsplit]
  calc ‖(∑ k ∈ Finset.range (m + 1), χ (k : ZMod N)) - χ (0 : ZMod N)‖
      ≤ ‖∑ k ∈ Finset.range (m + 1), χ (k : ZMod N)‖ + ‖χ (0 : ZMod N)‖ := norm_sub_le _ _
    _ ≤ B + ‖χ (0 : ZMod N)‖ := by gcongr; exact hB (m + 1)

open MeasureTheory in
/-- **Abel integral representation of `L(χ,·)`** for `Re s > 1`: from mathlib's
    `LSeries_eq_mul_integral'`, using only `‖χ(k)‖ ≤ 1` (so `∑‖χ(k)‖ = O(n)`). The integrand's
    partial sums are bounded (`chiPartialSum_bounded`), so the right-hand integral in fact converges
    for all `Re s > 0` — this representation is the analytic continuation that gives the strip bound. -/
theorem LFunction_eq_abel_integral {χ : DirichletCharacter ℂ N} {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.LFunction χ s
      = s * ∫ t in Set.Ioi (1 : ℝ),
          (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ (k : ZMod N)) * (t : ℂ) ^ (-(s + 1)) := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  refine LSeries_eq_mul_integral' (fun n => χ (n : ZMod N)) zero_le_one hs ?_
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, Filter.Eventually.of_forall (fun n => ?_)⟩
  have hnn : (0 : ℝ) ≤ ∑ k ∈ Finset.Icc 1 n, ‖χ (k : ZMod N)‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnn, Real.rpow_one]
  calc ∑ k ∈ Finset.Icc 1 n, ‖χ (k : ZMod N)‖
      ≤ ∑ _k ∈ Finset.Icc 1 n, (1 : ℝ) :=
        Finset.sum_le_sum (fun k _ => DirichletCharacter.norm_le_one χ _)
    _ = (n : ℝ) := by simp [Nat.card_Icc]
    _ = 1 * ‖(n : ℝ)‖ := by rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n), one_mul]

end DirichletLHadamard
