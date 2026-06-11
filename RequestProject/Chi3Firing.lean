import Mathlib

/-!
# The χ₃ signed-bucket firing — the geometric prime side

The prime counter runs up the helix sorting primes into χ₃'s two buckets by residue mod 6
(`p ≡ 1 → +`, `p ≡ 5 → −`). A **singularity fires** where the signed accumulation cancels
(`P₊ = P₋`), and it carries **energy `|primes|² = P₊²`** — nonzero even though the signed sum is `0`.
This is the geometric side of `EnergyBalance.energy_match_at_zero`: the `|primes|²` peak that must
match the spectral dip `n²`. No `½`, no on-line reasoning — pure prime counting.
-/

open Finset

namespace Chi3Firing

/-- χ₃'s sign on `p` by residue mod 3: `+1` for `p ≡ 1`, `−1` for `p ≡ 2`, `0` for `3 ∣ p`
    (so `p ≡ 1 mod 6 → +1`, `p ≡ 5 mod 6 → −1`). -/
def chi3Sign (p : ℕ) : ℝ := if p % 3 = 1 then 1 else if p % 3 = 2 then -1 else 0

variable (w : ℕ → ℝ)

/-- The **signed prime accumulation** `P₊ − P₋` up to `x` — the geometric prime side. -/
def signedAccum (x : ℕ) : ℝ := ∑ p ∈ range x, chi3Sign p * w p

/-- The **positive bucket** `P₊` — primes `≡ 1 (mod 6)`. -/
def posBucket (x : ℕ) : ℝ := ∑ p ∈ range x with p % 3 = 1, w p

/-- The **negative bucket** `P₋` — primes `≡ 5 (mod 6)`. -/
def negBucket (x : ℕ) : ℝ := ∑ p ∈ range x with p % 3 = 2, w p

/-- **The signed accumulation is `P₊ − P₋`.** -/
theorem signedAccum_eq_buckets (x : ℕ) : signedAccum w x = posBucket w x - negBucket w x := by
  rw [signedAccum, posBucket, negBucket, sum_filter, sum_filter, ← sum_sub_distrib]
  refine sum_congr rfl fun p _ => ?_
  rw [chi3Sign]
  have h3 : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
  rcases h3 with h | h | h <;> simp [h]

/-- **The firing condition**: the signed accumulation cancels, `P₊ = P₋`. -/
def Firing (x : ℕ) : Prop := posBucket w x = negBucket w x

/-- **At a firing the signed accumulation vanishes** — but the energy need not. -/
theorem signedAccum_zero_of_firing {x : ℕ} (h : Firing w x) : signedAccum w x = 0 := by
  rw [signedAccum_eq_buckets, h, sub_self]

/-- The **singularity energy** `|primes|² = P₊²`. -/
def firingEnergy (x : ℕ) : ℝ := (posBucket w x) ^ 2

/-- **At a firing the energy is `P₊² = P₋²`** — equal squared sides, though the signed sum is `0`.
    This is the `|primes|²` the spectral dip `n²` must match. -/
theorem firingEnergy_eq_neg_sq {x : ℕ} (h : Firing w x) :
    firingEnergy w x = (negBucket w x) ^ 2 := by rw [firingEnergy, h]

/-- The energy is non-negative (a squared amplitude). -/
theorem firingEnergy_nonneg (x : ℕ) : 0 ≤ firingEnergy w x := sq_nonneg _

end Chi3Firing
