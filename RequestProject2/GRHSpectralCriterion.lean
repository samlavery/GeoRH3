import Mathlib
import RequestProject.SpectralSide

/-!
# The GRH spectral criterion for Dirichlet `L(s,χ)`

The GRH analog of `riemannHypothesis_iff_spectral_unitary`, for any non-principal
Dirichlet character `χ` (χ₃ is an instance). Uses Mathlib's `DirichletCharacter.LFunction`
and the same Möbius spectral value `w(ρ)=1−1/ρ`:

* `GRH χ` ⟺ every nontrivial zero's `w(ρ)` is on the unit circle (`GRH_iff_spectral_unitary`);
* the **edge** is Euler-powered and already in Mathlib: no nontrivial zero has `Re ≥ 1`
  (`no_zero_re_ge_one`).
-/

noncomputable section
open Complex DirichletCharacter

namespace GRHSpectral

variable {N : ℕ} [NeZero N]

/-- The nontrivial zeros of `L(s,χ)`: the critical-strip zeros. -/
def NontrivialZeros (χ : DirichletCharacter ℂ N) : Set ℂ :=
  {s | 0 < s.re ∧ s.re < 1 ∧ LFunction χ s = 0}

/-- **GRH for χ** — the per-character instance: every nontrivial zero of
`L(s,χ)` lies on the critical line. -/
def GRH (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ ρ ∈ NontrivialZeros χ, ρ.re = 1 / 2

/-- **The actual GRH** — the conjecture itself, not an instance: EVERY
Dirichlet L-function, every modulus, every character, principal included,
has all its nontrivial zeros on the critical line. Contains RH (the
principal characters' strip zeros are ζ's: the finite Euler factors vanish
only on `re = 0`). The program's per-character capstones cover the `χ ≠ 1`
instances; the principal instances are the ζ content. -/
def GRHComplete : Prop :=
  ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M), GRH χ

/-- A nontrivial zero is nonzero (its real part is positive). -/
theorem nontrivial_ne_zero {χ : DirichletCharacter ℂ N} {ρ : ℂ}
    (hρ : ρ ∈ NontrivialZeros χ) : ρ ≠ 0 := by
  intro h; rw [h] at hρ; exact absurd hρ.1 (by simp)

/-- **The GRH(χ) spectral criterion.** GRH for `χ` holds ⟺ every nontrivial zero's
    Möbius spectral value `w(ρ) = 1 − 1/ρ` lies on the unit circle — i.e. the spectral
    operator is unitary on the `χ`-zeros. -/
theorem GRH_iff_spectral_unitary (χ : DirichletCharacter ℂ N) :
    GRH χ ↔ (∀ ρ ∈ NontrivialZeros χ, Complex.normSq (SpectralSide.w ρ) = 1) := by
  constructor
  · intro h ρ hρ
    exact (SpectralSide.w_unit_iff_half ρ (nontrivial_ne_zero hρ)).mpr (h ρ hρ)
  · intro h ρ hρ
    exact (SpectralSide.w_unit_iff_half ρ (nontrivial_ne_zero hρ)).mp (h ρ hρ)

/-- **The edge (Euler-powered, from Mathlib):** for non-principal `χ`, no zero has
    `Re ≥ 1`. This is what confines the zeros to the strip — the genuine Euler input,
    not a restatement. -/
theorem no_zero_re_ge_one {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {ρ : ℂ}
    (hρ : 1 ≤ ρ.re) : LFunction χ ρ ≠ 0 :=
  LFunction_ne_zero_of_one_le_re χ (.inl hχ) hρ

/-- Every nontrivial zero genuinely sits in the open strip on the upper side
    (`Re < 1`), recovered from the edge. -/
theorem nontrivial_re_lt_one {χ : DirichletCharacter ℂ N} {ρ : ℂ}
    (hρ : ρ ∈ NontrivialZeros χ) : ρ.re < 1 := hρ.2.1

end GRHSpectral

#print axioms GRHSpectral.GRH_iff_spectral_unitary
#print axioms GRHSpectral.no_zero_re_ge_one
