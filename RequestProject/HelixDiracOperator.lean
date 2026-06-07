import Mathlib
import RequestProject.HelixChannelInstance

/-!
# The chiral / Dirac block operator `A_N = [[0, Bᴴ], [B, 0]]`

The right Hilbert–Pólya object at finite rank. From the sampled analysis operator `B = B_N`
(`HelixChannelInstance.lossMatrix`) we form the **chiral block**

```
A_N = [ 0    Bᴴ ]
      [ B    0  ]
```

which is **manifestly self-adjoint by construction** (`diracBlock_isHermitian`). Hence its
spectrum is **real** — and `A_N² = diag(BᴴB, BBᴴ)` (`diracBlock_sq`), so
`spec(A_N) = ± singular_values(B)`. This is the genuine self-adjoint operator whose real
spectrum is the right object (unlike the PSD Gram, whose eigenvalues are singular values, not
a symmetric real spectrum).

The remaining open step is the **limit**: `Tr_reg((zI − A_N)⁻¹) → −Λ_F'/Λ_F(½ + iz)` and
"every pole of `−Λ_F'/Λ_F(½+iz)` is a limit of real spectral poles of `A_N`". Since `A_N`'s
spectral poles are real (self-adjoint) and limits of reals are real, that limit claim forces
each pole `z = γ − i(σ−½)` to be real, i.e. σ=½ — it *is* GRH_F.
-/

open Matrix
open scoped ComplexOrder

namespace HelixDirac

/-- A full channel: helix geometry (`angleUnit = π/m`, `pitch`, `radialUnit = e^m`) plus the
    arithmetic fibre `chi`. -/
structure Channel where
  m : ℕ
  angleUnit : ℝ
  pitch : ℝ
  radialUnit : ℝ
  chi : ℕ → ℂ

/-- ζ — helix unit `π/6`, radial `e³`, trivial fibre. -/
noncomputable def zeta : Channel :=
  ⟨3, Real.pi / 6, Real.pi / 6, Real.exp 3, fun _ => 1⟩

/-- χ₃ — helix unit `π/3`, radial `e⁶`, real mod-3 fibre. -/
noncomputable def chi3 : Channel :=
  ⟨6, Real.pi / 3, Real.pi / 3, Real.exp 6,
    fun n => if n % 3 = 1 then 1 else if n % 3 = 2 then -1 else 0⟩

/-- χ₈ — helix unit `π/2`, radial `e⁸`, real mod-8 fibre. -/
noncomputable def chi8 : Channel :=
  ⟨8, Real.pi / 2, Real.pi / 2, Real.exp 8,
    fun n => if n % 8 = 1 ∨ n % 8 = 7 then 1
             else if n % 8 = 3 ∨ n % 8 = 5 then -1 else 0⟩

variable {p q : ℕ}

/-- **The chiral / Dirac block operator** `A = [[0, Bᴴ], [B, 0]]`. -/
noncomputable def diracBlock (B : Matrix (Fin p) (Fin q) ℂ) :
    Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) ℂ :=
  Matrix.fromBlocks 0 Bᴴ B 0

/-- **`A = Aᴴ` — manifestly self-adjoint, by construction.** -/
theorem diracBlock_isHermitian (B : Matrix (Fin p) (Fin q) ℂ) :
    (diracBlock B).IsHermitian := by
  show (diracBlock B)ᴴ = diracBlock B
  unfold diracBlock
  rw [Matrix.fromBlocks_conjTranspose]
  simp

/-- **`A² = diag(BᴴB, BBᴴ)`** — the two Grams on the diagonal, so `spec(A) = ± sing.val.(B)`. -/
theorem diracBlock_sq (B : Matrix (Fin p) (Fin q) ℂ) :
    diracBlock B * diracBlock B = Matrix.fromBlocks (Bᴴ * B) 0 0 (B * Bᴴ) := by
  unfold diracBlock
  rw [Matrix.fromBlocks_multiply]
  simp

/-- **The Dirac operator's spectrum is real** — by self-adjointness. The `±` singular values
    of `B`; the finite-rank surrogate of the (now genuinely self-adjoint) HP spectrum. -/
theorem diracBlock_spectrum_real (B : Matrix (Fin p) (Fin q) ℂ) :
    spectrum ℝ (diracBlock B) =
      Set.range (diracBlock_isHermitian B).eigenvalues :=
  (diracBlock_isHermitian B).spectrum_real_eq_range_eigenvalues

/-- The channel's finite Dirac operator, on its sampled analysis operator `B_N`. -/
noncomputable def channelDirac (C : Channel) {m : ℕ} (u : Fin m → ℝ) (N : ℕ) :
    Matrix (Fin N ⊕ Fin m) (Fin N ⊕ Fin m) ℂ :=
  diracBlock (HelixChannelInstance.lossMatrix C.chi u N)

/-- **The channel's Dirac operator is self-adjoint with real spectrum** — the genuine
    self-adjoint HP operator for channel `C` at truncation `N`. -/
theorem channelDirac_isHermitian (C : Channel) {m : ℕ} (u : Fin m → ℝ) (N : ℕ) :
    (channelDirac C u N).IsHermitian :=
  diracBlock_isHermitian _

end HelixDirac
