import Mathlib
import RequestProject.HelixSurrogate

/-!
# Channel instantiation — the sampled analysis operator `lossMatrix F N`

Wires the abstract `L` of `HelixSurrogate` to the concrete, channel-specific **sampled
analysis operator**:

* **rows** — boundary sample points `u_j` (the critical-line boundary `s_j = ½ + i u_j`);
* **columns** — arithmetic atoms, the integer `k+1` for `k : Fin N`;
* **entry** — the completed projection-loss response of atom `n = k+1` at `u_j`:
  the von Mangoldt explicit-formula atom `Λ(n)·χ(n)·n^{-s_j}`.

The channel (helix unit `π/d`) selects the character `χ` (π/6 → ζ, π/3 → χ₃, π/2 → χ₄, …).
The completed-boundary Gram `lossMatrixᴴ · lossMatrix` is then an **instance of the verified
scaffold**: PSD, Hermitian, real spectrum — all inherited, on the actual arithmetic atoms.

The substantive open step remains the limit `N → ∞`: whether the eigen-modes of this Gram
converge onto the zeros of `L(·,χ)` (the loss-modes = L-functions identification).
-/

open Matrix
open scoped ComplexOrder

namespace HelixChannelInstance

variable {m : ℕ}

/-- The boundary point at scale sample `uj`: the critical-line point `½ + i·uj`. -/
noncomputable def boundaryPoint (uj : ℝ) : ℂ := (1 / 2 : ℂ) + Complex.I * (uj : ℂ)

/-- **The sampled analysis operator.** Entry `(j, k)` is the completed projection-loss
    response of arithmetic atom `n = k+1` at boundary sample `u j`:
    `Λ(n) · χ(n) · n^{-s_j}` with `s_j = ½ + i (u j)`. -/
noncomputable def lossMatrix (χ : ℕ → ℂ) (u : Fin m → ℝ) (N : ℕ) :
    Matrix (Fin m) (Fin N) ℂ :=
  fun j k =>
    ((ArithmeticFunction.vonMangoldt (k.val + 1) : ℝ) : ℂ) * χ (k.val + 1) *
      ((k.val + 1 : ℕ) : ℂ) ^ (-boundaryPoint (u j))

/-- The completed-boundary Gram of the channel: `lossMatrixᴴ · lossMatrix`. -/
noncomputable def completedBoundaryMatrix (χ : ℕ → ℂ) (u : Fin m → ℝ) (N : ℕ) :
    Matrix (Fin N) (Fin N) ℂ :=
  HelixSurrogate.boundaryMatrix (lossMatrix χ u N)

/-- **The channel's completed-boundary Gram is positive semidefinite** (scaffold instance). -/
theorem completedBoundary_posSemidef (χ : ℕ → ℂ) (u : Fin m → ℝ) (N : ℕ) :
    (completedBoundaryMatrix χ u N).PosSemidef :=
  HelixSurrogate.completedBoundary_posSemidef (lossMatrix χ u N)

/-- **It is Hermitian** — the channel's completed-boundary spectral operator `A_N`. -/
theorem completedBoundary_isHermitian (χ : ℕ → ℂ) (u : Fin m → ℝ) (N : ℕ) :
    (completedBoundaryMatrix χ u N).IsHermitian :=
  HelixSurrogate.boundaryMatrix_isHermitian (lossMatrix χ u N)

/-- **Its spectrum is real** — Hermitian ⟹ real spectrum, now on the actual arithmetic
    atoms of the channel. The finite-rank surrogate of the Hilbert–Pólya conclusion for `χ`. -/
theorem completedBoundary_spectrum_real (χ : ℕ → ℂ) (u : Fin m → ℝ) (N : ℕ) :
    spectrum ℝ (completedBoundaryMatrix χ u N) =
      Set.range (completedBoundary_isHermitian χ u N).eigenvalues :=
  HelixSurrogate.boundaryMatrix_spectrum_real (lossMatrix χ u N)

/-- The trivial channel `χ ≡ 1` (helix unit `π/6`): the ζ instance. -/
def zetaChar : ℕ → ℂ := fun _ => 1

end HelixChannelInstance
