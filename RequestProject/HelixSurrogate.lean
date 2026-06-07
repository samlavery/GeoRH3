import Mathlib

/-!
# Finite-rank bounded surrogate for the helix Hilbert–Pólya flow

Algebraic-first scaffold: a **quadratic form**, finite **truncations**, **unitarity as norm
preservation**, and only then the **spectral operator**. Everything here is finite and
algebraic — unconditional and circularity-free (no σ appears anywhere).

* `BoundaryForm L f = ‖L f‖²` — the boundary form = projection-loss energy, `≥ 0` (step 1);
* `boundaryMatrix L = Lᴴ L` — the completed boundary as the projection-loss Gram (steps 2,5);
* `completedBoundary_posSemidef` — PSD **by construction** (the matrix form of "boundary ≥ 0");
* `unitary_preserves_form` — `Uᴴ U = 1` preserves the boundary energy (step 3);
* `boundaryMatrix_isHermitian` + `boundaryMatrix_spectrum_real` — the Hermitian spectral
  operator `A_N` with **real** spectrum (step 6).

HONEST SCOPE: at finite rank the real-spectrum fact is structural, so this surrogate does not
decide GRH. It pins the algebraic core so the only remaining step is the **limit** `N → ∞`
(does every L-zero appear as a loss-mode) — the substantive loss-modes = L-functions claim.
-/

open Matrix
open scoped ComplexOrder

namespace HelixSurrogate

variable {m N : ℕ}

/-! ## Step 1 — the boundary quadratic form = projection-loss energy, nonnegative.

`L` is the projection-loss map at truncation `N` (kept abstract; a channel `F` instantiates it). -/

/-- The boundary form of `f`: the projection-loss energy `‖L f‖² = Σ |(L f)ᵢ|²`. -/
noncomputable def BoundaryForm (L : Matrix (Fin m) (Fin N) ℂ) (f : Fin N → ℂ) : ℝ :=
  ∑ i, ‖(L *ᵥ f) i‖ ^ 2

/-- **The boundary form is nonnegative** — `boundaryForm_nonneg` — by construction it is a
    sum of squared norms (the completed projection-loss energy). -/
theorem boundaryForm_nonneg (L : Matrix (Fin m) (Fin N) ℂ) (f : Fin N → ℂ) :
    0 ≤ BoundaryForm L f :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-! ## Steps 2 & 5 — the completed boundary IS the projection-loss Gram, PSD by construction. -/

/-- The completed boundary matrix: the Gram of the projection-loss map, `Lᴴ L`. -/
noncomputable def boundaryMatrix (L : Matrix (Fin m) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Lᴴ * L

/-- **The completed boundary IS the projection-loss Gram** (by construction). -/
theorem completedBoundary_eq_projectionLossGram (L : Matrix (Fin m) (Fin N) ℂ) :
    boundaryMatrix L = Lᴴ * L := rfl

/-- **The completed boundary matrix is positive semidefinite — by construction.**
    This is the matrix form of "the completed boundary form is non-negative". -/
theorem completedBoundary_posSemidef (L : Matrix (Fin m) (Fin N) ℂ) :
    (boundaryMatrix L).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self L

/-! ## Step 6 — the spectral operator `A_N`, Hermitian with real spectrum. -/

/-- The Hermitian spectral operator `A_N := boundaryMatrix L` (self-adjoint at finite rank). -/
theorem boundaryMatrix_isHermitian (L : Matrix (Fin m) (Fin N) ℂ) :
    (boundaryMatrix L).IsHermitian :=
  (completedBoundary_posSemidef L).isHermitian

/-- **Hermitian ⟹ real spectrum.** `spectrum ℝ A_N` is exactly its real eigenvalues — no
    off-axis spectral value. The finite-rank surrogate of the Hilbert–Pólya conclusion. -/
theorem boundaryMatrix_spectrum_real (L : Matrix (Fin m) (Fin N) ℂ) :
    spectrum ℝ (boundaryMatrix L) =
      Set.range (boundaryMatrix_isHermitian L).eigenvalues :=
  (boundaryMatrix_isHermitian L).spectrum_real_eq_range_eigenvalues

/-- PSD ⟹ the spectral parameters are nonnegative reals. -/
theorem boundaryMatrix_eigenvalues_nonneg (L : Matrix (Fin m) (Fin N) ℂ) (i : Fin N) :
    0 ≤ (completedBoundary_posSemidef L).1.eigenvalues i :=
  (completedBoundary_posSemidef L).eigenvalues_nonneg i

/-! ## Step 3 — unitarity as norm preservation (finite, dot-product form). -/

/-- **Unitarity = norm preservation.** A finite unitary `Uᴴ U = 1` preserves the boundary
    energy `⟨·,·⟩` — the finite surrogate of "the winding group is unitary on `H_F`". -/
theorem unitary_preserves_form (U : Matrix (Fin N) (Fin N) ℂ) (hU : Uᴴ * U = 1)
    (f : Fin N → ℂ) :
    star (U *ᵥ f) ⬝ᵥ (U *ᵥ f) = star f ⬝ᵥ f := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hU,
    Matrix.one_mulVec]

/-! ## Step 4 — the complex structure `J` (`i` as a real-linear map), separate from PSD.

Orientation/symmetry, kept apart from non-negativity: `J² = -1`, and `J` acts as
multiplication by `i` on the 2D frame (`frame (J v) = i • frame v`) — the geometric `i`
(with `i² = FE`). -/

/-- The real-linear complex structure `J` (a quarter-turn rotation of the real 2-plane). -/
def J : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

/-- **`J² = -1`** — `J` is a genuine complex structure. -/
theorem J_sq : J * J = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

/-- The frame map `ℝ² → ℂ`, `(a, b) ↦ a + b·i`. -/
def frame (v : Fin 2 → ℝ) : ℂ := (v 0 : ℂ) + (v 1 : ℂ) * Complex.I

/-- **Frame preservation**: `frame (J v) = i · frame v`. `J` acts as multiplication by `i`
    on the 2D frame — the orientation/symmetry structure. -/
theorem frame_J (v : Fin 2 → ℝ) : frame (J *ᵥ v) = Complex.I * frame v := by
  have h0 : (J *ᵥ v) 0 = - v 1 := by
    simp [J, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have h1 : (J *ᵥ v) 1 = v 0 := by
    simp [J, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  unfold frame
  rw [h0, h1, mul_add, mul_left_comm Complex.I (v 1 : ℂ) Complex.I, Complex.I_mul_I]
  push_cast; ring

end HelixSurrogate
