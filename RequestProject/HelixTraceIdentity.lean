import Mathlib
import RequestProject.HelixDiracOperator

/-!
# The finite resolvent trace identity (generic — every channel at once)

`Tr((z·1 − A)⁻¹) = Σ_i 1/(z − λ_i)` for any Hermitian `A`, with the spectral poles being the
real eigenvalues. Proved once, generically; specialized to the Dirac operator of *every*
channel `C` (`channelDirac_resolvent_trace`). The poles of the finite trace are real (`A`
self-adjoint), so the limit `T_N → −Λ'/Λ(½+iz)` can only have real poles — the GRH content.
-/

open Matrix Unitary
open scoped ComplexOrder

namespace HelixTrace

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Finite resolvent trace identity for any Hermitian matrix.** For `z` not an eigenvalue,
    `Tr((z·1 − A)⁻¹) = Σ_i 1/(z − λ_i)`. -/
theorem hermitian_resolvent_trace {A : Matrix n n ℂ} (hA : A.IsHermitian) {z : ℂ}
    (hz : ∀ i, z ≠ (hA.eigenvalues i : ℂ)) :
    Matrix.trace ((z • (1 : Matrix n n ℂ) - A)⁻¹) =
      ∑ i, (z - (hA.eigenvalues i : ℂ))⁻¹ := by
  classical
  set d : n → ℂ := fun i => z - (hA.eigenvalues i : ℂ) with hd
  have hdne : ∀ i, d i ≠ 0 := fun i => sub_ne_zero.mpr (hz i)
  set Φ := conjStarAlgAut ℂ (Matrix n n ℂ) hA.eigenvectorUnitary with hΦ
  have hAeq : A = Φ (diagonal (RCLike.ofReal ∘ hA.eigenvalues)) := hA.spectral_theorem
  have hdiag : diagonal d
      = z • (1 : Matrix n n ℂ) - diagonal (RCLike.ofReal ∘ hA.eigenvalues) := by
    ext i j
    rcases eq_or_ne i j with h | h
    · subst h
      simp [hd, Matrix.diagonal_apply_eq, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.one_apply_eq, Function.comp]
    · simp [hd, Matrix.diagonal_apply_ne _ h, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.one_apply_ne h]
  have hMeq : z • (1 : Matrix n n ℂ) - A = Φ (diagonal d) := by
    simp only [hdiag, hAeq, map_sub, map_smul, map_one]
  have hR : (z • (1 : Matrix n n ℂ) - A) * Φ (diagonal (fun i => (d i)⁻¹)) = 1 := by
    rw [hMeq, ← map_mul, diagonal_mul_diagonal,
      show (fun i => d i * (d i)⁻¹) = (1 : n → ℂ) from
        funext fun i => mul_inv_cancel₀ (hdne i)]
    simp
  rw [Matrix.inv_eq_right_inv hR, hΦ, conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal]

/-- **The resolvent trace identity for every channel's Dirac operator** (all `C` at once):
    the poles in `z` of `Tr((z·1 − A_N)⁻¹)` are the real spectral values `μ_{N,j}`. -/
theorem channelDirac_resolvent_trace (C : HelixDirac.Channel) {m : ℕ} (u : Fin m → ℝ) (N : ℕ)
    {z : ℂ} (hz : ∀ i, z ≠ ((HelixDirac.channelDirac_isHermitian C u N).eigenvalues i : ℂ)) :
    Matrix.trace ((z • (1 : Matrix (Fin N ⊕ Fin m) (Fin N ⊕ Fin m) ℂ)
        - HelixDirac.channelDirac C u N)⁻¹) =
      ∑ i, (z - ((HelixDirac.channelDirac_isHermitian C u N).eigenvalues i : ℂ))⁻¹ :=
  hermitian_resolvent_trace (HelixDirac.channelDirac_isHermitian C u N) hz

end HelixTrace
