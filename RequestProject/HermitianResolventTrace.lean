import Mathlib

/-!
# The finite Hermitian resolvent-trace realization (the Frobenius scaffold)

`Tr((z·1 − A)⁻¹) = Σ_i 1/(z − λ_i)` for any Hermitian matrix `A`, the poles being its **real**
eigenvalues `λ_i`. This is the finite, kernel-clean form of the Frobenius/Hilbert–Pólya scaffold
that a resolvent-trace identity plugs into: a self-adjoint operator's resolvent trace is the sum
over its **real** spectrum, so any limit of such traces can only have **real** poles. That real-
poles fact is the on-line forcing in finite form — exactly the role "Frobenius acts on a
finite-dimensional space with real/√q-pure eigenvalues" plays in the function-field proof.

Mathlib-only, no `sorry`, no custom axiom. This is scaffolding, **not** the open weld: it does not
claim the eigenvalues are the ζ-zeros (that identification is the deferred analytic step). What it
proves is that the resolvent realization, once present, forces reality of the poles.
-/

open Matrix Unitary
open scoped ComplexOrder

namespace HermitianResolventTrace

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Finite resolvent-trace identity for any Hermitian matrix.** For `z` not an eigenvalue,
    `Tr((z·1 − A)⁻¹) = Σ_i 1/(z − λ_i)`, with `λ_i` the (real) eigenvalues. -/
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

/-- **The poles are real.** Every pole of `z ↦ Tr((z·1 − A)⁻¹)` is an eigenvalue `λ_i`, and these
    are real (`A` Hermitian): `Im (λ_i : ℂ) = 0`. The on-line forcing in finite form — a
    self-adjoint operator's resolvent has poles only on the real axis. -/
theorem hermitian_resolvent_poles_real {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    ∀ i, ((hA.eigenvalues i : ℂ)).im = 0 := by
  intro i; simp

/-- **Real poles pass to the limit.** If `z_N → z` and every `z_N` is real (`Im = 0`), then `z`
    is real. The limit half of the on-line forcing: a uniform limit of the finite Hermitian
    resolvent traces — whose poles are all real (`hermitian_resolvent_poles_real`) — cannot
    acquire a non-real pole, because a non-real limit pole would be a limit of real finite poles.
    (`Im` is continuous; the limit of `0` is `0`.) -/
theorem real_pole_of_limit {z : ℂ} {zN : ℕ → ℂ} (hreal : ∀ N, (zN N).im = 0)
    (hlim : Filter.Tendsto zN Filter.atTop (nhds z)) : z.im = 0 := by
  have h : Filter.Tendsto (fun N => (zN N).im) Filter.atTop (nhds z.im) :=
    (Complex.continuous_im.tendsto z).comp hlim
  simp only [hreal] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

end HermitianResolventTrace

#print axioms HermitianResolventTrace.hermitian_resolvent_trace
#print axioms HermitianResolventTrace.hermitian_resolvent_poles_real
#print axioms HermitianResolventTrace.real_pole_of_limit
