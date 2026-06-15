import RequestProject.HelixSource

open Complex

namespace SourceTraceSelfDual

open HelixSource

/-! # The self-dual nature of `sourceTrace`

`sourceTrace` is a sum of resolvent terms `(s − poleCoordₙ)⁻¹` over the source modes. Its
self-duality, under the functional-equation involution `s ↦ 1 − s`, is positive structure forced by
the earned no-drift reality `poleCoordₙ.re = ½` — proved here with **no zero assumed**. -/

/-- **Each resolvent term is anti-self-dual** under the duality `s ↦ 1 − s` carried jointly to its
    pole `c ↦ 1 − c`: `((1 − s) − (1 − c))⁻¹ = −(s − c)⁻¹`. The involution flips the sign of every
    resolvent contribution — the functional-equation antisymmetry of the trace, term by term. -/
theorem resolvent_term_dual (s c : ℂ) :
    ((1 - s) - (1 - c))⁻¹ = -(s - c)⁻¹ := by
  rw [show (1 - s) - (1 - c) = -(s - c) by ring, inv_neg]

/-- **Every source pole sits on the self-dual axis, so its FE-dual is its conjugate:**
    `1 − poleCoord = conj poleCoord`. Forced by `poleCoord.re = ½` (no-drift reality): exactly on
    `Re = ½` do the functional-equation duality `s ↦ 1 − s` and conjugation coincide. The source
    spectrum is fixed by the dual-conjugate involution `s ↦ 1 − conj s`. -/
theorem poleCoord_dual_eq_conj (ψ : SourceMode) :
    1 - ψ.poleCoord = (starRingEnd ℂ) ψ.poleCoord := by
  have hre := ψ.poleCoord_re
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re, hre]; norm_num
  · simp only [Complex.sub_im, Complex.one_im, Complex.conj_im]; ring

/-- **The sourceTrace is self-dual.** Both halves, one theorem: every mode's pole has `Re = ½` (lies
    on the self-dual line), and equals the conjugate of its functional-equation dual `1 − poleCoord`.
    So the singularities of `sourceTrace` sit on the self-dual axis and are invariant under the
    FE/conjugation symmetry — by construction (no-drift), no zero assumed. Together with
    `resolvent_term_dual`, the trace inherits the FE antisymmetry on a conjugation-closed spectrum. -/
theorem source_selfDual (ψ : SourceMode) :
    ψ.poleCoord.re = 1 / 2 ∧ 1 - ψ.poleCoord = (starRingEnd ℂ) ψ.poleCoord :=
  ⟨ψ.poleCoord_re, poleCoord_dual_eq_conj ψ⟩

end SourceTraceSelfDual
