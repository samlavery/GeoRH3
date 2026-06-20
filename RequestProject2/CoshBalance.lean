import Mathlib

/-- `CoshBalance` is the critical-line abscissa `1/2`, expressed via `Real.cosh 0`
to make explicit that `1/2` here describes *where the nontrivial zeros are conjectured
to lie* — it is not an assumption that they do. By definition `Real.cosh 0 = 1`, so
`CoshBalance = 1/2`. -/
noncomputable def CoshBalance : ℝ := Real.cosh 0 / 2

@[simp] lemma CoshBalance_eq_half : CoshBalance = 1 / 2 := by
  simp [CoshBalance]

@[simp] lemma CoshBalance_complex : ((CoshBalance : ℝ) : ℂ) = 1 / 2 := by
  rw [CoshBalance_eq_half]; push_cast; ring
