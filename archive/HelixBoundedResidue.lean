import Mathlib

/-!
# Bounded-residue ingredients for the helix spine (Pillar 4 / Link 3)

Two verified, reusable, axiom-clean ingredients for the arrow
`pole → bounded residue functional → source mode` (see `HELIX_SPINE.md`):

* `riesz_source_mode` — **the manufacture arrow, abstractly.** A *bounded* linear functional on the
  (complete) projection-loss inner-product space is represented by a vector `v` with `‖v‖ ≤ √C` and
  `|φ f|² ≤ C‖f‖²` (Fréchet–Riesz). This is `Res_ρ bounded ⇒ v_ρ ∈ H` once `Res_ρ` is exhibited as a
  continuous functional with `‖Res_ρ‖ ≤ √C_ρ`.

* `summable_radial_weight` — **the area-law radial convergence.** For bounded coefficients, the
  radial-weighted Dirichlet energy `Σ ‖a n‖² · n^{−(2σ+β)}` converges for `1 < 2σ+β`; the radius-`√n`
  weight `n^{−β}` (`β>0`) pushes the abscissa from `½` to `(1−β)/2`.

**HONEST SCOPE (Rule Four).** These are *ingredients*, not the scalp. `riesz_source_mode` does NOT prove
boundedness of the actual residue functional — producing `C_ρ` on the concrete energy norm is the real
upstream obligation. And `summable_radial_weight` is the **static / half-plane** convergence (finite for
all strip `σ`): it makes `v_ρ` exist but does NOT force on-line. The on-line forcing needs a
**σ-independent / flow-invariant** projection-loss norm so that off-line ⇒ infinite norm — that, plus the
Weil/Li equality and the capture (`SourceComplete`), is the open content (see `HELIX_SPINE.md`).
-/

namespace HelixSpine

open ComplexConjugate in
/-- **Riesz manufacture arrow.** A bounded functional `φ : H →L[ℂ] ℂ` with `‖φ‖ ≤ √C` is represented by
    a vector `v` (`φ f = ⟪v, f⟫`) with `‖v‖ ≤ √C`, hence `|φ f|² ≤ C‖f‖²`. -/
theorem riesz_source_mode
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : H →L[ℂ] ℂ) (C : ℝ) (hC : 0 ≤ C) (hφ : ‖φ‖ ≤ Real.sqrt C) :
    ∃ v : H, (∀ f, φ f = inner ℂ v f) ∧ ‖v‖ ≤ Real.sqrt C ∧
      ∀ f, ‖φ f‖ ^ 2 ≤ C * ‖f‖ ^ 2 := by
  refine ⟨(InnerProductSpace.toDual ℂ H).symm φ, ?_, ?_, ?_⟩
  · intro f
    exact (InnerProductSpace.toDual_symm_apply (x := f)).symm
  · have := LinearIsometryEquiv.norm_map (InnerProductSpace.toDual ℂ H).symm φ
    rw [this]; exact hφ
  · intro f
    have h1 : ‖φ f‖ ≤ ‖φ‖ * ‖f‖ := φ.le_opNorm f
    have hf : 0 ≤ ‖f‖ := norm_nonneg f
    have h2 : ‖φ f‖ ≤ Real.sqrt C * ‖f‖ := le_trans h1 (mul_le_mul_of_nonneg_right hφ hf)
    have hnn : 0 ≤ ‖φ f‖ := norm_nonneg _
    have h3 : ‖φ f‖ ^ 2 ≤ (Real.sqrt C * ‖f‖) ^ 2 := by
      have := mul_le_mul h2 h2 hnn (le_trans hnn h2)
      simpa [pow_two] using this
    calc ‖φ f‖ ^ 2 ≤ (Real.sqrt C * ‖f‖) ^ 2 := h3
      _ = (Real.sqrt C) ^ 2 * ‖f‖ ^ 2 := by ring
      _ = C * ‖f‖ ^ 2 := by rw [Real.sq_sqrt hC]

/-- **Area-law radial convergence** (finiteness of `C_ρ`, static/half-plane form). For bounded
    `a : ℕ → ℂ` and `1 < 2σ + β`, the radial-weighted Dirichlet energy is summable. -/
theorem summable_radial_weight
    (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1)
    (σ β : ℝ) (h : 1 < 2 * σ + β) :
    Summable (fun n : ℕ => ‖a n‖ ^ 2 * (n : ℝ) ^ (-(2 * σ + β))) := by
  have hp : -(2 * σ + β) < -1 := by linarith
  have hdom : Summable (fun n : ℕ => (n : ℝ) ^ (-(2 * σ + β))) :=
    Real.summable_nat_rpow.mpr hp
  refine hdom.of_nonneg_of_le ?_ ?_
  · intro n
    have hw : 0 ≤ (n : ℝ) ^ (-(2 * σ + β)) := Real.rpow_nonneg (by positivity) _
    positivity
  · intro n
    have hw : 0 ≤ (n : ℝ) ^ (-(2 * σ + β)) := Real.rpow_nonneg (by positivity) _
    have hsq : ‖a n‖ ^ 2 ≤ 1 := by nlinarith [ha n, norm_nonneg (a n)]
    calc ‖a n‖ ^ 2 * (n : ℝ) ^ (-(2 * σ + β))
        ≤ 1 * (n : ℝ) ^ (-(2 * σ + β)) := mul_le_mul_of_nonneg_right hsq hw
      _ = (n : ℝ) ^ (-(2 * σ + β)) := one_mul _

/-- On the critical line `σ = ½`, any strictly-positive radial weight `β > 0` already gives
    summability (`2·½ + β = 1 + β > 1`) — the line is strictly inside the convergence region. -/
theorem summable_radial_weight_on_line
    (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (β : ℝ) (hβ : 0 < β) :
    Summable (fun n : ℕ => ‖a n‖ ^ 2 * (n : ℝ) ^ (-(2 * (1 / 2 : ℝ) + β))) :=
  summable_radial_weight a ha (1 / 2) β (by linarith)

end HelixSpine
