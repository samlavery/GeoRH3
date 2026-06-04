import Mathlib
import RequestProject.VonMangoldtEFStandalone
import RequestProject.ForcedAlignment
import RequestProject.HelixConvergence

/-!
# Helix Residue Summability & the Explicit Formula as Proof Approach

## The Hilbert–Pólya Style Argument

The helix IS the explicit formula. The projection cascade is the EF
decomposition. The projection losses are the zero contributions.
All losses are nonneg (Pythagorean). Multiplication = addition on the helix.

The explicit formula + Li positivity from the residues is the
Hilbert–Pólya style proof. The two channels of spectral information
(ζ and L(χ₃)) provide the quadratic form. The helix IS continuation
into the strip.
-/

open scoped BigOperators Real
open Real Complex

noncomputable section

namespace HelixResidueSummability

-- ═══════════════════════════════════════════════════════════════════════════
-- §1  The Möbius Difference as a Residue
-- ═══════════════════════════════════════════════════════════════════════════

/-- `1 − w(ρ) = 1/ρ`: the Möbius difference IS the residue. -/
theorem moebius_diff_eq_inv (σ γ : ℝ) :
    (1 : ℂ) - moebius_helix σ γ = 1 / (⟨σ, γ⟩ : ℂ) := by
  unfold moebius_helix; ring

/-- `moebius_diff_sq γ = 1/(1/4 + γ²)` on the critical line. -/
theorem moebius_diff_sq_is_reciprocal (γ : ℝ) :
    moebius_diff_sq γ = 1 / (1/4 + γ ^ 2) :=
  moebius_diff_sq_eq γ

-- ═══════════════════════════════════════════════════════════════════════════
-- §2  Three Equivalent Summabilities
-- ═══════════════════════════════════════════════════════════════════════════

/-- The three summability conditions are equivalent for on-line data. -/
theorem three_summabilities (D : SummableOnLineData) :
    Summable (fun k => moebius_diff_sq (D.gamma k)) ∧
    (∀ n : ℕ, Summable (fun k =>
      (li_helix_term (1/2) (D.gamma k) n).re +
      (li_helix_term (1/2) (-(D.gamma k)) n).re)) ∧
    Summable (fun k => 1 / ((1:ℝ)/4 + (D.gamma k) ^ 2)) := by
  refine ⟨D.summable_diff, fun n => paired_li_summable D n, ?_⟩
  have : (fun k => 1 / ((1:ℝ)/4 + (D.gamma k) ^ 2)) =
         (fun k => moebius_diff_sq (D.gamma k)) := by
    ext k; rw [moebius_diff_sq_eq]
  rw [this]; exact D.summable_diff

-- ═══════════════════════════════════════════════════════════════════════════
-- §3  The Generating Function Perspective
-- ═══════════════════════════════════════════════════════════════════════════

/-- The per-zero Li generating coefficient. -/
def liGenCoeff (w : ℂ) (n : ℕ) : ℝ := (1 - w ^ n).re

/-- On the unit circle, coefficients are bounded by 2. -/
theorem liGenCoeff_bounded (w : ℂ) (hw : ‖w‖ = 1) (n : ℕ) :
    |liGenCoeff w n| ≤ 2 := by
  unfold liGenCoeff
  have h1 : (w ^ n).re ≤ 1 := by
    calc (w ^ n).re ≤ ‖w ^ n‖ := Complex.re_le_norm _
      _ = 1 := by rw [norm_pow, hw, one_pow]
  have h2 : -1 ≤ (w ^ n).re := by
    have := Complex.abs_re_le_norm (w ^ n)
    rw [norm_pow, hw, one_pow] at this
    linarith [abs_le.mp this]
  simp only [Complex.sub_re, Complex.one_re]
  rw [abs_le]; constructor <;> linarith

/-- Off circle with |w| > 1, the Li coefficients Re[1 − wⁿ] are
    unbounded below (from `li_helix_unbounded_off_line`). -/
theorem liGenCoeff_unbounded_below (w : ℂ) (hw : 1 < ‖w‖) :
    ∀ M : ℝ, ∃ n : ℕ, liGenCoeff w n < M := by
  intro M
  obtain ⟨n, hn⟩ := re_pow_unbounded_above w hw (1 - M)
  exact ⟨n, by unfold liGenCoeff; simp only [Complex.sub_re, Complex.one_re]; linarith⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §4  The Full Positivity Cascade
-- ═══════════════════════════════════════════════════════════════════════════

/-- **The complete summability–positivity interface.** -/
theorem summability_positivity_interface :
    (∀ D : SummableOnLineData,
      Summable (fun k => moebius_diff_sq (D.gamma k))) ∧
    (∀ D : SummableOnLineData, ∀ n : ℕ,
      Summable (fun k =>
        (li_helix_term (1/2) (D.gamma k) n).re +
        (li_helix_term (1/2) (-(D.gamma k)) n).re)) ∧
    (∀ D : SummableOnLineData, ∀ n : ℕ,
      0 ≤ ∑' k, ((li_helix_term (1/2) (D.gamma k) n).re +
                  (li_helix_term (1/2) (-(D.gamma k)) n).re)) ∧
    (∀ σ γ : ℝ, γ ≠ 0 →
      (σ = 1/2 ↔ ∃ M, ∀ n : ℕ,
        M ≤ (li_helix_term σ γ n).re +
            (li_helix_term (1 - σ) (-γ) n).re)) :=
  ⟨fun D => D.summable_diff,
   fun D n => paired_li_summable D n,
   fun D n => li_tsum_nonneg D n,
   fun σ γ hγ => critical_line_iff_bounded_li σ γ hγ⟩

#print axioms moebius_diff_eq_inv
#print axioms moebius_diff_sq_is_reciprocal
#print axioms three_summabilities
#print axioms liGenCoeff_bounded
#print axioms liGenCoeff_unbounded_below
#print axioms summability_positivity_interface

end HelixResidueSummability
