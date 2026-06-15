import Mathlib
import RequestProject.VonMangoldtEFStandalone

/-!
# Jensen Formula & Zero-Count for ξ — Standalone

Isolated headlines for the Jensen-based zero-counting machinery:

* `xi_zero_count_disk_bound` — the disk zero-counting bound
  `#{ρ ∈ B_R : ξ(ρ) = 0} ≤ C·R·log R`, the Jensen ⇒ density estimate.

* `xi_zero_count_strip_bound` — the strip zero-counting bound (Riemann–von
  Mangoldt): `N(T) := #{ρ : 0 < Re(ρ) < 1, |Im(ρ)| ≤ T, ζ(ρ) = 0}`
  satisfies `N(T) ≤ C·T·log T` for large T.

* `helix_winding_density` — in helix coordinates, the density of winding
  frequencies `ν = γ/U` up to height `T/U` is `O(T log T)`.

The disk bound comes from Jensen's formula applied to the entire function `ξ`
of order ≤ 1. The strip bound follows since nontrivial zeros of ζ are zeros
of ξ and lie in `|Re(s) − 1/2| < 1/2`, so they fit in a disk of radius
`√(1/4 + T²) ≤ T + 1`.

All definitions (`riemannXi`, `NontrivialZeros`, `U`) are re-exported from
`VMEFStandalone`, which builds them from Mathlib's `riemannZeta`,
`completedRiemannZeta₀`, etc.

## Axiom footprint
`[propext, Classical.choice, Quot.sound]` (modulo unproven bounds).
-/

open Real Complex VMEFStandalone
open scoped BigOperators

noncomputable section

namespace JensenStandalone

-- ═══════════════════════════════════════════════════════════════════════════
-- §0  Re-exports from VMEFStandalone (no self-defined duplicates)
-- ═══════════════════════════════════════════════════════════════════════════

-- `riemannXi`, `NontrivialZeros`, `U`, `U_pos` are all imported
-- from `VMEFStandalone` via `open VMEFStandalone`.
-- `riemannXi` is built from Mathlib's `completedRiemannZeta₀`.
-- `NontrivialZeros` is built from Mathlib's `riemannZeta`.

/-- Re-export of `VMEFStandalone.riemannXi` for backward compatibility. -/
def riemannXi : ℂ → ℂ := VMEFStandalone.riemannXi

/-- Re-export of `VMEFStandalone.U` for backward compatibility. -/
def U : ℝ := VMEFStandalone.U

theorem U_pos : 0 < U := VMEFStandalone.U_pos

/-- The zero-counting function `N(T)`: number of nontrivial zeros with `|Im(ρ)| ≤ T`.
    Uses `VMEFStandalone.NontrivialZeros` (= `{ s | 0 < s.re ∧ s.re < 1 ∧ riemannZeta s = 0 }`). -/
def zeroCount (T : ℝ) : ℕ :=
  (NontrivialZeros ∩ { s : ℂ | |s.im| ≤ T }).ncard

-- ═══════════════════════════════════════════════════════════════════════════
-- §1  Disk Zero-Count Bound (Jensen → density)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Disk zero-count bound for `ξ`.**
There are `C, R₀ > 0` with `#{ρ ∈ closedBall 0 R : ξ(ρ) = 0} ≤ C·R·log R`
for all `R ≥ R₀`. This follows from Jensen's formula and the order-1 growth
of ξ. Uses `VMEFStandalone.riemannXi` (built from Mathlib's
`completedRiemannZeta₀`). -/
theorem xi_zero_count_disk_bound :
    ∃ C > (0 : ℝ), ∃ R₀ > (0 : ℝ), ∀ R, R₀ ≤ R →
      ((Metric.closedBall (0 : ℂ) R ∩ {z | riemannXi z = 0}).ncard : ℝ)
        ≤ C * R * Real.log R := by
  simpa [riemannXi, VMEFStandalone.riemannXi, ZD.riemannXi] using
    ZD.ZeroCount.xi_zero_count_disk_bound

-- ═══════════════════════════════════════════════════════════════════════════
-- §2  Strip Zero-Count Bound (Riemann–von Mangoldt)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Strip zero-count bound (Riemann–von Mangoldt).**
`N(T) ≤ C · T · log T` for all sufficiently large `T`.
This is the standard Riemann–von Mangoldt formula `N(T) ~ (T/2π) log(T/2π)`,
stated as an upper bound. -/
theorem strip_zero_count_bound :
    ∃ C > (0 : ℝ), ∃ T₀ > (0 : ℝ), ∀ T, T₀ ≤ T →
      (zeroCount T : ℝ) ≤ C * T * Real.log T := by
  obtain ⟨C, hC, R₀, hR₀, hDisk⟩ := xi_zero_count_disk_bound
  refine ⟨4 * C, by positivity, max (max R₀ 2) (Real.exp 1), by positivity, ?_⟩
  intro T hT
  have hT_R₀ : R₀ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hT_two : (2 : ℝ) ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hT_exp : Real.exp 1 ≤ T := le_trans (le_max_right _ _) hT
  have hT_pos : 0 < T := lt_of_lt_of_le (by norm_num) hT_two
  have hT_one : (1 : ℝ) ≤ T := le_trans (by norm_num) hT_two
  let S : Set ℂ := NontrivialZeros ∩ {s : ℂ | |s.im| ≤ T}
  let B : Set ℂ := Metric.closedBall (0 : ℂ) (T + 1) ∩ {z | riemannXi z = 0}
  have hsub : S ⊆ B := by
    intro z hz
    rcases hz with ⟨hzNT, hzim⟩
    constructor
    · rw [Metric.mem_closedBall, dist_zero_right]
      have hre_abs : |z.re| ≤ 1 := abs_le.mpr ⟨by linarith [hzNT.1], le_of_lt hzNT.2.1⟩
      have hnorm_le : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      have him_abs : |z.im| ≤ T := hzim
      linarith
    · simpa [riemannXi, VMEFStandalone.riemannXi, VMEFStandalone.NontrivialZeros,
        ZD.riemannXi, ZD.NontrivialZeros] using
        ZD.ZeroCount.riemannXi_zero_of_mem_NontrivialZeros z
          (by simpa [VMEFStandalone.NontrivialZeros, ZD.NontrivialZeros] using hzNT)
  have hBfin : B.Finite := by
    simpa [B, riemannXi, VMEFStandalone.riemannXi, ZD.riemannXi] using
      ZD.ZeroCount.riemannXi_zeros_finite_in_closedBall (T + 1)
  have hncard_le : S.ncard ≤ B.ncard := Set.ncard_le_ncard hsub hBfin
  have hzero_le : (zeroCount T : ℝ) ≤ (B.ncard : ℝ) := by
    unfold zeroCount
    exact_mod_cast hncard_le
  have hDiskT := hDisk (T + 1) (by linarith)
  have hTp1_pos : 0 < T + 1 := by linarith
  have hTp1_le_twoT : T + 1 ≤ 2 * T := by linarith
  have hlogT_ge_one : (1 : ℝ) ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos 1) hT_exp
    rwa [Real.log_exp] at this
  have hlogT_nonneg : 0 ≤ Real.log T := le_trans zero_le_one hlogT_ge_one
  have hlogTp1_le : Real.log (T + 1) ≤ 2 * Real.log T := by
    have hsq : T + 1 ≤ T * T := by nlinarith
    have hlog := Real.log_le_log hTp1_pos hsq
    have hmul : Real.log (T * T) = Real.log T + Real.log T := by
      rw [Real.log_mul hT_pos.ne' hT_pos.ne']
    linarith
  have hmul_logs :
      (T + 1) * Real.log (T + 1) ≤ (2 * T) * (2 * Real.log T) := by
    apply mul_le_mul hTp1_le_twoT hlogTp1_le
    · exact Real.log_nonneg (by linarith)
    · positivity
  have hscaled :
      C * ((T + 1) * Real.log (T + 1)) ≤ C * ((2 * T) * (2 * Real.log T)) :=
    mul_le_mul_of_nonneg_left hmul_logs (le_of_lt hC)
  calc
    (zeroCount T : ℝ) ≤ (B.ncard : ℝ) := hzero_le
    _ ≤ C * (T + 1) * Real.log (T + 1) := by simpa [B] using hDiskT
    _ ≤ (4 * C) * T * Real.log T := by nlinarith

-- ═══════════════════════════════════════════════════════════════════════════
-- §3  Helix Winding Density
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Helix winding density.**
The number of nontrivial zeros with winding frequency `|ν| = |γ/U| ≤ Ω`
is at most `C · (U·Ω) · log(U·Ω)` for large `Ω`.
Uses `VMEFStandalone.U` (= `π/3`). -/
theorem helix_winding_density :
    ∃ C > (0 : ℝ), ∃ Ω₀ > (0 : ℝ), ∀ Ω, Ω₀ ≤ Ω →
      (zeroCount (U * Ω) : ℝ) ≤ C * (U * Ω) * Real.log (U * Ω) := by
  obtain ⟨C, hC, T₀, hT₀, hbound⟩ := strip_zero_count_bound
  refine ⟨C, hC, T₀ / U, div_pos hT₀ U_pos, fun Ω hΩ => ?_⟩
  apply hbound
  have hU := U_pos
  have h1 : T₀ = T₀ / U * U := by field_simp
  calc T₀ = T₀ / U * U := h1
    _ ≤ Ω * U := by nlinarith
    _ = U * Ω := by ring

-- ═══════════════════════════════════════════════════════════════════════════
-- §4  Infinitely Many Zeros (from lower density bound)
-- ═══════════════════════════════════════════════════════════════════════════

/-- A lower bound on zero density implies infinitely many zeros. -/
theorem infinitely_many_zeros_of_lower_density
    (hDensity : ∃ c > (0 : ℝ), ∃ T₀ > (0 : ℝ), ∀ T, T₀ ≤ T →
      c * T ≤ (zeroCount T : ℝ)) :
    ∀ N : ℕ, ∃ T : ℝ, 0 < T ∧ N ≤ zeroCount T := by
  intro N
  obtain ⟨c, hc, T₀, hT₀, hbound⟩ := hDensity
  set T := max T₀ ((N : ℝ) / c + 1) with hT_def
  refine ⟨T, by positivity, ?_⟩
  have h := hbound T (le_max_left T₀ _)
  suffices hle : (N : ℝ) ≤ (zeroCount T : ℝ) from Nat.cast_le.mp hle
  have : (N : ℝ) < c * T := calc
    (N : ℝ) = c * ((N : ℝ) / c) := by field_simp
    _ < c * ((N : ℝ) / c + 1) := by linarith
    _ ≤ c * T := by apply mul_le_mul_of_nonneg_left (le_max_right _ _) (le_of_lt hc)
  linarith

end JensenStandalone
