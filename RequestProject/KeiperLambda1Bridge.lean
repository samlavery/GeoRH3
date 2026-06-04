import Mathlib
import RequestProject.XiPartialFraction
import RequestProject.XiProductMultPartialFraction
import RequestProject.XiOrderSummable
import RequestProject.XiLogDerivTerms
import RequestProject.KeiperLambda1Value
import RequestProject.KeiperLiPositivity
import RequestProject.KeiperLiNonempty
import RequestProject.XiHadamardQuotient
import RequestProject.XiOrder

/-!
# The Hadamard / Keiper–Li bridge for the first Li coefficient

This file connects the **zero-side** first Li coefficient (a sum over the
nontrivial zeros of the multiplicity-weighted real residues `Re(1/ρ)`) to the
**Keiper value** `ξ'/ξ(1)` and hence to its closed arithmetic form.

The multiplicity-weighted first Li coefficient (real part) is

  `lambda1Mult := ∑'_ρ (m_ρ) · Re(1/ρ)`,   `m_ρ = ZD.xiOrderNat ρ`.

## Main results

* `lambda1Mult_summable` — the defining series converges.
* `xiLogDeriv_one_re_eq` — **the bridge**: `(logDeriv riemannXi 1).re = lambda1Mult`.
* `lambda1Mult_eq_arith` — closed arithmetic form
    `lambda1Mult = 1 + γ/2 − ½·log(4π)`.
* `lambda1Mult_pos` — `0 < lambda1Mult`.

All results are unconditional and axiom-clean
(`[propext, Classical.choice, Quot.sound]`).

## Mechanism of the bridge

The repo partial fraction (`ZD.xi_logDeriv_partial_fraction`) gives a constant
`A` with `ξ'/ξ(s) = A + ∑'_ρ m_ρ·(1/(s−ρ) + 1/ρ)` for `s ∉ NTZ`. Evaluating at
`s = 0` (where every term vanishes) gives `ξ'/ξ(0) = A`; evaluating at `s = 1`
gives `ξ'/ξ(1) = A + S` with `S := ∑'_ρ m_ρ·(1/(1−ρ) + 1/ρ)`. The functional
equation `ξ(1−s) = ξ(s)` forces `ξ'/ξ(0) = −ξ'/ξ(1)`, hence `2·ξ'/ξ(1) = S`.
Taking real parts and reindexing the `1/(1−ρ)` part by the involution `ρ ↦ 1−ρ`
(which preserves both `NTZ` and the multiplicities) gives
`2·(ξ'/ξ(1)).re = 2·lambda1Mult`.
-/

open Complex Filter Topology Set

noncomputable section

namespace ZD

-- ═══════════════════════════════════════════════════════════════════════════
-- § Definition
-- ═══════════════════════════════════════════════════════════════════════════

/-- The multiplicity-weighted first Li coefficient, real part:
`lambda1Mult = ∑'_ρ (xiOrderNat ρ) · Re(1/ρ)`, over the nontrivial zeros. -/
def lambda1Mult : ℝ :=
  ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros}, (ZD.xiOrderNat ρ.val : ℝ) * (1 / ρ.val).re

-- ═══════════════════════════════════════════════════════════════════════════
-- § Supporting lemmas: invariance of NTZ and the multiplicities under ρ ↦ 1−ρ
-- ═══════════════════════════════════════════════════════════════════════════

/-- `0 ∉ NontrivialZeros`: `Re 0 = 0` is not `> 0`. -/
lemma zero_not_mem_ntz : (0 : ℂ) ∉ NontrivialZeros := by
  intro h
  rw [mem_NontrivialZeros_iff] at h
  simp only [Complex.zero_re] at h
  exact absurd h.1 (lt_irrefl 0)

/-- `1 ∉ NontrivialZeros`: `Re 1 = 1` is not `< 1`. -/
lemma one_not_mem_ntz : (1 : ℂ) ∉ NontrivialZeros := by
  intro h
  rw [mem_NontrivialZeros_iff] at h
  simp only [Complex.one_re] at h
  exact absurd h.2.1 (lt_irrefl 1)

/-- **`NontrivialZeros` is closed under `ρ ↦ 1 − ρ`.** Real part: `Re(1−ρ) =
1 − Re ρ ∈ (0,1)`. Vanishing: `ξ(1−ρ) = ξ(ρ) = 0` by the functional equation,
so `1 − ρ ∈ NTZ` via `riemannXi_eq_zero_iff`. -/
lemma one_sub_mem_ntz {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) : (1 - ρ) ∈ NontrivialZeros := by
  have hξρ : ZD.riemannXi ρ = 0 := (riemannXi_eq_zero_iff ρ).mpr hρ
  have hξ : ZD.riemannXi (1 - ρ) = 0 := by
    rw [ZD.ZeroCount.riemannXi_one_sub]; exact hξρ
  exact (riemannXi_eq_zero_iff (1 - ρ)).mp hξ

/-- **The multiplicities are invariant under `ρ ↦ 1 − ρ`.**
`xiOrderNat (1 − ρ) = xiOrderNat ρ`. Proof: `analyticOrderAt ξ (1−ρ) =
analyticOrderAt ξ ρ` via `AnalyticAt.analyticOrderAt_comp` with the affine map
`g s = 1 − s` (`deriv g = −1 ≠ 0`, so the comp factor has order `1`) and the
functional equation `ξ ∘ (1−·) = ξ`; transfer ℕ∞ ↔ ℕ by finiteness of the
order everywhere. -/
lemma xiOrderNat_one_sub (ρ : ℂ) : ZD.xiOrderNat (1 - ρ) = ZD.xiOrderNat ρ := by
  -- Order equality at the ℕ∞ level.
  have hord : analyticOrderAt ZD.riemannXi (1 - ρ) = analyticOrderAt ZD.riemannXi ρ := by
    have hg_an : AnalyticAt ℂ (fun s : ℂ => 1 - s) ρ := by
      apply AnalyticAt.sub <;> [exact analyticAt_const; exact analyticAt_id]
    have hf_an : AnalyticAt ℂ ZD.riemannXi ((fun s : ℂ => 1 - s) ρ) :=
      ZD.riemannXi_differentiable.analyticAt _
    have hcomp := hf_an.analyticOrderAt_comp hg_an
    -- order of (g x − g ρ) at ρ equals 1, via deriv g ρ = −1 ≠ 0.
    have hderiv : deriv (fun s : ℂ => 1 - s) ρ = -1 := by
      rw [deriv_const_sub, deriv_id'']
    have hord1 :
        analyticOrderAt (fun x => (fun s : ℂ => 1 - s) x - (fun s : ℂ => 1 - s) ρ) ρ = 1 :=
      hg_an.analyticOrderAt_sub_eq_one_of_deriv_ne_zero (by rw [hderiv]; norm_num)
    rw [hord1, mul_one] at hcomp
    -- ξ ∘ (1−·) = ξ near ρ (in fact everywhere) by the functional equation.
    have hcongr :
        analyticOrderAt (ZD.riemannXi ∘ (fun s : ℂ => 1 - s)) ρ = analyticOrderAt ZD.riemannXi ρ := by
      apply analyticOrderAt_congr
      filter_upwards with x
      simp only [Function.comp_apply]
      exact ZD.ZeroCount.riemannXi_one_sub x
    rw [hcongr] at hcomp
    exact hcomp.symm
  -- Transfer ℕ∞ → ℕ using finiteness of the order.
  unfold ZD.xiOrderNat
  have hne_a : analyticOrderAt ZD.riemannXi (1 - ρ) ≠ ⊤ :=
    ZD.riemannXi_analyticOrderAt_ne_top_everywhere (1 - ρ)
  have hne_b : analyticOrderAt ZD.riemannXi ρ ≠ ⊤ :=
    ZD.riemannXi_analyticOrderAt_ne_top_everywhere ρ
  have hcast :
      ((analyticOrderNatAt ZD.riemannXi (1 - ρ) : ℕ) : ℕ∞)
        = ((analyticOrderNatAt ZD.riemannXi ρ : ℕ) : ℕ∞) := by
    rw [Nat.cast_analyticOrderNatAt hne_a, Nat.cast_analyticOrderNatAt hne_b, hord]
  exact_mod_cast hcast

/-- **The functional-equation involution `ρ ↦ 1 − ρ` on the nontrivial zeros.** -/
def feInvol : {ρ : ℂ // ρ ∈ NontrivialZeros} ≃ {ρ : ℂ // ρ ∈ NontrivialZeros} :=
  Function.Involutive.toPerm
    (fun ρ => ⟨1 - ρ.val, one_sub_mem_ntz ρ.property⟩)
    (by intro ρ; apply Subtype.ext; simp)

@[simp] lemma feInvol_apply (ρ : {ρ : ℂ // ρ ∈ NontrivialZeros}) :
    (feInvol ρ).val = 1 - ρ.val := rfl

-- ═══════════════════════════════════════════════════════════════════════════
-- § Theorem 1: summability of the defining series
-- ═══════════════════════════════════════════════════════════════════════════

/-- **`lambda1Mult` summability.** `∑'_ρ m_ρ·Re(1/ρ)` converges, majorised
termwise by `∑'_ρ m_ρ/‖ρ‖²` using `0 ≤ Re(1/ρ) ≤ 1/‖ρ‖²` (the strip walls). -/
theorem lambda1Mult_summable :
    Summable (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} =>
      (ZD.xiOrderNat ρ.val : ℝ) * (1 / ρ.val).re) := by
  apply Summable.of_nonneg_of_le
    (fun ρ => mul_nonneg (by positivity) (li1Term_pos ρ.property).le)
    ?_ summable_xiOrderNat_div_norm_sq_nontrivialZeros
  intro ρ
  calc (ZD.xiOrderNat ρ.val : ℝ) * (1 / ρ.val).re
        ≤ (ZD.xiOrderNat ρ.val : ℝ) * (1 / ‖ρ.val‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (li1Term_le ρ.property) (by positivity)
    _ = (ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2 := by rw [mul_one_div]

/-- Summability of the reindexed (`1/(1−ρ)`) part, transferred from
`lambda1Mult_summable` through the involution `feInvol`, using
`xiOrderNat_one_sub`. -/
theorem lambda1Mult_summable_one_sub :
    Summable (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} =>
      (ZD.xiOrderNat ρ.val : ℝ) * (1 / (1 - ρ.val)).re) := by
  have hbase := lambda1Mult_summable
  have hfun :
      (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} =>
        (ZD.xiOrderNat ρ.val : ℝ) * (1 / (1 - ρ.val)).re)
        = (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} =>
            (ZD.xiOrderNat (feInvol ρ).val : ℝ) * (1 / (feInvol ρ).val).re) := by
    funext ρ
    rw [feInvol_apply, xiOrderNat_one_sub]
  rw [hfun]
  exact (feInvol.summable_iff).mpr hbase

-- ═══════════════════════════════════════════════════════════════════════════
-- § The functional equation for the logarithmic derivative
-- ═══════════════════════════════════════════════════════════════════════════

/-- **FE for `ξ'/ξ`**: `logDeriv ξ 0 = − logDeriv ξ 1`. Differentiating
`ξ(1−s) = ξ(s)` gives `ξ'(0) = −ξ'(1)`, while `ξ(0) = ξ(1) = 1/2`. -/
lemma logDeriv_riemannXi_zero_eq_neg_one :
    logDeriv ZD.riemannXi 0 = - logDeriv ZD.riemannXi 1 := by
  -- ξ'(0) = −ξ'(1).
  have hderiv0 : deriv ZD.riemannXi 0 = - deriv ZD.riemannXi 1 := by
    have hg : HasDerivAt (fun s : ℂ => 1 - s) (-1) 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_sub 1
    have h1 : HasDerivAt ZD.riemannXi (deriv ZD.riemannXi 1) ((fun s : ℂ => 1 - s) 0) := by
      have hpt : (fun s : ℂ => 1 - s) 0 = 1 := by norm_num
      rw [hpt]; exact (ZD.riemannXi_differentiable 1).hasDerivAt
    have hcomp : HasDerivAt (fun s => ZD.riemannXi (1 - s)) (deriv ZD.riemannXi 1 * -1) 0 :=
      h1.comp 0 hg
    have hEq : (fun s : ℂ => ZD.riemannXi (1 - s)) = ZD.riemannXi := by
      funext s; exact ZD.ZeroCount.riemannXi_one_sub s
    rw [hEq] at hcomp
    have h0 : HasDerivAt ZD.riemannXi (deriv ZD.riemannXi 0) 0 :=
      (ZD.riemannXi_differentiable 0).hasDerivAt
    have huniq := hcomp.unique h0
    rw [← huniq]; ring
  -- ξ(0) = ξ(1) = 1/2.
  have hξ0 : ZD.riemannXi 0 = 1 / 2 := ZD.ZeroCount.riemannXi_zero
  have hξ1 : ZD.riemannXi 1 = 1 / 2 := by
    have h : ZD.riemannXi (1 - 0) = ZD.riemannXi 0 := ZD.ZeroCount.riemannXi_one_sub 0
    rw [sub_zero] at h
    rw [h, hξ0]
  rw [logDeriv_apply, logDeriv_apply, hderiv0, hξ0, hξ1]
  rw [neg_div]

-- ═══════════════════════════════════════════════════════════════════════════
-- § Theorem 2: the bridge
-- ═══════════════════════════════════════════════════════════════════════════

/-- **The Keiper–Li / Hadamard bridge.**
`(logDeriv riemannXi 1).re = lambda1Mult`, i.e. the Keiper value `ξ'/ξ(1)` has
real part equal to the multiplicity-weighted zero-side first Li coefficient. -/
theorem xiLogDeriv_one_re_eq :
    (logDeriv ZD.riemannXi 1).re = lambda1Mult := by
  -- Partial fraction with its constant `A`.
  obtain ⟨A, hA⟩ := ZD.xi_logDeriv_partial_fraction
  -- Value at s = 0: every term vanishes, so ξ'/ξ(0) = A.
  have hval0 : logDeriv ZD.riemannXi 0 = A := by
    have h := hA 0 zero_not_mem_ntz
    rw [logDeriv_apply]
    -- the tsum vanishes term-by-term.
    have hzero : (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
        (ZD.xiOrderNat ρ.val : ℂ) * (1 / (0 - ρ.val) + 1 / ρ.val)) = 0 := by
      have hpt : ∀ ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
          (ZD.xiOrderNat ρ.val : ℂ) * (1 / (0 - ρ.val) + 1 / ρ.val) = 0 := by
        intro ρ
        rw [zero_sub, one_div_neg_eq_neg_one_div]
        ring
      rw [tsum_congr hpt, tsum_zero]
    rw [h, hzero, add_zero]
  -- Value at s = 1: ξ'/ξ(1) = A + S.
  set S : ℂ := ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
      (ZD.xiOrderNat ρ.val : ℂ) * (1 / (1 - ρ.val) + 1 / ρ.val) with hS_def
  have hval1 : logDeriv ZD.riemannXi 1 = A + S := by
    have h := hA 1 one_not_mem_ntz
    rw [logDeriv_apply]; exact h
  -- FE: A = logDeriv ξ 0 = − logDeriv ξ 1.
  have hAeq : A = - logDeriv ZD.riemannXi 1 := by
    rw [← hval0]; exact logDeriv_riemannXi_zero_eq_neg_one
  -- Combine: 2 · logDeriv ξ 1 = S.
  have h2L : 2 * logDeriv ZD.riemannXi 1 = S := by
    linear_combination hval1 + hAeq
  -- Summability of S (weighted partial fraction at s = 1).
  have hSsum : Summable (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} =>
      (ZD.xiOrderNat ρ.val : ℂ) * (1 / (1 - ρ.val) + 1 / ρ.val)) :=
    ZD.summable_weighted_partial_fraction one_not_mem_ntz
  -- Take real parts and split S.re into the two reindex-conjugate halves.
  have hSre : S.re
      = (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
            (ZD.xiOrderNat ρ.val : ℝ) * (1 / (1 - ρ.val)).re)
        + (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
            (ZD.xiOrderNat ρ.val : ℝ) * (1 / ρ.val).re) := by
    rw [hS_def, Complex.re_tsum hSsum]
    have hpt : ∀ ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
        ((ZD.xiOrderNat ρ.val : ℂ) * (1 / (1 - ρ.val) + 1 / ρ.val)).re
          = (ZD.xiOrderNat ρ.val : ℝ) * (1 / (1 - ρ.val)).re
            + (ZD.xiOrderNat ρ.val : ℝ) * (1 / ρ.val).re := by
      intro ρ
      simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im]
      ring
    rw [tsum_congr hpt, (lambda1Mult_summable_one_sub).tsum_add lambda1Mult_summable]
  -- Reindex the (1/(1−ρ)) half to lambda1Mult via the involution.
  have hreindex :
      (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
        (ZD.xiOrderNat ρ.val : ℝ) * (1 / (1 - ρ.val)).re) = lambda1Mult := by
    rw [lambda1Mult, ← feInvol.tsum_eq
      (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} =>
        (ZD.xiOrderNat ρ.val : ℝ) * (1 / ρ.val).re)]
    apply tsum_congr
    intro ρ
    rw [feInvol_apply, xiOrderNat_one_sub]
  -- Conclude: 2·(ξ'/ξ(1)).re = 2·lambda1Mult.
  have hfold : (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
      (ZD.xiOrderNat ρ.val : ℝ) * (1 / ρ.val).re) = lambda1Mult := rfl
  have h2re : 2 * (logDeriv ZD.riemannXi 1).re = 2 * lambda1Mult := by
    have heq : (2 * logDeriv ZD.riemannXi 1).re = S.re := by rw [h2L]
    rw [Complex.mul_re] at heq
    simp only [Complex.re_ofNat, Complex.im_ofNat] at heq
    rw [hSre, hreindex, hfold] at heq
    -- `heq : 2 * (logDeriv ξ 1).re - 0 * (logDeriv ξ 1).im = lambda1Mult + lambda1Mult`
    linarith [heq]
  linarith [h2re]

-- ═══════════════════════════════════════════════════════════════════════════
-- § Theorem 3: closed arithmetic form
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Closed arithmetic form of `lambda1Mult`.**
`lambda1Mult = 1 + γ/2 − ½·log(4π)`. Combines the bridge
(`xiLogDeriv_one_re_eq`) with the Keiper closed value
(`VMEFStandalone.keiperLambda1_value`), taking real parts. -/
theorem lambda1Mult_eq_arith :
    lambda1Mult = 1 + Real.eulerMascheroniConstant / 2 - Real.log (4 * Real.pi) / 2 := by
  have hbridge : (logDeriv ZD.riemannXi 1).re = lambda1Mult := xiLogDeriv_one_re_eq
  have hkeiper : logDeriv ZD.riemannXi 1
      = 1 + (Real.eulerMascheroniConstant : ℂ) / 2 - Complex.log (4 * Real.pi) / 2 :=
    VMEFStandalone.keiperLambda1_value
  rw [← hbridge, hkeiper]
  -- Take real parts of the closed complex value.
  have hlog : (Complex.log (4 * Real.pi)).re = Real.log (4 * Real.pi) := by
    have h4pi : (4 : ℂ) * (Real.pi : ℂ) = ((4 * Real.pi : ℝ) : ℂ) := by push_cast; ring
    rw [h4pi, Complex.log_ofReal_re]
  simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.div_re,
    Complex.ofReal_re, Complex.ofReal_im, hlog]
  norm_num [Complex.normSq]
  ring

-- ═══════════════════════════════════════════════════════════════════════════
-- § Theorem 4: positivity
-- ═══════════════════════════════════════════════════════════════════════════

/-- **`lambda1Mult > 0`, unconditional.** Every summand is `≥ 0`
(`m_ρ ≥ 0`, `Re(1/ρ) > 0`), and at least one nontrivial zero exists with a
strictly positive summand (`m_ρ ≥ 1`, `Re(1/ρ) > 0`). -/
theorem lambda1Mult_pos : 0 < lambda1Mult := by
  obtain ⟨ρ₀, hρ₀⟩ := nontrivialZeros_nonempty
  have hsummand_pos : 0 < (ZD.xiOrderNat ρ₀ : ℝ) * (1 / ρ₀).re := by
    apply mul_pos
    · exact_mod_cast xiOrderNat_pos_of_mem_NontrivialZeros hρ₀
    · exact li1Term_pos hρ₀
  have hnonneg : ∀ ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
      0 ≤ (ZD.xiOrderNat ρ.val : ℝ) * (1 / ρ.val).re :=
    fun ρ => mul_nonneg (by positivity) (li1Term_pos ρ.property).le
  exact lt_of_lt_of_le hsummand_pos
    (lambda1Mult_summable.le_tsum ⟨ρ₀, hρ₀⟩ (fun j _ => hnonneg j))

end ZD

end

#print axioms ZD.lambda1Mult_summable
#print axioms ZD.xiLogDeriv_one_re_eq
#print axioms ZD.lambda1Mult_eq_arith
#print axioms ZD.lambda1Mult_pos
