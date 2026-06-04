import Mathlib
import RequestProject.VonMangoldtEFStandalone
import RequestProject.ForcedAlignment
import RequestProject.HelixConvergence
import RequestProject.GreenHelmholtz

/-!
# Spectral Identification: Paired Li Coefficients as Norm-Squares

## The Goal

Prove unconditionally that each nontrivial zero ρ of ζ has a
**spectral identification**: its paired Li coefficient equals ‖v_ρ‖²
in a specific Hilbert space.

## What We Prove

### Unconditional results (no RH assumption):

1. **The Hilbert space**: H = ℂ with real inner product ⟨z,w⟩ = Re(z·w̄)
2. **The spectral vector**: v_ρ(n) = 1 - w(ρ)^n where w = 1 - 1/ρ
3. **On-line identification**: σ = 1/2 → paired_li = ‖v_ρ(n)‖² (proved)
4. **Off-line obstruction**: σ ≠ 1/2 → paired_li < 0 for large n (proved)
5. **Per-zero equivalence**: HasSpectralId(σ,γ) ⟺ σ = 1/2 (proved)
6. **EF anchor at σ > 1**: Re(zeroTerm(σ,ρ)) ≥ 0 unconditionally (proved)
7. **EF spectral identification at σ > 1**: each zero's EF contribution
   equals a norm-squared at σ > 1 (proved, unconditional)
8. **Weil form**: W(f) = Σ f(n)² Λ(n) ≥ 0 (proved)
9. **Hilbert-Pólya operator → RH** (proved)
10. **Paired Li unbounded for γ = 0 off-line** (proved, no γ ≠ 0 needed)

### The remaining gap:

The spectral identification at σ > 1 does NOT automatically extend
to the Li evaluation (n-th coefficient). The extension requires:
either (a) constructing a self-adjoint operator (Hilbert-Pólya), or
(b) proving the Weil positivity criterion.

Both (a) and (b) are equivalent to RH.

## Architecture

```
              Λ(n) ≥ 0                (Mathlib: vonMangoldt_nonneg)
                 │
                 ▼
         Euler product on helix       (EF: Σ Λ(n)/n^s = -ζ'/ζ)
                 │
                 ▼
         Per-zero decomposition       (Hadamard: ξ'/ξ = Σ zeroTerm)
                 │
     ┌───────────┴───────────┐
     │                       │
     ▼                       ▼
  σ > 1: algebraic       σ = 1/2: Li coefficient
  Re(zeroTerm) ≥ 0       paired_li = ‖v_ρ(n)‖²
  = ‖√(Re(zeroTerm))‖²   = ‖1 - w^n‖²
     │                       │
     └───────────┬───────────┘
                 │
                 ▼
         SPECTRAL IDENTIFICATION
         ‖v_ρ‖² = paired_li ≥ 0
                 │
                 ▼
         σ = 1/2 for each ρ  →  RH
```

The left branch (σ > 1) is unconditional but doesn't force σ = 1/2.
The right branch (σ = 1/2) forces σ = 1/2 but assumes it.
Connecting the two branches IS the Hilbert-Pólya conjecture.
-/

open scoped BigOperators Real
open Real Complex

noncomputable section

-- ═══════════════════════════════════════════════════════════════════════════
-- §1  The Spectral Vectors and On-Line Identification
-- ═══════════════════════════════════════════════════════════════════════════

/-- The **spectral vector** for zero ρ = (σ, γ) at index n. -/
def spectral_vector (sigma gamma : ℝ) (n : ℕ) : ℂ :=
  1 - moebius_helix sigma gamma ^ n

/-- The spectral vector equals li_helix_term. -/
theorem spectral_vector_eq_li (sigma gamma : ℝ) (n : ℕ) :
    spectral_vector sigma gamma n = li_helix_term sigma gamma n := by
  simp [spectral_vector, li_helix_term]

/-- **The on-line spectral identification.** -/
theorem spectral_identification_on_line (gamma : ℝ) (hg : gamma ≠ 0) (n : ℕ) :
    (li_helix_term (1/2) gamma n).re +
    (li_helix_term (1 - 1/2) (-gamma) n).re =
    ‖spectral_vector (1/2) gamma n‖ ^ 2 := by
  have h12 : (1:ℝ) - 1/2 = 1/2 := by norm_num
  rw [h12]; exact paired_li_eq_norm_sq gamma hg n

-- ═══════════════════════════════════════════════════════════════════════════
-- §2  The Spectral Identification Property
-- ═══════════════════════════════════════════════════════════════════════════

/-- **HasSpectralIdentification**: paired Li = ‖v(n)‖² for some v : ℕ → ℂ. -/
def HasSpectralIdentification (sigma gamma : ℝ) : Prop :=
  ∃ v : ℕ → ℂ, ∀ n : ℕ,
    (li_helix_term sigma gamma n).re +
    (li_helix_term (1 - sigma) (-gamma) n).re = ‖v n‖ ^ 2

/-- On-line zeros have the spectral identification. -/
theorem on_line_has_spectral_id (gamma : ℝ) (hg : gamma ≠ 0) :
    HasSpectralIdentification (1/2) gamma :=
  ⟨spectral_vector (1/2) gamma, fun n =>
    spectral_identification_on_line gamma hg n⟩

/-- Spectral identification → paired Li ≥ 0. -/
theorem spectral_id_forces_nonneg (sigma gamma : ℝ)
    (h : HasSpectralIdentification sigma gamma) (n : ℕ) :
    0 ≤ (li_helix_term sigma gamma n).re +
        (li_helix_term (1 - sigma) (-gamma) n).re := by
  obtain ⟨v, hv⟩ := h; rw [hv n]; positivity

/-- **Spectral identification forces σ = 1/2** (γ ≠ 0 case). -/
theorem spectral_id_forces_half (sigma gamma : ℝ) (hg : gamma ≠ 0)
    (h : HasSpectralIdentification sigma gamma) :
    sigma = 1/2 := by
  by_contra h_off
  obtain ⟨n₀, hn₀⟩ := paired_li_unbounded_off_line sigma gamma h_off hg (-1)
  linarith [spectral_id_forces_nonneg sigma gamma h n₀]

-- ═══════════════════════════════════════════════════════════════════════════
-- §3  Extending to γ = 0 (Real Zeros)
-- ═══════════════════════════════════════════════════════════════════════════

/-- The norm-squared of moebius_helix σ 0 is ((σ-1)/σ)². -/
private theorem moebius_norm_sq_gamma_zero (σ : ℝ) (hσ : 0 < σ) :
    ‖moebius_helix σ 0‖ ^ 2 = (σ - 1) ^ 2 / σ ^ 2 := by
  have h_sq : σ ^ 2 + 0 ^ 2 ≠ 0 := by positivity
  rw [moebius_norm_sq σ 0 h_sq]; ring

/-- For σ < 1/2 (and σ > 0), ‖moebius_helix σ 0‖ > 1. -/
private theorem moebius_norm_gt_one_low (σ : ℝ) (hσ1 : 0 < σ) (hσ2 : σ < 1/2) :
    1 < ‖moebius_helix σ 0‖ := by
  have h1 : 1 < ‖moebius_helix σ 0‖ ^ 2 := by
    rw [moebius_norm_sq_gamma_zero σ hσ1]
    rw [one_lt_div (by positivity : (0:ℝ) < σ ^ 2)]; nlinarith
  nlinarith [sq_nonneg (‖moebius_helix σ 0‖ - 1), norm_nonneg (moebius_helix σ 0)]

/-- For σ > 1/2 (and σ < 1), ‖moebius_helix σ 0‖ ≤ 1. -/
private theorem moebius_norm_le_one_high (σ : ℝ) (hσ1 : 0 < σ) (hσ2 : 1/2 < σ) (_hσ3 : σ < 1) :
    ‖moebius_helix σ 0‖ ≤ 1 := by
  have h1 : ‖moebius_helix σ 0‖ ^ 2 ≤ 1 := by
    rw [moebius_norm_sq_gamma_zero σ hσ1]
    rw [div_le_one (by positivity : (0:ℝ) < σ ^ 2)]; nlinarith
  nlinarith [sq_nonneg (‖moebius_helix σ 0‖ - 1), norm_nonneg (moebius_helix σ 0),
             sq_nonneg ‖moebius_helix σ 0‖]

/-- **Paired Li unbounded for γ = 0, σ ≠ 1/2, σ ∈ (0,1).**
    This extends `paired_li_unbounded_off_line` to the γ = 0 case,
    removing the γ ≠ 0 requirement. -/
theorem paired_li_unbounded_gamma_zero (σ : ℝ)
    (hσ1 : 0 < σ) (hσ2 : σ < 1) (hσ3 : σ ≠ 1/2) :
    ∀ M : ℝ, ∃ n : ℕ,
    (li_helix_term σ 0 n).re +
    (li_helix_term (1 - σ) 0 n).re < M := by
  intro M
  by_cases hlt : σ < 1/2
  · -- σ < 1/2: ‖moebius_helix σ 0‖ > 1, its Li is unbounded below
    have hw := moebius_norm_gt_one_low σ hσ1 hlt
    obtain ⟨n, hn⟩ := re_pow_unbounded_above (moebius_helix σ 0) hw (1 - (M - 2))
    refine ⟨n, ?_⟩
    have h_li : (li_helix_term σ 0 n).re = 1 - (moebius_helix σ 0 ^ n).re := by
      simp [li_helix_term]
    have h_partner_le : (li_helix_term (1 - σ) 0 n).re ≤ 2 :=
      li_re_le_two _ (moebius_norm_le_one_high (1-σ) (by linarith) (by linarith) (by linarith)) n
    linarith
  · -- σ > 1/2: symmetric — ‖moebius_helix (1-σ) 0‖ > 1
    push_neg at hlt
    have hgt : 1/2 < σ := lt_of_le_of_ne hlt (Ne.symm hσ3)
    have hw := moebius_norm_gt_one_low (1-σ) (by linarith) (by linarith)
    obtain ⟨n, hn⟩ := re_pow_unbounded_above (moebius_helix (1-σ) 0) hw (1 - (M - 2))
    refine ⟨n, ?_⟩
    have h_li : (li_helix_term (1 - σ) 0 n).re = 1 - (moebius_helix (1-σ) 0 ^ n).re := by
      simp [li_helix_term]
    have h_partner_le : (li_helix_term σ 0 n).re ≤ 2 :=
      li_re_le_two _ (moebius_norm_le_one_high σ hσ1 hgt hσ2) n
    linarith

/-- **Spectral identification forces σ = 1/2** — the γ = 0 case.
    Even for real zeros, the spectral identification forces on-line. -/
theorem spectral_id_forces_half_gamma_zero (σ : ℝ)
    (hσ1 : 0 < σ) (hσ2 : σ < 1)
    (h : HasSpectralIdentification σ 0) :
    σ = 1/2 := by
  by_contra h_off
  obtain ⟨n₀, hn₀⟩ := paired_li_unbounded_gamma_zero σ hσ1 hσ2 h_off (-1)
  have h_nn := spectral_id_forces_nonneg σ 0 h n₀
  simp only [neg_zero] at h_nn
  linarith

-- ═══════════════════════════════════════════════════════════════════════════
-- §4  The Complete Equivalence (No γ ≠ 0 Restriction)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **The Complete Spectral Identification Theorem.**
    For ANY (σ, γ) with 0 < σ < 1:
      HasSpectralIdentification(σ, γ) ⟺ σ = 1/2
    No restriction on γ. -/
theorem spectral_identification_complete (sigma gamma : ℝ)
    (hσ1 : 0 < sigma) (hσ2 : sigma < 1) :
    HasSpectralIdentification sigma gamma ↔ sigma = 1/2 := by
  constructor
  · -- → direction: spectral id forces σ = 1/2
    intro h
    by_cases hg : gamma = 0
    · subst hg; exact spectral_id_forces_half_gamma_zero sigma hσ1 hσ2 h
    · exact spectral_id_forces_half sigma gamma hg h
  · -- ← direction: σ = 1/2 gives spectral id
    intro h; subst h
    by_cases hg : gamma = 0
    · -- γ = 0, σ = 1/2: w = -1, paired = 1-(-1)^n + 1-(-1)^n = 2(1-(-1)^n)
      -- This is 0 or 4, always nonneg. But we need it = ‖v(n)‖²
      -- v(n) = 1 - (-1)^n which has norm² = |1-(-1)^n|² = (1-(-1)^n)²
      -- Paired = 2(1-(-1)^n) but ‖v‖² = (1-(-1)^n)² = 0 or 4
      -- These are equal! 2·0 = 0² and 2·2 = 4 = 2². Wait: 2·2 = 4 ≠ 2² = 4. OK that works.
      -- But actually for even n: paired = 0, ‖v‖² = 0. For odd n: paired = 4, ‖v‖² = 4. ✓
      subst hg
      refine ⟨fun n => (1 : ℂ) - moebius_helix (1/2) 0 ^ n, fun n => ?_⟩
      -- moebius_helix(1/2,0) = -1 has normSq = 1, so normSq identity applies
      simp only [li_helix_term, show (1:ℝ) - 1/2 = 1/2 from by norm_num]
      have hw_ns : Complex.normSq (moebius_helix (1/2) 0) = 1 := by
        have : moebius_helix (1/2) 0 = -1 := by
          unfold moebius_helix; simp [Complex.ext_iff]; norm_num
        rw [this]; simp [Complex.normSq_neg, Complex.normSq_one]
      have h_pow_ns : Complex.normSq (moebius_helix (1/2) 0 ^ n) = 1 := by
        rw [map_pow, hw_ns, one_pow]
      rw [← Complex.normSq_eq_norm_sq]
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re, Complex.sub_im,
                 Complex.one_im, zero_sub] at h_pow_ns ⊢
      nlinarith [sq_nonneg (moebius_helix (1/2) 0 ^ n).im]
    · exact on_line_has_spectral_id gamma hg

/-- **Spectral id for all zeros ⟺ all on line.** -/
theorem spectral_id_iff_all_on_line
    (zeros : ℕ → ℝ × ℝ)
    (h_strip : ∀ k, 0 < (zeros k).1 ∧ (zeros k).1 < 1) :
    (∀ k, HasSpectralIdentification (zeros k).1 (zeros k).2) ↔
    (∀ k, (zeros k).1 = 1/2) :=
  ⟨fun h k => (spectral_identification_complete _ _ (h_strip k).1 (h_strip k).2).mp (h k),
   fun h k => (spectral_identification_complete _ _ (h_strip k).1 (h_strip k).2).mpr (h k)⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §5  EF-Based Spectral Identification at σ > 1
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Unconditional spectral identification at σ > 1.**
    For each zero ρ in the critical strip and σ > 1:
      Re(zeroTerm(σ, ρ)) = ‖v_ρ(σ)‖²
    where v_ρ(σ) = √(Re(zeroTerm(σ, ρ))) ∈ ℝ ⊂ ℂ.
    Since Re(zeroTerm) ≥ 0 at σ > 1, this is well-defined. -/
theorem ef_spectral_id_sigma_gt_one (σ : ℝ) (hσ : 1 < σ)
    (ρ : ℂ) (hρ : ρ ∈ VMEFStandalone.NontrivialZeros) :
    (VMEFStandalone.zeroTerm (σ : ℂ) ρ).re =
    ‖(Real.sqrt ((VMEFStandalone.zeroTerm (σ : ℂ) ρ).re) : ℂ)‖ ^ 2 := by
  have h_nn := VMEFStandalone.re_zeroTerm_nonneg σ hσ ρ hρ.1 hρ.2.1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt h_nn]

/-- The spectral vector at σ > 1 is explicitly constructible. -/
def ef_spectral_vector (σ : ℝ) (ρ : ℂ) : ℂ :=
  Real.sqrt ((VMEFStandalone.zeroTerm (σ : ℂ) ρ).re)

/-- **The EF spectral identification at σ > 1 is a norm-squared.** -/
theorem ef_spectral_is_norm_sq (σ : ℝ) (hσ : 1 < σ)
    (ρ : ℂ) (hρ : ρ ∈ VMEFStandalone.NontrivialZeros) :
    (VMEFStandalone.zeroTerm (σ : ℂ) ρ).re = ‖ef_spectral_vector σ ρ‖ ^ 2 := by
  unfold ef_spectral_vector
  exact ef_spectral_id_sigma_gt_one σ hσ ρ hρ

-- ═══════════════════════════════════════════════════════════════════════════
-- §6  The Weil Positivity Bridge
-- ═══════════════════════════════════════════════════════════════════════════

/-- The Weil quadratic form. -/
def weilQuadForm (f : ℕ → ℝ) (S : Finset ℕ) : ℝ :=
  ∑ n ∈ S, f n ^ 2 * ArithmeticFunction.vonMangoldt n

/-- The Weil form is nonneg (from Λ ≥ 0). -/
theorem weilQuadForm_nonneg (f : ℕ → ℝ) (S : Finset ℕ) :
    0 ≤ weilQuadForm f S :=
  Finset.sum_nonneg fun _ _ =>
    mul_nonneg (sq_nonneg _) ArithmeticFunction.vonMangoldt_nonneg

/-- The Weil form is strictly positive when some prime has f(p) ≠ 0. -/
theorem weilQuadForm_pos (f : ℕ → ℝ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, Nat.Prime p) (hf : ∃ p ∈ S, f p ≠ 0) :
    0 < weilQuadForm f S := by
  obtain ⟨p, hp, hfp⟩ := hf
  apply lt_of_lt_of_le _ (Finset.single_le_sum
    (fun x _ => mul_nonneg (sq_nonneg (f x)) ArithmeticFunction.vonMangoldt_nonneg) hp)
  exact mul_pos (sq_pos_of_ne_zero hfp)
    (by rw [ArithmeticFunction.vonMangoldt_apply_prime (hS p hp)]
        exact Real.log_pos (by exact_mod_cast (hS p hp).one_lt))

-- ═══════════════════════════════════════════════════════════════════════════
-- §7  The Hilbert-Pólya Operator → RH
-- ═══════════════════════════════════════════════════════════════════════════

/-- **The Hilbert-Pólya Structure**: a self-adjoint operator whose spectral
    decomposition provides the spectral identification for all zeros. -/
structure HilbertPolyaOperator (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] where
  zeros : ℕ → ℝ × ℝ
  im_ne_zero : ∀ k, (zeros k).2 ≠ 0
  in_strip : ∀ k, 0 < (zeros k).1 ∧ (zeros k).1 < 1
  proj : ℕ → H →ₗ[ℝ] H
  proj_sa : ∀ k x y, @inner ℝ H _ (proj k x) y = @inner ℝ H _ x (proj k y)
  proj_idem : ∀ k x, proj k (proj k x) = proj k x
  x : ℕ → H
  identification : ∀ k n,
    (li_helix_term (zeros k).1 (zeros k).2 n).re +
    (li_helix_term (1 - (zeros k).1) (-(zeros k).2) n).re =
    ‖proj k (x n)‖ ^ 2

/-- **The Hilbert-Pólya operator proves RH.** -/
theorem hilbert_polya_implies_rh {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (HP : HilbertPolyaOperator H) :
    ∀ k, (HP.zeros k).1 = 1/2 := by
  intro k
  have h_id : HasSpectralIdentification (HP.zeros k).1 (HP.zeros k).2 :=
    ⟨fun n => (‖HP.proj k (HP.x n)‖ : ℝ), fun n => by
      rw [HP.identification k n, Complex.norm_real]; simp⟩
  exact spectral_id_forces_half _ _ (HP.im_ne_zero k) h_id

-- ═══════════════════════════════════════════════════════════════════════════
-- §8  Connecting to NontrivialZeros (Bridge to Mathlib's RH)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Spectral identification for ζ's zeros implies all on-line.**
    No γ ≠ 0 restriction — works for all zeros in the critical strip. -/
theorem spectral_id_implies_zeros_on_line
    (h : ∀ ρ : ℂ, ρ ∈ VMEFStandalone.NontrivialZeros →
      HasSpectralIdentification ρ.re ρ.im) :
    ∀ ρ : ℂ, ρ ∈ VMEFStandalone.NontrivialZeros → ρ.re = 1/2 := by
  intro ρ hρ
  exact (spectral_identification_complete ρ.re ρ.im hρ.1 hρ.2.1).mp (h ρ hρ)

-- ═══════════════════════════════════════════════════════════════════════════
-- §9  Boundary Extension Analysis
-- ═══════════════════════════════════════════════════════════════════════════

/-- **On-line boundary extension**: paired Li ≥ 0 at ALL n. -/
theorem boundary_extension_on_line (gamma : ℝ) (hg : gamma ≠ 0) :
    ∀ n : ℕ,
    0 ≤ (li_helix_term (1/2) gamma n).re +
        (li_helix_term (1 - 1/2) (-gamma) n).re :=
  fun n => by rw [spectral_identification_on_line gamma hg n]; positivity

/-- **Off-line boundary extension fails**: paired Li < 0 for some n. -/
theorem boundary_extension_fails_off_line (sigma gamma : ℝ)
    (hs : sigma ≠ 1/2) (hg : gamma ≠ 0) :
    ∃ n : ℕ,
    (li_helix_term sigma gamma n).re +
    (li_helix_term (1 - sigma) (-gamma) n).re < 0 := by
  obtain ⟨n, hn⟩ := paired_li_unbounded_off_line sigma gamma hs hg (-1)
  exact ⟨n, by linarith⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §10  The normSq Identity
-- ═══════════════════════════════════════════════════════════════════════════

/-- normSq(w^n) = 1 when normSq(w) = 1. -/
theorem normSq_pow_of_unit (w : ℂ) (hw : Complex.normSq w = 1) (n : ℕ) :
    Complex.normSq (w ^ n) = 1 := by
  induction n with
  | zero => simp [Complex.normSq]
  | succ n ih => rw [pow_succ, map_mul, ih, hw, mul_one]

/-- moebius_helix(1/2, γ) has unit normSq when γ ≠ 0. -/
theorem moebius_half_normSq (gamma : ℝ) (hg : gamma ≠ 0) :
    Complex.normSq (moebius_helix (1/2) gamma) = 1 := by
  have h1 : ‖moebius_helix (1/2) gamma‖ = 1 :=
    (moebius_unit_iff (1/2) gamma hg).mpr rfl
  rw [Complex.normSq_eq_norm_sq, h1]; norm_num

/-- normSq(1 - w^n) = 2(1 - Re(w^n)) when |w| = 1. -/
theorem normSq_one_sub_pow_unit (w : ℂ) (hw : Complex.normSq w = 1) (n : ℕ) :
    Complex.normSq (1 - w ^ n) = 2 * (1 - (w ^ n).re) := by
  have h1 := normSq_pow_of_unit w hw n
  simp only [Complex.normSq_apply] at h1 ⊢
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, zero_sub]
  nlinarith [sq_nonneg (w ^ n).im]

/-- **The normSq factorization for on-line spectral vectors.** -/
theorem normSq_spectral_factorization (gamma : ℝ) (hg : gamma ≠ 0) (n : ℕ) :
    Complex.normSq (spectral_vector (1/2) gamma n) =
    2 * (spectral_vector (1/2) gamma n).re := by
  rw [spectral_vector]
  exact normSq_one_sub_pow_unit _ (moebius_half_normSq gamma hg) n

/-- **Off-line obstruction**: normSq ≠ paired for off-line zeros. -/
theorem normSq_ne_paired_off_line (sigma gamma : ℝ) (hg : gamma ≠ 0)
    (hs : sigma ≠ 1/2) :
    ∃ n : ℕ, Complex.normSq (spectral_vector sigma gamma n) ≠
             (li_helix_term sigma gamma n).re +
             (li_helix_term (1 - sigma) (-gamma) n).re := by
  obtain ⟨n, hn⟩ := boundary_extension_fails_off_line sigma gamma hs hg
  exact ⟨n, fun heq => by linarith [Complex.normSq_nonneg (spectral_vector sigma gamma n)]⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §11  EF Anchor at σ > 1 (Algebraic)
-- ═══════════════════════════════════════════════════════════════════════════

/-- At σ > 1, each zero's EF contribution is nonneg (algebraic). -/
theorem ef_nonneg_anchor (σ : ℝ) (hσ : 1 < σ) (ρ : ℂ)
    (hρ : ρ ∈ VMEFStandalone.NontrivialZeros) :
    0 ≤ (VMEFStandalone.zeroTerm (σ : ℂ) ρ).re :=
  VMEFStandalone.re_zeroTerm_nonneg σ hσ ρ hρ.1 hρ.2.1

/-- The decomposition: Re(zeroTerm(σ,ρ)) = (σ-β)/|σ-ρ|² + β/|ρ|². -/
theorem ef_decomposition (σ β γ : ℝ) (hσ : 1 < σ)
    (hβ_pos : 0 < β) (hβ_lt : β < 1) :
    0 ≤ (σ - β) / ((σ - β) ^ 2 + γ ^ 2) + β / (β ^ 2 + γ ^ 2) :=
  add_nonneg (div_nonneg (by linarith) (by positivity))
             (div_nonneg (by linarith) (by positivity))

-- ═══════════════════════════════════════════════════════════════════════════
-- §12  Master Summary
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Master summary of the spectral identification framework.**

    **Unconditional results** (all sorry-free, clean axioms):
    1. On-line: paired_li = ‖1-w^n‖² (spectral_identification_on_line)
    2. Off-line γ≠0: paired_li → -∞ (paired_li_unbounded_off_line)
    3. Off-line γ=0: paired_li → -∞ (paired_li_unbounded_gamma_zero)
    4. HasSpectralId ⟺ σ=1/2 (spectral_identification_complete)
    5. EF at σ>1: Re(zeroTerm) = ‖√(Re)‖² (ef_spectral_is_norm_sq)
    6. Weil form nonneg (weilQuadForm_nonneg)
    7. Hilbert-Pólya operator → RH (hilbert_polya_implies_rh)
    8. Spectral id for all zeros → RH (spectral_id_implies_zeros_on_line)

    **The gap**: constructing the self-adjoint operator that extends the
    σ > 1 spectral identification to the Li evaluation at the boundary. -/
theorem spectral_id_master_summary :
    -- 1. On-line identification
    (∀ γ : ℝ, γ ≠ 0 → ∀ n,
      (li_helix_term (1/2) γ n).re + (li_helix_term (1-1/2) (-γ) n).re =
      ‖spectral_vector (1/2) γ n‖ ^ 2) ∧
    -- 2. Off-line failure (γ ≠ 0)
    (∀ σ γ : ℝ, σ ≠ 1/2 → γ ≠ 0 → ∃ n,
      (li_helix_term σ γ n).re + (li_helix_term (1-σ) (-γ) n).re < 0) ∧
    -- 3. Off-line failure (γ = 0)
    (∀ σ : ℝ, 0 < σ → σ < 1 → σ ≠ 1/2 → ∃ n,
      (li_helix_term σ 0 n).re + (li_helix_term (1-σ) 0 n).re < 0) ∧
    -- 4. Weil form nonneg
    (∀ f S, 0 ≤ weilQuadForm f S) :=
  ⟨fun γ hγ n => spectral_identification_on_line γ hγ n,
   fun σ γ hσ hγ => boundary_extension_fails_off_line σ γ hσ hγ,
   fun σ h1 h2 h3 => by
     obtain ⟨n, hn⟩ := paired_li_unbounded_gamma_zero σ h1 h2 h3 (-1)
     exact ⟨n, by linarith⟩,
   fun f S => weilQuadForm_nonneg f S⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §13  Axiom Audit
-- ═══════════════════════════════════════════════════════════════════════════

#print axioms spectral_identification_on_line
#print axioms spectral_id_forces_half
#print axioms spectral_id_forces_half_gamma_zero
#print axioms paired_li_unbounded_gamma_zero
#print axioms spectral_identification_complete
#print axioms spectral_id_iff_all_on_line
#print axioms hilbert_polya_implies_rh
#print axioms spectral_id_implies_zeros_on_line
#print axioms ef_spectral_is_norm_sq
#print axioms spectral_id_master_summary
#print axioms weilQuadForm_nonneg
#print axioms boundary_extension_on_line
#print axioms boundary_extension_fails_off_line
#print axioms normSq_spectral_factorization
#print axioms normSq_ne_paired_off_line

end
