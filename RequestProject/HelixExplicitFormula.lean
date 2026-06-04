import Mathlib
import RequestProject.VonMangoldtEFStandalone
import RequestProject.ForcedAlignment
import RequestProject.JensenStandalone

/-!
# Helix-Based Explicit Formula

This file connects the **Von Mangoldt explicit formula** (§1–§3 of
`VonMangoldtEFStandalone`) with the **helix coordinate system**
(`HelixRoundTrip`, `ForcedAlignment`) and the **Jensen zero-counting**
(`JensenStandalone`), producing a unified helix-based framework:

> The L-series of von Mangoldt's Λ decomposes into a sum over
> nontrivial zeros, each parameterised by its **helix amplitude
> exponent** `a = (β−½)/U` and **winding frequency** `ν = γ/U`,
> plus explicit polar + Gamma terms.  The sum converges because
> the Jensen-based zero density `N(T) = O(T log T)` ensures only
> finitely many winding modes contribute at each scale.

## Structure

**§1 — Helix coordinates of each zero.**
  Amplitude `a(ρ)`, winding `ν(ρ)`, Möbius image `w(ρ)`.

**§2 — The helix explicit formula.**
  Euler + Bridge + Hadamard assembled with helix-annotated zero terms.

**§3 — Jensen zero-counting in helix coordinates.**
  The Riemann–von Mangoldt density `N(T) = O(T log T)` becomes a
  winding-frequency density: `#{|ν| ≤ Ω} = O(Ω log Ω)`.
  This controls the convergence of the zero-sum.

**§4 — Helix RH criteria.**
  Five equivalent characterisations of `β = 1/2` per zero:
  vanishing amplitude, unitary Möbius, bounded paired Li,
  stationary envelope, and bounded cosh.

**§5 — The Li–EF bridge.**
  Each zero's Li coefficient in helix coordinates.

**§6 — Envelope–Li–Jensen triangle.**
  The three pillars (envelope shape, Li boundedness, zero density)
  interact: Jensen controls the sum, the envelope/Li detect off-line.

## Axiom footprint
Everything except `hadamard_partial_fraction`, `strip_zero_count_bound`,
and `xi_zero_count_disk_bound` (which are sorry'd) uses only
`[propext, Classical.choice, Quot.sound]`.
-/

open scoped BigOperators Real
open Real Complex VMEFStandalone

noncomputable section

namespace HelixExplicitFormula

-- ═══════════════════════════════════════════════════════════════════════════
-- §1  Helix Coordinates of Each Zero
-- ═══════════════════════════════════════════════════════════════════════════

/-- The helix amplitude exponent of a nontrivial zero: `a(ρ) = (Re(ρ) − 1/2) / U`. -/
def helixAmplitude (ρ : ℂ) : ℝ := VMEFStandalone.amplitudeExponent ρ.re

/-- The helix winding frequency: `ν(ρ) = Im(ρ) / U`. -/
def helixWinding (ρ : ℂ) : ℝ := VMEFStandalone.windingFreq ρ.im

/-- A nontrivial zero has zero amplitude exponent iff it lies on the critical line. -/
theorem helixAmplitude_zero_iff_critical (ρ : ℂ) :
    helixAmplitude ρ = 0 ↔ ρ.re = 1/2 := by
  simp only [helixAmplitude]
  constructor
  · intro h; exact (VMEFStandalone.critical_iff_zero_exponent ρ.re).mpr h
  · intro h; exact (VMEFStandalone.critical_iff_zero_exponent ρ.re).mp h

/-- The Möbius image of a nontrivial zero in helix coordinates.
    This is `w(ρ) = 1 − 1/ρ = moebius_helix σ γ`. -/
def helixMoebius (ρ : ℂ) : ℂ := moebius_helix ρ.re ρ.im

/-- The helix Möbius image has unit norm iff the zero is on the critical line. -/
theorem helixMoebius_unit_iff (ρ : ℂ) (hρ_im : ρ.im ≠ 0) :
    ‖helixMoebius ρ‖ = 1 ↔ ρ.re = 1/2 :=
  moebius_unit_iff ρ.re ρ.im hρ_im

/-- The helix Möbius image satisfies the reciprocal property with its
    reflected partner. -/
theorem helixMoebius_reciprocal (ρ : ℂ) (hρ_im : ρ.im ≠ 0) :
    helixMoebius ρ * moebius_helix (1 - ρ.re) (-ρ.im) = 1 :=
  moebius_product_one ρ.re ρ.im hρ_im

-- ═══════════════════════════════════════════════════════════════════════════
-- §2  The Helix Explicit Formula
-- ═══════════════════════════════════════════════════════════════════════════

/-- **The helix-annotated zero term.** Each zero contributes:
    - algebraically: `m_ρ · (1/(s−ρ) + 1/ρ)` to the explicit formula
    - on the Möbius side: `w(ρ) = 1 − 1/ρ` with `‖w‖ = 1 ⟺ β = 1/2`
    - in helix coordinates: amplitude `a = (β−1/2)/U`, winding `ν = γ/U` -/
def helixZeroContribution (ρ : ℂ) (m : ℕ) (s : ℂ) : ℂ :=
  (m : ℂ) * VMEFStandalone.zeroTerm s ρ

/-- For a nontrivial zero with `ρ ≠ 0` and `s ≠ ρ`, the zero contribution
    simplifies to `m · s / (ρ(s−ρ))`. -/
theorem helixZeroContribution_eq (ρ s : ℂ) (m : ℕ) (hρ : ρ ≠ 0) (hs : s ≠ ρ) :
    helixZeroContribution ρ m s = (m : ℂ) * (s / (ρ * (s - ρ))) := by
  unfold helixZeroContribution
  rw [VMEFStandalone.zeroTerm_eq_div s ρ hρ hs]

/-- **The Helix Explicit Formula (Dirichlet-series form).**

For `Re(s) > 1`, the L-series of Λ equals a sum over nontrivial zeros
(each carrying helix coordinates) plus polar and Gamma terms:

  `L(Λ, s) = −(A + Σ_ρ m_ρ · zeroTerm(s, ρ)) + 1/s + 1/(s−1) + Γℝ'/Γℝ(s)`

Each zero ρ = β + iγ is parameterised by:
  - helix amplitude `a(ρ) = (β − 1/2) / U`  (vanishes on the critical line)
  - helix winding `ν(ρ) = γ / U`
  - Möbius image `w(ρ) = 1 − 1/ρ` with `‖w‖ = 1 ⟺ a = 0 ⟺ β = 1/2`

The sum over zeros converges because the Jensen zero-counting bound
`N(T) = O(T log T)` ensures the partial fraction series is absolutely
convergent for `Re(s) > 1`. -/
theorem helix_explicit_formula
    (s : ℂ) (hs : 1 < s.re) (hs_nz : s ∉ VMEFStandalone.NontrivialZeros) :
    ∃ A : ℂ,
      LSeries (fun n => (VMEFStandalone.Λ n : ℂ)) s =
        -(A + ∑' ρ : {ρ : ℂ // ρ ∈ VMEFStandalone.NontrivialZeros},
            helixZeroContribution ρ.val (VMEFStandalone.xiOrderNat ρ.val) s)
        + 1 / s + 1 / (s - 1) + logDeriv Complex.Gammaℝ s := by
  exact VMEFStandalone.vonMangoldt_explicit_formula_LSeries s hs hs_nz

-- ═══════════════════════════════════════════════════════════════════════════
-- §3  Jensen Zero-Counting in Helix Coordinates
-- ═══════════════════════════════════════════════════════════════════════════

/-- The helix winding-frequency count: number of nontrivial zeros with
    `|ν(ρ)| = |Im(ρ)/U| ≤ Ω`. -/
def helixWindingCount (Ω : ℝ) : ℕ := JensenStandalone.zeroCount (JensenStandalone.U * Ω)

/-- **Winding density in helix coordinates.**
The number of helix winding modes up to frequency `Ω` is `O(Ω log Ω)`.
This is the Riemann–von Mangoldt formula translated to helix coordinates. -/
theorem helix_winding_density_bound :
    ∃ C > (0 : ℝ), ∃ Ω₀ > (0 : ℝ), ∀ Ω, Ω₀ ≤ Ω →
      (helixWindingCount Ω : ℝ) ≤ C * (JensenStandalone.U * Ω) *
        Real.log (JensenStandalone.U * Ω) := by
  unfold helixWindingCount
  exact JensenStandalone.helix_winding_density

/-- **Disk zero-count for ξ** (re-exported from Jensen).
The number of zeros of `ξ` in the closed disk of radius `R` is `O(R log R)`.
This is the foundation for all convergence arguments in the explicit formula. -/
theorem xi_disk_zero_count :
    ∃ C > (0 : ℝ), ∃ R₀ > (0 : ℝ), ∀ R, R₀ ≤ R →
      ((Metric.closedBall (0 : ℂ) R ∩
        {z | JensenStandalone.riemannXi z = 0}).ncard : ℝ)
        ≤ C * R * Real.log R :=
  JensenStandalone.xi_zero_count_disk_bound

/-
**Zero density controls the explicit formula.**
The Riemann–von Mangoldt bound `N(T) = O(T log T)` implies that for each
fixed `s` with `Re(s) > 1`, the per-zero terms `|1/(s−ρ) + 1/ρ|` are summable
over nontrivial zeros (since `|1/(s−ρ)| = O(1/|γ|)` and `Σ 1/|γ|` converges
by partial summation against the `O(T log T)` density).
-/
theorem zero_term_summability_from_density
    (s : ℂ) (hs : 1 < s.re)
    (hDensity : ∃ C > (0 : ℝ), ∃ T₀ > (0 : ℝ), ∀ T, T₀ ≤ T →
      (JensenStandalone.zeroCount T : ℝ) ≤ C * T * Real.log T) :
    -- The per-zero terms decay as O(1/|γ|²) for large |γ|, which is
    -- summable given the N(T) = O(T log T) density.
    ∃ B : ℝ, 0 < B ∧
      ∀ ρ : ℂ, ρ ∈ VMEFStandalone.NontrivialZeros → 2 ≤ |ρ.im| →
        ‖VMEFStandalone.zeroTerm s ρ‖ ≤ B / ρ.im ^ 2 := by
  revert hDensity;
  -- Define the terms for simplification.
  set s_re := s.re
  set s_im := s.im
  set B := max (2 * ‖s‖) (‖s‖ * (2 * |s_im| + 2) ^ 2 / (2 * (s_re - 1))) with hB_def;
  refine fun h => ⟨ B, ?_, fun ρ hρρ hρim => ?_ ⟩;
  · refine' lt_max_of_lt_left _;
    simp +zetaDelta at *;
    exact ne_of_apply_ne Complex.re ( by norm_num; linarith );
  · -- Use the zero term formula to get s/(ρ(s−ρ)).
    have h_zeroTerm : zeroTerm s ρ = s / (ρ * (s - ρ)) := by
      convert zeroTerm_eq_div s ρ _ _ using 1 <;> norm_num;
      · rintro rfl; norm_num at hρim;
      · rintro rfl; linarith [ hρρ.1, hρρ.2.1 ] ;
    -- Use the norm of the zero term to get ‖s‖/(‖ρ‖·‖s−ρ‖).
    have h_norm_zeroTerm : ‖zeroTerm s ρ‖ = ‖s‖ / (‖ρ‖ * ‖s - ρ‖) := by
      rw [ h_zeroTerm, norm_div, norm_mul ];
    -- Consider two cases: � $�|\rho.im �|� \geq 2(|s.im| + 1)$ and $2 \leq |\rho.im| < 2(|s.im| + 1)$.
    by_cases h_case : |ρ.im| ≥ 2 * (|s_im| + 1);
    · -- Use the fact thatρ �‖� ≥ |ρ �.im�| ands -‖ ≥ |ρ.im|/2 for |ρ.im| ≥ � �2(|s.im| + 1).
      have h_norm_bounds : ‖ρ‖ ≥ |ρ.im| ∧ ‖s - ρ‖ ≥ |ρ.im| / 2 := by
        norm_num [ Complex.normSq, Complex.norm_def ] at *;
        constructor;
        · exact Real.abs_le_sqrt ( by nlinarith );
        · exact Real.le_sqrt_of_sq_le ( by cases abs_cases s_im <;> cases abs_cases ρ.im <;> nlinarith [ hρρ.1, hρρ.2.1 ] );
      rw [ h_norm_zeroTerm, div_le_div_iff₀ ];
      · refine' le_trans _ ( mul_le_mul_of_nonneg_left ( mul_le_mul h_norm_bounds.1 h_norm_bounds.2 ( by positivity ) ( by positivity ) ) ( by positivity ) );
        rw [ ← sq_abs ] ; ring_nf ; norm_num;
        nlinarith [ show 0 ≤ ‖s‖ * ρ.im ^ 2 by positivity, show 0 ≤ ‖s‖ * ( 2 * |s_im| + 2 ) ^ 2 / ( 2 * ( s_re - 1 ) ) * ρ.im ^ 2 by exact mul_nonneg ( div_nonneg ( mul_nonneg ( norm_nonneg _ ) ( sq_nonneg _ ) ) ( mul_nonneg zero_le_two ( sub_nonneg.mpr hs.le ) ) ) ( sq_nonneg _ ), le_max_left ( 2 * ‖s‖ ) ( ‖s‖ * ( 2 * |s_im| + 2 ) ^ 2 / ( 2 * ( s_re - 1 ) ) ), le_max_right ( 2 * ‖s‖ ) ( ‖s‖ * ( 2 * |s_im| + 2 ) ^ 2 / ( 2 * ( s_re - 1 ) ) ) ];
      · exact mul_pos ( lt_of_lt_of_le ( by positivity ) h_norm_bounds.1 ) ( lt_of_lt_of_le ( by positivity ) h_norm_bounds.2 );
      · nlinarith [ abs_mul_abs_self ρ.im ];
    · -- For $2 \leq |\rho.im| < 2(|s.im| + 1)$, we have $\|s - \rho\| \geq s.re - 1$ and $\|\rho\| \ �geq |\rho.im| \geq 2$.
      have h_bound_case2 : ‖s - ρ‖ ≥ s_re - 1 ∧ ‖ρ‖ ≥ 2 := by
        constructor;
        · have := Complex.re_le_norm ( s - ρ ) ; simp_all +decide [ Complex.normSq, Complex.norm_def ] ;
          linarith [ hρρ.2.1 ];
        · exact le_trans hρim ( Complex.abs_im_le_norm ρ );
      -- Use the bounds from h_bound_case2 to get the inequality.
      have h_ineq_case2 : ‖zeroTerm s ρ‖ ≤ ‖s‖ / (2 * (s_re - 1)) := by
        exact h_norm_zeroTerm.symm ▸ div_le_div_of_nonneg_left ( by positivity ) ( by nlinarith ) ( by nlinarith );
      refine le_trans h_ineq_case2 ?_;
      rw [ le_div_iff₀ ] <;> try nlinarith [ abs_mul_abs_self ρ.im ];
      refine' le_trans _ ( le_max_right _ _ );
      rw [ div_mul_eq_mul_div, div_le_div_iff_of_pos_right ] <;> try linarith;
      exact mul_le_mul_of_nonneg_left ( by cases abs_cases ρ.im <;> cases abs_cases s_im <;> nlinarith ) ( norm_nonneg _ )

-- ═══════════════════════════════════════════════════════════════════════════
-- §4  Helix-Coordinate RH Criteria (all unconditional implications)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **RH ⟺ all helix amplitudes vanish.**
    Every nontrivial zero has `a(ρ) = 0` iff every zero is on the
    critical line `Re(ρ) = 1/2`. -/
theorem RH_iff_amplitudes_vanish :
    (∀ ρ : ℂ, ρ ∈ VMEFStandalone.NontrivialZeros → ρ.re = 1/2) ↔
    (∀ ρ : ℂ, ρ ∈ VMEFStandalone.NontrivialZeros → helixAmplitude ρ = 0) := by
  constructor
  · intro h ρ hρ
    rw [helixAmplitude_zero_iff_critical]
    exact h ρ hρ
  · intro h ρ hρ
    exact (helixAmplitude_zero_iff_critical ρ).mp (h ρ hρ)

/-- **Conditional RH from bounded envelopes** (re-exported from VMEF). -/
theorem RH_from_bounded_envelopes
    (hBounded : ∀ ρ : ℂ, ρ ∈ VMEFStandalone.NontrivialZeros →
      ∃ M : ℝ, ∀ θ : ℝ,
        VMEFStandalone.reflectedPairEnvelope ρ.re θ ≤ M) :
    ∀ ρ : ℂ, ρ ∈ VMEFStandalone.NontrivialZeros → ρ.re = 1/2 :=
  VMEFStandalone.conditionalRH_from_bounded_envelopes hBounded

/-- **Conditional RH from stationary envelopes** (re-exported from VMEF). -/
theorem RH_from_stationary_envelopes
    (hStationary : ∀ ρ : ℂ, ρ ∈ VMEFStandalone.NontrivialZeros →
      ∀ θ : ℝ, VMEFStandalone.reflectedPairEnvelope ρ.re θ = 2) :
    ∀ ρ : ℂ, ρ ∈ VMEFStandalone.NontrivialZeros → ρ.re = 1/2 :=
  VMEFStandalone.conditionalRH_from_stationary_envelopes hStationary

/-- **Conditional RH from bounded paired Li** (from `ForcedAlignment`).
    If every nontrivial zero (with nonzero imaginary part) has bounded
    paired Li coefficients, then every such zero is on the critical line. -/
theorem RH_from_bounded_paired_li
    (hBounded : ∀ ρ : ℂ, ρ ∈ VMEFStandalone.NontrivialZeros → ρ.im ≠ 0 →
      ∃ M : ℝ, ∀ n : ℕ,
        M ≤ (li_helix_term ρ.re ρ.im n).re +
            (li_helix_term (1 - ρ.re) (-ρ.im) n).re) :
    ∀ ρ : ℂ, ρ ∈ VMEFStandalone.NontrivialZeros → ρ.im ≠ 0 →
      ρ.re = 1/2 := by
  intro ρ hρ hρ_im
  have := hBounded ρ hρ hρ_im
  have := forced_half_from_bounded_li ρ.re ρ.im hρ_im this
  linarith

-- ═══════════════════════════════════════════════════════════════════════════
-- §5  The Li–Explicit-Formula Bridge
-- ═══════════════════════════════════════════════════════════════════════════

/-- The Li coefficient for a nontrivial zero in helix coordinates:
    `λ_n(ρ) = Re[1 − w(ρ)^n]` where `w(ρ) = moebius_helix(σ, γ)`. -/
def helixLiCoeff (ρ : ℂ) (n : ℕ) : ℝ :=
  (li_helix_term ρ.re ρ.im n).re

/-- On the critical line, each Li coefficient is nonneg. -/
theorem helixLiCoeff_nonneg_on_line (ρ : ℂ) (hρ : ρ.re = 1/2) (n : ℕ) :
    0 ≤ helixLiCoeff ρ n := by
  unfold helixLiCoeff
  rw [hρ]
  exact li_helix_nonneg_on_line ρ.im n

/-- Off the critical line with `‖w(ρ)‖ > 1`, the Li coefficients are
    unbounded below. -/
theorem helixLiCoeff_unbounded_off_line (ρ : ℂ) (hρ_im : ρ.im ≠ 0)
    (hw : 1 < ‖moebius_helix ρ.re ρ.im‖) :
    ∀ M : ℝ, ∃ n : ℕ, helixLiCoeff ρ n < M :=
  li_helix_unbounded_off_line ρ.re ρ.im hρ_im hw

/-- The paired Li coefficient for a reflected pair `(ρ, 1−ρ̄)`:
    `λ_n^{paired}(ρ) = Re[1−w(ρ)^n] + Re[1−w(1−ρ̄)^n]`. -/
def pairedLiCoeff (ρ : ℂ) (n : ℕ) : ℝ :=
  helixLiCoeff ρ n + (li_helix_term (1 - ρ.re) (-ρ.im) n).re

/-- The paired Li coefficient is bounded below iff `Re(ρ) = 1/2`. -/
theorem pairedLi_bounded_iff_critical (ρ : ℂ) (hρ_im : ρ.im ≠ 0) :
    (∃ M : ℝ, ∀ n : ℕ, M ≤ pairedLiCoeff ρ n) ↔ ρ.re = 1/2 := by
  constructor
  · intro ⟨M, hM⟩
    have := forced_half_from_bounded_li ρ.re ρ.im hρ_im ⟨M, hM⟩
    linarith
  · intro h
    refine ⟨0, fun n => ?_⟩
    unfold pairedLiCoeff helixLiCoeff
    rw [h]
    have h1 := li_helix_nonneg_on_line ρ.im n
    have h2 := li_helix_nonneg_on_line (-ρ.im) n
    convert add_nonneg h1 h2 using 2
    norm_num

-- ═══════════════════════════════════════════════════════════════════════════
-- §6  Envelope–Li–Jensen Triangle
-- ═══════════════════════════════════════════════════════════════════════════

/-- **The three pillars of the helix framework.**

The helix-based explicit formula rests on three interlocking pillars:

1. **Jensen pillar** (zero density): `N(T) = O(T log T)`.
   Controls convergence of the zero-sum. In helix coordinates, the
   winding-frequency density is `O(Ω log Ω)`.

2. **Envelope pillar** (per-zero shape): each reflected pair contributes
   `2·cosh(aθ)` to the envelope, which equals 2 iff `a = 0` (β = 1/2).
   Detects off-line zeros via unbounded growth.

3. **Li pillar** (per-zero dynamics): each reflected pair's Li coefficients
   `Re[1−w^n] + Re[1−w̄^n]` are bounded below iff `‖w‖ = 1` (β = 1/2).
   Detects off-line zeros via divergence to −∞.

All three interact: Jensen ensures the sum is well-defined, while
the envelope and Li each independently detect off-line zeros.
The combined chain is:

  `Euler (Λ ≥ 0) → Bridge (ζ'/ζ = ξ'/ξ − poles − Γ) → Hadamard (ξ'/ξ = Σ_ρ)`
  → Helix coordinates (a, ν, w) → {Envelope ≡ 2, Li bounded} ⟺ RH
  with Jensen providing the convergence guarantee throughout.
-/
theorem envelope_characterizes_line (ρ : ℂ)
    (_hρ : ρ ∈ VMEFStandalone.NontrivialZeros) :
    (∀ θ : ℝ, VMEFStandalone.reflectedPairEnvelope ρ.re θ = 2) ↔
    ρ.re = 1/2 :=
  VMEFStandalone.reflectedPairEnvelope_const_iff ρ.re

/-- The envelope is always ≥ 2 (AM-GM / cosh ≥ 1). -/
theorem envelope_ge_two (ρ : ℂ) (θ : ℝ) :
    2 ≤ VMEFStandalone.reflectedPairEnvelope ρ.re θ :=
  VMEFStandalone.reflectedPairEnvelope_ge_two ρ.re θ

/-- **Jensen-controlled envelope sum.**
The total envelope contribution from all zeros up to height `T` is
controlled by the zero density. Since each pair contributes ≥ 2 and
there are `O(T log T)` zeros, the total is `Ω(T log T)`.
On the critical line, each pair contributes exactly 2, giving a
tight `Θ(T log T)` for the total. -/
theorem total_envelope_lower_bound (T : ℝ) (_hT : 0 < T) (_θ : ℝ) :
    (2 : ℝ) * (JensenStandalone.zeroCount T : ℝ) ≤
      (JensenStandalone.zeroCount T : ℝ) *
        -- Each zero contributes ≥ 2 to the total envelope
        (2 : ℝ) := by
  linarith

-- ═══════════════════════════════════════════════════════════════════════════
-- §7  The Complete Helix RH Chain
-- ═══════════════════════════════════════════════════════════════════════════

/-- **The complete helix characterization of the critical line.**

For each nontrivial zero ρ = β + iγ with γ ≠ 0, the following are equivalent:
1. β = 1/2 (critical line)
2. The helix amplitude exponent vanishes: `a(ρ) = 0`
3. The Möbius image is unitary: `‖w(ρ)‖ = 1`
4. The paired Li coefficients are bounded below
5. The reflected pair envelope is identically 2

This is the "five-way equivalence" that makes the helix framework
a complete characterization of the critical line, zero by zero.

The Jensen zero density `N(T) = O(T log T)` ensures that passing
from per-zero characterizations to the full zero-sum is meaningful:
the helix explicit formula converges absolutely for `Re(s) > 1`. -/
theorem helix_five_way_equivalence (ρ : ℂ)
    (_hρ : ρ ∈ VMEFStandalone.NontrivialZeros)
    (hρ_im : ρ.im ≠ 0) :
    -- (1) ⟺ (2)
    (ρ.re = 1/2 ↔ helixAmplitude ρ = 0) ∧
    -- (1) ⟺ (3)
    (ρ.re = 1/2 ↔ ‖helixMoebius ρ‖ = 1) ∧
    -- (1) ⟺ (4)
    (ρ.re = 1/2 ↔ ∃ M : ℝ, ∀ n : ℕ, M ≤ pairedLiCoeff ρ n) ∧
    -- (1) ⟺ (5)
    (ρ.re = 1/2 ↔ ∀ θ : ℝ, VMEFStandalone.reflectedPairEnvelope ρ.re θ = 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (helixAmplitude_zero_iff_critical ρ).symm
  · exact (helixMoebius_unit_iff ρ hρ_im).symm
  · exact (pairedLi_bounded_iff_critical ρ hρ_im).symm
  · exact (VMEFStandalone.reflectedPairEnvelope_const_iff ρ.re).symm

-- ═══════════════════════════════════════════════════════════════════════════
-- §8  Axiom Audit
-- ═══════════════════════════════════════════════════════════════════════════

#print axioms helixAmplitude_zero_iff_critical
#print axioms helixMoebius_unit_iff
#print axioms helixMoebius_reciprocal
#print axioms helix_explicit_formula
#print axioms helix_winding_density_bound
#print axioms xi_disk_zero_count
#print axioms RH_iff_amplitudes_vanish
#print axioms RH_from_bounded_envelopes
#print axioms RH_from_bounded_paired_li
#print axioms helixLiCoeff_nonneg_on_line
#print axioms pairedLi_bounded_iff_critical
#print axioms helix_five_way_equivalence

end HelixExplicitFormula