import RequestProject.HelixVonNeumannReceiver

/-!
# Discharging the spectral conditions `hesc` / `hsum` for the zero-height spectrum

The von Neumann receiver needs two spectral conditions: the spectrum escapes to ∞ (`hesc`) and is
trace-class (`hsum`). Here they are **discharged** for the natural spectrum `μₙ = Im ρₙ` (the imaginary
heights of the nontrivial zeros), from facts already proven:

* the zeros are **finite in every ball** (`NontrivialZeros_inter_closedBall_finite`), so any injective
  enumeration is **proper** (`‖ρₙ‖ → ∞`); confined to the strip `0 < Re < 1`, the heights then escape
  (`|Im ρ| ≥ ‖ρ‖ − |Re ρ| > ‖ρ‖ − 1`), giving `hesc`;
* `∑ 1/‖ρ‖² < ∞` (from `summable_lOrderNat_div_norm_sq_nontrivialZeros`), and the on-line pole
  `½+iμₙ` satisfies `‖½+iμₙ‖² > ¼‖ρₙ‖²`, so `∑ ‖½+iμₙ‖⁻² < ∞`, giving `hsum`.

So `grh_of_zeroHeightSpectrum_traceIdentity` derives GRH from **only the enumeration and `hCompat`** —
every analytic spectral condition is now a theorem. `hCompat` (the trace identity) stands alone.
-/

open Complex Filter Topology HelixSource HelixLimit

namespace HelixVonNeumannSpectrum

variable {N : ℕ} [NeZero N]

/-- `‖z‖² = z.re² + z.im²`. -/
private theorem normSq_re_im (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring

/-- `(ofReal μ).poleCoord.im = μ`. -/
private theorem poleCoord_im (μ : ℝ) : (SourceMode.ofReal μ).poleCoord.im = μ := by
  rw [SourceMode.ofReal_poleCoord]
  simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]

/-- `‖(ofReal μ).poleCoord‖² = ¼ + μ²` (the on-line pole `½+iμ`). -/
theorem poleCoord_normSq (μ : ℝ) : ‖(SourceMode.ofReal μ).poleCoord‖ ^ 2 = 1 / 4 + μ ^ 2 := by
  rw [normSq_re_im, SourceMode.poleCoord_re, poleCoord_im]; ring

/-- `∑ 1/‖ρ‖² < ∞` over the nontrivial zeros (drop the multiplicity weight, which is `≥ 1`). -/
theorem summable_inv_norm_sq_zeros {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) :
    Summable (fun ρ : {ρ : ℂ // ρ ∈ GRHSpectral.NontrivialZeros χ} => ‖ρ.val‖⁻¹ ^ 2) := by
  have hw := DirichletLHadamard.summable_lOrderNat_div_norm_sq_nontrivialZeros hχ hχp
  refine Summable.of_nonneg_of_le (fun ρ => by positivity) (fun ρ => ?_) hw
  have h1 : (1 : ℝ) ≤ (DirichletLHadamard.lOrderNat χ ρ.val : ℝ) := by
    exact_mod_cast DirichletLHadamard.lOrderNat_pos hχ ρ.property
  rw [inv_pow, div_eq_mul_inv]
  exact le_mul_of_one_le_left (by positivity) h1

/-- **Proper enumeration.** An injective enumeration of the nontrivial zeros escapes to ∞: only
finitely many zeros lie in any ball, so the enumeration leaves every ball. -/
theorem zeroEnum_proper {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (e : ℕ → {ρ : ℂ // ρ ∈ GRHSpectral.NontrivialZeros χ}) (hinj : Function.Injective e) :
    Tendsto (fun n => ‖(e n).val‖) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  rw [← Nat.cofinite_eq_atTop, eventually_cofinite]
  have hfin : (GRHSpectral.NontrivialZeros χ ∩ Metric.closedBall (0 : ℂ) b).Finite :=
    DirichletLHadamard.NontrivialZeros_inter_closedBall_finite hχ b
  refine Set.Finite.of_finite_image (f := fun n : ℕ => (e n).val) (hfin.subset ?_) ?_
  · rintro z ⟨n, hn, rfl⟩
    simp only [Set.mem_setOf_eq, not_le] at hn
    exact ⟨(e n).property, by rw [Metric.mem_closedBall, dist_zero_right]; exact hn.le⟩
  · intro a _ c _ h
    exact hinj (Subtype.ext h)

/-- **`hesc` discharged for the zero-height spectrum.** With `μₙ = Im ρₙ`, the heights escape (strip +
proper enumeration), and `‖½+iμₙ‖ ≥ |μₙ|`. -/
theorem vonNeumann_hesc_zeroHeights {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (e : ℕ → {ρ : ℂ // ρ ∈ GRHSpectral.NontrivialZeros χ}) (hinj : Function.Injective e) :
    Tendsto (fun n => ‖(SourceMode.ofReal ((e n).val.im)).poleCoord‖) atTop atTop := by
  have hproper := zeroEnum_proper hχ e hinj
  have him_tendsto : Tendsto (fun n => |(e n).val.im|) atTop atTop := by
    have hlb : ∀ n, ‖(e n).val‖ - 1 ≤ |(e n).val.im| := by
      intro n
      have hRe0 : 0 < (e n).val.re := (e n).property.1
      have hRe1 : (e n).val.re < 1 := (e n).property.2.1
      have hReabs : |(e n).val.re| < 1 := by rw [abs_of_pos hRe0]; exact hRe1
      have htri : ‖(e n).val‖ ≤ |(e n).val.re| + |(e n).val.im| := by
        conv_lhs => rw [← Complex.re_add_im (e n).val]
        refine le_trans (norm_add_le _ _) (le_of_eq ?_)
        simp [norm_mul, Complex.norm_real, Complex.norm_I, Real.norm_eq_abs]
      linarith
    have hlin : Tendsto (fun n => ‖(e n).val‖ - 1) atTop atTop := by
      simpa using Filter.tendsto_atTop_add_const_right atTop (-1) hproper
    exact tendsto_atTop_mono hlb hlin
  have hge : ∀ n, |(e n).val.im| ≤ ‖(SourceMode.ofReal ((e n).val.im)).poleCoord‖ := by
    intro n
    rw [show |(e n).val.im| = Real.sqrt ((e n).val.im ^ 2) from (Real.sqrt_sq_eq_abs _).symm,
        show ‖(SourceMode.ofReal ((e n).val.im)).poleCoord‖
           = Real.sqrt (‖(SourceMode.ofReal ((e n).val.im)).poleCoord‖ ^ 2) from
             (Real.sqrt_sq (norm_nonneg _)).symm]
    apply Real.sqrt_le_sqrt
    rw [poleCoord_normSq]; nlinarith [sq_nonneg ((e n).val.im)]
  exact tendsto_atTop_mono hge him_tendsto

/-- **`hsum` discharged for the zero-height spectrum** from `∑ 1/‖ρ‖² < ∞`: `‖½+iμₙ‖² > ¼‖ρₙ‖²`. -/
theorem vonNeumann_hsum_zeroHeights {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (hχp : χ.IsPrimitive)
    (e : ℕ → {ρ : ℂ // ρ ∈ GRHSpectral.NontrivialZeros χ}) (hinj : Function.Injective e) :
    Summable (fun n => ‖(SourceMode.ofReal ((e n).val.im)).poleCoord‖⁻¹ ^ 2) := by
  have hz : Summable (fun n => (4 : ℝ) * ‖(e n).val‖⁻¹ ^ 2) :=
    ((summable_inv_norm_sq_zeros hχ hχp).comp_injective hinj).mul_left 4
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hz
  rw [inv_pow, inv_pow, poleCoord_normSq]
  have hRe0 : 0 < (e n).val.re := (e n).property.1
  have hRe1 : (e n).val.re < 1 := (e n).property.2.1
  have hρ_pos : 0 < ‖(e n).val‖ :=
    norm_pos_iff.mpr (GRHSpectral.nontrivial_ne_zero (e n).property)
  have hineq : 1 / 4 * ‖(e n).val‖ ^ 2 ≤ 1 / 4 + (e n).val.im ^ 2 := by
    rw [normSq_re_im]; nlinarith
  rw [show (4 : ℝ) * (‖(e n).val‖ ^ 2)⁻¹ = (1 / 4 * ‖(e n).val‖ ^ 2)⁻¹ from by
    rw [mul_inv]; norm_num]
  rw [← one_div, ← one_div]
  exact one_div_le_one_div_of_le (by positivity) hineq

/-- **GRH from the zero-height spectrum + the single trace identity.** Every spectral condition is now
a theorem (escape and trace-class follow from the proven zero distribution); the only remaining input
is `hCompat` — the constructed real-spectrum trace equals `−L'/L(½+i·)`. -/
theorem grh_of_zeroHeightSpectrum_traceIdentity {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hχp : χ.IsPrimitive)
    (e : ℕ → {ρ : ℂ // ρ ∈ GRHSpectral.NontrivialZeros χ}) (hinj : Function.Injective e)
    (hCompat : ∀ z, HelixVonNeumannReceiver.vonNeumannReceiver (fun n => (e n).val.im) z
        = -logDeriv (DirichletCharacter.LFunction χ) (1 / 2 + Complex.I * z)) :
    GRHSpectral.GRH χ :=
  HelixVonNeumannReceiver.grh_of_vonNeumannReceiver_traceIdentity χ (fun n => (e n).val.im)
    (vonNeumann_hesc_zeroHeights hχ e hinj)
    (vonNeumann_hsum_zeroHeights hχ hχp e hinj) hCompat

end HelixVonNeumannSpectrum
