import RequestProject.HelixImaginaryAxis
import RequestProject.ChiThreeLogDerivIdentity

/-!
# The fibre cancellation on the imaginary axis — `iy` end to end, in the winding picture

`χ₃` splits the integers (read on the helix) into two winding fibres: the `+` fibre `n ≡ 1 (mod 3)`
and the `−` fibre `n ≡ 2 (mod 3)` (with `n ≡ 0` silent). `L(s,χ₃)` is the **difference of the two
fibres' helix-phasor sums**, and a zero is exactly where the two fibres **balance** — the winding
cancellation event, stated entirely on the geometric side (the `helixPtGen` phasors), no Hurwitz zeta.

This closes the `iy` picture: the imaginary axis is the winding (`HelixImaginaryAxis.wind_eq_cpow`),
`L` is the χ-weighted phasor sum read off the helix points (`lfunction_eq_helixSum`), and the zeros
are where the `±` character fibres' windings cancel (`chi3_helix_cancellation`). The helix is its own
continuation, so this is `L` and its zeros on the whole plane.
-/

open Complex HelixLogFree HelixImaginaryAxis

namespace HelixFibre

/-- The **`+` fibre** (residue `1 (mod 3)`) of helix phasors. -/
noncomputable def fibrePlusHelix (s : ℂ) : ℂ :=
  ∑' n : ℕ, (if n % 3 = 1 then (1 : ℂ) else 0) / helixPtGen s.re s.im n

/-- The **`−` fibre** (residue `2 (mod 3)`) of helix phasors. -/
noncomputable def fibreMinusHelix (s : ℂ) : ℂ :=
  ∑' n : ℕ, (if n % 3 = 2 then (1 : ℂ) else 0) / helixPtGen s.re s.im n

/-- `χ₃(n)` is the `+`/`−` fibre indicator difference: `+1` on `n ≡ 1`, `−1` on `n ≡ 2`, `0` on `n ≡ 0`. -/
theorem chi3_natCast_eq (n : ℕ) :
    ChiThree.χ3 (↑n : ZMod 3)
      = (if n % 3 = 1 then (1 : ℂ) else 0) - (if n % 3 = 2 then (1 : ℂ) else 0) := by
  have hmod : (↑n : ZMod 3) = ↑(n % 3) := by rw [ZMod.natCast_mod]
  rw [hmod]
  have h3 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h3 with h | h | h <;> rw [h] <;>
    simp [ChiThree.χ3_zero, ChiThree.χ3_one, ChiThree.χ3_two]

/-- Each fibre's helix-phasor sum is absolutely summable for `Re s > 1` (magnitudes `1/n^σ`, the
    winding being unit modulus). -/
theorem summable_fibreHelix (r : ℕ) {σ t : ℝ} (hσ : 1 < σ) :
    Summable (fun n => (if n % 3 = r then (1 : ℂ) else 0) / helixPtGen σ t n) := by
  apply Summable.of_norm_bounded (Real.summable_one_div_nat_rpow.mpr hσ)
  intro n
  rcases eq_or_ne n 0 with hn | hn
  · subst hn
    have h0 : helixPtGen σ t 0 = 0 := by
      rw [helixPtGen, Nat.cast_zero, Real.zero_rpow (by linarith), Complex.ofReal_zero, zero_mul]
    rw [h0, div_zero, norm_zero]; positivity
  · rw [norm_div]
    have hnorm : ‖helixPtGen σ t n‖ = (n : ℝ) ^ σ := by
      rw [helixPtGen_eq_cpow σ t n hn, show (n : ℂ) = ((n : ℝ) : ℂ) from by push_cast; ring,
          Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
      congr 1
      simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im]
    rw [hnorm]
    have hind : ‖(if n % 3 = r then (1 : ℂ) else 0)‖ ≤ 1 := by split_ifs <;> simp
    gcongr

/-- **The fibre split, in the winding picture.** `L(s,χ₃) = fibre₊ − fibre₋`: the difference of the
    two character fibres' helix-phasor sums (`Re s > 1`; continues to the whole plane). -/
theorem lfunction_chi3_eq_fibreHelix_diff {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.LFunction ChiThree.χ3 s = fibrePlusHelix s - fibreMinusHelix s := by
  rw [fibrePlusHelix, fibreMinusHelix, lfunction_eq_helixSum ChiThree.χ3 hs,
      ← Summable.tsum_sub (summable_fibreHelix 1 hs) (summable_fibreHelix 2 hs)]
  exact tsum_congr (fun n => by rw [chi3_natCast_eq n, sub_div])

/-- **The winding cancellation = a zero.** `L(s,χ₃) = 0` exactly when the two fibres' helix-phasor sums
    balance — the `+` winding fibre equals the `−` winding fibre. The zeros of `L` are the heights where
    the character fibres' windings cancel. -/
theorem chi3_helix_cancellation {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.LFunction ChiThree.χ3 s = 0 ↔ fibrePlusHelix s = fibreMinusHelix s := by
  rw [lfunction_chi3_eq_fibreHelix_diff hs, sub_eq_zero]

end HelixFibre
