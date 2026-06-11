import Mathlib
import RequestProject.SpectralSide
import RequestProject.HelixCollapseReality

/-!
# The Möbius / Cayley operator face of the on-line closure — 2-D

The on-line closure lives in 1-D as a real wave (`HelixOnlineClosure`: `Λ(½+it)` real). Its **2-D
operator face** is the **Möbius spectral value** `w(s) = 1 − 1/s` — *the same operator the
Hilbert–Pólya pipeline uses* (`SpectralSide.w`, with `SpectralSide.w_unit_iff_half`,
`SpectralSide.riemannHypothesis_iff_spectral_unitary`). The critical line maps to the **unit circle**,
and the spectral value is **unitary** (`conj w = w⁻¹`).

**The functional equation IS Möbius circle-inversion (Rule Five — the correct 2-D operator).** The
1-D reflection `s ↦ 1−s` is the *shadow* of the 2-D Möbius inversion `w ↦ 1/w`:

* `w_FE_inversion` : `w(1−s) = (w s)⁻¹` — the FE rendered as circle inversion (from
  `SpectralSide.w_FE_reciprocal`, `w(s)·w(1−s)=1`).
* `completedΛ_mobius_inversion` : `Λ` takes equal values at `s` and its **Möbius-inversion partner**
  `s'` (the point with `w s' = (w s)⁻¹`). So the operator acting on the completed wave is circle
  inversion `w ↦ 1/w`, not the bare 1-D `s ↦ 1−s`.

The pure circle geometry (FE-free, true at every point with `Re = ½`):

* `norm_w_eq_one_on_line` : `‖w(½+it)‖ = 1` — line → unit circle, from `‖z−1‖ = ‖z‖` on the line.
* `w_conj_eq_inv_on_line` : `conj(w(½+it)) = w(½+it)⁻¹` — conjugation *is* inversion on `|w|=1`.

Assembled, the on-line reality is read **through the Möbius operator**:

* `line_value_real` : `Λ(½+it)` is real — derived via the **Möbius inversion** FE step
  (`completedΛ_mobius_inversion`) together with Schwarz conjugation, *not* the bare functional
  equation. Real-on-the-line ↔ unitary-on-the-circle; the `s ↔ 1−s` reflection stays in 1-D as the
  shadow, the inversion `w ↔ 1/w` does the 2-D work.

**Honest scope (Rules Two & Four).** The analytic input is irreducible: `Λ`'s symmetry is a fact about
the L-function (`completedRiemannZeta_one_sub` + Schwarz reflection `completedRiemannZeta_conj`). What
changes here is the *operator* that carries it — circle inversion `w ↦ 1/w` (the correct 2-D/3-D map,
singular only at `s ∈ {0,1}`, the two points off the relevant locus) rather than the 1-D `s ↦ 1−s`.
This is the *reality* mechanism only; it does **not** by itself exclude off-line zeros (that forcing is
the FTA/prime-welding, not here).
-/

open Complex

namespace HelixMobiusClosure

/-- The Möbius operator is the pipeline's `SpectralSide.w (s) = 1 − 1/s`. -/
local notation "w" => SpectralSide.w

/-- **The functional equation as Möbius circle-inversion.** `w(1−s) = (w s)⁻¹`: the FE involution
    `s ↦ 1−s` is exactly inversion `w ↦ 1/w` of the spectral coordinate. From
    `SpectralSide.w_FE_reciprocal` (`w(s)·w(1−s)=1`). The two singular arguments `s ∈ {0,1}` (`w`'s pole
    and the origin) are excluded by `hs`/`hs1`. -/
theorem w_FE_inversion (s : ℂ) (hs : s ≠ 0) (hs1 : (1 : ℂ) - s ≠ 0) :
    w (1 - s) = (w s)⁻¹ := by
  have hrec : w s * w (1 - s) = 1 := SpectralSide.w_FE_reciprocal s hs hs1
  have hws_ne : w s ≠ 0 := left_ne_zero_of_mul_eq_one hrec
  rw [inv_eq_one_div, eq_div_iff hws_ne, mul_comm]
  exact hrec

/-- **The Möbius operator is injective.** `w a = w b → a = b` (it is the Cayley map, a Möbius
    transformation; injective even with the junk value `w 0 = 1`). -/
theorem w_injective : Function.Injective w := by
  intro a b h
  unfold SpectralSide.w at h
  rw [one_div, one_div] at h
  exact inv_inj.mp (sub_right_inj.mp h)

/-- **`Λ` is invariant under the Möbius inversion of its spectral coordinate.** For `s` (off the two
    singular arguments `0`, `1`) and any `s'` whose Möbius value is the *inverse* `w s' = (w s)⁻¹`,
    `Λ(s') = Λ(s)`. The reflection acting on the completed wave is **circle inversion `w ↦ 1/w`** — the
    correct 2-D operator — with the analytic content supplied by `completedRiemannZeta_one_sub`; the
    1-D `s ↦ 1−s` is its shadow (`s' = 1−s`, forced by `w_injective` + `w_FE_inversion`). -/
theorem completedΛ_mobius_inversion {s s' : ℂ} (hs : s ≠ 0) (hs1 : (1 : ℂ) - s ≠ 0)
    (hpart : w s' = (w s)⁻¹) :
    completedRiemannZeta s' = completedRiemannZeta s := by
  have hss' : s' = 1 - s := w_injective (by rw [hpart, w_FE_inversion s hs hs1])
  rw [hss']; exact completedRiemannZeta_one_sub s

/-- `1/2 + it` and its reflection `1/2 − it` are nonzero (both have real part `1/2`); the helper for
    applying the Möbius operator on the critical line, where `s ∉ {0,1}` always. -/
private theorem line_ne_zero (t : ℝ) : (1 / 2 + (t : ℂ) * I) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.zero_re, Complex.div_ofNat_re, Complex.one_re] at hre
  norm_num at hre

/-- **Line → unit circle.** `‖w(½+it)‖ = 1`, for every `t`. From the circle reflection
    `z − 1 = −conj z` on the line (hence `‖z−1‖ = ‖z‖`) — **not** the functional equation. -/
theorem norm_w_eq_one_on_line (t : ℝ) : ‖w (1 / 2 + (t : ℂ) * I)‖ = 1 := by
  have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  set z : ℂ := 1 / 2 + (t : ℂ) * I with hz
  have hz0 : z ≠ 0 := line_ne_zero t
  have hwz : w z = (z - 1) / z := by rw [SpectralSide.w]; field_simp
  have hrefl : z - 1 = -(starRingEnd ℂ) z := by
    rw [hz, hhalf]
    apply Complex.ext <;>
      simp only [Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im, Complex.conj_re,
        Complex.conj_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re,
        Complex.one_im] <;> ring
  have hnorm : ‖z - 1‖ = ‖z‖ := by rw [hrefl, norm_neg, Complex.norm_conj]
  rw [hwz, norm_div, hnorm, div_self (norm_ne_zero_iff.mpr hz0)]

/-- **The unitary condition, from the circle.** On the line, `conj(w(½+it)) = w(½+it)⁻¹` — conjugation
    *is* inversion on `|w|=1`. The 2-D Cayley face of the on-line closure: the spectral value is
    unitary. No functional equation. -/
theorem w_conj_eq_inv_on_line (t : ℝ) :
    (starRingEnd ℂ) (w (1 / 2 + (t : ℂ) * I)) = (w (1 / 2 + (t : ℂ) * I))⁻¹ :=
  (inv_eq_conj (norm_w_eq_one_on_line t)).symm

/-- **On-line reality, read through the Möbius operator.** `Λ(½+it)` is real. Proof: Schwarz
    conjugation gives `conj Λ(s) = Λ(conj s) = Λ(1−s)` (as `conj(½+it) = ½−it = 1−s`), and the
    **Möbius inversion** FE step (`completedΛ_mobius_inversion`, `w(1−s) = (w s)⁻¹`) gives
    `Λ(1−s) = Λ(s)`; hence `conj Λ(s) = Λ(s)`. The FE enters only as circle inversion of the spectral
    coordinate — the 2-D operator — never as the bare `s ↦ 1−s`. -/
theorem line_value_real (t : ℝ) :
    completedRiemannZeta (1 / 2 + (t : ℂ) * I)
      = (((completedRiemannZeta (1 / 2 + (t : ℂ) * I)).re : ℝ) : ℂ) := by
  set s : ℂ := 1 / 2 + (t : ℂ) * I with hs_def
  have hs : s ≠ 0 := line_ne_zero t
  have hs1 : (1 : ℂ) - s ≠ 0 := by
    have : (1 : ℂ) - s = 1 / 2 + ((-t : ℝ) : ℂ) * I := by rw [hs_def]; push_cast; ring
    rw [this]; exact line_ne_zero (-t)
  -- conj s = 1 − s on the line
  have hconjs : (starRingEnd ℂ) s = 1 - s := by
    rw [hs_def]; apply Complex.ext
    · simp [Complex.add_re, Complex.mul_re, Complex.sub_re]; ring
    · simp [Complex.add_im, Complex.mul_im, Complex.sub_im]
  -- Schwarz reflection: Λ(1−s) = conj Λ(s)
  have hschwarz : completedRiemannZeta (1 - s) = (starRingEnd ℂ) (completedRiemannZeta s) := by
    have h := HelixCollapse.completedRiemannZeta_conj s
    rw [hconjs] at h
    rw [← h, Complex.conj_conj]
  -- Möbius inversion (the FE, as the 2-D operator): Λ(1−s) = Λ(s)
  have hfe : completedRiemannZeta (1 - s) = completedRiemannZeta s :=
    completedΛ_mobius_inversion hs hs1 (w_FE_inversion s hs hs1)
  -- combine ⟹ Λ(s) is its own conjugate ⟹ real
  have hreal : (starRingEnd ℂ) (completedRiemannZeta s) = completedRiemannZeta s := by
    rw [← hschwarz, hfe]
  have him : (completedRiemannZeta s).im = 0 := Complex.conj_eq_iff_im.mp hreal
  rw [Complex.ext_iff, Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨rfl, him⟩

/-- **On-line reality, imaginary-part form**: `Im Λ(½+it) = 0`, via the Möbius operator. -/
theorem line_im_zero (t : ℝ) : (completedRiemannZeta (1 / 2 + (t : ℂ) * I)).im = 0 := by
  rw [line_value_real t, Complex.ofReal_im]

end HelixMobiusClosure

#print axioms HelixMobiusClosure.w_FE_inversion
#print axioms HelixMobiusClosure.completedΛ_mobius_inversion
#print axioms HelixMobiusClosure.line_value_real
