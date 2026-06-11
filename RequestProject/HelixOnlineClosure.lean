import Mathlib
import RequestProject.HelixCollapseReality
import RequestProject.HelixMobiusClosure

/-!
# The on-line closure mechanism — unconditional (ζ), read through the Möbius operator

On the critical line the completed wave is **real**, and a zero there is a **transversal real-axis
crossing**. The reflection that does the work is the **Möbius circle-inversion** `w ↦ 1/w` of the
spectral coordinate `w(s) = 1 − 1/s` (`SpectralSide.w`, the Hilbert–Pólya pipeline's operator) — the
correct 2-D/3-D operator. The 1-D functional equation `s ↦ 1−s` is its **shadow**: `w(1−s) = (w s)⁻¹`
(`HelixMobiusClosure.w_FE_inversion`).

* `line_value_real` / `line_im_zero` — `Λ(½+it)` is real, the on-line closure. Now derived **through
  the Möbius operator** (`HelixMobiusClosure.line_value_real`): Schwarz conjugation + the Möbius
  inversion FE step `completedΛ_mobius_inversion`, *not* the bare `s ↦ 1−s`. Real-on-the-line ↔
  unitary-on-the-circle (`HelixMobiusClosure.w_conj_eq_inv_on_line`).

* `sigma_refl` / `im_odd` — the **1-D radial shadow**: `Im Λ(½+x+it)` is *odd* in the radial offset `x`,
  the transversal crossing pinned to the center. Stated in the strip coordinate `x`, where the Möbius
  inversion appears as its 1-D reflection `s ↦ 1−s` (kept here as the shadow, per Rule Five).

**Honest scope — what this is and is NOT (Rules Two & Four).** This is the *reality* mechanism: it makes
the on-line closure a real-axis crossing and pins it transversally at the center. It is a property of
the **functional equation + real coefficients alone** (the analytic input `completedRiemannZeta_one_sub`
+ Schwarz `completedRiemannZeta_conj` is irreducible; what changed is the *operator* carrying it —
circle inversion, not the 1-D reflection). It does **not** exclude off-line zeros: a function with an FE
and real coefficients but **no Euler product** (Davenport–Heilbronn) has the same reality and
transversality and still has zeros off the line. The off-line forcing must come from the FTA /
prime-welding, which this file does not use. Do not read "real wave, transversal crossing" as "zeros on
the line"; it is the on-line half only.
-/

open Complex

namespace HelixOnlineClosure

/-- **Reflection across the critical line.** `Λ(½−x+it) = conj Λ(½+x+it)` — from the functional equation
    `Λ(1−s)=Λ(s)` and Schwarz conjugation `conj(Λ(s)) = Λ(conj s)`. This is the **1-D radial shadow** of
    the Möbius inversion (`HelixMobiusClosure.completedΛ_mobius_inversion` is the 2-D operator form);
    stated totally in the strip offset `x`, so the inversion shows up as the reflection `s ↦ 1−s`. -/
theorem sigma_refl (x t : ℝ) :
    completedRiemannZeta (1/2 - (x:ℂ) + (t:ℂ)*I)
      = (starRingEnd ℂ) (completedRiemannZeta (1/2 + (x:ℂ) + (t:ℂ)*I)) := by
  have hconj : (starRingEnd ℂ) (completedRiemannZeta (1/2 + (x:ℂ) + (t:ℂ)*I))
      = completedRiemannZeta ((starRingEnd ℂ) (1/2 + (x:ℂ) + (t:ℂ)*I)) := by
    have h := HelixCollapse.completedRiemannZeta_conj ((starRingEnd ℂ) (1/2 + (x:ℂ) + (t:ℂ)*I))
    rwa [Complex.conj_conj] at h
  rw [hconj]
  have hc : (starRingEnd ℂ) (1/2 + (x:ℂ) + (t:ℂ)*I) = 1/2 + (x:ℂ) - (t:ℂ)*I := by
    simp only [map_add, map_div₀, map_one, map_ofNat, Complex.conj_ofReal, map_mul,
      Complex.conj_I, mul_neg]
    ring
  rw [hc, show (1/2 - (x:ℂ) + (t:ℂ)*I) = 1 - (1/2 + (x:ℂ) - (t:ℂ)*I) from by ring,
     completedRiemannZeta_one_sub]

/-- **The transversality (1-D radial shadow).** `Im Λ(½+x+it)` is an *odd* function of the radial offset
    `x`. So `Im` crosses `0` at `x=0` and flips sign across the line — the on-line closure is a
    transversal real-axis crossing, pinned to the center locally. -/
theorem im_odd (x t : ℝ) :
    (completedRiemannZeta (1/2 + (x:ℂ) + (t:ℂ)*I)).im
      = -(completedRiemannZeta (1/2 - (x:ℂ) + (t:ℂ)*I)).im := by
  rw [sigma_refl x t, Complex.conj_im]; ring

/-- **Reality on the line** — `Im Λ(½+it) = 0`. Read **through the Möbius operator**
    (`HelixMobiusClosure.line_im_zero`): the FE step is circle inversion `w ↦ 1/w` of the spectral
    coordinate, not the bare `s ↦ 1−s`. -/
theorem line_im_zero (t : ℝ) : (completedRiemannZeta (1/2 + (t:ℂ)*I)).im = 0 :=
  HelixMobiusClosure.line_im_zero t

/-- The completed wave on the line **is** a real number: `Λ(½+it) = (Z t : ℂ)` with `Z t` its real
    part. The on-line closure is the vanishing of the real wave `Z`. Read through the Möbius operator
    (`HelixMobiusClosure.line_value_real`). -/
theorem line_value_real (t : ℝ) :
    completedRiemannZeta (1/2 + (t:ℂ)*I)
      = (((completedRiemannZeta (1/2 + (t:ℂ)*I)).re : ℝ) : ℂ) :=
  HelixMobiusClosure.line_value_real t

end HelixOnlineClosure
