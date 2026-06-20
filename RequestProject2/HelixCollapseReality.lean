import Mathlib

/-!
# The dimensional collapse, reality axis: the completed ζ is real on the critical line

`completedRiemannZeta (½ + it)` is **real** — its imaginary part is `0`. Geometrically: the 3-D helix,
seen down the collapse axis, reads as a **real 1-D wave** `Z(t)` (the Hardy `Z`). This is the *reality*
forcing axis — **not** Li/Weil positivity (Hilbert–Pólya needs no `≥0`): it comes purely from the
functional equation `Λ(1−s) = Λ(s)` together with the Schwarz-reflection conjugation symmetry
`conj (Λ (conj s)) = Λ s`, since on the line `conj(½+it) = 1−(½+it)`.

This lives on the **analytic / bridge** side (it is a fact about the `L`-function `Λ`, which carries `log`
via `Γ` and `π^{-s/2}`), not inside the log-free 3-D helix. It is the *wave the collapse produces*.

**Honest scope (Rule Four).** This is the collapse-to-real-wave fact ONLY. It does **not** locate the
zeros — that is the cylinder / area-law inheritance (a separate brick). Do not conflate "real on the
line" with "zeros on the line."

**Dirichlet-`L` caveat.** The same proof transfers, but realness is *not* automatic: `Λ(χ,1−s) =
ε(χ)·Λ(χ⁻¹,s)` pairs `χ` with `χ⁻¹` through a root number `ε(χ)` of modulus `1` (generally complex).
So `Λ(χ,½+it)` is real only when `χ` is a real primitive character with `ε(χ)=1`; otherwise it carries a
fixed root-number phase. The root-number phase is the genuine caveat.

The conjugation lemma `completedRiemannZeta_conj` (Schwarz reflection for `Λ`) is reusable and not in
mathlib; it is proved here on the strip from the real Dirichlet coefficients and extended by the
identity theorem.
-/

open Complex

namespace HelixCollapse

/-- Conjugation symmetry of `Λ` on the strip `1 < Re s`, from the real Dirichlet coefficients. -/
theorem completedRiemannZeta_conj_strip {s : ℂ} (hs : 1 < s.re) :
    (starRingEnd ℂ) (completedRiemannZeta ((starRingEnd ℂ) s)) = completedRiemannZeta s := by
  have hcs : 1 < ((starRingEnd ℂ) s).re := by simpa using hs
  rw [completedZeta_eq_tsum_of_one_lt_re hs, completedZeta_eq_tsum_of_one_lt_re hcs]
  simp only [map_mul]
  rw [conj_tsum]
  congr 1
  · have harg : (((Real.pi : ℝ) : ℂ)).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]; exact Real.pi_ne_zero.symm
    have hpi : ∀ z : ℂ, (starRingEnd ℂ) (((Real.pi : ℝ) : ℂ) ^ z)
        = ((Real.pi : ℝ) : ℂ) ^ ((starRingEnd ℂ) z) := by
      intro z
      have := Complex.conj_cpow ((Real.pi : ℝ) : ℂ) ((starRingEnd ℂ) z) harg
      rw [conj_ofReal] at this
      simpa using this.symm
    rw [hpi, ← Gamma_conj]
    simp only [map_div₀, map_neg, map_ofNat, RingHomCompTriple.comp_apply, RingHom.id_apply]
  · apply tsum_congr
    intro n
    rw [map_div₀, map_one]
    congr 1
    have harg : ((n : ℂ)).arg ≠ Real.pi := by
      have h0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
      rw [show ((n : ℂ)) = ((n : ℝ) : ℂ) by push_cast; ring, Complex.arg_ofReal_of_nonneg h0]
      exact Real.pi_ne_zero.symm
    rw [Complex.cpow_conj _ _ harg]
    simp

/-- Conjugation symmetry of the pole-removed `Λ₀` on the strip. -/
theorem completedRiemannZeta₀_conj_strip {s : ℂ} (hs : 1 < s.re) :
    (starRingEnd ℂ) (completedRiemannZeta₀ ((starRingEnd ℂ) s)) = completedRiemannZeta₀ s := by
  have e1 : ∀ z : ℂ, completedRiemannZeta₀ z = completedRiemannZeta z + 1 / z + 1 / (1 - z) := by
    intro z; have := completedRiemannZeta_eq z; rw [this]; ring
  rw [e1, e1 s]
  simp only [map_add, map_div₀, map_one, map_sub, RingHomCompTriple.comp_apply, RingHom.id_apply]
  rw [completedRiemannZeta_conj_strip hs]

/-- Conjugation symmetry of the ENTIRE `Λ₀` on all of ℂ, via the identity theorem applied to the
holomorphic Schwarz reflection `g(s) = conj(Λ₀(conj s))`. -/
theorem completedRiemannZeta₀_conj (s : ℂ) :
    (starRingEnd ℂ) (completedRiemannZeta₀ ((starRingEnd ℂ) s)) = completedRiemannZeta₀ s := by
  set g : ℂ → ℂ := fun z => (starRingEnd ℂ) (completedRiemannZeta₀ ((starRingEnd ℂ) z)) with hg
  have hg_diff : Differentiable ℂ g := by
    intro x
    have hd : DifferentiableAt ℂ completedRiemannZeta₀ ((starRingEnd ℂ) x) :=
      differentiable_completedZeta₀ _
    have h2 := hd.conj_conj
    rw [Complex.conj_conj] at h2
    exact h2.congr_of_eventuallyEq (by filter_upwards with y; rfl)
  have hg_an : AnalyticOnNhd ℂ g Set.univ := analyticOnNhd_univ_iff_differentiable.mpr hg_diff
  have hΛ₀_an : AnalyticOnNhd ℂ completedRiemannZeta₀ Set.univ :=
    analyticOnNhd_univ_iff_differentiable.mpr differentiable_completedZeta₀
  have hev : g =ᶠ[nhds (2 : ℂ)] completedRiemannZeta₀ := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hmem : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by norm_num
    filter_upwards [hopen.mem_nhds hmem] with z hz
    exact completedRiemannZeta₀_conj_strip hz
  have heq := hΛ₀_an.eqOn_of_preconnected_of_eventuallyEq hg_an isPreconnected_univ
    (Set.mem_univ (2 : ℂ)) hev.symm
  exact (heq (Set.mem_univ s)).symm

/-- Conjugation symmetry of `Λ` EVERYWHERE (the poles `1/s`, `1/(1-s)` cancel symmetrically). -/
theorem completedRiemannZeta_conj (s : ℂ) :
    (starRingEnd ℂ) (completedRiemannZeta ((starRingEnd ℂ) s)) = completedRiemannZeta s := by
  rw [completedRiemannZeta_eq ((starRingEnd ℂ) s), completedRiemannZeta_eq s]
  simp only [map_sub, map_div₀, map_one, RingHomCompTriple.comp_apply, RingHom.id_apply]
  rw [completedRiemannZeta₀_conj]

/-- **The reality axis.** On the critical line `s = ½ + t·I`, the completed Riemann zeta lands on the
real axis: its imaginary part is `0`. The 3-D spiral collapses to a real 1-D wave. -/
theorem completedRiemannZeta_critical_line_im_zero (t : ℝ) :
    (completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I)).im = 0 := by
  set s : ℂ := 1 / 2 + (t : ℂ) * Complex.I with hs
  have hconj : (starRingEnd ℂ) s = 1 - s := by
    rw [hs]
    apply Complex.ext
    · simp; ring
    · simp
  have hFE : completedRiemannZeta (1 - s) = completedRiemannZeta s := completedRiemannZeta_one_sub s
  have hcj := completedRiemannZeta_conj s
  rw [hconj, hFE] at hcj
  exact Complex.conj_eq_iff_im.mp hcj

/-- **The reality axis, existential form**: `Λ(½+it)` equals a real number. -/
theorem completedRiemannZeta_critical_line_real (t : ℝ) :
    ∃ r : ℝ, completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I) = (r : ℂ) := by
  refine ⟨(completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I)).re, ?_⟩
  rw [Complex.ext_iff, Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨rfl, completedRiemannZeta_critical_line_im_zero t⟩

end HelixCollapse
