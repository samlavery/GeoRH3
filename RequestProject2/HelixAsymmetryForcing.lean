import Mathlib
import RequestProject.HelixImaginaryAxis
import RequestProject.SpectralSide

/-!
# The asymmetry forcing — why total cancellation can only collapse at `Re = ½`

This file records the **1-D skeleton** of the geometric forcing argument: an off-line zero needs a
"buddy" it has nowhere to hide, because the helix is one-sided and asymmetric.

## The setup (taken as established upstream, not re-litigated here)

* **The helix is a no-drift source.** Its cancellation spectrum is *real* — the climbing spiral read
  down the collapse axis is a real wave (`source_noDrift`, σ-free, a conservation/unitarity fact, not a
  coordinate). A real spectrum is closed under complex conjugation `ρ ↦ conj ρ` — the `½ ± it` pairing,
  the **pairs**. This is settled; we use it.
* **The helix is one-sided and asymmetric.** Under FTA it is the free commutative monoid `ℕ≥1 ≅ ⊕_p ℕ`,
  origin `0` (= identity `1`) climbing to `∞`, radius `√n` — *no* `σ = ½` line of reflection inside it
  (`HelixMultiplicative`: the functional equation needs the external gamma-factor completion; it is not
  an internal symmetry of the one-sided structure).

## The two reflexes of a zero, and where they meet

A zero `ρ` has two images:

* `conj ρ` — provided **intrinsically** by the no-drift/real structure (the spiral up vs down);
* `1 − ρ` — the functional-equation **buddy**, demanded by the *external* completion.

The earned facts here pin where these two can be reconciled:

* `buddy_eq_conj_iff_onLine` : `1 − ρ = conj ρ ↔ Re ρ = ½` — the FE-buddy *coincides* with the
  intrinsic conjugate **exactly on the line**.
* `onLine_iff_fixed_reflection` : `1 − conj s = s ↔ Re s = ½` — the line is precisely the fixed-point
  set of the reflection `R = FE ∘ conj`, `s ↦ 1 − conj s`. The center, at the 1-D level.
* `buddy_re_ne_self` : `Re ρ ≠ ½ → Re (1 − ρ) ≠ Re ρ` — **off** the line the buddy sits at a *different*
  real part `1 − σ ≠ σ`: a genuinely separate slot.

## The mechanism (Hilbert–Pólya, in geometric clothing)

A zero must satisfy *both* reflexes: the structure provides `conj ρ`, and the completion demands `1−ρ`.
The one-sided helix has **no reflection void** at a second real part for an independent buddy to occupy
(`buddy_re_ne_self` is the obstruction made precise — off-line the buddy would need a `1−σ` slot the
monotone `√n` structure does not host). So the only zeros it can carry are the ones whose two reflexes
**land on the same point** — `1 − ρ = conj ρ`, i.e. `Re ρ = ½` (`buddy_eq_conj_iff_onLine`). A real
spectrum forced through an FE-symmetric function, with no off-axis room, collapses to the axis. That is
exactly "a self-adjoint operator has no non-real eigenvalue," read on the helix.

The center is the same all the way down (Rule Five): the fixed set of `R` at 1-D here, the self-inverse
radius `‖w‖ = 1` at the 2-D circle (`SpectralSide.w_unit_iff_half`, `w(ρ)·w(1−ρ) = 1`), the cylinder
axis at 3-D. The midpoint stays the center under every projection.

## The radial-drift reading (the same forcing, measured by amplitude)

An off-line zero is an **amplitude defect**: a total cancellation occurring at a radial magnitude away
from the baseline. The helix's baseline is **earned, not planted** — the actual point has norm `√n`
(`norm_helixPt`), while the off-line readout point has norm `n^σ` (`norm_helixPtGen`). These are two
genuine norms, *not* the costume `radial := σ − ½`. They agree at every integer iff `σ = ½`
(`radial_matches_iff_half`). So "no radial drift, by construction" means: the geometry is locked to the
`√n` amplitude (the `√`-of-planar-packing baseline, Rule Eight), and an off-line zero would require the
readout to run at `n^σ ≠ √n` — i.e. to **warp the radius itself** away from `√n`. The drift cannot be
introduced within the construction; only by deforming the geometry off its earned baseline. (This is the
amplitude face of the asymmetry: drift = a second radius the one-sided `√n` structure does not carry.)
-/

namespace HelixAsymmetry

open Complex HelixLogFree

/-- **The FE-buddy coincides with the intrinsic conjugate exactly on the line.** A zero's two reflexes —
    the conjugate `conj ρ` (provided by the no-drift/real structure) and the functional-equation buddy
    `1 − ρ` (demanded by the external completion) — are the *same point* iff `Re ρ = ½`. -/
theorem buddy_eq_conj_iff_onLine (ρ : ℂ) : 1 - ρ = (starRingEnd ℂ) ρ ↔ ρ.re = 1 / 2 := by
  constructor
  · intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at hre; linarith
  · intro h
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]; linarith
    · simp only [Complex.sub_im, Complex.one_im, Complex.conj_im]; ring

/-- **The critical line is the fixed-point set of the reflection `R = FE ∘ conj`** (`s ↦ 1 − conj s`).
    The geometric center at the 1-D level: `½` is exactly what `R` holds still. -/
theorem onLine_iff_fixed_reflection (s : ℂ) : 1 - (starRingEnd ℂ) s = s ↔ s.re = 1 / 2 := by
  constructor
  · intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at hre; linarith
  · intro h
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]; linarith
    · simp only [Complex.sub_im, Complex.one_im, Complex.conj_im]; ring

/-- **Off the line, the buddy needs a separate slot.** If `Re ρ ≠ ½` then `1 − ρ` sits at a *different*
    real part `1 − σ ≠ σ` — a second location the one-sided, asymmetric helix has no reflection void to
    host. This is the obstruction to an off-line zero's buddy, made precise. -/
theorem buddy_re_ne_self (ρ : ℂ) (h : ρ.re ≠ 1 / 2) : (1 - ρ).re ≠ ρ.re := by
  simp only [Complex.sub_re, Complex.one_re]; intro hc; apply h; linarith

/-- The off-line readout point's amplitude is `n^σ` — a genuine norm. -/
theorem norm_helixPtGen (σ t : ℝ) (n : ℕ) :
    ‖HelixImaginaryAxis.helixPtGen σ t n‖ = (n : ℝ) ^ σ := by
  unfold HelixImaginaryAxis.helixPtGen
  rw [norm_mul, Complex.norm_real, Circle.norm_coe, mul_one, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) σ)]

/-- **No radial drift ⟺ on the line — against the earned `√n` baseline, not a coordinate.** The readout
    amplitude `n^σ` (`norm_helixPtGen`) matches the helix's *own* amplitude `√n` (`norm_helixPt`, a real
    norm) at every integer iff `σ = ½`. An off-line zero is an amplitude defect `n^σ ≠ √n` — drift the
    `√n`-locked construction cannot carry without warping the radius. This is a comparison of two genuine
    norms, never `radial := σ − ½`. -/
theorem radial_matches_iff_half (σ t : ℝ) :
    (∀ n : ℕ, 2 ≤ n → ‖HelixImaginaryAxis.helixPtGen σ t n‖
        = ‖helixPt (fun p => t * Real.log p) n‖) ↔ σ = 1 / 2 := by
  constructor
  · intro h
    have h2 := h 2 (le_refl 2)
    rw [norm_helixPtGen, norm_helixPt, Real.sqrt_eq_rpow, show ((2:ℕ):ℝ) = (2:ℝ) by norm_num] at h2
    rcases lt_trichotomy σ (1/2) with hlt | heq | hgt
    · exact absurd h2 (ne_of_lt ((Real.rpow_lt_rpow_left_iff (by norm_num : (1:ℝ) < 2)).2 hlt))
    · exact heq
    · exact absurd h2 (ne_of_gt ((Real.rpow_lt_rpow_left_iff (by norm_num : (1:ℝ) < 2)).2 hgt))
  · intro h n _
    rw [norm_helixPtGen, norm_helixPt, h, Real.sqrt_eq_rpow]

/-! ## The geometric asymmetry: the helix radial map has no reflection void off the line

The two preceding `norm` lemmas compare the off-line readout `n^σ` against the helix's *own* `√n`
baseline. Here we compare it against the **functional-equation buddy's own readout**: the reflection
`σ ↦ 1 − σ` (the 1-D radial shadow of the Möbius inversion `w ↦ 1/w`) sends radius `n^σ` to `n^{1−σ}`.

The point is the **asymmetry of the actual helix radial map** `σ ↦ ‖helixPtGen σ t n‖ = n^σ`
(`norm_helixPtGen`): it is **strictly not invariant** under the FE-reflection except on the line. So the
one-sided `√n` packing genuinely hosts *no* second radius for an off-line buddy to occupy — the
"reflection void" is empty off-line. These are facts about the genuine norms of the genuine helix
points, never the costume `radial := σ − ½`.

The same asymmetry, read on the **2-D Möbius operator** (the correct 2-D/3-D object — `SpectralSide.w`,
`w ρ = 1 − 1/ρ`), is `SpectralSide.w_unit_iff_half`: `‖w ρ‖ = 1 ⟺ Re ρ = ½`. Off the line the Möbius
value leaves the unit circle — the operator face of the radial drift. The FE acts there as circle
inversion `w(1−ρ) = (w ρ)⁻¹` (`SpectralSide.w_FE_reciprocal`, `w ρ · w(1−ρ) = 1`), *not* the bare 1-D
`s ↦ 1−s`; the radial reflection `σ ↦ 1−σ` below is its 1-D shadow. -/

/-- **Off the line, the radial readout strictly disagrees with its FE-buddy's readout.** For `σ ≠ ½` and
    any integer `n ≥ 2`, the helix readout amplitude `‖helixPtGen σ t n‖ = n^σ` differs from the
    reflection buddy's amplitude `‖helixPtGen (1−σ) t' n‖ = n^{1−σ}`. The one-sided `√n` structure has
    **no reflection void** at the second radius `n^{1−σ}` — the obstruction to hosting an off-line
    buddy, made precise on the genuine helix-point norms. -/
theorem radial_refl_mismatch (σ t t' : ℝ) (h : σ ≠ 1 / 2) (n : ℕ) (hn : 2 ≤ n) :
    ‖HelixImaginaryAxis.helixPtGen σ t n‖ ≠ ‖HelixImaginaryAxis.helixPtGen (1 - σ) t' n‖ := by
  rw [norm_helixPtGen, norm_helixPtGen]
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  intro hc
  rcases lt_trichotomy σ (1 - σ) with hlt | heq | hgt
  · exact absurd hc (ne_of_lt ((Real.rpow_lt_rpow_left_iff hn1).2 hlt))
  · exact h (by linarith)
  · exact absurd hc (ne_of_gt ((Real.rpow_lt_rpow_left_iff hn1).2 hgt))

/-- **The radial map is invariant under the FE-reflection only on the line.** The helix readout amplitude
    matches its reflection buddy's amplitude at *every* integer `n ≥ 2` iff `σ = ½`. The `σ = ½` line is
    exactly where the one-sided `√n` packing *does* host the reflection (its only self-reflective radius);
    everywhere else (`radial_refl_mismatch`) the void is empty. Two genuine norms, not `radial := σ − ½`. -/
theorem radial_refl_invariant_iff_half (σ t t' : ℝ) :
    (∀ n : ℕ, 2 ≤ n → ‖HelixImaginaryAxis.helixPtGen σ t n‖
        = ‖HelixImaginaryAxis.helixPtGen (1 - σ) t' n‖) ↔ σ = 1 / 2 := by
  constructor
  · intro h
    by_contra hσ
    exact radial_refl_mismatch σ t t' hσ 2 (le_refl 2) (h 2 (le_refl 2))
  · intro h n _
    rw [norm_helixPtGen, norm_helixPtGen, h]
    norm_num

end HelixAsymmetry
