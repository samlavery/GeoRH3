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

/-! ## Standing-line uniqueness: `σ = ½` is the only real fiber line

`line_value_real` shows `Λ` is a standing (real) wave on the line `Re = ½`. This section proves
the converse closure: it is a standing wave on **no other** vertical line. Together: `σ = ½` is
exactly the locus where the fiber collapses to a real 1-D wave — the only line on which a sign
flip (a captured node of the real wave) can exist at all.

Proof shape (all unconditional):
1. reality on the line `σ₀` + Schwarz reflection (`HelixCollapse.completedRiemannZeta_conj`) +
   the functional equation (`completedRiemannZeta_one_sub`) force the horizontal translation
   invariance `Λ(σ₀+it) = Λ(σ₀+it+p)` with `p = 1 − 2σ₀`, at every height `t`;
2. the identity theorem (`AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`, applied on the
   plane minus the four *real* translated poles — open and path-connected since
   `Module.rank ℝ ℂ = 2`) propagates the invariance to every non-real point;
3. a nonzero period would transport the pole of `Λ` at `1` (`completedRiemannZeta_residue_one`)
   onto a point of analyticity: along `sₙ = 1 + i/(n+1)` the products `(sₙ−1)·Λ(sₙ)` tend to `1`,
   yet equal `(sₙ−1)·Λ(sₙ+q) → 0·Λ(1+q) = 0`. Hence `p = 0`, i.e. `σ₀ = ½`. -/

open Filter Topology

namespace HelixMobiusClosure

/-- **`σ = ½` is the only standing line.** If the completed zeta fiber is real at *every* height
`t` on the vertical line `Re = σ₀`, then `σ₀ = ½`. This is the reality-uniqueness half of the
standing-wave description of the critical line: `line_value_real` gives reality *on* `½`; this
theorem says it happens on no other line, so `½` is the unique line carrying sign flips of the
real wave. -/
theorem standing_line_unique (σ₀ : ℝ)
    (hreal : ∀ t : ℝ, (completedRiemannZeta (σ₀ + t * Complex.I)).im = 0) :
    σ₀ = 1/2 := by
  by_contra hσ
  -- the putative horizontal period `p = 1 − 2σ₀` (nonzero exactly off the half line)
  obtain ⟨p, hp_def⟩ : ∃ p : ℝ, p = 1 - 2 * σ₀ := ⟨_, rfl⟩
  have hp_ne : p ≠ 0 := by
    rw [hp_def]
    intro h
    exact hσ (by linarith)
  -- STEP A (pointwise, all `t`): reality + Schwarz + FE  ⟹  `Λ(σ₀+it) = Λ(σ₀+it+p)`
  have hA : ∀ t : ℝ, completedRiemannZeta ((σ₀ : ℂ) + (t : ℂ) * I)
      = completedRiemannZeta ((σ₀ : ℂ) + (t : ℂ) * I + (p : ℂ)) := by
    intro t
    have hself : (starRingEnd ℂ) (completedRiemannZeta ((σ₀ : ℂ) + (t : ℂ) * I))
        = completedRiemannZeta ((σ₀ : ℂ) + (t : ℂ) * I) :=
      Complex.conj_eq_iff_im.mpr (hreal t)
    have hconjs : (starRingEnd ℂ) ((σ₀ : ℂ) + (t : ℂ) * I) = (σ₀ : ℂ) - (t : ℂ) * I := by
      apply Complex.ext <;> simp
    have hschwarz := HelixCollapse.completedRiemannZeta_conj ((σ₀ : ℂ) + (t : ℂ) * I)
    rw [hconjs] at hschwarz
    have h1 : completedRiemannZeta ((σ₀ : ℂ) - (t : ℂ) * I)
        = completedRiemannZeta ((σ₀ : ℂ) + (t : ℂ) * I) := by
      have h := congrArg (starRingEnd ℂ) hschwarz
      rw [Complex.conj_conj] at h
      rw [h, hself]
    have h2 : (σ₀ : ℂ) + (t : ℂ) * I + (p : ℂ) = 1 - ((σ₀ : ℂ) - (t : ℂ) * I) := by
      rw [hp_def]
      push_cast
      ring
    rw [h2, completedRiemannZeta_one_sub, h1]
  -- STEP B (identity theorem): the translation invariance holds at every non-real point
  have hper : ∀ z : ℂ, z.im ≠ 0 →
      completedRiemannZeta z = completedRiemannZeta (z + (p : ℂ)) := by
    -- the four (all real) bad points: the poles of `Λ` and their pulled-back translates
    set B : Set ℂ := {0, 1, ((-p : ℝ) : ℂ), ((1 - p : ℝ) : ℂ)} with hB_def
    have hB_fin : B.Finite := by
      rw [hB_def]
      exact (((Set.finite_singleton _).insert _).insert _).insert _
    have hcompl : ∀ z : ℂ, z.im ≠ 0 → z ∈ Bᶜ := by
      intro z hz hmem
      rw [hB_def] at hmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with rfl | rfl | rfl | rfl <;> simp at hz
    have hnotB : ∀ z : ℂ, z ∈ Bᶜ →
        z ≠ 0 ∧ z ≠ 1 ∧ z ≠ ((-p : ℝ) : ℂ) ∧ z ≠ ((1 - p : ℝ) : ℂ) := by
      intro z hz
      rw [hB_def] at hz
      simpa only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using hz
    have hUopen : IsOpen (Bᶜ : Set ℂ) := hB_fin.isClosed.isOpen_compl
    have hUconn : IsPreconnected (Bᶜ : Set ℂ) := by
      have hrank : 1 < Module.rank ℝ ℂ := by
        rw [Complex.rank_real_complex]
        exact_mod_cast Nat.one_lt_two
      exact (hB_fin.countable.isPathConnected_compl_of_one_lt_rank
        hrank).isConnected.isPreconnected
    have hf_an : AnalyticOnNhd ℂ completedRiemannZeta (Bᶜ : Set ℂ) := by
      refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUopen
      exact (differentiableAt_completedZeta (hnotB z hz).1 (hnotB z hz).2.1).differentiableWithinAt
    have hg_an : AnalyticOnNhd ℂ (fun z => completedRiemannZeta (z + (p : ℂ))) (Bᶜ : Set ℂ) := by
      refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUopen
      have h0 : z + (p : ℂ) ≠ 0 := fun h =>
        (hnotB z hz).2.2.1 (by push_cast; linear_combination h)
      have h1 : z + (p : ℂ) ≠ 1 := fun h =>
        (hnotB z hz).2.2.2 (by push_cast; linear_combination h)
      exact ((differentiableAt_completedZeta h0 h1).comp z
        (differentiableAt_id.add_const _)).differentiableWithinAt
    -- the anchor `σ₀ + i` and the nontrivial vertical approach `σ₀ + (1 + 1/(n+1))·i`
    have hz₀ : ((σ₀ : ℂ) + I) ∈ (Bᶜ : Set ℂ) := hcompl _ (by simp)
    have hu_tend : Tendsto (fun n : ℕ => (σ₀ : ℂ) + ((1 + 1/(n+1) : ℝ) : ℂ) * I)
        atTop (𝓝[≠] ((σ₀ : ℂ) + I)) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · have hr : Tendsto (fun n : ℕ => (1 + 1/(n+1) : ℝ)) atTop (𝓝 1) := by
          simpa using tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
        have hc : Tendsto (fun n : ℕ => ((1 + 1/(n+1) : ℝ) : ℂ))
            atTop (𝓝 ((1 : ℝ) : ℂ)) := (Complex.continuous_ofReal.tendsto _).comp hr
        simpa using tendsto_const_nhds.add (hc.mul_const I)
      · filter_upwards with n
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro h
        have him := congrArg Complex.im h
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add] at him
        have hpos : (0 : ℝ) < 1/(n+1) := by positivity
        linarith
    have hfreq : ∃ᶠ z in 𝓝[≠] ((σ₀ : ℂ) + I),
        completedRiemannZeta z = completedRiemannZeta (z + (p : ℂ)) :=
      hu_tend.frequently (Frequently.of_forall fun n => hA (1 + 1/(n+1)))
    have hEq : Set.EqOn completedRiemannZeta (fun z => completedRiemannZeta (z + (p : ℂ)))
        (Bᶜ : Set ℂ) :=
      hf_an.eqOn_of_preconnected_of_frequently_eq hg_an hUconn hz₀ hfreq
    intro z hz
    exact hEq (hcompl z hz)
  -- STEP C: a nonzero real period would replicate the pole at `1` at a regular point.
  -- Normalize the period so the transfer target `1 + q` avoids both poles.
  obtain ⟨q, hq0, hq1, hq⟩ : ∃ q : ℝ, ((1 : ℂ) + (q : ℂ) ≠ 0) ∧ ((1 : ℂ) + (q : ℂ) ≠ 1) ∧
      ∀ z : ℂ, z.im ≠ 0 → completedRiemannZeta z = completedRiemannZeta (z + (q : ℂ)) := by
    by_cases hp1 : p = -1
    · -- reverse the period: `q = 1`, reading the identity at `z + 1`
      refine ⟨1, by norm_num, by norm_num, fun z hz => ?_⟩
      have h1 : (z + 1).im ≠ 0 := by simpa using hz
      have h := hper (z + 1) h1
      rw [hp1] at h
      push_cast at h
      rw [show z + 1 + (-1 : ℂ) = z from by ring] at h
      rw [Complex.ofReal_one]
      exact h.symm
    · refine ⟨p, fun h => hp1 ?_, fun h => hp_ne ?_, fun z hz => hper z hz⟩
      · have hcast : ((p : ℝ) : ℂ) = ((-1 : ℝ) : ℂ) := by push_cast; linear_combination h
        exact_mod_cast hcast
      · have hcast : ((p : ℝ) : ℂ) = ((0 : ℝ) : ℂ) := by push_cast; linear_combination h
        exact_mod_cast hcast
  -- approach the pole at `1` along the non-real points `1 + i/(n+1)`
  have hu_im : ∀ n : ℕ, ((1 : ℂ) + ((1/(n+1) : ℝ) : ℂ) * I).im ≠ 0 := by
    intro n
    simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
    positivity
  have hu_tend : Tendsto (fun n : ℕ => (1 : ℂ) + ((1/(n+1) : ℝ) : ℂ) * I)
      atTop (𝓝[≠] (1 : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hc : Tendsto (fun n : ℕ => ((1/(n+1) : ℝ) : ℂ)) atTop (𝓝 ((0 : ℝ) : ℂ)) :=
        (Complex.continuous_ofReal.tendsto _).comp
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      simpa using tendsto_const_nhds.add (hc.mul_const I)
    · filter_upwards with n
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      exact hu_im n (by rw [h]; simp)
  -- the residue forces `(sₙ−1)·Λ(sₙ) → 1`, while the period rewrites `Λ(sₙ)` to `Λ(sₙ+q)`
  have hres' : Tendsto (fun n : ℕ => ((1 : ℂ) + ((1/(n+1) : ℝ) : ℂ) * I - 1)
      * completedRiemannZeta ((1 : ℂ) + ((1/(n+1) : ℝ) : ℂ) * I + (q : ℂ)))
      atTop (𝓝 1) := by
    refine (completedRiemannZeta_residue_one.comp hu_tend).congr fun n => ?_
    simp only [Function.comp_apply]
    rw [hq _ (hu_im n)]
  have hzero : Tendsto (fun n : ℕ => ((1 : ℂ) + ((1/(n+1) : ℝ) : ℂ) * I - 1)
      * completedRiemannZeta ((1 : ℂ) + ((1/(n+1) : ℝ) : ℂ) * I + (q : ℂ)))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (1 : ℂ) + ((1/(n+1) : ℝ) : ℂ) * I - 1)
        atTop (𝓝 0) := by
      simpa using (hu_tend.mono_right nhdsWithin_le_nhds).sub_const 1
    have h2 : Tendsto
        (fun n : ℕ => completedRiemannZeta ((1 : ℂ) + ((1/(n+1) : ℝ) : ℂ) * I + (q : ℂ)))
        atTop (𝓝 (completedRiemannZeta ((1 : ℂ) + (q : ℂ)))) := by
      have hcont : ContinuousAt completedRiemannZeta ((1 : ℂ) + (q : ℂ)) :=
        (differentiableAt_completedZeta hq0 hq1).continuousAt
      exact hcont.tendsto.comp ((hu_tend.mono_right nhdsWithin_le_nhds).add_const _)
    simpa using h1.mul h2
  exact one_ne_zero (tendsto_nhds_unique hres' hzero)

end HelixMobiusClosure

#print axioms HelixMobiusClosure.standing_line_unique

/-! ## ζ is nonvanishing on the real segment (0,1)

The classical fact that the Riemann zeta function has no zeros on the real interval `(0,1)`,
by the Λ-negativity argument:

1. `ζ(σ) = Λ(σ) / Γℝ(σ)` with `Γℝ(σ) ≠ 0` for `σ > 0` (`riemannZeta_def_of_ne_zero`,
   `Complex.Gammaℝ_ne_zero_of_re_pos`), so it suffices that `Λ(σ) ≠ 0`.
2. `Λ(σ) = Λ₀(σ) − 1/σ − 1/(1−σ)` (`completedRiemannZeta_eq`), and on `(0,1)` the pole terms
   give `1/σ + 1/(1−σ) ≥ 4` (AM–HM, equality exactly at `σ = ½`).
3. The entire part is small: `‖Λ₀(σ)‖ ≤ 2`. Unfolding `Λ₀` to the Mellin transform of the
   FE-modified theta kernel (`WeakFEPair.Λ₀`, `WeakFEPair.f_modif` of `hurwitzEvenFEPair 0`),
   the integrand is dominated by `4·exp(−πt)` on `(1,∞)` — geometric bound on the theta tail
   `evenKernel 0 t − 1 = 2∑_{n≥0} exp(−π(n+1)²t)` — and by the constant `4·exp(−π)` on `(0,1)`
   — theta functional equation `evenKernel_functional_equation` plus `u²·exp(−πu) ≤ exp(−π)`
   for `u = 1/t ≥ 1`. Both integrals are `≤ 2`.

Hence `Re Λ(σ) ≤ ‖Λ₀(σ)‖ − 4 ≤ −2 < 0`, so `Λ(σ) ≠ 0` and `ζ(σ) ≠ 0`. -/

namespace ZetaRealSegment

open MeasureTheory HurwitzZeta Set

/-! ### The theta tail: explicit sum, non-negativity, geometric bound -/

/-- The theta tail `evenKernel 0 t − 1` as the explicit sum `2∑_{n≥0} exp(−π(n+1)²t)`. -/
private lemma hasSum_evenKernel_sub_one {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ ↦ 2 * Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * t))
      (evenKernel 0 t - 1) := by
  have h := hasSum_nat_cosKernel₀ 0 ht
  simp only [mul_zero, zero_mul, Real.cos_zero, mul_one, QuotientAddGroup.mk_zero] at h
  rwa [evenKernel_eq_cosKernel_of_zero]

/-- The theta tail is non-negative for `t > 0`. -/
private lemma evenKernel_sub_one_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ evenKernel 0 t - 1 :=
  hasSum_le (fun n ↦ by positivity) hasSum_zero (hasSum_evenKernel_sub_one ht)

/-- `exp(−1) ≤ 1/2` (i.e. `2 ≤ e`). -/
private lemma exp_neg_one_le_half : Real.exp (-1 : ℝ) ≤ 1 / 2 := by
  have h2e : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  have hprod : Real.exp (-1 : ℝ) * Real.exp 1 = 1 := by
    rw [← Real.exp_add]; norm_num
  nlinarith [Real.exp_pos (-1 : ℝ)]

/-- Geometric bound for the theta tail: for `t ≥ 1`, `evenKernel 0 t − 1 ≤ 4·exp(−πt)`. -/
private lemma evenKernel_sub_one_le {t : ℝ} (ht : 1 ≤ t) :
    evenKernel 0 t - 1 ≤ 4 * Real.exp (-Real.pi * t) := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hr0 : 0 < Real.exp (-Real.pi * t) := Real.exp_pos _
  have hr_half : Real.exp (-Real.pi * t) ≤ 1 / 2 := by
    have h1 : Real.exp (-Real.pi * t) ≤ Real.exp (-1) := by
      rw [Real.exp_le_exp]
      nlinarith [Real.pi_gt_three]
    linarith [exp_neg_one_le_half]
  -- the geometric majorant ∑ 2·r·rⁿ = 2r/(1−r), r = exp(−πt)
  have hgeom : HasSum
      (fun n : ℕ ↦ 2 * Real.exp (-Real.pi * t) * Real.exp (-Real.pi * t) ^ n)
      (2 * Real.exp (-Real.pi * t) * (1 - Real.exp (-Real.pi * t))⁻¹) :=
    (hasSum_geometric_of_lt_one hr0.le (by linarith)).mul_left _
  have hle : evenKernel 0 t - 1
      ≤ 2 * Real.exp (-Real.pi * t) * (1 - Real.exp (-Real.pi * t))⁻¹ := by
    refine hasSum_le (fun n ↦ ?_) (hasSum_evenKernel_sub_one ht0) hgeom
    have hπt : 0 < Real.pi * t := mul_pos Real.pi_pos ht0
    have hexp : Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * t)
        ≤ Real.exp (-Real.pi * t) * Real.exp (-Real.pi * t) ^ n := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, Real.exp_le_exp]
      nlinarith [mul_nonneg hπt.le (sq_nonneg ((n : ℝ))),
        mul_nonneg hπt.le (Nat.cast_nonneg (α := ℝ) n)]
    nlinarith [hexp]
  have hinv : (1 - Real.exp (-Real.pi * t))⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) two_pos]
    have h2 : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
    rw [h2]
    linarith
  calc evenKernel 0 t - 1
      ≤ 2 * Real.exp (-Real.pi * t) * (1 - Real.exp (-Real.pi * t))⁻¹ := hle
    _ ≤ 2 * Real.exp (-Real.pi * t) * 2 := by
        exact mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = 4 * Real.exp (-Real.pi * t) := by ring

/-- For `u ≥ 1`, `u²·exp(−πu) ≤ exp(−π)` (since `u² ≤ e^{2(u−1)} ≤ e^{π(u−1)}`). -/
private lemma sq_mul_exp_le {u : ℝ} (hu : 1 ≤ u) :
    u ^ 2 * Real.exp (-Real.pi * u) ≤ Real.exp (-Real.pi) := by
  have h1 : u ≤ Real.exp (u - 1) := by
    have := Real.add_one_le_exp (u - 1); linarith
  have h2 : u ^ 2 ≤ Real.exp (u - 1) ^ 2 := by
    nlinarith [Real.exp_pos (u - 1)]
  calc u ^ 2 * Real.exp (-Real.pi * u)
      ≤ Real.exp (u - 1) ^ 2 * Real.exp (-Real.pi * u) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = Real.exp ((u - 1) + (u - 1) + -Real.pi * u) := by
        rw [sq, ← Real.exp_add, ← Real.exp_add]
    _ ≤ Real.exp (-Real.pi) := by
        rw [Real.exp_le_exp]
        nlinarith [Real.pi_gt_three]

/-! ### The dominating function for the Mellin integrand -/

/-- Dominating function for the Mellin integrand of the modified theta kernel:
`4·exp(−πt)` on `(1,∞)`, the constant `4·exp(−π)` on `(0,1)`, `0` elsewhere. -/
private noncomputable def mellinBound (t : ℝ) : ℝ :=
  (Ioi (1 : ℝ)).indicator (fun u ↦ 4 * Real.exp (-Real.pi * u)) t +
  (Ioo (0 : ℝ) 1).indicator (fun _ ↦ 4 * Real.exp (-Real.pi)) t

private lemma integrableOn_piece_one :
    IntegrableOn (fun u : ℝ ↦ 4 * Real.exp (-Real.pi * u)) (Ioi (1 : ℝ)) :=
  (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr Real.pi_pos) 1).const_mul 4

private lemma integrableOn_piece_two :
    IntegrableOn (fun _ : ℝ ↦ 4 * Real.exp (-Real.pi)) (Ioo (0 : ℝ) 1) :=
  integrableOn_const (hs := by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)

private lemma integrable_mellinBound : Integrable mellinBound := by
  have h1 : Integrable ((Ioi (1 : ℝ)).indicator fun u ↦ 4 * Real.exp (-Real.pi * u)) :=
    IntegrableOn.integrable_indicator integrableOn_piece_one measurableSet_Ioi
  have h2 : Integrable ((Ioo (0 : ℝ) 1).indicator fun _ : ℝ ↦ 4 * Real.exp (-Real.pi)) :=
    IntegrableOn.integrable_indicator integrableOn_piece_two measurableSet_Ioo
  exact h1.add h2

private lemma integral_mellinBound_le : ∫ t in Ioi (0 : ℝ), mellinBound t ≤ 4 := by
  have h1 : Integrable ((Ioi (1 : ℝ)).indicator fun u ↦ 4 * Real.exp (-Real.pi * u)) :=
    IntegrableOn.integrable_indicator integrableOn_piece_one measurableSet_Ioi
  have h2 : Integrable ((Ioo (0 : ℝ) 1).indicator fun _ : ℝ ↦ 4 * Real.exp (-Real.pi)) :=
    IntegrableOn.integrable_indicator integrableOn_piece_two measurableSet_Ioo
  have key : ∫ t in Ioi (0 : ℝ), mellinBound t
      = (∫ t in Ioi (1 : ℝ), 4 * Real.exp (-Real.pi * t))
        + ∫ _ in Ioo (0 : ℝ) 1, (4 * Real.exp (-Real.pi) : ℝ) := by
    simp only [mellinBound]
    rw [integral_add h1.integrableOn h2.integrableOn,
      setIntegral_indicator measurableSet_Ioi, setIntegral_indicator measurableSet_Ioo,
      inter_eq_right.mpr (Ioi_subset_Ioi zero_le_one),
      inter_eq_right.mpr Ioo_subset_Ioi_self]
  rw [key]
  have e1 : (∫ t in Ioi (1 : ℝ), 4 * Real.exp (-Real.pi * t)) ≤ 2 := by
    rw [integral_const_mul, integral_exp_mul_Ioi (neg_lt_zero.mpr Real.pi_pos) 1,
      neg_div_neg_eq, ← mul_div_assoc]
    rw [div_le_iff₀ Real.pi_pos]
    have he : Real.exp (-Real.pi * 1) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [Real.pi_pos]
    nlinarith [Real.pi_gt_three]
  have e2 : (∫ _ in Ioo (0 : ℝ) 1, (4 * Real.exp (-Real.pi) : ℝ)) ≤ 2 := by
    rw [setIntegral_const, Real.volume_real_Ioo_of_le zero_le_one]
    simp only [sub_zero, smul_eq_mul, one_mul]
    have h1' : Real.exp (-Real.pi) ≤ Real.exp (-1) := by
      rw [Real.exp_le_exp]
      linarith [Real.pi_gt_three]
    linarith [exp_neg_one_le_half]
  linarith

/-! ### The pointwise bound on the Mellin integrand -/

/-- The FE-modified theta kernel of `hurwitzEvenFEPair 0`, computed explicitly:
`θ(t) − 1` on `(1,∞)` and `θ(t) − t^{−1/2}` on `(0,1)`. -/
private lemma f_modif_apply (t : ℝ) :
    (hurwitzEvenFEPair (0 : UnitAddCircle)).f_modif t
      = (Ioi (1 : ℝ)).indicator (fun x : ℝ ↦ ((evenKernel 0 x : ℝ) : ℂ) - 1) t
        + (Ioo (0 : ℝ) 1).indicator
            (fun x : ℝ ↦ ((evenKernel 0 x : ℝ) : ℂ) - ((x ^ (-(1 / 2) : ℝ) : ℝ) : ℂ)) t := by
  have hf : (hurwitzEvenFEPair (0 : UnitAddCircle)).f
      = fun x : ℝ ↦ ((evenKernel 0 x : ℝ) : ℂ) := rfl
  have hf₀ : (hurwitzEvenFEPair (0 : UnitAddCircle)).f₀ = 1 := by
    simp [hurwitzEvenFEPair]
  have hε : (hurwitzEvenFEPair (0 : UnitAddCircle)).ε = 1 := rfl
  have hk : (hurwitzEvenFEPair (0 : UnitAddCircle)).k = 1 / 2 := rfl
  have hg₀ : (hurwitzEvenFEPair (0 : UnitAddCircle)).g₀ = 1 := rfl
  simp only [WeakFEPair.f_modif, Pi.add_apply, hf, hf₀, hε, hk, hg₀, smul_eq_mul, one_mul,
    mul_one]

/-- Pointwise domination of the Mellin integrand by `mellinBound`, for `σ ∈ (0,1)`. -/
private lemma norm_integrand_le {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) (t : ℝ) :
    ‖(t : ℂ) ^ ((σ : ℂ) / 2 - 1) • (hurwitzEvenFEPair (0 : UnitAddCircle)).f_modif t‖
      ≤ mellinBound t := by
  have hexp_eq : (σ : ℂ) / 2 - 1 = ((σ / 2 - 1 : ℝ) : ℂ) := by push_cast; ring
  rw [f_modif_apply, hexp_eq]
  simp only [mellinBound]
  rcases lt_trichotomy t 1 with htlt | rfl | htgt
  · rcases le_or_gt t 0 with ht0 | ht0
    · -- `t ≤ 0`: everything vanishes
      have hm1 : t ∉ Ioi (1 : ℝ) := by simp only [mem_Ioi, not_lt]; linarith
      have hm2 : t ∉ Ioo (0 : ℝ) 1 := fun h ↦ absurd h.1 (not_lt.mpr ht0)
      simp only [indicator_of_notMem hm1, indicator_of_notMem hm2, add_zero, smul_zero,
        norm_zero, le_refl]
    · -- `0 < t < 1`: kernel functional equation + `u²e^{−πu} ≤ e^{−π}` at `u = 1/t`
      have hm1 : t ∉ Ioi (1 : ℝ) := by simp only [mem_Ioi, not_lt]; linarith
      have hm2 : t ∈ Ioo (0 : ℝ) 1 := ⟨ht0, htlt⟩
      simp only [indicator_of_notMem hm1, indicator_of_mem hm2, zero_add]
      rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.ofReal_re,
        ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      have hu0 : 0 < 1 / t := by positivity
      have hu1 : 1 ≤ 1 / t := (one_le_div ht0).mpr htlt.le
      -- the kernel FE turns the `(0,1)` data into `(1,∞)` data
      have hFE : evenKernel 0 t - t ^ (-(1 / 2) : ℝ)
          = t ^ (-(1 / 2) : ℝ) * (evenKernel 0 (1 / t) - 1) := by
        have h := evenKernel_functional_equation (0 : UnitAddCircle) t
        rw [← evenKernel_eq_cosKernel_of_zero] at h
        have h2 : (1 : ℝ) / t ^ (1 / 2 : ℝ) = t ^ (-(1 / 2) : ℝ) := by
          rw [Real.rpow_neg ht0.le, one_div]
        rw [h2] at h
        rw [h]; ring
      rw [hFE, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _),
        abs_of_nonneg (evenKernel_sub_one_nonneg hu0)]
      have hψ0 : 0 ≤ evenKernel 0 (1 / t) - 1 := evenKernel_sub_one_nonneg hu0
      have hpow : t ^ (-2 : ℝ) = (1 / t) ^ 2 := by
        rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg ht0.le,
          Real.rpow_natCast, one_div, inv_pow]
      calc t ^ (σ / 2 - 1) * (t ^ (-(1 / 2) : ℝ) * (evenKernel 0 (1 / t) - 1))
          = t ^ ((σ / 2 - 1) + (-(1 / 2))) * (evenKernel 0 (1 / t) - 1) := by
            rw [Real.rpow_add ht0, mul_assoc]
        _ ≤ t ^ (-2 : ℝ) * (4 * Real.exp (-Real.pi * (1 / t))) := by
            apply mul_le_mul
            · exact Real.rpow_le_rpow_of_exponent_ge ht0 htlt.le (by linarith)
            · exact evenKernel_sub_one_le hu1
            · exact hψ0
            · positivity
        _ = 4 * ((1 / t) ^ 2 * Real.exp (-Real.pi * (1 / t))) := by
            rw [hpow]; ring
        _ ≤ 4 * Real.exp (-Real.pi) :=
            mul_le_mul_of_nonneg_left (sq_mul_exp_le hu1) (by norm_num)
  · -- `t = 1`: both sides vanish
    have hm1 : (1 : ℝ) ∉ Ioi (1 : ℝ) := by simp [mem_Ioi]
    have hm2 : (1 : ℝ) ∉ Ioo (0 : ℝ) 1 := by simp [mem_Ioo]
    simp only [indicator_of_notMem hm1, indicator_of_notMem hm2, add_zero, smul_zero,
      norm_zero, le_refl]
  · -- `1 < t`: theta-tail geometric bound, `t^{σ/2−1} ≤ 1`
    have hm1 : t ∈ Ioi (1 : ℝ) := htgt
    have hm2 : t ∉ Ioo (0 : ℝ) 1 := fun h ↦ absurd h.2 (not_lt.mpr htgt.le)
    simp only [indicator_of_mem hm1, indicator_of_notMem hm2, add_zero]
    have ht0 : 0 < t := zero_lt_one.trans htgt
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.ofReal_re,
      show ((evenKernel 0 t : ℝ) : ℂ) - 1 = ((evenKernel 0 t - 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (evenKernel_sub_one_nonneg ht0)]
    calc t ^ (σ / 2 - 1) * (evenKernel 0 t - 1)
        ≤ 1 * (4 * Real.exp (-Real.pi * t)) := by
          apply mul_le_mul
          · exact Real.rpow_le_one_of_one_le_of_nonpos htgt.le (by linarith)
          · exact evenKernel_sub_one_le htgt.le
          · exact evenKernel_sub_one_nonneg ht0
          · norm_num
      _ = 4 * Real.exp (-Real.pi * t) := one_mul _

/-! ### The Λ₀ bound and the conclusion -/

/-- The entire part of the completed zeta is uniformly small on the real segment:
`‖Λ₀(σ)‖ ≤ 2` for `σ ∈ (0,1)`. -/
private lemma norm_completedRiemannZeta₀_le {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    ‖completedRiemannZeta₀ (σ : ℂ)‖ ≤ 2 := by
  have heq : completedRiemannZeta₀ (σ : ℂ)
      = (∫ t in Ioi (0 : ℝ),
          (t : ℂ) ^ ((σ : ℂ) / 2 - 1) • (hurwitzEvenFEPair (0 : UnitAddCircle)).f_modif t) / 2 :=
    rfl
  rw [heq, norm_div, Complex.norm_ofNat]
  have hbound : ‖∫ t in Ioi (0 : ℝ),
      (t : ℂ) ^ ((σ : ℂ) / 2 - 1) • (hurwitzEvenFEPair (0 : UnitAddCircle)).f_modif t‖ ≤ 4 :=
    (norm_integral_le_of_norm_le integrable_mellinBound.integrableOn
      (Filter.Eventually.of_forall fun t ↦ norm_integrand_le h0 h1 t)).trans
      integral_mellinBound_le
  linarith

/-- The completed zeta is nonzero on the real segment `(0,1)`: its real part is `≤ −2`. -/
private lemma completedRiemannZeta_ne_zero_of_mem_Ioo {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    completedRiemannZeta (σ : ℂ) ≠ 0 := by
  have h1σ : 0 < 1 - σ := by linarith
  -- AM–HM: the pole terms contribute at least 4
  have hpole : 4 ≤ 1 / σ + 1 / (1 - σ) := by
    rw [div_add_div _ _ (ne_of_gt h0) (ne_of_gt h1σ), le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (1 - 2 * σ)]
  have hΛ₀re : (completedRiemannZeta₀ (σ : ℂ)).re ≤ 2 :=
    (Complex.re_le_norm _).trans (norm_completedRiemannZeta₀_le h0 h1)
  have hre : (completedRiemannZeta (σ : ℂ)).re
      = (completedRiemannZeta₀ (σ : ℂ)).re - (1 / σ + 1 / (1 - σ)) := by
    rw [completedRiemannZeta_eq]
    rw [show (1 : ℂ) / (σ : ℂ) = ((1 / σ : ℝ) : ℂ) by push_cast; ring,
      show (1 : ℂ) - (σ : ℂ) = ((1 - σ : ℝ) : ℂ) by push_cast; ring,
      show (1 : ℂ) / ((1 - σ : ℝ) : ℂ) = ((1 / (1 - σ) : ℝ) : ℂ) by push_cast; ring]
    simp only [Complex.sub_re, Complex.ofReal_re]
    ring
  intro hzero
  rw [hzero] at hre
  simp only [Complex.zero_re] at hre
  linarith

end ZetaRealSegment

/-- **The Riemann zeta function has no zeros on the real segment `(0,1)`.** Classical and
unconditional: for real `σ ∈ (0,1)` the completed zeta satisfies
`Re Λ(σ) ≤ ‖Λ₀(σ)‖ − (1/σ + 1/(1−σ)) ≤ 2 − 4 < 0`, and `Γℝ(σ) ≠ 0`, so
`ζ(σ) = Λ(σ)/Γℝ(σ) ≠ 0`. -/
theorem riemannZeta_ne_zero_of_mem_Ioo {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    riemannZeta (σ : ℂ) ≠ 0 := by
  rw [riemannZeta_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt h0))]
  exact div_ne_zero (ZetaRealSegment.completedRiemannZeta_ne_zero_of_mem_Ioo h0 h1)
    (Complex.Gammaℝ_ne_zero_of_re_pos (by simpa using h0))

#print axioms riemannZeta_ne_zero_of_mem_Ioo
