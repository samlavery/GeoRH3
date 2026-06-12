import RequestProject.DirichletLHadamardComplete
import RequestProject.HelixThreeFourOne
import RequestProject.DirichletClosureLedger
import RequestProject.DirichletLZeroSet
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# The zero-bound: a zero pushes `Re(L'/L)` up, diagonally by `1/(σ−β)`

The second classical ingredient of a zero-free region (the first being `primeWindingEnergy_nonneg`, the
3-4-1 positivity). From the Hadamard partial fraction `logDeriv Λ_χ(s) = A + ∑_ρ ord(ρ)[1/(s−ρ)+1/ρ]`,
each resolvent term has **strictly positive real part** for `Re s > 1` (the convergent region), and at
`s = σ + i·Im ρ₀` the diagonal term is exactly `1/(σ − Re ρ₀)` — diverging as `σ → Re ρ₀⁺`. So a zero
near `Re = 1` forces `Re(logDeriv Λ)` large and positive there; fed into the 3-4-1 inequality
`3·(pole) − 4·(zero) + (…) ≥ 0`, a zero too close to `Re = 1` contradicts the positivity. These bricks
are kernel-clean and non-circular — pure resolvent geometry, no `σ−½` coordinate.
-/

open Complex

namespace HelixZeroFree

variable {N : ℕ} [NeZero N]

/-- **Resolvent positivity in the convergent region.** For `Re s > 1` and a point `ρ` with `Re ρ < 1`,
`Re(1/(s−ρ)) = (Re s − Re ρ)/‖s−ρ‖² > 0`. Every zero contributes a *positive* real part to
`Re(logDeriv Λ)` in the convergent region — the source of the zero-bound. -/
theorem resolvent_re_pos {s ρ : ℂ} (hs : 1 < s.re) (hρ : ρ.re < 1) :
    0 < (1 / (s - ρ)).re := by
  have hne : s - ρ ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [h] at hs; linarith
  rw [one_div, Complex.inv_re, Complex.sub_re]
  exact div_pos (by linarith) (Complex.normSq_pos.mpr hne)

/-- **The diagonal resolvent term.** At `s = σ + i·Im ρ` (matching the zero's height), the resolvent is
real and equals `1/(σ − Re ρ)` — the large positive term a zero contributes, diverging as
`σ → Re ρ⁺`. -/
theorem resolvent_re_diagonal {ρ : ℂ} {σ : ℝ} (_hσ : ρ.re < σ) :
    (1 / ((σ : ℂ) + Complex.I * (ρ.im : ℝ) - ρ)).re = 1 / (σ - ρ.re) := by
  have h1 : (σ : ℂ) + Complex.I * (ρ.im : ℝ) - ρ = ((σ - ρ.re : ℝ) : ℂ) := by
    apply Complex.ext <;>
      simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
        Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im]
  rw [h1, one_div, ← Complex.ofReal_inv, Complex.ofReal_re, one_div]

/-- **A nontrivial zero has `Re ρ < 1`** — the precondition for `resolvent_re_pos`. -/
theorem nontrivialZero_re_lt_one {χ : DirichletCharacter ℂ N} {ρ : ℂ}
    (hρ : ρ ∈ GRHSpectral.NontrivialZeros χ) : ρ.re < 1 := hρ.2.1

/-- **The zero-bound, assembled per term.** For a nontrivial zero `ρ₀` and `σ > 1`, evaluating the
resolvent of the Hadamard sum at `s = σ + i·Im ρ₀`: the `ρ₀`-term is exactly `1/(σ − Re ρ₀) > 0`, and
every other `ρ`-term has positive real part. So the zero `ρ₀` injects a controlled, *positive,
divergent-as-σ→Re ρ₀* contribution into `Re(logDeriv Λ_χ)` — the precise mechanism the 3-4-1 inequality
turns into "no zeros near `Re = 1`." -/
theorem zero_diagonal_pos {χ : DirichletCharacter ℂ N} {ρ₀ : ℂ}
    (hρ₀ : ρ₀ ∈ GRHSpectral.NontrivialZeros χ) {σ : ℝ} (hσ : 1 < σ) :
    (1 / ((σ : ℂ) + Complex.I * (ρ₀.im : ℝ) - ρ₀)).re = 1 / (σ - ρ₀.re)
      ∧ 0 < 1 / (σ - ρ₀.re) := by
  have hlt : ρ₀.re < σ := lt_trans (nontrivialZero_re_lt_one hρ₀) hσ
  exact ⟨resolvent_re_diagonal hlt, by
    apply div_pos one_pos; linarith [nontrivialZero_re_lt_one hρ₀]⟩

/-- **The 3-4-1 optimization — the arithmetical heart of the zero-free region.** Once the three
analytic bounds (pole `3·A ≤ 3/δ`, zero `−4·B ≥ 4/(ε+δ)`, remainder `≤ C`) are fed into the 3-4-1
inequality `0 ≤ 3A + 4B + D`, what remains is purely arithmetic: evaluated at the optimal scale
`δ = 1/(2C)`, the inequality `0 ≤ 3/δ − 4/(ε+δ) + C` forces `ε ≥ 1/(14C)`. With `ε = (1−β)·𝓛` and
`C ≍ 𝓛`, this is exactly the zero-free region `1 − β ≥ c/𝓛`. Kernel-clean, non-circular. -/
theorem zerofree_optimization {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε)
    (h : 0 ≤ 3 / (1 / (2 * C)) - 4 / (ε + 1 / (2 * C)) + C) :
    1 / (14 * C) ≤ ε := by
  have hC0 : C ≠ 0 := hC.ne'
  have hden : 0 < ε + 1 / (2 * C) := by positivity
  have e1 : 3 / (1 / (2 * C)) = 6 * C := by field_simp; norm_num
  rw [e1] at h
  have h2 : 4 / (ε + 1 / (2 * C)) ≤ 7 * C := by linarith
  rw [div_le_iff₀ hden, mul_add] at h2
  have e2 : 7 * C * (1 / (2 * C)) = 7 / 2 := by field_simp
  rw [e2] at h2
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 14 * C)]
  nlinarith [h2]

/-! ## The analytic 3-4-1 is in Mathlib; here is its zero-repulsion form

The full de la Vallée Poussin product inequality
`‖L(χ⁰,1+x)³ · L(χ,1+x+iy)⁴ · L(χ²,1+x+2iy)‖ ≥ 1` is **already in Mathlib**
(`DirichletCharacter.norm_LFunction_product_ge_one`), as is the simple-pole bound
(`DirichletCharacter.LFunctionTrivChar_isBigO_near_one_horizontal`) and the edge consequence
(`DirichletCharacter.LFunction_ne_zero_of_one_le_re`). Do not rebuild them. What Mathlib does NOT
have is the interior region `1 − β ≥ c/log(N(|t|+2))`. The composite below welds Mathlib's two
bounds into the **quantitative repulsion shape** the region proof consumes: approaching the edge at
any height `y`, the `L(χ)⁴·L(χ²)` factors must carry mass `≥ (x/C)³` — so a zero of `L(χ)` at
height `y` (which kills the fourth-power factor linearly in the distance) cannot sit too close to
`Re = 1` once the growth/derivative bounds quantify "linearly". The remaining ingredients for the
region are exactly: an upper bound for `‖L‖` near the edge (the repo's order-1 growth side) and the
mean-value step `‖L(1+x+iy)‖ = ‖L(1+x+iy) − L(β+iy)‖ ≤ M·(1+x−β)`; fed back into this repulsion
and `zerofree_optimization`, they give the region. -/

/-- **Zero repulsion near the edge — uniform in height**: there are `C > 0` and a window
    `x₀ > 0`, BOTH independent of the height `y`, with
    `(x/C)³ ≤ ‖L(χ, 1+x+iy)‖⁴ · ‖L(χ², 1+x+2iy)‖` for all `0 < x < x₀` and ALL `y`. The pole's
    cube is the only thing fighting the product inequality's `≥ 1`, it is bounded by `(C/x)³`,
    and it lives on the real axis — its constants never see `y`. -/
theorem zero_repulsion_near_one (χ : DirichletCharacter ℂ N) :
    ∃ C > (0 : ℝ), ∃ x₀ > (0 : ℝ), ∀ y : ℝ, ∀ x : ℝ, 0 < x → x < x₀ →
      (x / C) ^ 3 ≤ ‖DirichletCharacter.LFunction χ (1 + (x : ℂ) + Complex.I * (y : ℂ))‖ ^ 4
        * ‖DirichletCharacter.LFunction (χ ^ 2) (1 + (x : ℂ) + 2 * Complex.I * (y : ℂ))‖ := by
  obtain ⟨c, hc, hO⟩ :=
    (DirichletCharacter.LFunctionTrivChar_isBigO_near_one_horizontal (N := N)).exists_pos
  rw [Asymptotics.isBigOWith_iff] at hO
  obtain ⟨x₀, hx₀, hwin⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp hO
  refine ⟨c, hc, x₀, hx₀, fun y x hx0 hxx₀ => ?_⟩
  have hx := hwin ⟨hx0, hxx₀⟩
  have hnorm1x : ‖(1 : ℂ) / (x : ℂ)‖ = 1 / x := by
    rw [norm_div, norm_one]
    simp [abs_of_pos hx0]
  rw [hnorm1x] at hx
  have hA : ‖DirichletCharacter.LFunctionTrivChar N (1 + x)‖ ≤ c / x := by
    calc ‖DirichletCharacter.LFunctionTrivChar N (1 + x)‖ ≤ c * (1 / x) := hx
      _ = c / x := by ring
  have hprod := DirichletCharacter.norm_LFunction_product_ge_one (χ := χ) hx0 y
  rw [norm_mul, norm_mul, norm_pow, norm_pow] at hprod
  set b := ‖DirichletCharacter.LFunction χ (1 + x + Complex.I * y)‖ with hb
  set d := ‖DirichletCharacter.LFunction (χ ^ 2) (1 + x + 2 * Complex.I * y)‖ with hd
  have hP : (0 : ℝ) ≤ b ^ 4 * d := by positivity
  have ha3 : ‖DirichletCharacter.LFunctionTrivChar N (1 + x)‖ ^ 3 ≤ (c / x) ^ 3 :=
    pow_le_pow_left₀ (norm_nonneg _) hA 3
  have hstep : (1 : ℝ) ≤ (c / x) ^ 3 * (b ^ 4 * d) := by
    calc (1 : ℝ) ≤ ‖DirichletCharacter.LFunctionTrivChar N (1 + x)‖ ^ 3 * b ^ 4 * d := hprod
      _ = ‖DirichletCharacter.LFunctionTrivChar N (1 + x)‖ ^ 3 * (b ^ 4 * d) := by ring
      _ ≤ (c / x) ^ 3 * (b ^ 4 * d) := mul_le_mul_of_nonneg_right ha3 hP
  have hxc : (x / c) ^ 3 * ((c / x) ^ 3 * (b ^ 4 * d)) = b ^ 4 * d := by
    field_simp
  calc (x / c) ^ 3 = (x / c) ^ 3 * 1 := by ring
    _ ≤ (x / c) ^ 3 * ((c / x) ^ 3 * (b ^ 4 * d)) :=
        mul_le_mul_of_nonneg_left hstep (by positivity)
    _ = b ^ 4 * d := hxc

/-- **Cauchy derivative bound for `L` on the right half-plane**: for `χ ≠ 1`, on any disk
    `ball c r` staying right of the imaginary axis (`r < Re c`),
    `‖L'(c)‖ ≤ N·(‖c‖+r)/(r·(Re c − r))` — the ledger growth bound `‖L‖ ≤ N‖s‖/Re s` pushed
    through Cauchy's estimate. Explicit, uniform in height: the `M` the mean-value step feeds on. -/
theorem norm_deriv_LFunction_le (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {c : ℂ} {r : ℝ} (hr : 0 < r) (hrc : r < c.re) :
    ‖deriv (DirichletCharacter.LFunction χ) c‖
      ≤ (N : ℝ) * (‖c‖ + r) / (r * (c.re - r)) := by
  have hL : Differentiable ℂ (DirichletCharacter.LFunction χ) :=
    fun z => DirichletClosureLedger.LFunction_differentiableAt χ hχ z
  have hd : DiffContOnCl ℂ (DirichletCharacter.LFunction χ) (Metric.ball c r) :=
    hL.diffContOnCl
  have hC : ∀ z ∈ Metric.sphere c r, ‖DirichletCharacter.LFunction χ z‖
      ≤ (N : ℝ) * (‖c‖ + r) / (c.re - r) := by
    intro z hz
    rw [Metric.mem_sphere, dist_eq_norm] at hz
    have habs : |(z - c).re| ≤ ‖z - c‖ := Complex.abs_re_le_norm _
    rw [hz] at habs
    have hre : (z - c).re = z.re - c.re := by simp [Complex.sub_re]
    have hzre : c.re - r ≤ z.re := by
      have := (abs_le.mp habs).1
      rw [hre] at this
      linarith
    have hzre0 : 0 < z.re := by linarith
    have hznorm : ‖z‖ ≤ ‖c‖ + r := by
      calc ‖z‖ = ‖c + (z - c)‖ := by ring_nf
        _ ≤ ‖c‖ + ‖z - c‖ := norm_add_le _ _
        _ = ‖c‖ + r := by rw [hz]
    have hmain := DirichletClosureLedger.norm_LFunction_le_half_plane χ hχ z hzre0
    have hden : (0 : ℝ) < c.re - r := by linarith
    calc ‖DirichletCharacter.LFunction χ z‖ ≤ (N : ℝ) * ‖z‖ / z.re := hmain
      _ ≤ (N : ℝ) * (‖c‖ + r) / (c.re - r) := by
          gcongr
  have hcau := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hd hC
  calc ‖deriv (DirichletCharacter.LFunction χ) c‖
      ≤ ((N : ℝ) * (‖c‖ + r) / (c.re - r)) / r := hcau
    _ = (N : ℝ) * (‖c‖ + r) / (r * (c.re - r)) := by
        rw [div_div]
        ring_nf

/-- **The mean-value zero-penalty**: if `L(χ, ρ) = 0`, then at the same height the value a
    distance `σ₁ − Re ρ` to the right is bounded LINEARLY in that distance:
    `‖L(σ₁ + i·Im ρ)‖ ≤ M·(σ₁ − Re ρ)`, with `M` any derivative bound on the connecting segment.
    This is the step that kills the fourth-power factor in `zero_repulsion_near_one`: a zero too
    close to `Re = 1` starves the product inequality. -/
theorem norm_LFunction_le_of_zero (χ : DirichletCharacter ℂ N)
    {ρ : ℂ} (hρ0 : DirichletCharacter.LFunction χ ρ = 0) {σ₁ : ℝ} (hσ₁ : ρ.re ≤ σ₁)
    (hdiff : ∀ z ∈ segment ℝ ρ ((σ₁ : ℂ) + (ρ.im : ℝ) * Complex.I),
      DifferentiableAt ℂ (DirichletCharacter.LFunction χ) z)
    {M : ℝ} (hM : ∀ z ∈ segment ℝ ρ ((σ₁ : ℂ) + (ρ.im : ℝ) * Complex.I),
      ‖deriv (DirichletCharacter.LFunction χ) z‖ ≤ M) :
    ‖DirichletCharacter.LFunction χ ((σ₁ : ℂ) + (ρ.im : ℝ) * Complex.I)‖
      ≤ M * (σ₁ - ρ.re) := by
  have hbound : ∀ z ∈ segment ℝ ρ ((σ₁ : ℂ) + (ρ.im : ℝ) * Complex.I),
      ‖fderiv ℂ (DirichletCharacter.LFunction χ) z‖ ≤ M := by
    intro z hz
    rw [← norm_deriv_eq_norm_fderiv]
    exact hM z hz
  have key := (convex_segment ρ ((σ₁ : ℂ) + (ρ.im : ℝ) * Complex.I)).norm_image_sub_le_of_norm_fderiv_le
    hdiff hbound (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
  rw [hρ0, sub_zero] at key
  have hdiff_eq : ((σ₁ : ℂ) + (ρ.im : ℝ) * Complex.I) - ρ = (((σ₁ - ρ.re : ℝ)) : ℂ) := by
    apply Complex.ext <;> simp
  have hdist : ‖((σ₁ : ℂ) + (ρ.im : ℝ) * Complex.I) - ρ‖ = σ₁ - ρ.re := by
    rw [hdiff_eq, Complex.norm_real,
      Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ σ₁ - ρ.re)]
  rw [hdist] at key
  exact key

set_option maxHeartbeats 1000000 in
/-- **The effective zero-free region (polynomial form) — unconditional, explicit, every
    non-quadratic character.** For `χ ≠ 1` with `χ² ≠ 1` there is `c > 0` such that EVERY zero of
    `L(χ)` satisfies `Re ρ ≤ 1 − c/(1+|Im ρ|)⁵`. The assembly: Mathlib's dlVP product inequality
    (via `zero_repulsion_near_one`), the ledger's polynomial growth bound through Cauchy's
    estimate (`norm_deriv_LFunction_le`), and the mean-value zero-penalty
    (`norm_LFunction_le_of_zero`). The classical `c/log` form needs a logarithmic growth bound in
    place of the ledger's polynomial one — a sharper instrument, same machine. Quadratic `χ`
    (where `χ² = 1` puts the `L(χ²)`-factor's pole in play) is the classical exceptional-zero
    case, excluded here honestly. -/
theorem zero_free_region_poly (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχ2 : χ ^ 2 ≠ 1) :
    ∃ c > (0 : ℝ), ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 →
      ρ.re ≤ 1 - c / (1 + |ρ.im|) ^ 5 := by
  obtain ⟨C, hC, x₀, hx₀, hrep⟩ := zero_repulsion_near_one χ
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  set c₀ : ℝ := 1 / (2458624 * C ^ 3 * (N : ℝ) ^ 5) with hc₀def
  have hc₀ : 0 < c₀ := by positivity
  refine ⟨min (min x₀ (1 / 4)) c₀, by positivity, fun ρ hρ0 => ?_⟩
  set y := ρ.im with hydef
  set β := ρ.re with hβdef
  have hy1 : (1 : ℝ) ≤ 1 + |y| := by linarith [abs_nonneg y]
  have hy5 : (1 : ℝ) ≤ (1 + |y|) ^ 5 := one_le_pow₀ hy1
  have hcle : min (min x₀ (1 / 4)) c₀ / (1 + |y|) ^ 5 ≤ min (min x₀ (1 / 4)) c₀ :=
    div_le_self (by positivity) hy5
  have hβ1 : β < 1 := by
    by_contra h
    push_neg at h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) h hρ0
  rcases le_or_gt β (3 / 4 : ℝ) with hβ34 | hβ34
  · have h14 : min (min x₀ (1 / 4)) c₀ ≤ 1 / 4 :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    linarith
  rcases le_or_gt x₀ (1 - β) with hbig | hsmall
  · have h1 : min (min x₀ (1 / 4)) c₀ ≤ x₀ := le_trans (min_le_left _ _) (min_le_left _ _)
    linarith
  -- MAIN CASE: 3/4 < β < 1, x := 1 − β ∈ (0, x₀) ∩ (0, 1/4)
  set x : ℝ := 1 - β with hxdef
  have hx0 : 0 < x := by simp only [hxdef]; linarith
  have hx14 : x ≤ 1 / 4 := by simp only [hxdef]; linarith
  have hrep' := hrep y x hx0 hsmall
  set M : ℝ := 14 * (N : ℝ) * (1 + |y|) with hMdef
  have hM0 : 0 < M := by positivity
  -- (b) the derivative bound on the connecting segment
  have hseg : ∀ z ∈ segment ℝ ρ (((1 + x : ℝ) : ℂ) + (ρ.im : ℝ) * Complex.I),
      ‖deriv (DirichletCharacter.LFunction χ) z‖ ≤ M := by
    intro z hz
    obtain ⟨a, b, ha, hb, hab, hzeq⟩ := hz
    have hptre : ((((1 + x : ℝ)) : ℂ) + (ρ.im : ℝ) * Complex.I).re = 1 + x := by simp
    have hptim : ((((1 + x : ℝ)) : ℂ) + (ρ.im : ℝ) * Complex.I).im = y := by simp [hydef]
    have hzre : z.re = a * β + b * (1 + x) := by
      have := congrArg Complex.re hzeq
      simp only [Complex.add_re, Complex.smul_re, hptre, smul_eq_mul] at this
      rw [← this, hβdef]
    have hzim : z.im = y := by
      have := congrArg Complex.im hzeq
      simp only [Complex.add_im, Complex.smul_im, hptim, smul_eq_mul] at this
      rw [← this, hydef]
      linear_combination ρ.im * hab
    have hre_lo : β ≤ z.re := by
      rw [hzre]
      nlinarith [mul_nonneg hb (show (0 : ℝ) ≤ 1 + x - β by linarith)]
    have hre_hi : z.re ≤ 1 + x := by
      rw [hzre]
      nlinarith [mul_nonneg ha (show (0 : ℝ) ≤ 1 + x - β by linarith)]
    have hznorm : ‖z‖ ≤ 5 / 4 + |y| := by
      have h1 : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      have h2 : |z.re| ≤ 5 / 4 := by
        rw [abs_le]
        constructor <;> linarith
      rw [hzim] at h1
      linarith
    have hderiv := norm_deriv_LFunction_le χ hχ (c := z)
      (r := 1 / 2) (by norm_num) (by linarith : (1 : ℝ) / 2 < z.re)
    calc ‖deriv (DirichletCharacter.LFunction χ) z‖
        ≤ (N : ℝ) * (‖z‖ + 1 / 2) / (1 / 2 * (z.re - 1 / 2)) := hderiv
      _ ≤ M := by
          rw [div_le_iff₀ (by nlinarith : (0 : ℝ) < 1 / 2 * (z.re - 1 / 2))]
          rw [hMdef]
          nlinarith [mul_nonneg hN0.le (abs_nonneg y), abs_nonneg y,
            mul_le_mul_of_nonneg_left hznorm hN0.le,
            mul_le_mul_of_nonneg_left (show (1 : ℝ) / 4 ≤ z.re - 1 / 2 by linarith)
              (by positivity : (0 : ℝ) ≤ 14 * (N : ℝ) * (1 + |y|) * (1 / 2))]
  -- (c) the mean-value zero-penalty
  have hMV := norm_LFunction_le_of_zero χ hρ0 (σ₁ := 1 + x)
    (by rw [← hβdef]; linarith)
    (fun z _ => DirichletClosureLedger.LFunction_differentiableAt χ hχ z) hseg
  have h2x : M * ((1 + x) - ρ.re) = M * (2 * x) := by
    rw [← hβdef, hxdef]; ring_nf
  rw [h2x] at hMV
  -- (d) point alignment with the repulsion
  have hpt : (((1 + x : ℝ)) : ℂ) + (ρ.im : ℝ) * Complex.I
      = 1 + (x : ℂ) + Complex.I * (y : ℂ) := by
    rw [hydef]; push_cast; ring
  rw [hpt] at hMV
  -- (e) the χ²-factor bound from the ledger growth
  set pt2 : ℂ := 1 + (x : ℂ) + 2 * Complex.I * (y : ℂ) with hpt2def
  have hpt2re : pt2.re = 1 + x := by simp [hpt2def]
  have hpt2im : pt2.im = 2 * y := by simp [hpt2def]
  have hKb := DirichletClosureLedger.norm_LFunction_le_half_plane (χ ^ 2) hχ2 pt2
    (by rw [hpt2re]; linarith)
  have hK : ‖DirichletCharacter.LFunction (χ ^ 2) pt2‖ ≤ 4 * (N : ℝ) * (1 + |y|) := by
    have hpt2norm : ‖pt2‖ ≤ 9 / 4 + 2 * |y| := by
      have h1 : ‖pt2‖ ≤ |pt2.re| + |pt2.im| := Complex.norm_le_abs_re_add_abs_im pt2
      rw [hpt2re, hpt2im, abs_mul] at h1
      have h3 : |(1 : ℝ) + x| ≤ 5 / 4 := by
        rw [abs_le]; constructor <;> linarith
      have h4 : |(2 : ℝ)| = 2 := by norm_num
      rw [h4] at h1
      linarith
    calc ‖DirichletCharacter.LFunction (χ ^ 2) pt2‖
        ≤ (N : ℝ) * ‖pt2‖ / pt2.re := hKb
      _ ≤ (N : ℝ) * (9 / 4 + 2 * |y|) / 1 := by
          rw [hpt2re]
          gcongr <;> linarith
      _ = (N : ℝ) * (9 / 4 + 2 * |y|) := div_one _
      _ ≤ 4 * (N : ℝ) * (1 + |y|) := by nlinarith [abs_nonneg y]
  -- (f) combine: (x/C)³ ≤ (M·2x)⁴·(4N(1+|y|)) and cancel x³
  have hb4 : ‖DirichletCharacter.LFunction χ (1 + (x : ℂ) + Complex.I * (y : ℂ))‖ ^ 4
      ≤ (M * (2 * x)) ^ 4 :=
    pow_le_pow_left₀ (norm_nonneg _) hMV 4
  have hcomb : (x / C) ^ 3 ≤ (M * (2 * x)) ^ 4 * (4 * (N : ℝ) * (1 + |y|)) := by
    calc (x / C) ^ 3
        ≤ ‖DirichletCharacter.LFunction χ (1 + (x : ℂ) + Complex.I * (y : ℂ))‖ ^ 4
          * ‖DirichletCharacter.LFunction (χ ^ 2) pt2‖ := hrep'
      _ ≤ (M * (2 * x)) ^ 4 * (4 * (N : ℝ) * (1 + |y|)) :=
          mul_le_mul hb4 hK (norm_nonneg _) (by positivity)
  have hexp : (M * (2 * x)) ^ 4 * (4 * (N : ℝ) * (1 + |y|))
      = (2458624 * (N : ℝ) ^ 5 * (1 + |y|) ^ 5 * x) * x ^ 3 := by
    rw [hMdef]; ring
  rw [div_pow, hexp, show x ^ 3 / C ^ 3 = (1 / C ^ 3) * x ^ 3 from by ring] at hcomb
  have hfin : 1 / C ^ 3 ≤ 2458624 * (N : ℝ) ^ 5 * (1 + |y|) ^ 5 * x :=
    le_of_mul_le_mul_right hcomb (by positivity : (0 : ℝ) < x ^ 3)
  -- (g) extract the lower bound on x = 1 − β
  have hxlow : c₀ / (1 + |y|) ^ 5 ≤ x := by
    have h1 : 1 ≤ C ^ 3 * (2458624 * (N : ℝ) ^ 5 * (1 + |y|) ^ 5 * x) := by
      have h2 := mul_le_mul_of_nonneg_left hfin
        (by positivity : (0 : ℝ) ≤ C ^ 3)
      rw [show C ^ 3 * (1 / C ^ 3) = 1 from by
        field_simp] at h2
      exact h2
    rw [hc₀def, div_div, div_le_iff₀ (by positivity)]
    nlinarith [h1]
  have hmono : min (min x₀ (1 / 4)) c₀ / (1 + |y|) ^ 5 ≤ c₀ / (1 + |y|) ^ 5 := by
    gcongr
    exact min_le_right _ _
  linarith

/-- **The corridor — both edges forbidden, unconditionally.** For primitive non-quadratic `χ`,
    the nontrivial zeros live in the SHRUNKEN strip
    `c/(1+|t|)⁵ ≤ Re ρ ≤ 1 − c/(1+|t|)⁵`: the `Re = 1` exclusion (`zero_free_region_poly`)
    reflects through the functional-equation pairing `ρ ↦ 1−ρ ∈ Z(χ⁻¹)` to forbid the `Re = 0`
    edge symmetrically. The first unconditional interior narrowing of the critical strip in the
    development — the void's first deeded real estate, at both walls. -/
theorem zero_corridor (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχp : χ.IsPrimitive)
    (hχ2 : χ ^ 2 ≠ 1) :
    ∃ c > (0 : ℝ), ∀ ρ ∈ GRHSpectral.NontrivialZeros χ,
      c / (1 + |ρ.im|) ^ 5 ≤ ρ.re ∧ ρ.re ≤ 1 - c / (1 + |ρ.im|) ^ 5 := by
  obtain ⟨c₁, hc₁, hreg₁⟩ := zero_free_region_poly χ hχ hχ2
  have hχinv : χ⁻¹ ≠ 1 := DirichletLHadamard.inv_ne_one_of_ne_one hχ
  have hχinv2 : (χ⁻¹) ^ 2 ≠ 1 := by
    intro h
    rw [inv_pow] at h
    exact hχ2 (inv_eq_one.mp h)
  obtain ⟨c₂, hc₂, hreg₂⟩ := zero_free_region_poly χ⁻¹ hχinv hχinv2
  refine ⟨min c₁ c₂, lt_min hc₁ hc₂, fun ρ hρ => ⟨?_, ?_⟩⟩
  · have hpair := DirichletLHadamard.one_sub_mem_NontrivialZeros_inv hχ hχp hρ
    have hz : DirichletCharacter.LFunction χ⁻¹ (1 - ρ) = 0 := hpair.2.2
    have hbound := hreg₂ (1 - ρ) hz
    have him : (1 - ρ).im = -ρ.im := by simp
    have hre : (1 - ρ).re = 1 - ρ.re := by simp
    rw [him, abs_neg, hre] at hbound
    have hmin : min c₁ c₂ / (1 + |ρ.im|) ^ 5 ≤ c₂ / (1 + |ρ.im|) ^ 5 := by
      gcongr
      exact min_le_right _ _
    linarith
  · have hz : DirichletCharacter.LFunction χ ρ = 0 := hρ.2.2
    have hbound := hreg₁ ρ hz
    have hmin : min c₁ c₂ / (1 + |ρ.im|) ^ 5 ≤ c₁ / (1 + |ρ.im|) ^ 5 := by
      gcongr
      exact min_le_left _ _
    linarith

end HelixZeroFree
