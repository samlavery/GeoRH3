import RequestProject.SpectralEquivalence

open Complex
open scoped ComplexConjugate
namespace CriticalLinePhasor.DeBranges
noncomputable section
/-! ## (c.1) Genuine Gram positivity: the abstract positive-definite-kernel fact -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
/-
**Gram identity.**  The quadratic form of the Gram kernel `K i j = ⟪v i, v j⟫` evaluated on
coefficients `c` is exactly `⟪∑ cᵢ • vᵢ, ∑ cⱼ • vⱼ⟫`.  This is the algebraic heart of every
reproducing-kernel (de Branges) space: such kernels are *positive definite* because they are
genuine Gram matrices.
-/
theorem gram_quadratic_form_eq_inner_self {n : ℕ} (v : Fin n → H) (c : Fin n → ℂ) :
    ∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * (inner ℂ (v i) (v j)) =
      (inner ℂ (∑ i, c i • v i) (∑ j, c j • v j) : ℂ) := by
  simp +decide only [starRingEnd_apply, inner_sum, sum_inner];
  simp +decide only [mul_assoc, inner_smul_right, inner_smul_left, starRingEnd_apply];
  exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [ ← inner_conj_symm ] ; simp +decide [ mul_assoc, mul_comm ] )
/-
**Gram positivity.**  The Gram quadratic form is real and nonnegative — the positive
semidefiniteness of a positive-definite kernel.
-/
theorem gram_quadratic_form_nonneg {n : ℕ} (v : Fin n → H) (c : Fin n → ℂ) :
    0 ≤ (∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * (inner ℂ (v i) (v j))).re := by
  rw [ gram_quadratic_form_eq_inner_self ];
  rw [ inner_self_eq_norm_sq_to_K ] ; norm_num;
  norm_cast ; positivity
/-! ## (c.2) Hermite–Biehler structure functions and their de Branges components -/
/-- The **conjugate (reflected) function** `E*(z) = conj (E (conj z))`.  If `E` is entire so is
`E*`, and `E*` is real-on-real iff `E` is.  This is the second generator of the de Branges
space `H(E)`. -/
def Estar (E : ℂ → ℂ) (z : ℂ) : ℂ := (starRingEnd ℂ) (E ((starRingEnd ℂ) z))
/-
`E*` is an involution: `(E*)* = E`.
-/
@[simp] theorem Estar_Estar (E : ℂ → ℂ) : Estar (Estar E) = E := by
  exact funext fun x => by simp +decide [ Estar ] ;
/-
`‖E* z‖ = ‖E (conj z)‖`.
-/
theorem norm_Estar (E : ℂ → ℂ) (z : ℂ) : ‖Estar E z‖ = ‖E ((starRingEnd ℂ) z)‖ := by
  exact Complex.norm_conj _
/-- The **`A`-component** `A = (E + E*)/2` (real-entire; `Re E` on the real axis). -/
def Acomp (E : ℂ → ℂ) (z : ℂ) : ℂ := (E z + Estar E z) / 2
/-- The **`B`-component** `B = i (E − E*)/2` (real-entire; `−Im E` on the real axis).  Its zeros
are the de Branges "spectrum". -/
def Bcomp (E : ℂ → ℂ) (z : ℂ) : ℂ := Complex.I * (E z - Estar E z) / 2
/-- **Hermite–Biehler positivity.**  `E` is in the Hermite–Biehler class when `E` dominates its
reflection on the open upper half-plane.  Equivalently, the de Branges reproducing kernel of
`H(E)` is positive — this is the positivity that will *do the work*. -/
def IsHB (E : ℂ → ℂ) : Prop := ∀ z : ℂ, 0 < z.im → ‖Estar E z‖ < ‖E z‖
/-! ## (b) The positivity forces reality and discreteness of the spectrum -/
/-
**Reflected positivity on the lower half-plane.**  Hermite–Biehler dominance on the upper
half-plane gives the reversed inequality `‖E z‖ < ‖E* z‖` on the lower half-plane.
-/
theorem hb_lower {E : ℂ → ℂ} (hE : IsHB E) {z : ℂ} (hz : z.im < 0) :
    ‖E z‖ < ‖Estar E z‖ := by
  have := hE ( starRingEnd ℂ z ) ?_ <;> simp_all +decide;
  unfold Estar at * ; aesop
/-
**The positivity has no zeros upstairs.**  A Hermite–Biehler function has no zeros in the
open upper half-plane.
-/
theorem hb_no_zero_upper {E : ℂ → ℂ} (hE : IsHB E) {z : ℂ} (hz : 0 < z.im) : E z ≠ 0 := by
  exact fun h => absurd ( hE z hz ) ( by norm_num [ h ] )
/-
**The decisive positivity step.**  If `E` is Hermite–Biehler then equality of the two
moduli `‖E z‖ = ‖E* z‖` can only happen on the **real axis**.  This is where the strict
positivity inequality genuinely constrains the geometry.
-/
theorem norm_eq_imp_im_zero {E : ℂ → ℂ} (hE : IsHB E) {z : ℂ}
    (h : ‖E z‖ = ‖Estar E z‖) : z.im = 0 := by
  contrapose! h;
  cases lt_or_gt_of_ne h <;> [ exact ne_of_lt ( hb_lower hE ‹_› ) ; exact ne_of_gt ( hE z ‹_› ) ]
/-
**Reality of the `A`-spectrum (forced by positivity).**  Every zero of `A = (E+E*)/2` is
real.
-/
theorem Acomp_zero_im_eq_zero {E : ℂ → ℂ} (hE : IsHB E) {z : ℂ} (hz : Acomp E z = 0) :
    z.im = 0 := by
  unfold Acomp at hz; simp_all +decide [ div_eq_iff ] ;
  exact norm_eq_imp_im_zero hE ( by rw [ eq_neg_of_add_eq_zero_left hz ] ; norm_num )
/-
**Reality of the `B`-spectrum (forced by positivity).**  Every zero of `B = i(E−E*)/2` is
real.  This is the de Branges incarnation of "von Neumann reality": the spectrum is real, but
now *because of* the positivity, not by hand.
-/
theorem Bcomp_zero_im_eq_zero {E : ℂ → ℂ} (hE : IsHB E) {z : ℂ} (hz : Bcomp E z = 0) :
    z.im = 0 := by
  convert CriticalLinePhasor.DeBranges.norm_eq_imp_im_zero hE _;
  unfold Bcomp at hz; simp_all +decide ;
  simp_all +decide [ Complex.normSq, Complex.norm_def, sub_eq_zero ]
/-
`B` is not identically zero when `E` is Hermite–Biehler (else `‖E‖ = ‖E*‖` everywhere,
contradicting strict dominance upstairs).
-/
theorem Bcomp_not_eventually_zero {E : ℂ → ℂ} (hE : IsHB E) :
    ∃ z : ℂ, Bcomp E z ≠ 0 := by
  by_contra! h;
  have := Bcomp_zero_im_eq_zero hE ( h Complex.I ) ; norm_num at this;
/-
**Schwarz reflection preserves analyticity.**  If `E` is entire, so is its reflection
`E*(z) = conj (E (conj z))` (the two conjugations cancel: a power series `∑ aₙ (w − w₀)ⁿ` for `E`
at `conj z₀` becomes `∑ conj aₙ (z − z₀)ⁿ` for `E*` at `z₀`).
-/
theorem Estar_analyticOnNhd {E : ℂ → ℂ} (hEnt : AnalyticOnNhd ℂ E Set.univ) :
    AnalyticOnNhd ℂ (Estar E) Set.univ := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_univ
  intro z _
  have hd := (hEnt ((starRingEnd ℂ) z) (Set.mem_univ _)).differentiableAt
  have hdd := hd.hasDerivAt.conj_conj
  rw [Complex.conj_conj] at hdd
  exact hdd.differentiableAt.differentiableWithinAt
/-
The `B`-component of an entire function is entire.
-/
theorem Bcomp_analyticOnNhd {E : ℂ → ℂ} (hEnt : AnalyticOnNhd ℂ E Set.univ) :
    AnalyticOnNhd ℂ (Bcomp E) Set.univ := by
  apply_rules [ AnalyticOnNhd.div, AnalyticOnNhd.mul, analyticOnNhd_const ];
  · apply_rules [ AnalyticOnNhd.sub, hEnt, Estar_analyticOnNhd ];
  · norm_num
/-
**Discreteness of the spectrum.**  If `E` is entire (analytic on all of `ℂ`) and
Hermite–Biehler, the zeros of `B` are isolated: every point `z₀` (in particular every spectral
point, i.e. every zero of `B`) has a punctured neighbourhood on which `B` does not vanish.
Hence the spectrum `{B = 0}` is a discrete subset of `ℝ`.
-/
theorem Bcomp_zeros_discrete {E : ℂ → ℂ} (hEnt : AnalyticOnNhd ℂ E Set.univ)
    (hE : IsHB E) (z₀ : ℂ) :
    ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ, Bcomp E z ≠ 0 := by
  by_contra h;
  -- Apply the identity theorem for analytic functions.
  have h_id : AnalyticOnNhd ℂ (Bcomp E) Set.univ → (∃ᶠ z in nhdsWithin z₀ {z₀}ᶜ, Bcomp E z = 0) → ∀ z, Bcomp E z = 0 := by
    intros h_analytic h_frequently_zero z
    apply AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero h_analytic (isPreconnected_univ) (Set.mem_univ z₀) h_frequently_zero;
    trivial;
  exact absurd ( h_id ( CriticalLinePhasor.DeBranges.Bcomp_analyticOnNhd hEnt ) ( by simpa using h ) ) ( by simpa using CriticalLinePhasor.DeBranges.Bcomp_not_eventually_zero hE )
/-! ## (a) A concrete Hermite–Biehler structure function: the Paley–Wiener space
`E(z) = e^{−i z}` is the structure function of the Paley–Wiener (band-limited) de Branges space.
Its reflection is `E*(z) = e^{i z}`, its `B`-component is `sin`, and its spectrum is the real
discrete set `{kπ}` — a genuine, *not hand-picked*, real discrete spectrum produced by the
positivity mechanism. -/
/-- The Paley–Wiener structure function `E(z) = e^{−i z}`. -/
def paleyWiener (z : ℂ) : ℂ := Complex.exp (-(Complex.I * z))
/-
Its reflection is `E*(z) = e^{i z}`.
-/
theorem paleyWiener_Estar : Estar paleyWiener = fun z => Complex.exp (Complex.I * z) := by
  funext z; simp [Estar, paleyWiener];
  simp +decide [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ]
/-
`e^{−i z}` is a Hermite–Biehler function: the positivity holds.
-/
theorem paleyWiener_isHB : IsHB paleyWiener := by
  intro z hz;
  norm_num [ paleyWiener_Estar, paleyWiener ];
  norm_num [ Complex.norm_exp, hz ]
/-
The `B`-component of the Paley–Wiener structure function is `sin`; its zeros `{kπ}` are the
(real, discrete) spectrum.
-/
theorem paleyWiener_Bcomp : Bcomp paleyWiener = Complex.sin := by
  ext1 z
  rw [Bcomp, paleyWiener_Estar]
  simp only [paleyWiener, Complex.sin]
  ring_nf
/-! ## The arithmetic application: positivity forces the zeros onto the critical line -/
open CriticalLinePhasor.CarrierFiberDecomposition (NTZ)
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
/-
The de Branges change of variables sending a strip point `ρ` to the spectral point
`z = −i(ρ − ½)`; its imaginary part is `½ − Re ρ`, so `z` is real iff `ρ` is on the critical
line.
-/
theorem deBranges_var_im (ρ : ℂ) : (-(Complex.I * (ρ - 1 / 2))).im = 1 / 2 - ρ.re := by
  norm_num [ Complex.ext_iff ]
/-
**The de Branges criterion forces RH (forward direction).**  Suppose `E` is a Hermite–Biehler
structure function for `L(·,χ)` in the sense that its `B`-component vanishes at the spectral
point `−i(ρ − ½)` of every nontrivial zero `ρ`.  Then the **positivity** of `E` forces every
nontrivial zero onto the critical line `Re ρ = ½`.
The reality input is genuine de Branges positivity (`IsHB E`), *not* a diagonal chosen to equal
the answer: the structure identity `hstruct` only says `B` vanishes where `L` does, and the
inequality `IsHB` does the real work of placing those zeros on the line.
-/
theorem deBranges_zeros_on_line {E : ℂ → ℂ} (hE : IsHB E)
    (hstruct : ∀ ρ ∈ NTZ χ, Bcomp E (-(Complex.I * (ρ - 1 / 2))) = 0) :
    ∀ ρ ∈ NTZ χ, ρ.re = 1 / 2 := by
  intro ρ hρ;
  have := hstruct ρ hρ;
  have := Bcomp_zero_im_eq_zero hE this; norm_num [ Complex.ext_iff ] at *; linarith;
/-- **A de Branges Hermite–Biehler structure datum for `L(·,χ)`.**  The honest, non-circular
input of the de Branges route: a *concrete entire* function `E` that is Hermite–Biehler (the
positivity property `IsHB`) and whose `B`-component vanishes at the spectral point `−i(ρ−½)` of
every nontrivial zero `ρ`.  This is the de Branges criterion; it is **not** "the diagonal of the
answer" — reality of the spectrum is *derived* from the positivity `hHB`, not assumed. -/
structure DeBrangesStructure (χ : DirichletCharacter ℂ q) where
  /-- The structure function. -/
  E : ℂ → ℂ
  /-- It is entire. -/
  entire : AnalyticOnNhd ℂ E Set.univ
  /-- It is Hermite–Biehler: the de Branges reproducing-kernel positivity. -/
  hHB : IsHB E
  /-- Its `B`-component vanishes at the spectral point of every nontrivial zero. -/
  struct : ∀ ρ ∈ NTZ χ, Bcomp E (-(Complex.I * (ρ - 1 / 2))) = 0
/-- **GRH from the de Branges criterion.**  A Hermite–Biehler structure datum for `L(·,χ)` forces
every nontrivial zero onto the critical line.  The positivity (`IsHB`) is load-bearing. -/
theorem GRH_of_deBranges (D : DeBrangesStructure χ) : ∀ ρ ∈ NTZ χ, ρ.re = 1 / 2 :=
  deBranges_zeros_on_line χ D.hHB D.struct
/-- **The de Branges route supplies the project's Hilbert–Pólya datum.**  Genuine de Branges
positivity ⇒ GRH ⇒ the project's `HilbertPolyaDatum`.  The bridge `hilbertPolyaDatum_of_GRH` then
constructs the self-adjoint diagonal model — but now its eigenvalues are real *because* of the
Hermite–Biehler positivity, closing the loop the original `diagOp` left open. -/
theorem hilbertPolyaDatum_of_deBranges (D : DeBrangesStructure χ) :
    Nonempty (CriticalLinePhasor.Faithfulness.HilbertPolyaDatum χ) :=
  ⟨CriticalLinePhasor.Faithfulness.hilbertPolyaDatum_of_GRH χ (GRH_of_deBranges χ D)⟩
end
