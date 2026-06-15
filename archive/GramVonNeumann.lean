import Mathlib

/-!
# The Gram / von Neumann energy package — the operator form of the Green–Helmholtz energy

This is the **closed form** of the Green–Helmholtz positive energy, as an honest, kernel-clean
positivity (a non-negative `≥ 0` PSD Gram form — Rule Three: non-negativity with attainable kernel,
*not* strict positivity).

**Operator / von Neumann side.** `A = −d²/dΘ² + μ²` is the Helmholtz operator. Its plane waves are
eigenfunctions with eigenvalue `μ² + ν² > 0` (`ghOperator_planeWave_eigenvalue`,
`ghOperator_eigenvalue_pos`) — so `A` is positive, hence `G_μ := A⁻¹` is positive, with **spectral
symbol** `Ĝ_μ(ν) = 1/(μ² + ν²) > 0` (`GHSymbol`, `GHSymbol_pos`).

**Kernel / Gram side.** `A⁻¹` has the Green kernel `K_μ(x,y) = (1/2μ)·e^{−μ|x−y|}` (`GHKernel`), since
`(−d²/dx² + μ²)K_μ = δ`. The Green–Helmholtz / Gram energy of a finite atom field `Σ c_q δ_{x_q}` is

`E = Σ_{q,r} c_q · conj(c_r) · K_μ(x_q, x_r)  =  ‖A^{-1/2} f‖²  ≥ 0.`

**The heart (`exp_kernel_psd`, `ghKernel_gram_nonneg`).** `K_μ` is a **positive-definite kernel**:
for sorted positions `x_j`, the exact sum-of-squares

`Σ_{j,k} c_j conj(c_k) e^{−μ|x_j−x_k|} = Σ_i w_i · |Σ_{j≥i} c_j e^{−μ x_j}|²,   w_i ≥ 0`

(from the factorization `e^{−μ|x_j−x_k|} = e^{−μx_j}e^{−μx_k}·e^{2μ x_{min}}` and the telescoping
`Σ_{i≤m} w_i = e^{2μ x_m}`) makes the energy manifestly `≥ 0`. Self-contained — no Fourier, no Bochner.

**Prime-trace instantiation (`primeTraceGramEnergy_nonneg`).** The prime trace
`T_χ = Σ_q Λ(q)χ(q) q^{−1/2} δ_{log q}` (`= −L'/L(½+iγ,χ)`, regularized) is such an atom field, with
positions `log q` (the helix-winding coordinates) and coefficients `Λ(q)χ(q) q^{−1/2}`. Its
Green–Helmholtz energy is `≥ 0` for every finite collection of prime powers — unconditionally.
-/

open Finset ComplexConjugate

namespace GramVonNeumann

/-! ## The spectral symbol and the von Neumann operator -/

/-- The **spectral symbol** of `G_μ = A⁻¹`: `Ĝ_μ(ν) = 1/(μ² + ν²)`. -/
noncomputable def GHSymbol (μ ν : ℝ) : ℝ := 1 / (μ ^ 2 + ν ^ 2)

/-- `Ĝ_μ(ν) > 0` — the inverse operator's symbol is strictly positive (`A`'s symbol `μ²+ν² > 0`). -/
theorem GHSymbol_pos {μ : ℝ} (hμ : 0 < μ) (ν : ℝ) : 0 < GHSymbol μ ν := by
  rw [GHSymbol]; positivity

/-- **The Helmholtz operator's eigenvalue is `μ² + ν² > 0`.** -/
theorem ghOperator_eigenvalue_pos {μ : ℝ} (hμ : 0 < μ) (ν : ℝ) : 0 < μ ^ 2 + ν ^ 2 := by
  positivity

/-- **`A = −d²/dΘ² + μ²` acts on the plane wave `e^{iνΘ}` with eigenvalue `μ² + ν²`.**
    This is the von Neumann/spectral content: `A` is a positive self-adjoint operator (positive
    eigenvalues), so `A⁻¹ = G_μ` is positive. -/
theorem ghOperator_planeWave_eigenvalue (μ ν : ℝ) (θ : ℂ) :
    -(deriv (deriv (fun z => Complex.exp (Complex.I * ν * z))) θ)
        + (μ ^ 2 : ℂ) * Complex.exp (Complex.I * ν * θ)
      = ((μ ^ 2 + ν ^ 2 : ℝ)) * Complex.exp (Complex.I * ν * θ) := by
  have hd1 : ∀ z, HasDerivAt (fun z => Complex.exp (Complex.I * ν * z))
      (Complex.exp (Complex.I * ν * z) * (Complex.I * ν)) z := by
    intro z
    have : HasDerivAt (fun z : ℂ => Complex.I * ν * z) (Complex.I * ν) z := by
      simpa using (hasDerivAt_id z).const_mul (Complex.I * (ν : ℂ))
    exact this.cexp
  have hderiv1 : deriv (fun z => Complex.exp (Complex.I * ν * z))
      = fun z => Complex.exp (Complex.I * ν * z) * (Complex.I * ν) :=
    funext fun z => (hd1 z).deriv
  rw [hderiv1, ((hd1 θ).mul_const (Complex.I * ν)).deriv]
  have hI : Complex.I * (ν : ℂ) * (Complex.I * ν) = -(ν : ℂ) ^ 2 := by
    rw [mul_mul_mul_comm, Complex.I_mul_I]; ring
  rw [mul_assoc, hI]; push_cast; ring

/-! ## The Green kernel -/

/-- The **Green–Helmholtz kernel** `K_μ(x,y) = (1/2μ)·e^{−μ|x−y|}` — the kernel of `A⁻¹`, since
    `(−d²/dx² + μ²)K_μ = δ`. -/
noncomputable def GHKernel (μ x y : ℝ) : ℝ := (1 / (2 * μ)) * Real.exp (-μ * |x - y|)

/-- `K_μ` is symmetric. -/
theorem GHKernel_symm (μ x y : ℝ) : GHKernel μ x y = GHKernel μ y x := by
  rw [GHKernel, GHKernel, abs_sub_comm]

/-- `K_μ(x,y) > 0`. -/
theorem GHKernel_pos {μ : ℝ} (hμ : 0 < μ) (x y : ℝ) : 0 < GHKernel μ x y := by
  rw [GHKernel]; positivity

/-! ## The heart: positive-definiteness of the exponential kernel -/

/-- **The exponential kernel `e^{−μ|x−y|}` is positive semidefinite.** For sorted positions `x_j`,
    the Gram form `Σ_{j,k} c_j conj(c_k) e^{−μ|x_j−x_k|}` is `≥ 0`, via the **exact sum of squares**

    `Σ_{j,k} c_j conj(c_k) e^{−μ|x_j−x_k|} = Σ_i w_i · ‖Σ_{j≥i} c_j e^{−μ x_j}‖²`,  `w_i ≥ 0`,

    from `e^{−μ|x_j−x_k|} = e^{−μx_j}e^{−μx_k}·(e^{μ x_{min}})²`, `(e^{μ x_m})² = Σ_{i≤m} w_i`
    (telescoping), and the swap `Σ_i w_i [i≤j][i≤k] = (e^{μ x_min})²`. Self-contained — no Fourier. -/
theorem exp_kernel_psd (μ : ℝ) (hμ : 0 < μ) (n : ℕ) (x : ℕ → ℝ)
    (hx : ∀ i j, i ≤ j → x i ≤ x j) (c : ℕ → ℂ) :
    0 ≤ (∑ j ∈ range n, ∑ k ∈ range n,
        c j * conj (c k) * (Real.exp (-μ * |x j - x k|) : ℂ)).re := by
  set usq : ℕ → ℝ := fun k => Real.exp (μ * x k) ^ 2 with husq
  set g : ℕ → ℝ := fun k => Real.exp (-μ * x k) with hg
  set w : ℕ → ℝ := fun k => if k = 0 then usq 0 else usq k - usq (k - 1) with hw
  set a : ℕ → ℂ := fun j => c j * (g j : ℂ) with ha
  set G : ℕ → ℂ := fun i => ∑ j ∈ range n, if i ≤ j then a j else 0 with hG
  have hwall : ∀ k, 0 ≤ w k := by
    intro k; simp only [hw]
    by_cases h0 : k = 0
    · simp only [if_pos h0, husq]; positivity
    · simp only [if_neg h0]
      have hle : usq (k - 1) ≤ usq k := by simp only [husq]; gcongr; exact hx (k - 1) k (by omega)
      linarith
  have htel : ∀ m, m < n → (∑ i ∈ range n, if i ≤ m then w i else 0) = usq m := by
    intro m hm
    rw [← Finset.sum_filter]
    have hfilter : (range n).filter (fun i => i ≤ m) = range (m + 1) := by
      ext i; simp only [mem_filter, mem_range, Nat.lt_succ_iff]
      exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
    rw [hfilter, Finset.sum_range_succ']
    simp only [hw, Nat.add_sub_cancel, if_neg (Nat.succ_ne_zero _), if_pos rfl]
    rw [Finset.sum_range_sub usq]; ring
  have hker : ∀ j k, Real.exp (-μ * |x j - x k|) = g j * g k * usq (min j k) := by
    intro j k
    have hxmin : x (min j k) = min (x j) (x k) := by
      rcases le_total j k with h | h
      · rw [min_eq_left h, min_eq_left (hx j k h)]
      · rw [min_eq_right h, min_eq_right (hx k j h)]
    simp only [hg, husq, pow_two]
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1; rw [hxmin]
    rcases le_total (x j) (x k) with h | h
    · rw [abs_of_nonpos (by linarith), min_eq_left h]; ring
    · rw [abs_of_nonneg (by linarith), min_eq_right h]; ring
  have hterm : ∀ j ∈ range n, ∀ k ∈ range n,
      c j * conj (c k) * (Real.exp (-μ * |x j - x k|) : ℂ)
      = a j * conj (a k) * ((∑ i ∈ range n, if i ≤ j ∧ i ≤ k then w i else 0 : ℝ) : ℂ) := by
    intro j hj k hk
    rw [mem_range] at hj hk
    have hsum : (∑ i ∈ range n, if i ≤ j ∧ i ≤ k then w i else 0) = usq (min j k) := by
      rw [← htel (min j k) (lt_of_le_of_lt (min_le_left j k) hj)]
      exact Finset.sum_congr rfl (fun i _ => if_congr le_min_iff.symm rfl rfl)
    rw [hker, hsum]
    simp only [ha, map_mul, Complex.conj_ofReal]; push_cast; ring
  rw [Finset.sum_congr rfl (fun j hj => Finset.sum_congr rfl (fun k hk => hterm j hj k hk))]
  have hcrux : ∑ j ∈ range n, ∑ k ∈ range n,
        a j * conj (a k) * ((∑ i ∈ range n, if i ≤ j ∧ i ≤ k then w i else 0 : ℝ) : ℂ)
      = ∑ i ∈ range n, (w i : ℂ) * (G i * conj (G i)) := by
    set f : ℕ → ℕ → ℂ := fun i j => if i ≤ j then a j else 0 with hf
    have hLHS : ∀ j k, a j * conj (a k) *
          ((∑ i ∈ range n, if i ≤ j ∧ i ≤ k then w i else 0 : ℝ) : ℂ)
        = ∑ i ∈ range n, f i j * conj (f i k) * (w i : ℂ) := by
      intro j k
      rw [Complex.ofReal_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [hf]
      by_cases hij : i ≤ j <;> by_cases hik : i ≤ k <;> simp [hij, hik]
    have hRHS : ∀ i, (w i : ℂ) * (G i * conj (G i))
        = ∑ j ∈ range n, ∑ k ∈ range n, f i j * conj (f i k) * (w i : ℂ) := by
      intro i
      simp only [hG, hf]
      rw [map_sum, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun k _ => ?_); ring
    rw [Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => hLHS j k)),
        Finset.sum_congr rfl (fun i _ => hRHS i),
        Finset.sum_congr rfl (fun j _ => Finset.sum_comm), Finset.sum_comm]
  rw [hcrux, Complex.re_sum]
  apply Finset.sum_nonneg
  intro i _
  rw [Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_nonneg (hwall i) (Complex.normSq_nonneg _)

/-- **The Green–Helmholtz Gram energy is `≥ 0`.** For sorted positions, the kernel `K_μ`'s Gram form
    is non-negative — `E_GH(f) = Σ_{q,r} c_q conj(c_r) K_μ(x_q,x_r) ≥ 0`. (`K_μ` PSD via
    `exp_kernel_psd`, scaled by `1/2μ > 0`.) -/
theorem ghKernel_gram_nonneg (μ : ℝ) (hμ : 0 < μ) (n : ℕ) (x : ℕ → ℝ)
    (hx : ∀ i j, i ≤ j → x i ≤ x j) (c : ℕ → ℂ) :
    0 ≤ (∑ j ∈ range n, ∑ k ∈ range n,
        c j * conj (c k) * (GHKernel μ (x j) (x k) : ℂ)).re := by
  have hfac : (∑ j ∈ range n, ∑ k ∈ range n, c j * conj (c k) * (GHKernel μ (x j) (x k) : ℂ))
      = ((1 / (2 * μ) : ℝ) : ℂ) *
          ∑ j ∈ range n, ∑ k ∈ range n, c j * conj (c k) * (Real.exp (-μ * |x j - x k|) : ℂ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [GHKernel]; push_cast; ring
  rw [hfac, Complex.re_ofReal_mul]
  exact mul_nonneg (by positivity) (exp_kernel_psd μ hμ n x hx c)

/-! ## Index-free (unsorted) positivity

The same positivity holds for **arbitrary** positions — no sortedness hypothesis — because the Gram
form is invariant under simultaneously permuting `(x, c)`, and any finite family can be sorted
(`Tuple.sort`). This is the standard "the kernel is positive-definite" statement. -/

/-- `Fin`-indexed monotone PSD — the `range`/`ℕ` lemma `exp_kernel_psd` transported to `Fin n` (via a
    monotone extension of the finite family to `ℕ`). -/
theorem exp_kernel_psd_fin_mono (μ : ℝ) (hμ : 0 < μ) (n : ℕ) (x : Fin n → ℝ)
    (hx : Monotone x) (c : Fin n → ℂ) :
    0 ≤ (∑ j : Fin n, ∑ k : Fin n,
        c j * conj (c k) * (Real.exp (-μ * |x j - x k|) : ℂ)).re := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · set X : ℕ → ℝ := fun t => x ⟨min t (n - 1), by omega⟩ with hX
    set C : ℕ → ℂ := fun t => if h : t < n then c ⟨t, h⟩ else 0 with hC
    have hXmono : ∀ i j, i ≤ j → X i ≤ X j := by
      intro i j hij; apply hx; simp only [Fin.mk_le_mk]; omega
    have key := exp_kernel_psd μ hμ n X hXmono C
    have hCj : ∀ j : Fin n, C ↑j = c j := by intro j; simp [hC]
    have hXj : ∀ j : Fin n, X ↑j = x j := by
      intro j; simp only [hX]; congr 1; ext; simp only []; omega
    have heq : (∑ j : Fin n, ∑ k : Fin n, c j * conj (c k) * (Real.exp (-μ * |x j - x k|) : ℂ))
        = ∑ j ∈ range n, ∑ k ∈ range n, C j * conj (C k) * (Real.exp (-μ * |X j - X k|) : ℂ) := by
      rw [← Fin.sum_univ_eq_sum_range
        (fun j => ∑ k ∈ range n, C j * conj (C k) * (Real.exp (-μ * |X j - X k|) : ℂ)) n]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [← Fin.sum_univ_eq_sum_range
        (fun k => C ↑j * conj (C k) * (Real.exp (-μ * |X ↑j - X k|) : ℂ)) n]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [hCj, hCj, hXj, hXj]
    rw [heq]; exact key

/-- **The exponential kernel is positive semidefinite — index-free.** No ordering hypothesis on the
    positions: the Gram form is invariant under simultaneously permuting `(x, c)` (`Equiv.sum_comp`),
    and `Tuple.sort` sorts any finite family, reducing to `exp_kernel_psd_fin_mono`. -/
theorem exp_kernel_psd_fin (μ : ℝ) (hμ : 0 < μ) (n : ℕ) (x : Fin n → ℝ) (c : Fin n → ℂ) :
    0 ≤ (∑ j : Fin n, ∑ k : Fin n,
        c j * conj (c k) * (Real.exp (-μ * |x j - x k|) : ℂ)).re := by
  set σ := Tuple.sort x with hσ
  have hreindex :
      (∑ j : Fin n, ∑ k : Fin n, c j * conj (c k) * (Real.exp (-μ * |x j - x k|) : ℂ))
      = ∑ j : Fin n, ∑ k : Fin n,
          c (σ j) * conj (c (σ k)) * (Real.exp (-μ * |x (σ j) - x (σ k)|) : ℂ) := by
    rw [← Equiv.sum_comp σ
      (fun j => ∑ k : Fin n, c j * conj (c k) * (Real.exp (-μ * |x j - x k|) : ℂ))]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Equiv.sum_comp σ
      (fun k => c (σ j) * conj (c k) * (Real.exp (-μ * |x (σ j) - x k|) : ℂ))]
  rw [hreindex]
  exact exp_kernel_psd_fin_mono μ hμ n (fun i => x (σ i)) (Tuple.monotone_sort x) (fun i => c (σ i))

/-- **The Green–Helmholtz Gram energy is `≥ 0` — index-free.** Arbitrary positions, arbitrary
    coefficients: `Σ_{q,r} c_q conj(c_r) K_μ(x_q,x_r) ≥ 0`, no sortedness needed. -/
theorem ghKernel_gram_nonneg_fin (μ : ℝ) (hμ : 0 < μ) (n : ℕ) (x : Fin n → ℝ) (c : Fin n → ℂ) :
    0 ≤ (∑ j : Fin n, ∑ k : Fin n, c j * conj (c k) * (GHKernel μ (x j) (x k) : ℂ)).re := by
  have hfac : (∑ j : Fin n, ∑ k : Fin n, c j * conj (c k) * (GHKernel μ (x j) (x k) : ℂ))
      = ((1 / (2 * μ) : ℝ) : ℂ) *
          ∑ j : Fin n, ∑ k : Fin n, c j * conj (c k) * (Real.exp (-μ * |x j - x k|) : ℂ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [GHKernel]; push_cast; ring
  rw [hfac, Complex.re_ofReal_mul]
  exact mul_nonneg (by positivity) (exp_kernel_psd_fin μ hμ n x c)

/-! ## The Hermitian (self-adjoint) structure — the half Hilbert–Pólya uses

For Hilbert–Pólya we do **not** need PSD. The receiver asks for `IsSelfAdjoint a` (`a = a⋆`), strictly
weaker than positive: it gives a **real** spectrum (zeros real ⟹ on the line), not a nonnegative one —
and the heights `γ` run over all of `ℝ`, so nonnegativity would be the *wrong* condition (Rule Eight:
"Hilbert–Pólya needs no Li/Weil `≥ 0`"). The H-P-relevant property of the Gram form is therefore that it
is **Hermitian / real** (`K` real symmetric ⟹ the form is self-conjugate), not that it is `≥ 0`. The
`≥ 0` theorems above are the Weil/Li energy — kept for that route, but **not** on the H-P chain. -/

/-- **The Gram form is real (Hermitian).** `Σ_{j,k} c_j conj(c_k) K(x_j,x_k)` has zero imaginary part:
    `K` real symmetric makes the form self-conjugate. This is the **self-adjoint** half — `a = a⋆`,
    real spectrum — and is what the H-P receiver consumes; positivity (`≥ 0`) is not used. -/
theorem ghKernel_gram_real_fin (μ : ℝ) (n : ℕ) (x : Fin n → ℝ) (c : Fin n → ℂ) :
    (∑ j : Fin n, ∑ k : Fin n, c j * conj (c k) * (GHKernel μ (x j) (x k) : ℂ)).im = 0 := by
  rw [← Complex.conj_eq_iff_im, map_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_mul, map_mul, Complex.conj_conj, Complex.conj_ofReal, GHKernel_symm μ (x k) (x j)]
  ring

/-! ## The prime-trace instantiation -/

/-- The **prime-trace atom coefficient** `Λ(q)·χ(q)·q^{−1/2}` — the weight of the prime power `q` in
    the trace `T_χ = −L'/L(½+iγ,χ)`. -/
noncomputable def primeTraceCoeff {N : ℕ} (χ : DirichletCharacter ℂ N) (q : ℕ) : ℂ :=
  (ArithmeticFunction.vonMangoldt q : ℂ) * χ (q : ZMod N) / (Real.sqrt q : ℂ)

/-- The **prime-trace Green–Helmholtz energy** over the first `n` prime-power atoms
    `q 0 < q 1 < …` (positions `log(q j)`, coefficients `Λ(q)χ(q)q^{−1/2}`):

    `E_χ = Σ_{j,k} Λ(q_j)χ(q_j)q_j^{−1/2} · conj(Λ(q_k)χ(q_k)q_k^{−1/2}) · K_μ(log q_j, log q_k).` -/
noncomputable def primeTraceGramEnergy {N : ℕ} (χ : DirichletCharacter ℂ N) (μ : ℝ)
    (q : ℕ → ℕ) (n : ℕ) : ℂ :=
  ∑ j ∈ range n, ∑ k ∈ range n,
    primeTraceCoeff χ (q j) * conj (primeTraceCoeff χ (q k)) *
      (GHKernel μ (Real.log (q j)) (Real.log (q k)) : ℂ)

/-- **The prime-trace Green–Helmholtz energy is `≥ 0`** — the von Neumann / Gram closed form
    `E_χ = ‖A^{-1/2} T_χ‖² ≥ 0`, unconditional, for every finite collection of prime powers. The
    increasing prime powers `q` give increasing log-positions, so the kernel PSD applies. -/
theorem primeTraceGramEnergy_nonneg {N : ℕ} (χ : DirichletCharacter ℂ N) (μ : ℝ) (hμ : 0 < μ)
    (q : ℕ → ℕ) (hq : ∀ i j, i ≤ j → q i ≤ q j) (hq1 : ∀ i, 1 ≤ q i) (n : ℕ) :
    0 ≤ (primeTraceGramEnergy χ μ q n).re := by
  refine ghKernel_gram_nonneg μ hμ n (fun i => Real.log (q i)) ?_ (fun i => primeTraceCoeff χ (q i))
  intro i j hij
  exact Real.log_le_log (by exact_mod_cast hq1 i) (by exact_mod_cast hq i j hij)

end GramVonNeumann
