import Mathlib
import RequestProject.ChiThreeLogDerivIdentity

/-!
# Ledger 1 — the L-channel cancellation (the corrected firing)

The **cancellation is on the L-side**, not the prime-trace side: `L(s,χ₃) = 0` exactly when the two
character fibres balance — the positive residue class `3k+1` against the negative class `3k+2`:

`L(s,χ₃) = Σ_{k≥0}(3k+1)^{-s} − Σ_{k≥0}(3k+2)^{-s}`   (continued via Hurwitz zeta),

so a zero is `fibrePlus = fibreMinus`. The **pole** (singularity) lives one ledger over, on
`−L'/L`. No prime trace here, no `½` — pure character-fibre balance.
-/

open HurwitzZeta Complex
open ZMod (toAddCircle)

namespace Chi3Fibre

/-- The **positive character fibre** of χ₃ — the continued `Σ_{k≥0} (3k+1)^{-s}`, i.e.
    `3^{-s} · ζ_H(1/3, s)`. -/
noncomputable def fibrePlus (s : ℂ) : ℂ :=
  (3 : ℂ) ^ (-s) * hurwitzZeta (toAddCircle (1 : ZMod 3)) s

/-- The **negative character fibre** of χ₃ — the continued `Σ_{k≥0} (3k+2)^{-s}`, i.e.
    `3^{-s} · ζ_H(2/3, s)`. -/
noncomputable def fibreMinus (s : ℂ) : ℂ :=
  (3 : ℂ) ^ (-s) * hurwitzZeta (toAddCircle (2 : ZMod 3)) s

/-- **`L(s,χ₃)` is the fibre difference `fibrePlus − fibreMinus`** — the (analytically continued)
    `Σ(3k+1)^{-s} − Σ(3k+2)^{-s}`, from Mathlib's Hurwitz-zeta decomposition of `LFunction`
    (`χ₃(0)=0, χ₃(1)=1, χ₃(2)=−1`). -/
theorem LFunction_chi3_eq_fibre_diff (s : ℂ) :
    DirichletCharacter.LFunction ChiThree.χ3 s = fibrePlus s - fibreMinus s := by
  rw [fibrePlus, fibreMinus,
      show DirichletCharacter.LFunction ChiThree.χ3 s
        = ZMod.LFunction (fun j => ChiThree.χ3 j) s from rfl,
      ZMod.LFunction, show (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} from by decide,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [ChiThree.χ3_zero, ChiThree.χ3_one, ChiThree.χ3_two]
  push_cast
  ring

/-- **Ledger 1 — the L-channel cancellation.** A zero of `L(·,χ₃)` is *exactly* a balance of the two
    character fibres: the positive class `3k+1` and the negative class `3k+2` cancel. No prime trace,
    no `½` — the zero **is** the fibre cancellation. -/
theorem chi3_zero_iff_fibre_balance (s : ℂ) :
    DirichletCharacter.LFunction ChiThree.χ3 s = 0 ↔ fibrePlus s = fibreMinus s := by
  rw [LFunction_chi3_eq_fibre_diff, sub_eq_zero]

/-! ## On the line, a χ₃ zero is a real-axis (self-dual) condition

`χ₃` is a **real** Dirichlet character (values in `{0, 1, −1}`), so its Dirichlet coefficients are real.
That makes `L(·,χ₃)` satisfy **Schwarz reflection** `conj (L(conj s)) = L(s)` everywhere (extended off the
strip by the identity theorem, since `L(·,χ₃)` is entire as `χ₃ ≠ 1`). On the critical line `conj(½+it) =
½−it`, so the reflection pairs the value at `+t` with the (conjugate of the) value at `−t`.

The consequence is the **self-dual real-axis structure** of an on-line zero, the "max-constructive /
max-destructive" picture:

* the value at `+t` and the value at `−t` are complex conjugates (`LFunction_chi3_line_conj`);
* hence their **product** `L(½+it)·L(½−it)` is a genuine **non-negative real** number — exactly
  `‖L(½+it)‖²` (`chi3_line_prod_eq_normSq`), the conjugate-pair product;
* a χ₃ zero on the line is the vanishing of that real quantity, equivalently the fibre balance at `+t`
  multiplied by the fibre balance at its conjugate buddy `−t` collapsing to `0`
  (`chi3_line_zero_iff_real`).

**Honest scope (Rules Four & Five).** This is the *on-line reality / self-duality* structure only — the
1-D shadow. It does **not** force `Re ρ = ½`: it is a statement *about* points already on the line
`½+it`, derived from real coefficients (Schwarz) alone. Schwarz reflection holds for any real-coefficient
L-function (Euler product or not), so it cannot by itself locate the zeros. The off-line forcing is the
separate FTA/winding content; here we only earn that, *where a zero sits on the line*, it is a real-axis
self-dual event. -/

/-- `χ₃` takes **real** values: `conj (χ₃ n) = χ₃ n` for every `n`. (Values in `{0, 1, −1}`.) -/
theorem chi3_conj_eq (n : ℕ) :
    (starRingEnd ℂ) (ChiThree.χ3 (n : ZMod 3)) = ChiThree.χ3 (n : ZMod 3) := by
  have hmod : (n : ZMod 3) = ((n % 3 : ℕ) : ZMod 3) := (ZMod.natCast_mod n 3).symm
  rw [hmod]
  have h3 : n % 3 < 3 := Nat.mod_lt n (by norm_num)
  interval_cases (n % 3) <;> simp [ChiThree.χ3_zero, ChiThree.χ3_one, ChiThree.χ3_two]

/-- **Schwarz reflection on the strip** `Re s > 1`: `conj (L(conj s, χ₃)) = L(s, χ₃)`, straight from the
    real Dirichlet coefficients of `χ₃` (`chi3_conj_eq`). -/
theorem LFunction_chi3_conj_strip {s : ℂ} (hs : 1 < s.re) :
    (starRingEnd ℂ) (DirichletCharacter.LFunction ChiThree.χ3 ((starRingEnd ℂ) s))
      = DirichletCharacter.LFunction ChiThree.χ3 s := by
  have hcs : 1 < ((starRingEnd ℂ) s).re := by simpa using hs
  rw [DirichletCharacter.LFunction_eq_LSeries ChiThree.χ3 hcs,
      DirichletCharacter.LFunction_eq_LSeries ChiThree.χ3 hs, LSeries, LSeries, conj_tsum]
  refine tsum_congr (fun n => ?_)
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, map_div₀]
    congr 1
    · exact chi3_conj_eq n
    · have harg : ((n : ℂ)).arg ≠ Real.pi := by
        have h0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
        rw [show ((n : ℂ)) = ((n : ℝ) : ℂ) by push_cast; ring,
            Complex.arg_ofReal_of_nonneg h0]
        exact Real.pi_ne_zero.symm
      rw [Complex.cpow_conj _ _ harg, Complex.conj_conj, Complex.conj_natCast]

/-- **Schwarz reflection of `L(·,χ₃)` on all of `ℂ`.** `conj (L(conj s, χ₃)) = L(s, χ₃)` — extended from
    the strip (`LFunction_chi3_conj_strip`) to the whole plane by the identity theorem, using that
    `L(·,χ₃)` is entire (`differentiable_LFunction`, valid as `χ₃ ≠ 1`). A genuine fact about the
    L-function from its real coefficients; no functional equation, no completed L, no root number. -/
theorem LFunction_chi3_conj (s : ℂ) :
    (starRingEnd ℂ) (DirichletCharacter.LFunction ChiThree.χ3 ((starRingEnd ℂ) s))
      = DirichletCharacter.LFunction ChiThree.χ3 s := by
  set g : ℂ → ℂ :=
    fun z => (starRingEnd ℂ) (DirichletCharacter.LFunction ChiThree.χ3 ((starRingEnd ℂ) z)) with hg
  have hLdiff : Differentiable ℂ (DirichletCharacter.LFunction ChiThree.χ3) :=
    DirichletCharacter.differentiable_LFunction ChiThree.χ3_ne_one
  have hg_diff : Differentiable ℂ g := by
    intro x
    have hd : DifferentiableAt ℂ (DirichletCharacter.LFunction ChiThree.χ3)
        ((starRingEnd ℂ) x) := hLdiff _
    have h2 := hd.conj_conj
    rw [Complex.conj_conj] at h2
    exact h2.congr_of_eventuallyEq (by filter_upwards with y; rfl)
  have hg_an : AnalyticOnNhd ℂ g Set.univ := analyticOnNhd_univ_iff_differentiable.mpr hg_diff
  have hL_an : AnalyticOnNhd ℂ (DirichletCharacter.LFunction ChiThree.χ3) Set.univ :=
    analyticOnNhd_univ_iff_differentiable.mpr hLdiff
  have hev : g =ᶠ[nhds (2 : ℂ)] DirichletCharacter.LFunction ChiThree.χ3 := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hmem : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by norm_num
    filter_upwards [hopen.mem_nhds hmem] with z hz
    exact LFunction_chi3_conj_strip hz
  have heq := hL_an.eqOn_of_preconnected_of_eventuallyEq hg_an isPreconnected_univ
    (Set.mem_univ (2 : ℂ)) hev.symm
  exact (heq (Set.mem_univ s)).symm

/-- **The conjugate pairing on the line.** `conj (L(½+it, χ₃)) = L(½−it, χ₃)`: the value at `+t` and the
    value at `−t` are complex conjugates (`conj(½+it) = ½−it`, then `LFunction_chi3_conj`). The on-line
    zero set is symmetric under `t ↦ −t`. -/
theorem LFunction_chi3_line_conj (t : ℝ) :
    (starRingEnd ℂ) (DirichletCharacter.LFunction ChiThree.χ3 (1 / 2 + (t : ℂ) * Complex.I))
      = DirichletCharacter.LFunction ChiThree.χ3 (1 / 2 - (t : ℂ) * Complex.I) := by
  have h := LFunction_chi3_conj (1 / 2 + (t : ℂ) * Complex.I)
  have hc : (starRingEnd ℂ) ((1 : ℂ) / 2 + (t : ℂ) * Complex.I) = 1 / 2 - (t : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [Complex.add_re, Complex.mul_re, Complex.sub_re]
    · simp [Complex.add_im, Complex.mul_im, Complex.sub_im]
  rw [hc] at h
  rw [← h, Complex.conj_conj]

/-- **The on-line value-product is a genuine non-negative real.** `L(½+it)·L(½−it) = ‖L(½+it)‖²` — the
    conjugate-pair product across the buddy `t ↦ −t` (`LFunction_chi3_line_conj`). The two fibre
    differences at `+t` and `−t` multiply to a single real quantity. -/
theorem chi3_line_prod_eq_normSq (t : ℝ) :
    DirichletCharacter.LFunction ChiThree.χ3 (1 / 2 + (t : ℂ) * Complex.I)
        * DirichletCharacter.LFunction ChiThree.χ3 (1 / 2 - (t : ℂ) * Complex.I)
      = ((‖DirichletCharacter.LFunction ChiThree.χ3 (1 / 2 + (t : ℂ) * Complex.I)‖ ^ 2 : ℝ) : ℂ) := by
  rw [← LFunction_chi3_line_conj t, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- **A χ₃ zero on the line is a real-axis condition.** `L(½+it, χ₃) = 0 ⟺ ‖L(½+it, χ₃)‖² = 0` — the
    vanishing of the genuine real quantity `‖L‖²` (equal, via Schwarz, to the conjugate-pair product
    `L(½+it)·L(½−it)`, `chi3_line_prod_eq_normSq`). Combined with `chi3_zero_iff_fibre_balance`
    (`L = 0 ⟺ fibrePlus = fibreMinus`), an on-line zero is the **self-dual** event: the positive and
    negative character fibres balance, and that balance reads off as a single real-axis crossing.

    **Honest scope (Rule Five):** this is the on-line reality/self-duality shadow only. It does NOT prove
    `Re ρ = ½`; it characterizes zeros *already on the line* as real-axis self-dual events. The forcing of
    the zeros onto the line is the separate FTA/winding content, not this lemma. -/
theorem chi3_line_zero_iff_real (t : ℝ) :
    DirichletCharacter.LFunction ChiThree.χ3 (1 / 2 + (t : ℂ) * Complex.I) = 0
      ↔ ‖DirichletCharacter.LFunction ChiThree.χ3 (1 / 2 + (t : ℂ) * Complex.I)‖ ^ 2 = 0 := by
  rw [pow_eq_zero_iff (by norm_num), norm_eq_zero]

end Chi3Fibre

/-! ## Character-agnostic fibre cancellation — on the line, unconditional

The cancellation `L = 0 ⟺ fibres cancel` is **not** special to χ₃. For **any** Dirichlet character of
**any** modulus, `L(χ,s)` is the χ-weighted sum of the residue-class fibres `F_j(s) = N^{-s}·ζ_H(j/N,s)`
(Mathlib's `ZMod.LFunction`, the Hurwitz-zeta continuation), valid for **all `s` — in particular on the
critical line `Re s = ½`**. So a zero is exactly a balance of the fibres, on the line, unconditionally.
This says nothing about *where* the zeros are (off-line is the separate forcing); it says the zero **is**
the fibre cancellation, everywhere the L-function is defined. -/

namespace DirichletFibre

open HurwitzZeta in
/-- The **character-agnostic residue-class fibre** `F_j(s) = N^{-s} · ζ_H(j/N, s)` — the continued
    `Σ_{n ≡ j (N)} n^{-s}`, valid for all `s`. -/
noncomputable def fibre (N : ℕ) [NeZero N] (j : ZMod N) (s : ℂ) : ℂ :=
  (N : ℂ) ^ (-s) * hurwitzZeta (toAddCircle j) s

/-- **`L(χ,s)` is the χ-weighted fibre sum** — for every character, every `s` (the Hurwitz continuation,
    so on the critical line too). -/
theorem LFunction_eq_fibre_sum {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) :
    DirichletCharacter.LFunction χ s = ∑ j : ZMod N, χ j * fibre N j s := by
  rw [show DirichletCharacter.LFunction χ s = ZMod.LFunction (fun j => χ j) s from rfl,
      ZMod.LFunction, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => by rw [fibre]; ring)

/-- **The cancellation, on the line and everywhere, character-agnostic, unconditional.** A zero of any
    Dirichlet `L`-function is *exactly* a balance of its residue-class fibres — including on the
    critical line. (`chi3_zero_iff_fibre_balance` is the `N=3` instance: `χ₃ = (0,1,−1)` collapses the
    sum to `fibrePlus − fibreMinus`.) -/
theorem zero_iff_fibre_cancellation {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) :
    DirichletCharacter.LFunction χ s = 0 ↔ ∑ j : ZMod N, χ j * fibre N j s = 0 := by
  rw [LFunction_eq_fibre_sum]

end DirichletFibre
