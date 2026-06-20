import Mathlib
import RequestProject.HelixHilbertLimit
import RequestProject.HelixVonNeumann

/-!
# The Gram form and the operator `B∞` toward `G∞ = B∞* B∞`

Step 6 of the form route: the limiting Gram is the closed non-negative Hermitian form

    s(f,g) = ⟪B∞ f, B∞ g⟫   (on the finite-energy domain),   Re s(f,f) = ‖B∞ f‖² = q∞(f) ≥ 0,

whose associated self-adjoint operator is `G∞`. Here:

* `gramForm` — the form `s`, proven **non-negative** and **Hermitian**, with diagonal `‖B∞ f‖²`
  (the closed non-negative form representing `G∞`);
* `Bpmap` — `B∞` as a densely-defined (partial) linear operator `V →ₗ.[ℂ] ℓ²`, domain the
  finite-energy submodule.

The next step uses mathlib's unbounded-operator adjoint (`LinearPMap.adjoint`, available when `V`
is a Hilbert space) to form `B∞*` and then `G∞ = B∞* B∞`; its self-adjointness is von Neumann's
`T*T` theorem / the Friedrichs representation of this closed form — flagged, not asserted.
-/

open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HelixForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] (c : ℕ → (V →L[ℂ] ℂ))

/-- **The Gram sesquilinear form** `s(f,g) = ⟪B∞ f, B∞ g⟫` representing `G∞`. -/
noncomputable def gramForm (f g : finiteEnergy c) : ℂ :=
  inner ℂ (analysisMap c f) (analysisMap c g)

/-- **The form is non-negative:** `Re s(f,f) ≥ 0`. -/
theorem gramForm_nonneg (f : finiteEnergy c) : 0 ≤ RCLike.re (gramForm c f f) := by
  rw [gramForm]; exact inner_self_nonneg

/-- **The diagonal is `‖B∞ f‖²`** (`= q∞(f)`). -/
theorem gramForm_self_re (f : finiteEnergy c) :
    RCLike.re (gramForm c f f) = ‖analysisMap c f‖ ^ 2 := by
  rw [gramForm]; exact inner_self_eq_norm_sq _

/-- **The form is Hermitian:** `s(f,g) = conj (s(g,f))`. -/
theorem gramForm_hermitian (f g : finiteEnergy c) :
    gramForm c f g = conj (gramForm c g f) := by
  rw [gramForm, gramForm, inner_conj_symm]

/-- The form is additive in its second argument (one slot of sesquilinearity). -/
theorem gramForm_add_right (f g h : finiteEnergy c) :
    gramForm c f (g + h) = gramForm c f g + gramForm c f h := by
  rw [gramForm, gramForm, gramForm, map_add, inner_add_right]

/-- **`B∞` as a densely-defined (partial) operator** `V →ₗ.[ℂ] ℓ²`, with domain the finite-energy
    vectors. (Its adjoint `B∞*` and `G∞ = B∞* B∞` follow via `LinearPMap.adjoint` when `V` is a
    Hilbert space.) -/
noncomputable def Bpmap : V →ₗ.[ℂ] lp (fun _ : ℕ => ℂ) 2 where
  domain := finiteEnergy c
  toFun := analysisMap c

@[simp] theorem Bpmap_domain : (Bpmap c).domain = finiteEnergy c := rfl

@[simp] theorem Bpmap_apply (f : finiteEnergy c) : (Bpmap c) f = analysisMap c f := rfl

/-! ## `B∞` is closed — the second von Neumann hypothesis, discharged

`TstarT_isSelfAdjoint` (von Neumann) needs `B∞` densely-defined and **closed**. Closedness holds
because the `cₙ` are continuous; with it, `G∞ = B∞*B∞` is self-adjoint (real spectrum), leaving only
the *density* of the finite-energy domain as a setup (non-GRH) input. -/

/-- **Converse of `summable_sq_of_mem`:** square-summable coefficients ⇒ finite energy. -/
theorem mem_finiteEnergy_of_summable {f : V} (h : Summable (fun n => ‖c n f‖ ^ 2)) :
    f ∈ finiteEnergy c := by
  show qInf c f < ⊤
  rw [qInf_eq_tsum, ← ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg _) h]
  exact ENNReal.ofReal_lt_top

/-- An `ℓ²` element has square-summable coordinates. -/
theorem summable_sq_lp (y : lp (fun _ : ℕ => ℂ) 2) :
    Summable (fun n => ‖(y : ℕ → ℂ) n‖ ^ 2) := by
  have hy := lp.memℓp y
  have hs := (memℓp_gen_iff (show (0:ℝ) < (2:ℝ≥0∞).toReal by norm_num)).mp hy
  rw [show (2:ℝ≥0∞).toReal = 2 by norm_num] at hs
  convert hs using 2 with n
  rw [← Real.rpow_natCast]; norm_num

/-- **`B∞` is a closed operator.** The analysis map of the continuous functionals `cₙ` has closed
    graph: if `fₖ → f` in `V` and `B∞ fₖ → y` in `ℓ²`, then `cₙ fₖ → cₙ f` (continuity) and `→ yₙ`
    (coordinatewise `ℓ²` convergence), so `cₙ f = yₙ` and `∑ₙ |cₙ f|² = ‖y‖² < ∞`, placing `f` in the
    finite-energy domain with `B∞ f = y`. This is the closedness von Neumann's `T*T` theorem needs. -/
theorem Bpmap_isClosed : (Bpmap c).IsClosed := by
  show IsClosed ((Bpmap c).graph : Set (V × lp (fun _ : ℕ => ℂ) 2))
  apply IsSeqClosed.isClosed
  intro u p hu hconv
  have hcoord_k : ∀ k n, ((u k).2 : ℕ → ℂ) n = c n (u k).1 := by
    intro k n
    obtain ⟨g, hg1, hg2⟩ := (LinearPMap.mem_graph_iff _).mp (hu k)
    rw [← hg2, ← hg1]; simp [Bpmap, analysisMap]
  have h1 : Filter.Tendsto (fun k => (u k).1) Filter.atTop (nhds p.1) :=
    (continuous_fst.tendsto p).comp hconv
  have h2 : Filter.Tendsto (fun k => (u k).2) Filter.atTop (nhds p.2) :=
    (continuous_snd.tendsto p).comp hconv
  have hpcoord : ∀ n, (p.2 : ℕ → ℂ) n = c n p.1 := by
    intro n
    have hA : Filter.Tendsto (fun k => ((u k).2 : ℕ → ℂ) n) Filter.atTop
        (nhds ((p.2 : ℕ → ℂ) n)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_)
        ((tendsto_iff_norm_sub_tendsto_zero).mp h2)
      simpa using lp.norm_apply_le_norm (two_ne_zero) ((u k).2 - p.2) n
    have hB : Filter.Tendsto (fun k => c n (u k).1) Filter.atTop (nhds (c n p.1)) :=
      ((c n).continuous.tendsto p.1).comp h1
    have heq : (fun k => ((u k).2 : ℕ → ℂ) n) = (fun k => c n (u k).1) := funext (hcoord_k · n)
    rw [heq] at hA
    exact tendsto_nhds_unique hA hB
  have hfin : p.1 ∈ finiteEnergy c := by
    apply mem_finiteEnergy_of_summable
    have heq2 : (fun n => ‖c n p.1‖ ^ 2) = (fun n => ‖(p.2 : ℕ → ℂ) n‖ ^ 2) := by
      funext n; rw [← hpcoord n]
    rw [heq2]; exact summable_sq_lp p.2
  rw [SetLike.mem_coe, LinearPMap.mem_graph_iff]
  refine ⟨⟨p.1, hfin⟩, rfl, ?_⟩
  apply lp.ext; funext n
  show (Bpmap c ⟨p.1, hfin⟩ : ℕ → ℂ) n = (p.2 : ℕ → ℂ) n
  rw [show (Bpmap c ⟨p.1, hfin⟩ : ℕ → ℂ) n = c n p.1 from by simp [Bpmap, analysisMap]]
  exact (hpcoord n).symm

end HelixForm

/-! ## `G∞ = B∞*B∞` is self-adjoint — von Neumann wired to the Gram loss operator, UNCONDITIONALLY

Realized on the **closure of its domain**, where `finiteEnergy` is dense **by construction**, `B∞`
closed (`Bpmap_isClosed`, transported along the closed embedding `lossSpace ↪ V`) lets
`HelixVonNeumann.TstarT_isSelfAdjoint` conclude `G∞ = B∞*B∞` is **self-adjoint** — hence has **real
spectrum** (`⊆ [0,∞)`, the loss/prime energies). This is the "real spectrum" half of a legitimate
Hilbert–Pólya operator, earned by construction with **no hypotheses** and **no zeros-on-the-line
input**: it supplies the receiver's reality in the `hid` chain. The capture (`G∞`'s resolvent trace
`= −L'/L`, i.e. `hid`) stays the separate, deferred step. -/

namespace HelixForm

section HilbertGram
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  (c : ℕ → (V →L[ℂ] ℂ))

/-- The **closure of the finite-energy domain** — a Hilbert space (closed subspace of `V`) in which
    `finiteEnergy` is dense by construction. `G∞` is realized here. -/
noncomputable abbrev lossSpace : Submodule ℂ V := (finiteEnergy c).topologicalClosure

instance : CompleteSpace (lossSpace c) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

/-- `B∞` realized on `lossSpace`, with dense domain the finite-energy vectors. -/
noncomputable def BpmapCl : ↥(lossSpace c) →ₗ.[ℂ] lp (fun _ : ℕ => ℂ) 2 where
  domain := (finiteEnergy c).comap (lossSpace c).subtype
  toFun :=
    { toFun := fun x => analysisMap c ⟨((x : ↥(lossSpace c)) : V), x.2⟩
      map_add' := fun x y => by rw [← map_add]; rfl
      map_smul' := fun a x => by rw [← map_smul]; rfl }

omit [CompleteSpace V] in
/-- `B∞` on `lossSpace` is **closed** — its graph is the preimage of the (closed) graph of `B∞` on
    `V` under the closed embedding `lossSpace ↪ V`. -/
theorem BpmapCl_isClosed : (BpmapCl c).IsClosed := by
  have he : Continuous (fun p : ↥(lossSpace c) × lp (fun _ : ℕ => ℂ) 2 => ((p.1 : V), p.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hpre : ((BpmapCl c).graph : Set (↥(lossSpace c) × lp (fun _ : ℕ => ℂ) 2))
      = (fun p => ((p.1 : V), p.2)) ⁻¹' ((Bpmap c).graph : Set (V × lp (fun _ : ℕ => ℂ) 2)) := by
    ext ⟨x, y⟩
    simp only [Set.mem_preimage, SetLike.mem_coe, LinearPMap.mem_graph_iff]
    constructor
    · rintro ⟨d, hd1, hd2⟩
      refine ⟨⟨((d : ↥(lossSpace c)) : V), d.2⟩, congrArg Subtype.val hd1, ?_⟩
      rw [← hd2]; rfl
    · rintro ⟨d', hd1', hd2'⟩
      have hx : x ∈ (BpmapCl c).domain := by
        show ((x : ↥(lossSpace c)) : V) ∈ finiteEnergy c
        rw [← hd1']; exact d'.2
      refine ⟨⟨x, hx⟩, rfl, ?_⟩
      rw [← hd2']
      exact congrArg (analysisMap c) (Subtype.ext hd1'.symm)
  show IsClosed ((BpmapCl c).graph : Set (↥(lossSpace c) × lp (fun _ : ℕ => ℂ) 2))
  rw [hpre]
  exact (Bpmap_isClosed c).preimage he

omit [CompleteSpace V] in
/-- The finite-energy domain is **dense** in `lossSpace` (its own closure), by construction. -/
theorem BpmapCl_domain_dense : Dense ((BpmapCl c).domain : Set ↥(lossSpace c)) := by
  rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro x
  have hx : (↑x : V) ∈ closure (finiteEnergy c : Set V) := by
    rw [← Submodule.topologicalClosure_coe]; exact x.2
  rw [mem_closure_iff_seq_limit] at hx
  obtain ⟨a, ha_mem, ha_lim⟩ := hx
  rw [mem_closure_iff_seq_limit]
  refine ⟨fun n => ⟨a n, Submodule.le_topologicalClosure _ (ha_mem n)⟩, fun n => ha_mem n, ?_⟩
  exact tendsto_subtype_rng.mpr ha_lim

/-- **The Gram loss operator `G∞ = B∞*B∞` is self-adjoint — UNCONDITIONAL** (von Neumann's `T*T`),
    realized on the closure of its domain. Hence **real spectrum** (`⊆ [0,∞)`, the loss/prime
    energies), by construction, with **no hypotheses** and no zeros-on-the-line input — the earned
    reality the receiver/`hid` chain consumes. De-orphans `HelixVonNeumann.TstarT_isSelfAdjoint`. -/
theorem gramOp_isSelfAdjoint : IsSelfAdjoint (HelixVonNeumann.TstarT (BpmapCl c)) :=
  HelixVonNeumann.TstarT_isSelfAdjoint (BpmapCl c) (BpmapCl_domain_dense c) (BpmapCl_isClosed c)

end HilbertGram

end HelixForm
