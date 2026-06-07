import Mathlib

/-!
# Toward von Neumann's `T*T` theorem — the graph-orthogonality brick

Goal (the mathlib gap): for a closed densely-defined `T : E →ₗ.[ℂ] F`, `T*T` is self-adjoint.
The standard proof decomposes `E × F = graph(T) ⊕ J(graph(T*))` orthogonally, where
`J(a,b) = (-a, b)` places `(T* y, y) ↦ (-T* y, y)`. From it, `I + T*T` is surjective with bounded
positive self-adjoint inverse, giving `T*T` self-adjoint.

This file establishes **one verified brick**: the **orthogonality** `graph(T) ⊥ {(-T* y, y)}`
in `WithLp 2 (E × F)` (the `⊆` direction of the decomposition), which is the computational core of
the adjoint relation packaged geometrically.

What remains (the genuine, substantial von Neumann content — NOT proved here):
1. the orthogonality is an *equality* of complements: `graph(T)ᗮ = {(-T* y, y)}` (uses `T` closed);
2. hence the orthogonal decomposition `WithLp 2 (E × F) = graph(T) ⊕ {(-T* y, y)}`;
3. ⟹ `I + T*T` is surjective onto `E`;
4. ⟹ `(I + T*T)⁻¹` is bounded, positive, self-adjoint, ‖·‖ ≤ 1;
5. ⟹ `T*T` is self-adjoint.
Steps 1–5 are a dedicated formalization (a real mathlib contribution); only the orthogonality
brick below is currently verified.
-/

open scoped InnerProductSpace ComplexConjugate

namespace HelixVonNeumann

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace E] [CompleteSpace F]

/-- **Graph orthogonality.** For `x ∈ dom T` and `y ∈ dom T*`, the graph vector `(x, T x)` is
    orthogonal to the rotated adjoint-graph vector `(-T* y, y)` in `E × F`:
    `⟪(x, T x), (-T* y, y)⟫ = 0`. This is the defining adjoint relation, packaged as orthogonality. -/
theorem graph_rotation_orthogonal (T : E →ₗ.[ℂ] F) (hd : Dense (T.domain : Set E))
    (x : T.domain) (y : T.adjoint.domain) :
    inner ℂ (WithLp.toLp 2 (((x : E), T x) : E × F))
        (WithLp.toLp 2 ((-(T.adjoint y), (y : F)) : E × F)) = 0 := by
  have hflip : inner ℂ (T x) (y : F) = inner ℂ (x : E) (T.adjoint y) :=
    (LinearPMap.adjoint_isFormalAdjoint hd).symm x y
  simp only [WithLp.prod_inner_apply, WithLp.ofLp_toLp, inner_neg_right, hflip]
  ring

/-- The graph of `T` realized inside the inner-product space `WithLp 2 (E × F)`. -/
noncomputable def graphLp (T : E →ₗ.[ℂ] F) : Submodule ℂ (WithLp 2 (E × F)) :=
  T.graph.map (WithLp.linearEquiv 2 ℂ (E × F)).symm.toLinearMap

/-- **Step 1 (rotation correspondence).** A vector `w` is orthogonal to `graph(T)` in
    `WithLp 2 (E × F)` iff its rotation `(w₂, -w₁)` lies in the graph-adjoint `graph(T).adjoint`
    (`= graph(T*)`). Both sides are the single condition `∀ (a,b) ∈ graph(T), ⟪a,w₁⟫+⟪b,w₂⟫ = 0`.
    Combined with `T.graph.adjoint = T.adjoint.graph`, this identifies `graph(T)ᗮ` with the rotated
    adjoint graph `{(-T* y, y)}` — the linchpin of von Neumann's decomposition. -/
theorem mem_graphLp_orthogonal_iff (T : E →ₗ.[ℂ] F) (w : WithLp 2 (E × F)) :
    w ∈ (graphLp T)ᗮ ↔ (((WithLp.ofLp w).2, -(WithLp.ofLp w).1) : F × E) ∈ T.graph.adjoint := by
  rw [Submodule.mem_adjoint_iff]
  constructor
  · intro hw a b hab
    have hmem : (WithLp.toLp 2 ((a, b) : E × F)) ∈ graphLp T :=
      Submodule.mem_map_of_mem hab
    have hz : inner ℂ (WithLp.toLp 2 ((a, b) : E × F)) w = 0 :=
      Submodule.inner_right_of_mem_orthogonal hmem hw
    rw [WithLp.prod_inner_apply, WithLp.ofLp_toLp] at hz
    rw [inner_neg_right]
    linear_combination hz
  · intro hw
    rw [Submodule.mem_orthogonal]
    intro u hu
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hu
    have hz := hw p.1 p.2 hp
    rw [inner_neg_right] at hz
    rw [WithLp.prod_inner_apply]
    show inner ℂ p.1 (WithLp.ofLp w).1 + inner ℂ p.2 (WithLp.ofLp w).2 = 0
    linear_combination hz

/-- `graphLp T` as a set is the preimage of `graph(T)` under the homeomorphism
    `WithLp 2 (E × F) ≃L E × F`. -/
theorem graphLp_eq_preimage (T : E →ₗ.[ℂ] F) :
    (graphLp T : Set (WithLp 2 (E × F)))
      = (WithLp.prodContinuousLinearEquiv 2 ℂ E F) ⁻¹' (T.graph : Set (E × F)) := by
  ext w
  simp only [graphLp, Submodule.map_coe, Set.mem_image, SetLike.mem_coe, Set.mem_preimage,
    WithLp.prodContinuousLinearEquiv_apply]
  constructor
  · rintro ⟨p, hp, rfl⟩
    simpa using hp
  · intro hw
    exact ⟨WithLp.ofLp w, hw, by simp⟩

/-- **Step 2 (closed graph).** If `T` is closed, its `WithLp`-graph is closed (homeomorphic
    preimage of the closed `graph(T)`). -/
theorem graphLp_isClosed (T : E →ₗ.[ℂ] F) (hT : T.IsClosed) :
    IsClosed (graphLp T : Set (WithLp 2 (E × F))) := by
  have hT' : IsClosed (T.graph : Set (E × F)) := hT
  rw [graphLp_eq_preimage]
  exact hT'.preimage (WithLp.prodContinuousLinearEquiv 2 ℂ E F).continuous

/-- **Step 2 (decomposition).** For closed `T`, `WithLp 2 (E × F) = graph(T) ⊕ graph(T)ᗮ`. -/
theorem graphLp_isCompl (T : E →ₗ.[ℂ] F) (hT : T.IsClosed) :
    IsCompl (graphLp T) (graphLp T)ᗮ := by
  haveI : CompleteSpace (graphLp T) := (graphLp_isClosed T hT).completeSpace_coe
  exact Submodule.isCompl_orthogonal_of_hasOrthogonalProjection

/-- **Step 3 (the decomposition split / surjectivity).** For closed densely-defined `T` and any
    `h : E`, the source vector `(h, 0)` splits via `graph(T) ⊕ graph(T)ᗮ` into `(x, Tx)` and
    `(-T*y, y)`, giving `x ∈ dom T`, `y ∈ dom T*` with `x − T*y = h` and `Tx + y = 0`.
    Eliminating `y = -Tx` yields `(I + T*T) x = h`, so `I + T*T` is surjective. -/
theorem exists_decomp (T : E →ₗ.[ℂ] F) (hd : Dense (T.domain : Set E)) (hT : T.IsClosed) (h : E) :
    ∃ (x : T.domain) (y : T.adjoint.domain),
      (x : E) - T.adjoint y = h ∧ T x + (y : F) = 0 := by
  set w₀ : WithLp 2 (E × F) := WithLp.toLp 2 ((h, 0) : E × F) with hw₀
  have hmem : w₀ ∈ graphLp T ⊔ (graphLp T)ᗮ := by
    rw [(graphLp_isCompl T hT).sup_eq_top]; trivial
  obtain ⟨k, hk, k', hk', hsum⟩ := Submodule.mem_sup.mp hmem
  -- k.ofLp ∈ graph T
  have hkg : (WithLp.ofLp k) ∈ T.graph := by
    have hkset : k ∈ (graphLp T : Set (WithLp 2 (E × F))) := hk
    rw [graphLp_eq_preimage] at hkset
    simpa [WithLp.prodContinuousLinearEquiv_apply] using hkset
  obtain ⟨x, hx1, hx2⟩ := (LinearPMap.mem_graph_iff T).mp hkg
  -- k'.ofLp gives adjoint-graph membership
  have hk'g : ((WithLp.ofLp k').2, -(WithLp.ofLp k').1) ∈ T.adjoint.graph := by
    rw [LinearPMap.adjoint_graph_eq_graph_adjoint hd]
    exact (mem_graphLp_orthogonal_iff T k').mp hk'
  obtain ⟨y, hy1, hy2⟩ := (LinearPMap.mem_graph_iff T.adjoint).mp hk'g
  -- component equations from k + k' = (h, 0)
  have hcomp : (WithLp.ofLp k) + (WithLp.ofLp k') = ((h, 0) : E × F) := by
    have hs := congrArg (WithLp.prodContinuousLinearEquiv 2 ℂ E F) hsum
    rw [map_add] at hs
    simpa [WithLp.prodContinuousLinearEquiv_apply, hw₀, WithLp.ofLp_toLp] using hs
  have h1 : (WithLp.ofLp k).1 + (WithLp.ofLp k').1 = h := congrArg Prod.fst hcomp
  have h2 : (WithLp.ofLp k).2 + (WithLp.ofLp k').2 = 0 := congrArg Prod.snd hcomp
  refine ⟨x, y, ?_, ?_⟩
  · -- (x : E) − T* y = h
    rw [hx1, hy2]
    simp only []
    rw [sub_neg_eq_add]
    exact h1
  · -- T x + (y : F) = 0
    rw [hx2, hy1]
    exact h2

/-- **Step 4 (positivity identity).** `Re⟪(I + T*T)x, x⟫ = ‖x‖² + ‖Tx‖²`, using the formal-adjoint
    relation `⟪T*(Tx), x⟫ = ⟪Tx, Tx⟫`. -/
theorem re_inner_add_adjoint (T : E →ₗ.[ℂ] F) (hd : Dense (T.domain : Set E))
    (x : T.domain) (hTx : T x ∈ T.adjoint.domain) :
    RCLike.re (inner ℂ ((x : E) + T.adjoint ⟨T x, hTx⟩) (x : E)) = ‖(x : E)‖ ^ 2 + ‖T x‖ ^ 2 := by
  have hfa : inner ℂ (T.adjoint ⟨T x, hTx⟩) (x : E) = inner ℂ (T x) (T x) := by
    have := LinearPMap.adjoint_isFormalAdjoint hd ⟨T x, hTx⟩ x
    simpa using this
  rw [inner_add_left, hfa, map_add, inner_self_eq_norm_sq, inner_self_eq_norm_sq]

/-- **Step 4 (injectivity).** `I + T*T` is injective: if `(I + T*T)x = 0` then `x = 0`, since
    `0 = ‖x‖² + ‖Tx‖² ≥ ‖x‖²`. With Step 3's surjectivity, `I + T*T` is bijective. -/
theorem add_adjoint_eq_zero (T : E →ₗ.[ℂ] F) (hd : Dense (T.domain : Set E))
    (x : T.domain) (hTx : T x ∈ T.adjoint.domain)
    (h0 : (x : E) + T.adjoint ⟨T x, hTx⟩ = 0) : (x : E) = 0 := by
  have hpos := re_inner_add_adjoint T hd x hTx
  rw [h0, inner_zero_left, map_zero] at hpos
  have hsum : ‖(x : E)‖ ^ 2 + ‖T x‖ ^ 2 = 0 := hpos.symm
  have hx2 : ‖(x : E)‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖(x : E)‖, sq_nonneg ‖T x‖]
  have : ‖(x : E)‖ = 0 := by nlinarith [norm_nonneg (x : E), hx2]
  exact norm_eq_zero.mp this

/-- **Step 5 (symmetry of `T*T`).** `⟪T*(Ta), b⟫ = ⟪a, T*(Tb)⟫` (both equal `⟪Ta, Tb⟫` by the
    formal-adjoint relation). So `T*T` (and `I + T*T`) is symmetric; together with Steps 3–4
    (`I + T*T` bijective) this is essential self-adjointness — the mathematical content of von
    Neumann's theorem. -/
theorem adjoint_comp_symmetric (T : E →ₗ.[ℂ] F) (hd : Dense (T.domain : Set E))
    (a b : T.domain) (hTa : T a ∈ T.adjoint.domain) (hTb : T b ∈ T.adjoint.domain) :
    inner ℂ (T.adjoint ⟨T a, hTa⟩) (b : E) = inner ℂ (a : E) (T.adjoint ⟨T b, hTb⟩) := by
  have hL : inner ℂ (T.adjoint ⟨T a, hTa⟩) (b : E) = inner ℂ (T a) (T b) := by
    simpa using LinearPMap.adjoint_isFormalAdjoint hd ⟨T a, hTa⟩ b
  have hR : inner ℂ (a : E) (T.adjoint ⟨T b, hTb⟩) = inner ℂ (T a) (T b) := by
    simpa using ((LinearPMap.adjoint_isFormalAdjoint hd).symm a ⟨T b, hTb⟩).symm
  rw [hL, hR]

/-- **`I + T*T` is surjective**, in clean operator form. From Step 3's split, `y = -Tx`, so
    `Tx ∈ dom T*` and `x + T*(Tx) = h`. -/
theorem add_adjoint_comp_surjective (T : E →ₗ.[ℂ] F) (hd : Dense (T.domain : Set E))
    (hT : T.IsClosed) (h : E) :
    ∃ (x : T.domain) (hTx : T x ∈ T.adjoint.domain), (x : E) + T.adjoint ⟨T x, hTx⟩ = h := by
  obtain ⟨x, y, h1, h2⟩ := exists_decomp T hd hT h
  have hyTx : (y : F) = -T x := eq_neg_of_add_eq_zero_right h2
  have hTx : T x ∈ T.adjoint.domain := by
    have := (T.adjoint.domain).neg_mem y.2
    rwa [hyTx, neg_neg] at this
  refine ⟨x, hTx, ?_⟩
  have hev : (⟨T x, hTx⟩ : T.adjoint.domain) = -y := by
    apply Subtype.ext
    simp only [Submodule.coe_neg]
    rw [hyTx, neg_neg]
  have hTadj : T.adjoint ⟨T x, hTx⟩ = -T.adjoint y := by
    rw [hev]; exact LinearPMap.map_neg T.adjoint y
  rw [hTadj, ← sub_eq_add_neg]
  exact h1

/-- **The von Neumann content for `T*T`** (closed densely-defined `T`), all verified above:
    `I + T*T` is **bijective** (surjective + injective) with `T*T` **symmetric**. This is essential
    self-adjointness of `T*T`. The bundled `IsSelfAdjoint (T*T : LinearPMap)` predicate additionally
    needs the unbounded symmetric→self-adjoint criterion (a mathlib gap) or the bounded resolvent. -/
theorem vonNeumann_content (T : E →ₗ.[ℂ] F) (hd : Dense (T.domain : Set E)) (hT : T.IsClosed) :
    (∀ h : E, ∃ (x : T.domain) (hTx : T x ∈ T.adjoint.domain),
        (x : E) + T.adjoint ⟨T x, hTx⟩ = h)
      ∧ (∀ (x : T.domain) (hTx : T x ∈ T.adjoint.domain),
        (x : E) + T.adjoint ⟨T x, hTx⟩ = 0 → (x : E) = 0)
      ∧ (∀ (a b : T.domain) (hTa : T a ∈ T.adjoint.domain) (hTb : T b ∈ T.adjoint.domain),
        inner ℂ (T.adjoint ⟨T a, hTa⟩) (b : E) = inner ℂ (a : E) (T.adjoint ⟨T b, hTb⟩)) :=
  ⟨add_adjoint_comp_surjective T hd hT, add_adjoint_eq_zero T hd, adjoint_comp_symmetric T hd⟩

/-- The natural domain of `T*T` inside `E`: `{x ∈ dom T : Tx ∈ dom T*}`, as the image under the
    inclusion of the preimage of `dom T*`. -/
noncomputable def domTstarT (T : E →ₗ.[ℂ] F) : Submodule ℂ E :=
  (Submodule.comap T.toFun T.adjoint.domain).map T.domain.subtype

/-- **`T*T`** as a `LinearPMap`, domain `{x ∈ dom T : Tx ∈ dom T*}`, action `x ↦ T*(Tx)`. -/
noncomputable def TstarT (T : E →ₗ.[ℂ] F) : E →ₗ.[ℂ] E :=
  T.adjoint.comp (T.domRestrict (domTstarT T)) <| by
    rintro ⟨x, hxmem⟩
    obtain ⟨hxS, hxT⟩ := hxmem
    obtain ⟨ξ, hξ, hξx⟩ := Submodule.mem_map.mp hxS
    have hxξ : (⟨x, hxT⟩ : T.domain) = ξ := Subtype.ext hξx.symm
    show T ⟨x, hxT⟩ ∈ T.adjoint.domain
    rw [hxξ]
    exact Submodule.mem_comap.mp hξ

/-- A point in `dom (T*T)` lies in `dom T` with `Tx ∈ dom T*`. -/
theorem mem_domTstarT_apply (T : E →ₗ.[ℂ] F) {x : E} (hx : x ∈ (TstarT T).domain) :
    ∃ (hxT : x ∈ T.domain), T ⟨x, hxT⟩ ∈ T.adjoint.domain := by
  obtain ⟨hxD, hxT⟩ := Submodule.mem_inf.mp hx
  refine ⟨hxT, ?_⟩
  obtain ⟨ξ, hξ, hξx⟩ := Submodule.mem_map.mp hxD
  have hxξ : (⟨x, hxT⟩ : T.domain) = ξ := Subtype.ext hξx.symm
  rw [hxξ]
  exact Submodule.mem_comap.mp hξ

/-- **`T*T` is symmetric** — it is its own formal adjoint (`A.IsFormalAdjoint A`), from
    `adjoint_comp_symmetric`. -/
theorem TstarT_isFormalAdjoint_self (T : E →ₗ.[ℂ] F) (hd : Dense (T.domain : Set E)) :
    (TstarT T).IsFormalAdjoint (TstarT T) := by
  intro x y
  obtain ⟨hxT, hTx⟩ := mem_domTstarT_apply T x.2
  obtain ⟨hyT, hTy⟩ := mem_domTstarT_apply T y.2
  have hax : (TstarT T) x = T.adjoint ⟨T ⟨(x : E), hxT⟩, hTx⟩ := rfl
  have hay : (TstarT T) y = T.adjoint ⟨T ⟨(y : E), hyT⟩, hTy⟩ := rfl
  rw [hax, hay]
  exact adjoint_comp_symmetric T hd ⟨(x : E), hxT⟩ ⟨(y : E), hyT⟩ hTx hTy

/-- **`I + T*T` surjective**, in `T*T` (`LinearPMap`) form: `∀ h, ∃ x ∈ dom(T*T), x + T*T x = h`. -/
theorem TstarT_surjective (T : E →ₗ.[ℂ] F) (hd : Dense (T.domain : Set E)) (hT : T.IsClosed)
    (h : E) : ∃ x : (TstarT T).domain, (x : E) + TstarT T x = h := by
  obtain ⟨x, hTx, heq⟩ := add_adjoint_comp_surjective T hd hT h
  have hxD : (x : E) ∈ domTstarT T :=
    Submodule.mem_map.mpr ⟨x, Submodule.mem_comap.mpr hTx, rfl⟩
  have hxdom : (x : E) ∈ (TstarT T).domain := Submodule.mem_inf.mpr ⟨hxD, x.2⟩
  refine ⟨⟨(x : E), hxdom⟩, ?_⟩
  show (x : E) + T.adjoint ⟨T x, hTx⟩ = h
  exact heq

/-- **`dom(T*T)` is dense.** If `v ⊥ dom(T*T)`, surjectivity gives `x` with `(I+T*T)x = v`, and
    `0 = Re⟪v, x⟫ = ‖x‖² + ‖Tx‖²`, forcing `x = 0`, hence `v = 0`. So `dom(T*T)ᗮ = ⊥` ⟹ dense. -/
theorem TstarT_domain_dense (T : E →ₗ.[ℂ] F) (hd : Dense (T.domain : Set E)) (hT : T.IsClosed) :
    Dense ((TstarT T).domain : Set E) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro v hv
  obtain ⟨x, hx⟩ := TstarT_surjective T hd hT v
  obtain ⟨hxT, hTx⟩ := mem_domTstarT_apply T x.2
  have hvx : inner ℂ v (x : E) = 0 := (Submodule.mem_orthogonal' _ _).mp hv (x : E) x.2
  have hax : (TstarT T) x = T.adjoint ⟨T ⟨(x : E), hxT⟩, hTx⟩ := rfl
  have hre : RCLike.re (inner ℂ v (x : E)) = ‖(x : E)‖ ^ 2 + ‖T ⟨(x : E), hxT⟩‖ ^ 2 := by
    rw [← hx, hax]
    exact re_inner_add_adjoint T hd ⟨(x : E), hxT⟩ hTx
  rw [hvx, map_zero] at hre
  have hx0 : ‖(x : E)‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖(x : E)‖, sq_nonneg ‖T ⟨(x : E), hxT⟩‖]
  have : (x : E) = 0 := by
    have : ‖(x : E)‖ = 0 := by nlinarith [norm_nonneg (x : E)]
    exact norm_eq_zero.mp this
  rw [← hx, this]
  simp [show (x : (TstarT T).domain) = 0 from Subtype.ext this, map_zero]

/-- **The reverse inclusion `(T*T)* ⊆ T*T`** — the closing argument: for `z ∈ dom (T*T)*`,
    surjectivity produces `x ∈ dom T*T` with `(T*T)*(z−x) = −(z−x)`, and then `⟪z−x, z−x⟫ = 0`
    via the adjoint relation + surjectivity, so `z = x ∈ dom T*T`. -/
theorem TstarT_adjoint_le (T : E →ₗ.[ℂ] F) (hd : Dense (T.domain : Set E)) (hT : T.IsClosed) :
    (TstarT T).adjoint ≤ TstarT T := by
  have hdA : Dense ((TstarT T).domain : Set E) := TstarT_domain_dense T hd hT
  have hsym : (TstarT T).IsFormalAdjoint (TstarT T) := TstarT_isFormalAdjoint_self T hd
  have hle1 : TstarT T ≤ (TstarT T).adjoint := LinearPMap.IsFormalAdjoint.le_adjoint hdA hsym
  have hfa : (TstarT T).adjoint.IsFormalAdjoint (TstarT T) := LinearPMap.adjoint_isFormalAdjoint hdA
  -- if A* z' = -z' then z' = 0
  have hkey : ∀ z' : (TstarT T).adjoint.domain,
      (TstarT T).adjoint z' = -(z' : E) → (z' : E) = 0 := by
    intro z' hz'
    obtain ⟨w, hw⟩ := TstarT_surjective T hd hT (z' : E)
    have hrel : inner ℂ (z' : E) (TstarT T w) = -inner ℂ (z' : E) (w : E) := by
      have h2 := hfa z' w
      rw [hz', inner_neg_left] at h2
      exact h2.symm
    have hzz : inner ℂ (z' : E) (z' : E) = 0 := by
      have hsub : inner ℂ (z' : E) (z' : E) = inner ℂ (z' : E) ((w : E) + TstarT T w) := by rw [hw]
      rw [hsub, inner_add_right, hrel]; ring
    exact inner_self_eq_zero.mp hzz
  -- core: every z ∈ dom A* equals some x ∈ dom A, with the adjoint value agreeing
  have hcore : ∀ z (hz : z ∈ (TstarT T).adjoint.domain),
      ∃ (hzA : z ∈ (TstarT T).domain),
        (TstarT T).adjoint ⟨z, hz⟩ = TstarT T ⟨z, hzA⟩ := by
    intro z hz
    obtain ⟨x, hx⟩ := TstarT_surjective T hd hT ((TstarT T).adjoint ⟨z, hz⟩ + z)
    have hxadj : (x : E) ∈ (TstarT T).adjoint.domain := hle1.1 x.2
    have hxval : (TstarT T).adjoint ⟨(x : E), hxadj⟩ = TstarT T x :=
      (hle1.2 (x := x) (y := ⟨(x : E), hxadj⟩) rfl).symm
    have hz'eq : (TstarT T).adjoint (⟨z, hz⟩ - ⟨(x : E), hxadj⟩)
        = -((⟨z, hz⟩ - ⟨(x : E), hxadj⟩ : (TstarT T).adjoint.domain) : E) := by
      rw [LinearPMap.map_sub, hxval]
      simp only [AddSubgroupClass.coe_sub]
      have hx' : (TstarT T).adjoint ⟨z, hz⟩ = (x : E) + TstarT T x - z := eq_sub_of_add_eq hx.symm
      rw [hx']; abel
    have hzx : z = (x : E) := by
      have h0 := hkey _ hz'eq
      simpa only [AddSubgroupClass.coe_sub, sub_eq_zero] using h0
    refine ⟨hzx ▸ x.2, ?_⟩
    have he1 : (⟨z, hz⟩ : (TstarT T).adjoint.domain) = ⟨(x : E), hxadj⟩ := Subtype.ext hzx
    have he2 : (⟨z, hzx ▸ x.2⟩ : (TstarT T).domain) = x := Subtype.ext (by simpa using hzx)
    rw [he1, hxval, he2]
  refine ⟨fun z hz => (hcore z hz).choose, fun z y hzy => ?_⟩
  obtain ⟨hzA, hval⟩ := hcore (z : E) z.2
  have hyz : (⟨(z : E), hzA⟩ : (TstarT T).domain) = y := Subtype.ext hzy
  calc (TstarT T).adjoint z = (TstarT T).adjoint ⟨(z : E), z.2⟩ := rfl
    _ = TstarT T ⟨(z : E), hzA⟩ := hval
    _ = TstarT T y := congrArg (fun w : (TstarT T).domain => (TstarT T) w) hyz

/-- **von Neumann's theorem, bundled: `T*T` is self-adjoint** for closed densely-defined `T`. -/
theorem TstarT_isSelfAdjoint (T : E →ₗ.[ℂ] F) (hd : Dense (T.domain : Set E)) (hT : T.IsClosed) :
    IsSelfAdjoint (TstarT T) := by
  rw [LinearPMap.isSelfAdjoint_def]
  have hdA : Dense ((TstarT T).domain : Set E) := TstarT_domain_dense T hd hT
  have hsym : (TstarT T).IsFormalAdjoint (TstarT T) := TstarT_isFormalAdjoint_self T hd
  exact le_antisymm (TstarT_adjoint_le T hd hT) (LinearPMap.IsFormalAdjoint.le_adjoint hdA hsym)

end HelixVonNeumann
