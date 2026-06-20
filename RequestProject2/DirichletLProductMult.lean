import Mathlib
import RequestProject.DirichletLZeroCount
import RequestProject.XiWeierstrassFactor
import RequestProject.XiProductZeros

/-!
# Multiplicity-indexed Weierstrass product `LProductMult χ` for Dirichlet `L`

Character-`χ` port of `ZD.xiProductMult`. Reindexes the Weierstrass product by the multiset of
nontrivial zeros of `Λ_χ`: each zero `ρ` appears `lOrderNat χ ρ` times. The reusable, character-free
factor apparatus `ZD.xiWeierstrassTerm` (a pure `(ρ,z)`-function) carries over directly; only the
zero-set (`GRHSpectral.NontrivialZeros χ`), the order (`lOrderNat χ`), and the just-proved
summability `summable_lOrderNat_div_norm_sq_nontrivialZeros` change.

Index type: `MultiZeroIdx χ := Σ (ρ : {ρ // ρ ∈ NontrivialZeros χ}), Fin (lOrderNat χ ρ.val)`.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

open Complex Set Filter Topology

noncomputable section

namespace DirichletLHadamard

variable {N : ℕ} [NeZero N]

/-- Multiset index set for `Λ_χ`: pairs `(ρ, k)` with `ρ ∈ NontrivialZeros χ`,
`k < lOrderNat χ ρ.val`. -/
abbrev MultiZeroIdx (χ : DirichletCharacter ℂ N) : Type :=
  Σ (ρ : {ρ : ℂ // ρ ∈ GRHSpectral.NontrivialZeros χ}), Fin (lOrderNat χ ρ.val)

/-- **Multiplicity-indexed Weierstrass product for `Λ_χ`.** Each zero `ρ` contributes
`lOrderNat χ ρ` copies of the factor `(1 - z/ρ)·exp(z/ρ)`. -/
noncomputable def LProductMult (χ : DirichletCharacter ℂ N) (z : ℂ) : ℂ :=
  ∏' p : MultiZeroIdx χ, (1 + ZD.xiWeierstrassTerm p.1.val z)

/-- **Summability of the multiplicity-indexed Weierstrass weights** on any closed ball. -/
theorem summable_multi_weierstrassTerm_bound {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hχp : χ.IsPrimitive) (M : ℝ) (hM : 0 < M) :
    Summable (fun p : MultiZeroIdx χ => 3 * M ^ 2 / ‖p.1.val‖ ^ 2) := by
  have h_summ_weighted :
      Summable (fun ρ : {ρ : ℂ // ρ ∈ GRHSpectral.NontrivialZeros χ} =>
        (lOrderNat χ ρ.val : ℝ) * (3 * M ^ 2 / ‖ρ.val‖ ^ 2)) := by
    have := (summable_lOrderNat_div_norm_sq_nontrivialZeros hχ hχp).mul_left (3 * M ^ 2)
    refine this.congr ?_
    intro ρ
    show 3 * M ^ 2 * ((lOrderNat χ ρ.val : ℝ) / ‖ρ.val‖ ^ 2) =
      (lOrderNat χ ρ.val : ℝ) * (3 * M ^ 2 / ‖ρ.val‖ ^ 2)
    ring
  apply (summable_sigma_of_nonneg (fun p => by positivity)).mpr
  refine ⟨fun ρ => ?_, ?_⟩
  · exact Summable.of_finite
  · refine h_summ_weighted.congr ?_
    intro ρ
    show (lOrderNat χ ρ.val : ℝ) * (3 * M ^ 2 / ‖ρ.val‖ ^ 2) =
      ∑' (_ : Fin (lOrderNat χ ρ.val)), 3 * M ^ 2 / ‖ρ.val‖ ^ 2
    rw [tsum_const, Nat.card_eq_fintype_card, Fintype.card_fin]
    push_cast
    ring

/-- **Weierstrass term closed-ball bound** for the multiplicity-indexed product. -/
theorem xiWeierstrassTerm_mult_closedBall_bound {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (M : ℝ) (hM : 0 < M) :
    ∀ᶠ p : MultiZeroIdx χ in cofinite,
      ∀ z ∈ Metric.closedBall (0 : ℂ) M,
        ‖ZD.xiWeierstrassTerm p.1.val z‖ ≤ 3 * M ^ 2 / ‖p.1.val‖ ^ 2 := by
  have h_bad_fin :
      {p : MultiZeroIdx χ | ‖p.1.val‖ < M}.Finite := by
    have h_base_fin :
        {ρ : {ρ : ℂ // ρ ∈ GRHSpectral.NontrivialZeros χ} | ‖ρ.val‖ < M}.Finite := by
      have h_ntz_fin : (GRHSpectral.NontrivialZeros χ ∩ Metric.closedBall (0 : ℂ) M).Finite :=
        NontrivialZeros_inter_closedBall_finite hχ M
      have h_image_fin :
          ((fun ρ : {ρ : ℂ // ρ ∈ GRHSpectral.NontrivialZeros χ} => ρ.val) ''
            {ρ | ‖ρ.val‖ < M}).Finite := by
        apply h_ntz_fin.subset
        intro w hw
        rcases hw with ⟨ρ, hρ_lt, hρ_eq⟩
        simp only [Set.mem_setOf_eq] at hρ_lt
        subst hρ_eq
        refine ⟨ρ.property, ?_⟩
        rw [Metric.mem_closedBall, dist_zero_right]; linarith
      exact h_image_fin.of_finite_image Subtype.val_injective.injOn
    set bigFinset : Finset (MultiZeroIdx χ) :=
      h_base_fin.toFinset.attach.biUnion (fun ρ =>
        (Finset.univ : Finset (Fin (lOrderNat χ ρ.val.val))).image (fun k =>
          (⟨ρ.val, k⟩ : MultiZeroIdx χ))) with hbig_def
    have h_subset : {p : MultiZeroIdx χ | ‖p.1.val‖ < M} ⊆ ↑bigFinset := by
      intro p hp
      simp only [Set.mem_setOf_eq] at hp
      have hp_in : p.1 ∈ h_base_fin.toFinset := by
        simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]; exact hp
      rw [Finset.mem_coe, hbig_def, Finset.mem_biUnion]
      refine ⟨⟨p.1, hp_in⟩, Finset.mem_attach _ _, ?_⟩
      rw [Finset.mem_image]
      refine ⟨p.2, Finset.mem_univ _, ?_⟩
      rfl
    exact bigFinset.finite_toSet.subset h_subset
  filter_upwards [h_bad_fin.compl_mem_cofinite] with p hp
  have hp_ge_M : M ≤ ‖p.1.val‖ := by
    by_contra h; push_neg at h
    exact hp h
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right] at hz
  have hz_le_ρ : ‖z‖ ≤ ‖p.1.val‖ := le_trans hz hp_ge_M
  have hρ_ne : p.1.val ≠ 0 := by
    intro heq; rw [heq, norm_zero] at hp_ge_M; linarith
  have h_bd := ZD.norm_xiWeierstrassTerm_le hρ_ne hz_le_ρ
  have hρ_sq_pos : (0 : ℝ) < ‖p.1.val‖ ^ 2 := by positivity
  calc ‖ZD.xiWeierstrassTerm p.1.val z‖
      ≤ 3 * ‖z‖ ^ 2 / ‖p.1.val‖ ^ 2 := h_bd
    _ ≤ 3 * M ^ 2 / ‖p.1.val‖ ^ 2 := by
        apply div_le_div_of_nonneg_right _ hρ_sq_pos.le
        have h_z_sq_le : ‖z‖ ^ 2 ≤ M ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg z) hz 2
        linarith

/-- **Multipliable on compact balls**. -/
theorem LProductMult_multipliableUniformlyOn_closedBall {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hχp : χ.IsPrimitive) (M : ℝ) (hM : 0 < M) :
    MultipliableUniformlyOn
      (fun p : MultiZeroIdx χ => fun z : ℂ => 1 + ZD.xiWeierstrassTerm p.1.val z)
      (Metric.closedBall (0 : ℂ) M) := by
  have h_summ := summable_multi_weierstrassTerm_bound hχ hχp M hM
  have h_bound := xiWeierstrassTerm_mult_closedBall_bound hχ M hM
  apply Summable.multipliableUniformlyOn_one_add (isCompact_closedBall _ _) h_summ h_bound
  intro p
  have hρ_ne : p.1.val ≠ 0 := by
    intro heq
    have hre : (0 : ℝ) < p.1.val.re := p.1.property.1
    rw [heq] at hre; simp at hre
  exact (ZD.xiWeierstrassTerm_differentiable hρ_ne).continuous.continuousOn

/-- **Multipliable locally uniformly on ℂ**. -/
theorem LProductMult_multipliableLocallyUniformlyOn_univ {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hχp : χ.IsPrimitive) :
    MultipliableLocallyUniformlyOn
      (fun p : MultiZeroIdx χ => fun z : ℂ => 1 + ZD.xiWeierstrassTerm p.1.val z)
      Set.univ := by
  apply multipliableLocallyUniformlyOn_of_of_forall_exists_nhds
  intro z _
  refine ⟨Metric.closedBall z 1, ?_, ?_⟩
  · exact nhdsWithin_le_nhds (Metric.closedBall_mem_nhds z zero_lt_one)
  · set M : ℝ := ‖z‖ + 1 with hM_def
    have hM_pos : 0 < M := by rw [hM_def]; linarith [norm_nonneg z]
    have h_sub : Metric.closedBall z 1 ⊆ Metric.closedBall (0 : ℂ) M := by
      intro w hw
      rw [Metric.mem_closedBall, dist_zero_right]
      rw [Metric.mem_closedBall] at hw
      calc ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
            have := norm_sub_norm_le w z; linarith
        _ = dist w z + ‖z‖ := by rw [dist_eq_norm]
        _ ≤ 1 + ‖z‖ := by linarith
        _ = M := by rw [hM_def]; ring
    exact (LProductMult_multipliableUniformlyOn_closedBall hχ hχp M hM_pos).mono h_sub

-- ═══════════════════════════════════════════════════════════════════════════
-- § Differentiability and zero set of LProductMult
-- ═══════════════════════════════════════════════════════════════════════════

/-- **`LProductMult χ` is entire**. -/
theorem LProductMult_differentiable {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hχp : χ.IsPrimitive) : Differentiable ℂ (LProductMult χ) := by
  intro z
  have h_open : IsOpen (Set.univ : Set ℂ) := isOpen_univ
  have h_conv := LProductMult_multipliableLocallyUniformlyOn_univ hχ hχp
  have h_diffOn : DifferentiableOn ℂ (LProductMult χ) Set.univ := by
    apply (h_conv.hasProdLocallyUniformlyOn.differentiableOn ?_ h_open)
    filter_upwards with s
    have h_each : ∀ p ∈ s,
        DifferentiableOn ℂ (fun x => 1 + ZD.xiWeierstrassTerm p.1.val x) Set.univ := by
      intro p _
      have hρ_ne : p.1.val ≠ 0 := by
        intro heq
        have hre : (0 : ℝ) < p.1.val.re := p.1.property.1
        rw [heq] at hre; simp at hre
      exact (ZD.one_add_xiWeierstrassTerm_differentiable hρ_ne).differentiableOn
    have := DifferentiableOn.finset_prod (u := s)
      (f := fun p => fun x => 1 + ZD.xiWeierstrassTerm p.1.val x) h_each
    convert this using 1 <;> try rfl
    funext x
    rw [Finset.prod_fn]
  exact (h_diffOn z (Set.mem_univ z)).differentiableAt
    (h_open.mem_nhds (Set.mem_univ z))

/-- **Multipliability at each point**. -/
theorem LProductMult_multipliable {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hχp : χ.IsPrimitive) (z : ℂ) :
    Multipliable (fun p : MultiZeroIdx χ => 1 + ZD.xiWeierstrassTerm p.1.val z) :=
  (LProductMult_multipliableLocallyUniformlyOn_univ hχ hχp).multipliable (Set.mem_univ z)

/-- **`LProductMult χ` vanishes at nontrivial zeros**. -/
theorem LProductMult_zero_of_mem_NontrivialZeros {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    {ρ : ℂ} (hρ : ρ ∈ GRHSpectral.NontrivialZeros χ) :
    LProductMult χ ρ = 0 := by
  have hρ_ne : ρ ≠ 0 := by
    intro heq
    have hre : (0 : ℝ) < ρ.re := hρ.1
    rw [heq] at hre; simp at hre
  have h_pos : 0 < lOrderNat χ ρ := lOrderNat_pos hχ hρ
  apply tprod_of_exists_eq_zero
  refine ⟨⟨⟨ρ, hρ⟩, ⟨0, h_pos⟩⟩, ?_⟩
  exact ZD.one_add_xiWeierstrassTerm_at_zero hρ_ne

/-- **`LProductMult χ` is nonzero off nontrivial zeros**. -/
theorem LProductMult_ne_zero_of_notMem_NontrivialZeros {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hχp : χ.IsPrimitive) {z : ℂ} (hz : z ∉ GRHSpectral.NontrivialZeros χ) :
    LProductMult χ z ≠ 0 := by
  apply tprod_one_add_ne_zero_of_summable
  · intro p
    have hρ_ne : p.1.val ≠ 0 := by
      intro heq
      have hre : (0 : ℝ) < p.1.val.re := p.1.property.1
      rw [heq] at hre; simp at hre
    apply ZD.one_add_xiWeierstrassTerm_ne_zero_of_ne hρ_ne
    intro heq
    exact hz (heq ▸ p.1.property)
  · set M : ℝ := ‖z‖ + 1 with hM_def
    have hM_pos : 0 < M := by rw [hM_def]; linarith [norm_nonneg z]
    have hz_in_ball : z ∈ Metric.closedBall (0 : ℂ) M := by
      rw [Metric.mem_closedBall, dist_zero_right, hM_def]; linarith
    have h_bd := xiWeierstrassTerm_mult_closedBall_bound hχ M hM_pos
    have h_summ : Summable (fun p : MultiZeroIdx χ => 3 * M ^ 2 / ‖p.1.val‖ ^ 2) :=
      summable_multi_weierstrassTerm_bound hχ hχp M hM_pos
    refine h_summ.of_norm_bounded_eventually ?_
    filter_upwards [h_bd] with p hp_bd
    have h_at_z : ‖ZD.xiWeierstrassTerm p.1.val z‖ ≤ 3 * M ^ 2 / ‖p.1.val‖ ^ 2 :=
      hp_bd z hz_in_ball
    rw [Real.norm_of_nonneg (by positivity)]
    exact h_at_z

/-- **Zero set of `LProductMult χ`** = `NontrivialZeros χ`. -/
theorem LProductMult_eq_zero_iff {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hχp : χ.IsPrimitive) (z : ℂ) :
    LProductMult χ z = 0 ↔ z ∈ GRHSpectral.NontrivialZeros χ := by
  constructor
  · intro hz
    by_contra h
    exact LProductMult_ne_zero_of_notMem_NontrivialZeros hχ hχp h hz
  · exact LProductMult_zero_of_mem_NontrivialZeros hχ

end DirichletLHadamard

#print axioms DirichletLHadamard.LProductMult_eq_zero_iff
#print axioms DirichletLHadamard.LProductMult_differentiable
