import Mathlib
import RequestProject.DirichletLProductMult
import RequestProject.XiProductMultOrder

/-!
# Order matching: `analyticOrderAt (LProductMult χ) ρ = lOrderNat χ ρ`

Character-`χ` port of `ZD.analyticOrderAt_xiProductMult_eq_xiOrderNat`. Splits the multiplicity-indexed
Weierstrass product `LProductMult χ` at the `ρ`-fiber: that fiber gives a zero of order
`lOrderNat χ ρ`, and the complementary product is analytic + nonzero at `ρ`. The character-free factor
lemma `ZD.analyticAt_xiWeierstrassFactor` is reused; the order-one factor lemma is re-proved with the
`χ`-membership hypothesis (only `ρ ≠ 0` is used).
-/

open Complex Set Filter Topology

set_option maxHeartbeats 800000

noncomputable section

namespace DirichletLHadamard

variable {N : ℕ} [NeZero N]

/-- **Closed form of `LProductMult χ` via sigma split.** -/
theorem LProductMult_eq_tprod_pow {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hχp : χ.IsPrimitive) (z : ℂ) :
    LProductMult χ z =
    ∏' ρ' : {ρ' : ℂ // ρ' ∈ GRHSpectral.NontrivialZeros χ},
      (1 + ZD.xiWeierstrassTerm ρ'.val z) ^ (lOrderNat χ ρ'.val) := by
  unfold LProductMult
  have h_mult := LProductMult_multipliable hχ hχp z
  rw [Multipliable.tprod_sigma' (fun b => Multipliable.of_finite) h_mult]
  apply tprod_congr
  intro ρ'
  show ∏' (_ : Fin (lOrderNat χ ρ'.val)), (1 + ZD.xiWeierstrassTerm ρ'.val z) =
    (1 + ZD.xiWeierstrassTerm ρ'.val z) ^ (lOrderNat χ ρ'.val)
  rw [tprod_eq_prod (s := Finset.univ) (fun x hx => absurd (Finset.mem_univ x) hx)]
  simp [Finset.prod_const]

/-- `analyticOrderAt (factor ρ) ρ = 1` for nontrivial zeros `ρ` (only `ρ ≠ 0` used). -/
theorem analyticOrderAt_LWeierstrassFactor_eq_one {χ : DirichletCharacter ℂ N} {ρ : ℂ}
    (hρ : ρ ∈ GRHSpectral.NontrivialZeros χ) :
    analyticOrderAt (fun w => 1 + ZD.xiWeierstrassTerm ρ w) ρ = 1 := by
  have hρ_ne : ρ ≠ 0 := by
    intro heq
    have : (0 : ℝ) < ρ.re := hρ.1
    rw [heq] at this; simp at this
  have h_anal : AnalyticAt ℂ (fun w => 1 + ZD.xiWeierstrassTerm ρ w) ρ :=
    ZD.analyticAt_xiWeierstrassFactor ρ ρ
  set g : ℂ → ℂ := fun w => -Complex.exp (w / ρ) / ρ with hg_def
  have hg_anal : AnalyticAt ℂ g ρ := by
    show AnalyticAt ℂ (fun w => -Complex.exp (w / ρ) / ρ) ρ
    have h_id : AnalyticAt ℂ (fun w : ℂ => w / ρ) ρ := by
      have : (fun w : ℂ => w / ρ) = (fun w : ℂ => w * ρ⁻¹) := by funext w; ring
      rw [this]; exact analyticAt_id.mul analyticAt_const
    have h_exp : AnalyticAt ℂ (fun w : ℂ => Complex.exp (w / ρ)) ρ := h_id.cexp
    have h_neg : AnalyticAt ℂ (fun w : ℂ => -Complex.exp (w / ρ)) ρ := h_exp.neg
    have h_fun_eq : (fun w : ℂ => -Complex.exp (w / ρ) / ρ) =
        (fun w : ℂ => -Complex.exp (w / ρ) * ρ⁻¹) := by funext w; ring
    rw [h_fun_eq]
    exact h_neg.mul analyticAt_const
  have hg_ne : g ρ ≠ 0 := by
    show (-Complex.exp (ρ / ρ) / ρ) ≠ 0
    have h_div : ρ / ρ = 1 := div_self hρ_ne
    rw [h_div]
    exact div_ne_zero (neg_ne_zero.mpr (Complex.exp_ne_zero 1)) hρ_ne
  have h_eq : ∀ᶠ w in nhds ρ, (1 + ZD.xiWeierstrassTerm ρ w) = (w - ρ) ^ 1 • g w := by
    filter_upwards with w
    unfold ZD.xiWeierstrassTerm ZD.xiWeierstrassFactor
    show 1 + ((1 - w / ρ) * Complex.exp (w / ρ) - 1) = (w - ρ) ^ 1 • (-Complex.exp (w / ρ) / ρ)
    rw [pow_one, smul_eq_mul]
    field_simp
    ring
  rw [(h_anal.analyticOrderAt_eq_natCast).mpr ⟨g, hg_anal, hg_ne, h_eq⟩]
  rfl

/-- Splitting lemma: near `ρ ∈ NontrivialZeros χ`,
`LProductMult χ z = (factor ρ)^{lOrderNat χ ρ} · g(z)` with `g` analytic nonzero at `ρ`. -/
theorem LProductMult_eq_factor_mul_rest {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hχp : χ.IsPrimitive) {ρ : ℂ} (hρ : ρ ∈ GRHSpectral.NontrivialZeros χ) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g ρ ∧ g ρ ≠ 0 ∧
      LProductMult χ =ᶠ[nhds ρ]
        (fun z => (1 + ZD.xiWeierstrassTerm ρ z) ^ (lOrderNat χ ρ) * g z) := by
  have hρ_ne : ρ ≠ 0 := by
    intro heq
    have : (0 : ℝ) < ρ.re := hρ.1
    rw [heq] at this; simp at this
  set ρ_sub : {ρ' : ℂ // ρ' ∈ GRHSpectral.NontrivialZeros χ} := ⟨ρ, hρ⟩ with hρ_sub_def
  set S : Set (MultiZeroIdx χ) := {p : MultiZeroIdx χ | p.1 = ρ_sub} with hS_def
  set g : ℂ → ℂ := fun z =>
    ∏' p : (Sᶜ : Set (MultiZeroIdx χ)), (1 + ZD.xiWeierstrassTerm p.val.1.val z) with hg_def
  refine ⟨g, ?_, ?_, ?_⟩
  · have h_mult_loc : MultipliableLocallyUniformlyOn
        (fun p : ↑(Sᶜ : Set (MultiZeroIdx χ)) =>
          fun z : ℂ => 1 + ZD.xiWeierstrassTerm p.val.1.val z) Set.univ := by
      apply multipliableLocallyUniformlyOn_of_of_forall_exists_nhds
      intro z _
      refine ⟨Metric.closedBall z 1, ?_, ?_⟩
      · exact nhdsWithin_le_nhds (Metric.closedBall_mem_nhds z zero_lt_one)
      · set M : ℝ := ‖z‖ + 1 with hMz_def
        have hMz_pos : 0 < M := by rw [hMz_def]; linarith [norm_nonneg z]
        have h_subM : Metric.closedBall z 1 ⊆ Metric.closedBall (0 : ℂ) M := by
          intro w hw
          rw [Metric.mem_closedBall, dist_zero_right]
          rw [Metric.mem_closedBall] at hw
          calc ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
                have := norm_sub_norm_le w z; linarith
            _ = dist w z + ‖z‖ := by rw [dist_eq_norm]
            _ ≤ 1 + ‖z‖ := by linarith
            _ = M := by rw [hMz_def]; ring
        have h_summ_sub : Summable (fun p : ↑(Sᶜ : Set (MultiZeroIdx χ)) =>
            3 * M ^ 2 / ‖p.val.1.val‖ ^ 2) :=
          (summable_multi_weierstrassTerm_bound hχ hχp M hMz_pos).subtype _
        have h_bd_full := xiWeierstrassTerm_mult_closedBall_bound hχ M hMz_pos
        have h_bd_sub : ∀ᶠ p : ↑(Sᶜ : Set (MultiZeroIdx χ)) in cofinite,
            ∀ w ∈ Metric.closedBall (0 : ℂ) M,
              ‖ZD.xiWeierstrassTerm p.val.1.val w‖ ≤ 3 * M ^ 2 / ‖p.val.1.val‖ ^ 2 :=
          (Subtype.val_injective.tendsto_cofinite
            (α := (Sᶜ : Set (MultiZeroIdx χ)))).eventually h_bd_full
        have h_cts : ∀ p : ↑(Sᶜ : Set (MultiZeroIdx χ)),
            ContinuousOn (fun z => ZD.xiWeierstrassTerm p.val.1.val z)
              (Metric.closedBall (0 : ℂ) M) := by
          intro p
          have hρp_ne : p.val.1.val ≠ 0 := by
            intro heq; have hre : (0 : ℝ) < p.val.1.val.re := p.val.1.property.1
            rw [heq] at hre; simp at hre
          exact (ZD.xiWeierstrassTerm_differentiable hρp_ne).continuous.continuousOn
        have h_main : MultipliableUniformlyOn
            (fun p : ↑(Sᶜ : Set (MultiZeroIdx χ)) =>
              fun z : ℂ => 1 + ZD.xiWeierstrassTerm p.val.1.val z)
            (Metric.closedBall (0 : ℂ) M) :=
          Summable.multipliableUniformlyOn_one_add
            (isCompact_closedBall _ _) h_summ_sub h_bd_sub h_cts
        exact h_main.mono h_subM
    have h_open : IsOpen (Set.univ : Set ℂ) := isOpen_univ
    have h_diffOn : DifferentiableOn ℂ g Set.univ := by
      apply (h_mult_loc.hasProdLocallyUniformlyOn.differentiableOn ?_ h_open)
      filter_upwards with s
      have h_each : ∀ p ∈ s,
          DifferentiableOn ℂ
            (fun x => (fun z : ℂ => 1 + ZD.xiWeierstrassTerm p.val.1.val z) x) Set.univ := by
        intro p _
        have hρp_ne : p.val.1.val ≠ 0 := by
          intro heq; have hre : (0 : ℝ) < p.val.1.val.re := p.val.1.property.1
          rw [heq] at hre; simp at hre
        exact (ZD.one_add_xiWeierstrassTerm_differentiable hρp_ne).differentiableOn
      have := DifferentiableOn.finset_prod (u := s)
        (f := fun p x => 1 + ZD.xiWeierstrassTerm p.val.1.val x) h_each
      convert this using 1 <;> try rfl
      funext x
      rw [Finset.prod_fn]
    exact (h_diffOn.analyticOnNhd h_open) ρ (Set.mem_univ ρ)
  · show (∏' p : (Sᶜ : Set (MultiZeroIdx χ)), (1 + ZD.xiWeierstrassTerm p.val.1.val ρ)) ≠ 0
    apply tprod_one_add_ne_zero_of_summable
    · intro p
      have hp_ne_sub : p.val.1 ≠ ρ_sub := p.property
      have hp_val_ne : p.val.1.val ≠ ρ := fun heq =>
        hp_ne_sub (Subtype.ext heq)
      have h_ne1 : p.val.1.val ≠ 0 := by
        intro heq; have hre : (0 : ℝ) < p.val.1.val.re := p.val.1.property.1
        rw [heq] at hre; simp at hre
      exact ZD.one_add_xiWeierstrassTerm_ne_zero_of_ne h_ne1 hp_val_ne.symm
    · set M : ℝ := ‖ρ‖ + 1 with hMρ_def
      have hMρ_pos : 0 < M := by rw [hMρ_def]; linarith [norm_nonneg ρ]
      have hρ_in_ball : ρ ∈ Metric.closedBall (0 : ℂ) M := by
        rw [Metric.mem_closedBall, dist_zero_right, hMρ_def]; linarith
      have h_summ_sub : Summable (fun p : ↑(Sᶜ : Set (MultiZeroIdx χ)) =>
          3 * M ^ 2 / ‖p.val.1.val‖ ^ 2) :=
        (summable_multi_weierstrassTerm_bound hχ hχp M hMρ_pos).subtype _
      have h_bd_full := xiWeierstrassTerm_mult_closedBall_bound hχ M hMρ_pos
      have h_bd_sub : ∀ᶠ p : ↑(Sᶜ : Set (MultiZeroIdx χ)) in cofinite,
          ‖ZD.xiWeierstrassTerm p.val.1.val ρ‖ ≤ 3 * M ^ 2 / ‖p.val.1.val‖ ^ 2 := by
        have : ∀ᶠ p : ↑(Sᶜ : Set (MultiZeroIdx χ)) in cofinite,
            ∀ w ∈ Metric.closedBall (0 : ℂ) M,
              ‖ZD.xiWeierstrassTerm p.val.1.val w‖ ≤ 3 * M ^ 2 / ‖p.val.1.val‖ ^ 2 :=
          (Subtype.val_injective.tendsto_cofinite
            (α := (Sᶜ : Set (MultiZeroIdx χ)))).eventually h_bd_full
        filter_upwards [this] with p hp_bd
        exact hp_bd ρ hρ_in_ball
      exact h_summ_sub.of_norm_bounded_eventually (by
        filter_upwards [h_bd_sub] with p hp
        rwa [Real.norm_of_nonneg (by positivity)])
  · apply Filter.EventuallyEq.of_eq
    funext z
    have hS_fin : (S : Set (MultiZeroIdx χ)).Finite := by
      let bigSet : Finset (MultiZeroIdx χ) :=
        (Finset.univ : Finset (Fin (lOrderNat χ ρ))).image
          (fun k : Fin (lOrderNat χ ρ) => (⟨ρ_sub, k⟩ : MultiZeroIdx χ))
      apply bigSet.finite_toSet.subset
      intro p hp
      change p.1 = ρ_sub at hp
      rw [Finset.mem_coe, Finset.mem_image]
      refine ⟨p.2.cast (by rw [hp]), Finset.mem_univ _, ?_⟩
      obtain ⟨p1, p2⟩ := p
      change p1 = ρ_sub at hp
      subst hp
      rfl
    have hS_mult : Multipliable ((fun p : MultiZeroIdx χ => 1 + ZD.xiWeierstrassTerm p.1.val z) ∘
        (Subtype.val : ↑(S : Set (MultiZeroIdx χ)) → MultiZeroIdx χ)) :=
      hS_fin.multipliable _
    have hSc_mult : Multipliable ((fun p : MultiZeroIdx χ => 1 + ZD.xiWeierstrassTerm p.1.val z) ∘
        (Subtype.val : ↑(Sᶜ : Set (MultiZeroIdx χ)) → MultiZeroIdx χ)) := by
      set M : ℝ := ‖z‖ + 1 with hMz_def
      have hMz_pos : 0 < M := by rw [hMz_def]; linarith [norm_nonneg z]
      have hz_in_ball : z ∈ Metric.closedBall (0 : ℂ) M := by
        rw [Metric.mem_closedBall, dist_zero_right, hMz_def]; linarith
      have h_summ_sub : Summable (fun p : ↑(Sᶜ : Set (MultiZeroIdx χ)) =>
          3 * M ^ 2 / ‖p.val.1.val‖ ^ 2) :=
        (summable_multi_weierstrassTerm_bound hχ hχp M hMz_pos).subtype _
      have h_bd_full := xiWeierstrassTerm_mult_closedBall_bound hχ M hMz_pos
      have h_bd_sub : ∀ᶠ p : ↑(Sᶜ : Set (MultiZeroIdx χ)) in cofinite,
          ‖ZD.xiWeierstrassTerm p.val.1.val z‖ ≤ 3 * M ^ 2 / ‖p.val.1.val‖ ^ 2 := by
        have : ∀ᶠ p : ↑(Sᶜ : Set (MultiZeroIdx χ)) in cofinite,
            ∀ w ∈ Metric.closedBall (0 : ℂ) M,
              ‖ZD.xiWeierstrassTerm p.val.1.val w‖ ≤ 3 * M ^ 2 / ‖p.val.1.val‖ ^ 2 :=
          (Subtype.val_injective.tendsto_cofinite
            (α := (Sᶜ : Set (MultiZeroIdx χ)))).eventually h_bd_full
        filter_upwards [this] with p hp_bd
        exact hp_bd z hz_in_ball
      have h_summ_term : Summable (fun p : ↑(Sᶜ : Set (MultiZeroIdx χ)) =>
          ‖ZD.xiWeierstrassTerm p.val.1.val z‖) :=
        h_summ_sub.of_norm_bounded_eventually (by
          filter_upwards [h_bd_sub] with p hp
          rwa [Real.norm_of_nonneg (by positivity)])
      exact multipliable_one_add_of_summable h_summ_term
    have h_full : (∏' p : (S : Set (MultiZeroIdx χ)), (1 + ZD.xiWeierstrassTerm p.val.1.val z)) *
        (∏' p : (Sᶜ : Set (MultiZeroIdx χ)), (1 + ZD.xiWeierstrassTerm p.val.1.val z)) =
        ∏' p : MultiZeroIdx χ, (1 + ZD.xiWeierstrassTerm p.1.val z) :=
      hS_mult.tprod_mul_tprod_compl hSc_mult
    have hS_eq : ∏' p : (S : Set (MultiZeroIdx χ)), (1 + ZD.xiWeierstrassTerm p.val.1.val z) =
        (1 + ZD.xiWeierstrassTerm ρ z) ^ (lOrderNat χ ρ) := by
      let e : Fin (lOrderNat χ ρ) ≃ (S : Set (MultiZeroIdx χ)) := {
        toFun := fun k => ⟨⟨ρ_sub, k⟩, rfl⟩
        invFun := fun p => p.val.2.cast (congrArg
          (fun r : {r : ℂ // r ∈ GRHSpectral.NontrivialZeros χ} => lOrderNat χ r.val) p.property)
        left_inv := fun k => by simp [Fin.cast]
        right_inv := fun p => by
          apply Subtype.ext
          obtain ⟨⟨p1, p2⟩, hp⟩ := p
          change p1 = ρ_sub at hp
          subst hp
          rfl
      }
      have h_rw := e.tprod_eq (fun p => (1 + ZD.xiWeierstrassTerm p.val.1.val z) : ↑S → ℂ)
      rw [← h_rw]
      rw [tprod_eq_prod (s := Finset.univ) (fun x hx => absurd (Finset.mem_univ x) hx)]
      show ∏ k : Fin (lOrderNat χ ρ), (1 + ZD.xiWeierstrassTerm (e k).val.1.val z) = _
      have h_ev : ∀ k : Fin (lOrderNat χ ρ), (e k).val.1.val = ρ := fun k => rfl
      simp_rw [h_ev]
      rw [Finset.prod_const]; simp
    rw [hS_eq] at h_full
    show LProductMult χ z = (1 + ZD.xiWeierstrassTerm ρ z) ^ lOrderNat χ ρ * g z
    unfold LProductMult
    rw [← h_full]

/-- **Order at a nontrivial zero matches `lOrderNat χ`.** -/
theorem analyticOrderAt_LProductMult_eq_lOrderNat {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hχp : χ.IsPrimitive) {ρ : ℂ} (hρ : ρ ∈ GRHSpectral.NontrivialZeros χ) :
    analyticOrderAt (LProductMult χ) ρ = (lOrderNat χ ρ : ℕ∞) := by
  obtain ⟨g, hg_anal, hg_ne, h_eq⟩ := LProductMult_eq_factor_mul_rest hχ hχp hρ
  rw [analyticOrderAt_congr h_eq]
  have h_fun_eq :
      (fun z => (1 + ZD.xiWeierstrassTerm ρ z) ^ lOrderNat χ ρ * g z) =
        ((fun w => 1 + ZD.xiWeierstrassTerm ρ w) ^ lOrderNat χ ρ) * g := by
    funext z; simp [Pi.pow_apply, Pi.mul_apply]
  rw [h_fun_eq]
  have h_anal_factor : AnalyticAt ℂ (fun w => 1 + ZD.xiWeierstrassTerm ρ w) ρ :=
    ZD.analyticAt_xiWeierstrassFactor ρ ρ
  have h_anal_pow : AnalyticAt ℂ
      ((fun w => 1 + ZD.xiWeierstrassTerm ρ w) ^ lOrderNat χ ρ) ρ :=
    h_anal_factor.pow _
  have h_order_g : analyticOrderAt g ρ = 0 :=
    (hg_anal.analyticOrderAt_eq_zero).mpr hg_ne
  rw [analyticOrderAt_mul h_anal_pow hg_anal,
      analyticOrderAt_pow h_anal_factor,
      analyticOrderAt_LWeierstrassFactor_eq_one hρ,
      h_order_g, add_zero]
  simp

end DirichletLHadamard

#print axioms DirichletLHadamard.analyticOrderAt_LProductMult_eq_lOrderNat
