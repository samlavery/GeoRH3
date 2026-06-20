import Mathlib
import RequestProject.XiLogDerivTerms
import RequestProject.DirichletLProductMult

/-!
# Product-side partial fraction for `LProductMult χ`

Character-`χ` port of `ZD.logDeriv_xiProductMult_partial_fraction`. The unconditional half of the
Hadamard identity: the multiplicity-weighted log-derivative of the Weierstrass product equals the
resolvent sum

  `logDeriv (LProductMult χ) s = ∑'_ρ (ord ρ) · (1/(s−ρ) + 1/ρ)`   (`s ∉ NontrivialZeros χ`).

The character-free factor log-derivative `ZD.logDeriv_one_add_xiWeierstrassTerm` and Mathlib's
`logDeriv_tprod_eq_tsum` carry over directly; only the zero-set / order / summability change.
-/

open Complex Filter Topology Set

noncomputable section

namespace DirichletLHadamard

variable {N : ℕ} [NeZero N]

/-- Summable majorant over `MultiZeroIdx χ`: `Σ p, 2‖s‖/‖p.1.val‖² < ∞`. -/
theorem summable_multi_weierstrassTerm_bound_aux {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hχp : χ.IsPrimitive) (s : ℂ) :
    Summable (fun p : MultiZeroIdx χ => 2 * ‖s‖ / ‖p.1.val‖ ^ 2) := by
  have h_summ_weighted :
      Summable (fun ρ : {ρ : ℂ // ρ ∈ GRHSpectral.NontrivialZeros χ} =>
        (lOrderNat χ ρ.val : ℝ) * (2 * ‖s‖ / ‖ρ.val‖ ^ 2)) := by
    have := (summable_lOrderNat_div_norm_sq_nontrivialZeros hχ hχp).mul_left (2 * ‖s‖)
    refine this.congr ?_
    intro ρ
    show 2 * ‖s‖ * ((lOrderNat χ ρ.val : ℝ) / ‖ρ.val‖ ^ 2) =
      (lOrderNat χ ρ.val : ℝ) * (2 * ‖s‖ / ‖ρ.val‖ ^ 2)
    ring
  apply (summable_sigma_of_nonneg (fun p => by positivity)).mpr
  refine ⟨fun ρ => Summable.of_finite, ?_⟩
  refine h_summ_weighted.congr ?_
  intro ρ
  show (lOrderNat χ ρ.val : ℝ) * (2 * ‖s‖ / ‖ρ.val‖ ^ 2) =
    ∑' (_ : Fin (lOrderNat χ ρ.val)), 2 * ‖s‖ / ‖ρ.val‖ ^ 2
  rw [tsum_const, Nat.card_eq_fintype_card, Fintype.card_fin]
  push_cast
  ring

/-- Summability of per-factor log-derivatives of `LProductMult χ` over `MultiZeroIdx χ`. -/
theorem summable_logDeriv_multi {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (hχp : χ.IsPrimitive)
    {s : ℂ} (hs : s ∉ GRHSpectral.NontrivialZeros χ) :
    Summable (fun p : MultiZeroIdx χ =>
      logDeriv (fun w => 1 + ZD.xiWeierstrassTerm p.1.val w) s) := by
  set K : ℝ := 2 * ‖s‖ + 1 with hK_def
  have hK_pos : 0 < K := by rw [hK_def]; linarith [norm_nonneg s]
  have h_maj_summ : Summable (fun p : MultiZeroIdx χ =>
      2 * ‖s‖ / ‖p.1.val‖ ^ 2) := summable_multi_weierstrassTerm_bound_aux hχ hχp s
  refine h_maj_summ.of_norm_bounded_eventually ?_
  have hfin_base : {ρ : {ρ : ℂ // ρ ∈ GRHSpectral.NontrivialZeros χ} | ‖ρ.val‖ < K}.Finite := by
    have h_ntz_fin : (GRHSpectral.NontrivialZeros χ ∩ Metric.closedBall (0 : ℂ) K).Finite :=
      NontrivialZeros_inter_closedBall_finite hχ K
    have h_image_fin :
        ((fun ρ : {ρ : ℂ // ρ ∈ GRHSpectral.NontrivialZeros χ} => ρ.val) ''
          {ρ | ‖ρ.val‖ < K}).Finite := by
      apply h_ntz_fin.subset
      intro w hw
      rcases hw with ⟨ρ, hρ_lt, hρ_eq⟩
      simp only [Set.mem_setOf_eq] at hρ_lt
      subst hρ_eq
      refine ⟨ρ.property, ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right]; linarith
    exact h_image_fin.of_finite_image Subtype.val_injective.injOn
  have hfin_multi : {p : MultiZeroIdx χ | ‖p.1.val‖ < K}.Finite := by
    set bigFinset : Finset (MultiZeroIdx χ) :=
      hfin_base.toFinset.attach.biUnion (fun ρ =>
        (Finset.univ : Finset (Fin (lOrderNat χ ρ.val.val))).image (fun k =>
          (⟨ρ.val, k⟩ : MultiZeroIdx χ))) with hbig_def
    have h_subset : {p : MultiZeroIdx χ | ‖p.1.val‖ < K} ⊆ ↑bigFinset := by
      intro p hp
      simp only [Set.mem_setOf_eq] at hp
      have hp_in : p.1 ∈ hfin_base.toFinset := by
        simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]; exact hp
      rw [Finset.mem_coe, hbig_def, Finset.mem_biUnion]
      refine ⟨⟨p.1, hp_in⟩, Finset.mem_attach _ _, ?_⟩
      rw [Finset.mem_image]
      exact ⟨p.2, Finset.mem_univ _, rfl⟩
    exact bigFinset.finite_toSet.subset h_subset
  filter_upwards [hfin_multi.compl_mem_cofinite] with p hp
  have hp_ge_K : K ≤ ‖p.1.val‖ := by
    by_contra h; push_neg at h; exact hp h
  have hρ_ne : p.1.val ≠ 0 := by
    intro heq; rw [heq, norm_zero] at hp_ge_K; linarith
  have hρ_norm_pos : 0 < ‖p.1.val‖ := norm_pos_iff.mpr hρ_ne
  have hs_ne_ρ : s ≠ p.1.val := fun h => hs (h ▸ p.1.property)
  rw [ZD.logDeriv_one_add_xiWeierstrassTerm hρ_ne hs_ne_ρ]
  have h_z_sub_norm : ‖s‖ + 1 ≤ ‖s - p.1.val‖ := by
    have h_abs : |‖p.1.val‖ - ‖s‖| ≤ ‖p.1.val - s‖ := abs_norm_sub_norm_le _ _
    have h_rev : ‖p.1.val - s‖ = ‖s - p.1.val‖ := norm_sub_rev _ _
    have h1 : ‖p.1.val‖ - ‖s‖ ≤ ‖s - p.1.val‖ := by
      have := le_abs_self (‖p.1.val‖ - ‖s‖); linarith
    linarith
  have h_z_sub_pos : 0 < ‖s - p.1.val‖ := by linarith [norm_nonneg s]
  have h_z_sub_ne : s - p.1.val ≠ 0 := fun heq => by
    rw [heq, norm_zero] at h_z_sub_pos; linarith
  have h_bound : ‖s / (p.1.val * (s - p.1.val))‖ ≤ 2 * ‖s‖ / ‖p.1.val‖ ^ 2 := by
    rw [norm_div, norm_mul]
    have h_denom_pos : 0 < ‖p.1.val‖ * ‖s - p.1.val‖ := by positivity
    have h_rhs_denom : 0 < ‖p.1.val‖ ^ 2 := by positivity
    rw [div_le_div_iff₀ h_denom_pos h_rhs_denom]
    have h_triangle : ‖p.1.val‖ ≤ ‖s‖ + ‖s - p.1.val‖ := by
      have h := norm_sub_norm_le p.1.val s
      have hrev : ‖p.1.val - s‖ = ‖s - p.1.val‖ := norm_sub_rev _ _
      linarith
    have h_sub_bd : ‖p.1.val‖ ≤ 2 * ‖s - p.1.val‖ := by
      linarith [h_z_sub_norm, h_triangle]
    have h_gap : ‖p.1.val‖ * (‖p.1.val‖ - 2 * ‖s - p.1.val‖) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _) (by linarith)
    nlinarith [h_gap, norm_nonneg s, h_denom_pos.le]
  exact h_bound

/-- **Per-factor log-deriv partial fraction of `LProductMult χ`** (off zeros). -/
theorem logDeriv_LProductMult_partial_fraction {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hχp : χ.IsPrimitive) {s : ℂ} (hs : s ∉ GRHSpectral.NontrivialZeros χ) :
    logDeriv (LProductMult χ) s =
      ∑' ρ : {ρ : ℂ // ρ ∈ GRHSpectral.NontrivialZeros χ},
        (lOrderNat χ ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val) := by
  have hf : ∀ p : MultiZeroIdx χ, (1 + ZD.xiWeierstrassTerm p.1.val s) ≠ 0 := by
    intro p
    have hρ_ne : p.1.val ≠ 0 := by
      intro heq; have hre : (0 : ℝ) < p.1.val.re := p.1.property.1
      rw [heq] at hre; simp at hre
    apply ZD.one_add_xiWeierstrassTerm_ne_zero_of_ne hρ_ne
    intro heq
    exact hs (heq ▸ p.1.property)
  have hd : ∀ p : MultiZeroIdx χ,
      DifferentiableOn ℂ (fun w => 1 + ZD.xiWeierstrassTerm p.1.val w) Set.univ := by
    intro p
    have hρ_ne : p.1.val ≠ 0 := by
      intro heq; have hre : (0 : ℝ) < p.1.val.re := p.1.property.1
      rw [heq] at hre; simp at hre
    exact (ZD.one_add_xiWeierstrassTerm_differentiable hρ_ne).differentiableOn
  have hm := summable_logDeriv_multi hχ hχp hs
  have htend := LProductMult_multipliableLocallyUniformlyOn_univ hχ hχp
  have hnez : ∏' p : MultiZeroIdx χ, (1 + ZD.xiWeierstrassTerm p.1.val s) ≠ 0 :=
    LProductMult_ne_zero_of_notMem_NontrivialZeros hχ hχp hs
  have h_log := logDeriv_tprod_eq_tsum isOpen_univ (Set.mem_univ s) hf hd hm htend hnez
  show logDeriv (LProductMult χ) s = _
  rw [show (LProductMult χ : ℂ → ℂ) =
      (fun x => ∏' i : MultiZeroIdx χ, (1 + ZD.xiWeierstrassTerm i.1.val x)) from rfl, h_log]
  have h_per_factor : ∀ p : MultiZeroIdx χ,
      logDeriv (fun w => 1 + ZD.xiWeierstrassTerm p.1.val w) s =
      s / (p.1.val * (s - p.1.val)) := by
    intro p
    have hρ_ne : p.1.val ≠ 0 := by
      intro heq; have hre : (0 : ℝ) < p.1.val.re := p.1.property.1
      rw [heq] at hre; simp at hre
    have hs_ne_ρ : s ≠ p.1.val := fun h => hs (h ▸ p.1.property)
    exact ZD.logDeriv_one_add_xiWeierstrassTerm hρ_ne hs_ne_ρ
  rw [tsum_congr h_per_factor]
  have h_sigma_summ : Summable (fun p : MultiZeroIdx χ => s / (p.1.val * (s - p.1.val))) := by
    refine hm.congr ?_
    intro p
    exact h_per_factor p
  rw [Summable.tsum_sigma'
    (γ := fun ρ : {ρ : ℂ // ρ ∈ GRHSpectral.NontrivialZeros χ} => Fin (lOrderNat χ ρ.val))
    (f := fun p : MultiZeroIdx χ => s / (p.1.val * (s - p.1.val)))
    (fun _ => Summable.of_finite) h_sigma_summ]
  apply tsum_congr
  intro ρ
  have hρ_ne : ρ.val ≠ 0 := by
    intro heq; have hre : (0 : ℝ) < ρ.val.re := ρ.property.1
    rw [heq] at hre; simp at hre
  have hs_ne_ρ : s - ρ.val ≠ 0 := by
    intro heq
    have : s = ρ.val := by linear_combination heq
    exact hs (this ▸ ρ.property)
  rw [show (∑' (_ : Fin (lOrderNat χ ρ.val)), s / (ρ.val * (s - ρ.val))) =
      (lOrderNat χ ρ.val : ℂ) * (s / (ρ.val * (s - ρ.val))) from ?_]
  · have h_alg : s / (ρ.val * (s - ρ.val)) = 1 / (s - ρ.val) + 1 / ρ.val := by
      field_simp; ring
    rw [h_alg]
  · rw [tsum_const, Nat.card_eq_fintype_card, Fintype.card_fin]
    push_cast; ring

/-- Summability of the multiplicity-weighted Hadamard partial-fraction terms off zeros. -/
theorem summable_weighted_partial_fraction {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hχp : χ.IsPrimitive) {s : ℂ} (hs : s ∉ GRHSpectral.NontrivialZeros χ) :
    Summable (fun ρ : {ρ : ℂ // ρ ∈ GRHSpectral.NontrivialZeros χ} =>
      (lOrderNat χ ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val)) := by
  have h_multi_summ := summable_logDeriv_multi hχ hχp hs
  have h_eq : ∀ p : MultiZeroIdx χ,
      logDeriv (fun w => 1 + ZD.xiWeierstrassTerm p.1.val w) s =
        s / (p.1.val * (s - p.1.val)) := by
    intro p
    have hρ_ne : p.1.val ≠ 0 := by
      intro heq; have hre : (0 : ℝ) < p.1.val.re := p.1.property.1
      rw [heq] at hre; simp at hre
    have hs_ne_ρ : s ≠ p.1.val := fun h => hs (h ▸ p.1.property)
    exact ZD.logDeriv_one_add_xiWeierstrassTerm hρ_ne hs_ne_ρ
  have h_sigma_summ :
      Summable (fun p : MultiZeroIdx χ => s / (p.1.val * (s - p.1.val))) :=
    h_multi_summ.congr h_eq
  have h_sigma := h_sigma_summ.sigma
  refine h_sigma.congr ?_
  intro ρ
  have hρ_ne : ρ.val ≠ 0 := by
    intro heq; have hre : (0 : ℝ) < ρ.val.re := ρ.property.1
    rw [heq] at hre; simp at hre
  have hs_ne_ρ : s - ρ.val ≠ 0 := by
    intro heq
    have : s = ρ.val := by linear_combination heq
    exact hs (this ▸ ρ.property)
  have h_simp :
      (fun c : Fin (lOrderNat χ ρ.val) =>
        s / ((⟨ρ, c⟩ : MultiZeroIdx χ).1.val * (s - (⟨ρ, c⟩ : MultiZeroIdx χ).1.val))) =
        fun _ : Fin (lOrderNat χ ρ.val) => s / (ρ.val * (s - ρ.val)) := by
    funext c; rfl
  rw [h_simp, tsum_const, Nat.card_eq_fintype_card, Fintype.card_fin]
  have h_alg : s / (ρ.val * (s - ρ.val)) = 1 / (s - ρ.val) + 1 / ρ.val := by
    field_simp; ring
  rw [h_alg, nsmul_eq_mul]

end DirichletLHadamard

#print axioms DirichletLHadamard.logDeriv_LProductMult_partial_fraction
