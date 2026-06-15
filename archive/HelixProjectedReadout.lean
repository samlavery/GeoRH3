import Mathlib
import RequestProject.HelixSourceFlow

/-!
# Projected readout: log-free source (A), earned log at the projection (B), the response identity (D)

Sam's three-layer reduction.

* **Layer A — log-free source geometry.** `ftaTheta F n = Σ_{p^e ‖ n} e · primeAngle p`, additive over
  products (`ftaTheta_mul`), from `Nat.factorization`. **No `log`.**
* **Layer B — radial projection dictionary.** `R(n)² = Cgeom·n`, `Cgeom = slope·U/π`; readout coordinate
  `projectedScale n = 2 log R(n)`. `projectedScale_eq_log_add_const`: `2 log R(n) = log n + log Cgeom`;
  `inv_projectedRadius_eq_const_mul_inv_sqrt`: `1/R(n) = (√Cgeom)⁻¹·(√n)⁻¹`. **This is where `log`
  enters — at the projection, earned from the area-law `R² ∝ n`, never in Layer A.**
* **Layer D — the response identity.** `scale_exp_eq`: `exp(−s·scale(n)) = Cgeom^{−s}·n^{−s}`, so the
  projected source sum `projectedResponse F s` equals `Cgeom^{−s}·L(χ,s)` *where it converges*
  (`projectedResponse_eq_LFunction`, `Re s > 1`); the on-line readout is the continuation
  (`completedReadout`), and its dips are exactly the critical-line `L`-zeros
  (`projectedResponse_zero_iff_lineReadout_zero`) because the geometric factor is nonzero. The bare
  `tsum` is `0` off the convergence strip — which is precisely why the on-line identity is stated through
  `DirichletCharacter.LFunction` (the analytic continuation), not the divergent series.

Honesty: `projectedResponse_eq_LFunction` is the genuine, non-vacuous content (a real identity in the
convergence region). `completedReadout` is the continuation of *that same expression* to the line; its
zeros being `L`'s zeros is `projectedResponse_zero_iff_lineReadout_zero`. The remaining pieces are Layer C
(`HelixSourceFlow.drift_zero_of_unitary` already gives the abstract unitary ⟹ real-frequency forcing) and
`SourceIdentity` (completeness: every zero is a captured on-line emit mode) — the honest gap.
-/

open Complex

namespace HelixProjected

/-- A log-free helix channel: character, pitch `U`, radial `mode` (slope `e^mode`), prime angles. -/
structure HelixChannel where
  q : ℕ
  χ : DirichletCharacter ℂ q
  U : ℝ
  mode : ℝ
  primeAngle : ℕ → ℝ
  U_pos : 0 < U

namespace HelixChannel
/-- Radial slope `e^mode`, always positive. -/
noncomputable def slope (F : HelixChannel) : ℝ := Real.exp F.mode
lemma slope_pos (F : HelixChannel) : 0 < F.slope := Real.exp_pos _
end HelixChannel

/-! ## Layer A — log-free FTA winding -/

/-- **Layer A.** `Θ(n) = Σ_{p^e ‖ n} e · primeAngle p`, from the prime factorization. No `log`. -/
noncomputable def ftaTheta (F : HelixChannel) (n : ℕ) : ℝ :=
  n.factorization.sum (fun p e => (e : ℝ) * F.primeAngle p)

/-- **Layer A theorem — multiplication → addition (FTA).** `Θ(mn) = Θ(m) + Θ(n)`. -/
theorem ftaTheta_mul (F : HelixChannel) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    ftaTheta F (m * n) = ftaTheta F m + ftaTheta F n := by
  unfold ftaTheta
  rw [Nat.factorization_mul hm hn]
  exact Finsupp.sum_add_index' (fun p => by simp) (fun p a b => by push_cast; ring)

/-! ## Layer B — radial projection, where `log` is earned -/

/-- The geometric channel constant `Cgeom = slope·U/π` (positive). -/
noncomputable def Cgeom (F : HelixChannel) : ℝ := F.slope * F.U / Real.pi

lemma Cgeom_pos (F : HelixChannel) : 0 < Cgeom F := by
  have := F.slope_pos; have := F.U_pos; unfold Cgeom; positivity

/-- `R(n)² = Cgeom·n` (the area-law, explicit). -/
noncomputable def projectedRadiusSq (F : HelixChannel) (n : ℕ) : ℝ := Cgeom F * (n : ℝ)

/-- `R(n) = √(Cgeom·n)`. -/
noncomputable def projectedRadius (F : HelixChannel) (n : ℕ) : ℝ := Real.sqrt (projectedRadiusSq F n)

/-- The projection readout coordinate `2 log R(n)`. **The single place `log` appears.** -/
noncomputable def projectedScale (F : HelixChannel) (n : ℕ) : ℝ := 2 * Real.log (projectedRadius F n)

/-- **Layer B theorem — the projection makes the scale `log n + log Cgeom`.** -/
theorem projectedScale_eq_log_add_const (F : HelixChannel) (n : ℕ) (hn : 0 < n) :
    projectedScale F n = Real.log (n : ℝ) + Real.log (Cgeom F) := by
  have hC := Cgeom_pos F
  unfold projectedScale projectedRadius projectedRadiusSq
  rw [Real.log_sqrt (by positivity),
      show (2 : ℝ) * (Real.log (Cgeom F * n) / 2) = Real.log (Cgeom F * n) by ring,
      Real.log_mul hC.ne' (Nat.cast_ne_zero.mpr hn.ne')]
  ring

/-- **Layer B lemma — the on-line radial damping.** `1/R(n) = (√Cgeom)⁻¹·(√n)⁻¹`. -/
theorem inv_projectedRadius_eq_const_mul_inv_sqrt (F : HelixChannel) (n : ℕ) :
    (projectedRadius F n)⁻¹ = (Real.sqrt (Cgeom F))⁻¹ * (Real.sqrt (n : ℝ))⁻¹ := by
  unfold projectedRadius projectedRadiusSq
  rw [Real.sqrt_mul (Cgeom_pos F).le, mul_inv]

/-! ## Layer D — the response identity via the analytic continuation `LFunction` -/

/-- **The geometric core at a complex parameter.** `exp(−s·scale(n)) = Cgeom^{−s}·n^{−s}` (`n > 0`).
    Combines Layer B's `2 log R = log n + log Cgeom` with `exp`/`cpow`. -/
theorem scale_exp_eq (F : HelixChannel) (s : ℂ) (n : ℕ) (hn : 0 < n) :
    Complex.exp (-s * (projectedScale F n : ℂ)) = (Cgeom F : ℂ) ^ (-s) * (n : ℂ) ^ (-s) := by
  have hC := Cgeom_pos F
  have hn' : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hlogn : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast n, ← Complex.ofReal_log hn'.le]
  rw [projectedScale_eq_log_add_const F n hn,
      Complex.cpow_def_of_ne_zero (show (Cgeom F : ℂ) ≠ 0 by exact_mod_cast hC.ne'),
      Complex.cpow_def_of_ne_zero (show (n : ℂ) ≠ 0 by exact_mod_cast hn'.ne'),
      ← Complex.ofReal_log hC.le, hlogn, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The projected source term at complex `s`, masked to `0` at `n = 0` (no atom `0`). -/
noncomputable def projTerm (F : HelixChannel) (s : ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else F.χ (n : ZMod F.q) * Complex.exp (-s * (projectedScale F n : ℂ))

/-- **Term identity.** Each projected term is `Cgeom^{−s}` times the Dirichlet `L`-series term. -/
theorem projTerm_eq (F : HelixChannel) (s : ℂ) (n : ℕ) :
    projTerm F s n = (Cgeom F : ℂ) ^ (-s) * LSeries.term (fun x => F.χ (x : ZMod F.q)) s n := by
  unfold projTerm
  rcases eq_or_ne n 0 with h | h
  · subst h; simp [LSeries.term_zero]
  · rw [if_neg h, LSeries.term_of_ne_zero h, scale_exp_eq F s n (Nat.pos_of_ne_zero h),
        Complex.cpow_neg (n : ℂ) s]
    ring

/-- The projected response: the geometric source sum `Σ χ(n)·exp(−s·scale(n))`. -/
noncomputable def projectedResponse (F : HelixChannel) (s : ℂ) : ℂ := ∑' n, projTerm F s n

/-- The response equals `Cgeom^{−s}` times the Dirichlet `L`-*series* (unconditional `tsum` form). -/
theorem projectedResponse_eq (F : HelixChannel) (s : ℂ) :
    projectedResponse F s = (Cgeom F : ℂ) ^ (-s) * LSeries (fun x => F.χ (x : ZMod F.q)) s := by
  unfold projectedResponse
  rw [tsum_congr (projTerm_eq F s), tsum_mul_left]
  rfl

/-- **Layer D — the response identity (convergent region).** Where the source sum converges (`Re s > 1`),
    the projected response is `Cgeom^{−s}·L(χ,s)`. The on-line readout is the continuation; the bare
    `tsum` is `0` off the convergence strip, which is exactly why the on-line statement routes through
    `LFunction`. This is the genuine, non-vacuous content of the projection identity. -/
theorem projectedResponse_eq_LFunction (F : HelixChannel) [NeZero F.q] {s : ℂ} (hs : 1 < s.re) :
    projectedResponse F s = (Cgeom F : ℂ) ^ (-s) * DirichletCharacter.LFunction F.χ s := by
  rw [projectedResponse_eq, DirichletCharacter.LFunction_eq_LSeries F.χ hs]

/-- The geometric prefactor `Cgeom^{−s}` is nonzero. -/
lemma Cgeom_cpow_ne_zero (F : HelixChannel) (s : ℂ) : (Cgeom F : ℂ) ^ (-s) ≠ 0 := by
  have hCne : (Cgeom F : ℂ) ≠ 0 := by exact_mod_cast (Cgeom_pos F).ne'
  intro h; rw [Complex.cpow_eq_zero_iff] at h; exact hCne h.1

/-- **The critical-line readout** `L(χ, ½+iγ)` (the analytic continuation on the line). -/
noncomputable def criticalLineReadout (F : HelixChannel) [NeZero F.q] (γ : ℝ) : ℂ :=
  DirichletCharacter.LFunction F.χ (1 / 2 + Complex.I * γ)

/-- **The geometric factor** `Cgeom^{−(½+iγ)}`. -/
noncomputable def geometricFactor (F : HelixChannel) (γ : ℝ) : ℂ :=
  (Cgeom F : ℂ) ^ (-(1 / 2 + Complex.I * γ))

lemma geometricFactor_ne_zero (F : HelixChannel) (γ : ℝ) : geometricFactor F γ ≠ 0 :=
  Cgeom_cpow_ne_zero F (1 / 2 + Complex.I * γ)

/-- **The completed readout** = geometric factor × critical-line `L`. The continuation of the same
    expression `projectedResponse_eq_LFunction` establishes for `Re s > 1`, evaluated on the line. -/
noncomputable def completedReadout (F : HelixChannel) [NeZero F.q] (γ : ℝ) : ℂ :=
  geometricFactor F γ * criticalLineReadout F γ

/-- **Layer D corollary — persistent dips equal critical-line zeros.** The completed readout vanishes
    exactly when the critical-line `L` does, because the geometric factor is nonzero. On the line
    `½+iγ` these are precisely the critical-line zeros of `L(χ)`. -/
theorem projectedResponse_zero_iff_lineReadout_zero (F : HelixChannel) [NeZero F.q] (γ : ℝ) :
    completedReadout F γ = 0 ↔ criticalLineReadout F γ = 0 := by
  rw [completedReadout, mul_eq_zero, or_iff_right (geometricFactor_ne_zero F γ)]

/-! ## Layer C — the unitary phase flow `U(γ)` is a pure phase (reality) -/

/-- **The flow factor is a pure phase (norm 1).** The phase flow `U(γ)` advances source mode `n` by
    `exp(−iγ·scale(n))`, which has norm `1`: the flow is unitary mode-by-mode — no drift, real frequency
    `scale(n)`. This is the concrete `‖·‖`-preservation that feeds the abstract reality forcing
    `HelixSourceFlow.drift_zero_of_unitary` (unitary ⟹ real frequency, σ-free, no Li/Weil positivity). -/
theorem flowPhase_norm_one (F : HelixChannel) (γ : ℝ) (n : ℕ) :
    ‖Complex.exp (-Complex.I * (γ : ℂ) * (projectedScale F n : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]

/-- The single-mode phase flow on `ℂ`: `U(τ)` multiplies by the unit phase `exp(−iτ·scale(n))`. This is
    `U(γ)` of the chain, restricted to one source mode. -/
noncomputable def modeFlow (F : HelixChannel) (n : ℕ) (τ : ℝ) : ℂ →L[ℂ] ℂ :=
  (Complex.exp (-Complex.I * (τ : ℂ) * (projectedScale F n : ℂ))) • ContinuousLinearMap.id ℂ ℂ

/-- **The phase flow is unitary** (`‖·‖`-preserving), because its factor is a pure phase. -/
theorem modeFlow_norm (F : HelixChannel) (n : ℕ) (τ : ℝ) (z : ℂ) :
    ‖modeFlow F n τ z‖ = ‖z‖ := by
  unfold modeFlow
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, norm_smul,
      flowPhase_norm_one, one_mul]

/-- **Reality, wired.** Any drifting eigenmode of the helix phase flow has zero drift `α = 0` — the
    frequency is real, no off-frame growth. This instantiates the abstract Hilbert–Pólya forcing
    `HelixSourceFlow.drift_zero_of_unitary` at the concrete flow `U(τ) = exp(−iτ·scale(n))`: σ-free,
    no Li/Weil positivity, the on-line property earned from unitarity alone. -/
theorem modeFlow_drift_zero (F : HelixChannel) (n : ℕ) {v : ℂ} {α β : ℝ}
    (h : HelixSourceFlow.IsDriftingMode (modeFlow F n) v α β) : α = 0 :=
  HelixSourceFlow.drift_zero_of_unitary (modeFlow F n) (fun τ w => modeFlow_norm F n τ w) h

/-- A drifting eigenmode of the phase flow is genuinely a harmonic with real frequency `β`. -/
theorem modeFlow_isHarmonic (F : HelixChannel) (n : ℕ) {v : ℂ} {α β : ℝ}
    (h : HelixSourceFlow.IsDriftingMode (modeFlow F n) v α β) :
    HelixSourceFlow.IsHarmonic (modeFlow F n) v β :=
  HelixSourceFlow.isHarmonic_of_unitary_drifting (modeFlow F n) (fun τ w => modeFlow_norm F n τ w) h

/-! ## Layer F — capture ⟹ GRH, with the on-line forcing EARNED from unitarity (not positivity) -/

section Capture
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A nontrivial zero `ρ` is **captured** by a source flow `U` if it is a genuine flow eigenmode whose
    drift is exactly `ρ.re − ½`: `∃ v ≠ 0, U τ v = e^{((ρ.re−½)+i·ρ.im)·τ} v`. This is the Hilbert–Pólya
    identification — the *existence of a flow mode at the zero*, **not** `ρ.re = ½` by definition. The
    on-line conclusion is then earned from unitarity, not assumed (contrast the circular "bounded drift",
    where boundedness `⟺ ρ.re ≤ ½` already *is* the conclusion). -/
def CapturedZero (U : ℝ → H →L[ℂ] H) (ρ : ℂ) : Prop :=
  ∃ v : H, HelixSourceFlow.IsDriftingMode U v (ρ.re - 1 / 2) ρ.im

/-- **On-line, earned (reality, not Li/Weil positivity).** A zero captured by a *unitary* flow lies on
    the critical line: unitarity forbids drift (`HelixSourceFlow.drift_zero_of_unitary`), so its drift
    `ρ.re − ½` must vanish. -/
theorem online_of_capturedZero (U : ℝ → H →L[ℂ] H) (hU : ∀ (τ : ℝ) (w : H), ‖U τ w‖ = ‖w‖)
    {ρ : ℂ} (h : CapturedZero U ρ) : ρ.re = 1 / 2 := by
  obtain ⟨v, hv⟩ := h
  have hα : ρ.re - 1 / 2 = 0 := HelixSourceFlow.drift_zero_of_unitary U hU hv
  linarith

/-- **Exhaustion (the Hilbert–Pólya gap):** the unitary source flow captures *every* nontrivial zero of
    `L(χ)`. This is the one remaining obligation — and it is geometric (does the source flow's spectrum
    reach every zero?), not another positivity. -/
def Exhausts (U : ℝ → H →L[ℂ] H) (F : HelixChannel) [NeZero F.q] : Prop :=
  ∀ ρ : ℂ, DirichletCharacter.LFunction F.χ ρ = 0 → 0 < ρ.re → ρ.re < 1 → CapturedZero U ρ

/-- **GRH from capture + unitarity.** If a unitary source flow captures every nontrivial zero of `L(χ)`,
    then every nontrivial zero lies on the critical line. The on-line forcing is *earned* from the flow's
    unitarity (the reality of a unitary spectrum); `Exhausts` is the remaining capture obligation. -/
theorem grh_from_exhaustion (U : ℝ → H →L[ℂ] H) (hU : ∀ (τ : ℝ) (w : H), ‖U τ w‖ = ‖w‖)
    (F : HelixChannel) [NeZero F.q] (hExh : Exhausts U F)
    {ρ : ℂ} (hρ : DirichletCharacter.LFunction F.χ ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    ρ.re = 1 / 2 :=
  online_of_capturedZero U hU (hExh ρ hρ h0 h1)

end Capture

/-! ## Layer C, full: the loss-space phase flow — the `lp` direct-sum of `modeFlow`, unconditional `hU`

Option 3 (flow-invariant loss metric): exhibit the unitary flow directly as the diagonal phase action
on the loss modes, `U(τ) : (wₙ) ↦ (e^{−iτ·scale(n)} wₙ)`, and prove `‖U τ w‖ = ‖w‖` by `lp`-norm
invariance under coordinatewise unit phases (Parseval) — per-mode unit modulus, norm preserved
blockwise. The frequencies `scale(n)` may run to `∞`; **no generator is formed, no Stone invoked.**
This is the genuine `hU`, the direct-sum of `modeFlow_norm`. -/

open scoped ENNReal BigOperators

/-- The loss space `ℓ²(ℕ)` carrying the source modes. -/
abbrev LossSpace : Type := lp (fun _ : ℕ => ℂ) 2

/-- The per-mode flow phase `exp(−iτ·scale(n))` as a coordinate (the `modeFlow` factor). -/
noncomputable def lossPhase (F : HelixChannel) (τ : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (-Complex.I * (τ : ℂ) * (projectedScale F n : ℂ))

theorem lossPhase_norm (F : HelixChannel) (τ : ℝ) (n : ℕ) : ‖lossPhase F τ n‖ = 1 :=
  flowPhase_norm_one F τ n

/-- Coordinatewise unit phases preserve `ℓ²`-membership. -/
theorem memℓp_lossFlow (F : HelixChannel) (τ : ℝ) (w : LossSpace) :
    Memℓp (fun n => lossPhase F τ n * (w : ℕ → ℂ) n) 2 := by
  apply memℓp_gen
  have h := lp.memℓp w
  rw [memℓp_gen_iff (show (0:ℝ) < (2 : ℝ≥0∞).toReal by norm_num)] at h
  refine h.congr (fun n => ?_)
  rw [norm_mul, lossPhase_norm, one_mul]

/-- **The loss-space phase flow as a linear isometry** — the `lp` direct-sum of `modeFlow`. -/
noncomputable def lossFlowIso (F : HelixChannel) (τ : ℝ) : LossSpace →ₗᵢ[ℂ] LossSpace where
  toFun w := ⟨fun n => lossPhase F τ n * (w : ℕ → ℂ) n, memℓp_lossFlow F τ w⟩
  map_add' w w' := by
    ext n; simp only [lp.coeFn_add, Pi.add_apply]; ring
  map_smul' c w := by
    ext n; simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring
  norm_map' w := by
    rw [lp.norm_eq_tsum_rpow (show (0:ℝ) < (2 : ℝ≥0∞).toReal by norm_num),
        lp.norm_eq_tsum_rpow (show (0:ℝ) < (2 : ℝ≥0∞).toReal by norm_num)]
    congr 1
    refine tsum_congr (fun n => ?_)
    congr 1
    show ‖lossPhase F τ n * (w : ℕ → ℂ) n‖ = ‖(w : ℕ → ℂ) n‖
    rw [norm_mul, lossPhase_norm, one_mul]

/-- The loss-space flow as a continuous linear map. -/
noncomputable def lossFlow (F : HelixChannel) (τ : ℝ) : LossSpace →L[ℂ] LossSpace :=
  (lossFlowIso F τ).toContinuousLinearMap

/-- **`hU`, unconditional, on the full loss space** — the genuine reality, no Stone, no generator.
    `‖U τ w‖² = Σₙ |e^{−iτ·scale(n)} wₙ|² = Σₙ |wₙ|² = ‖w‖²`, by `lp`-norm invariance under
    coordinatewise unit phases. The `lp` direct-sum of `modeFlow_norm`; the concrete `hU` feeding
    `HelixSourceFlow.drift_zero_of_unitary`.

    **Honest scope (do not cross this line).** This is the *easy* half. Because `U` is unitary **by
    construction**, it can host only `α = 0` modes — so the capture (that an actual zero *is* a mode of
    `U`) is a **separate, GRH-strength** obligation and must **not** be discharged by capturing into
    this by-construction-unitary flow (that is the circularity). `hU` lives here; the capture stays its
    own atom. -/
theorem lossFlow_norm (F : HelixChannel) (τ : ℝ) (w : LossSpace) : ‖lossFlow F τ w‖ = ‖w‖ :=
  (lossFlowIso F τ).norm_map w

/-- **Reality on the full loss space — `hU` discharged by the unconditional `lossFlow_norm`.** Any
    drifting eigenmode of the loss-space phase flow has zero drift `α = 0` (real frequency): the
    abstract forcing `HelixSourceFlow.drift_zero_of_unitary` instantiated at `lossFlow`, with the
    unitarity hypothesis supplied by `lossFlow_norm` (unconditional, no Stone, no generator). The `lp`
    direct-sum of `modeFlow_drift_zero`. Not a capture: the drifting-mode hypothesis is about a
    *specific* `v`, never the zeros — the on-line property earned from unitarity alone. -/
theorem lossFlow_drift_zero (F : HelixChannel) {v : LossSpace} {α β : ℝ}
    (h : HelixSourceFlow.IsDriftingMode (lossFlow F) v α β) : α = 0 :=
  HelixSourceFlow.drift_zero_of_unitary (lossFlow F) (fun τ w => lossFlow_norm F τ w) h

/-- **A drifting eigenmode of the loss-space flow is genuinely a harmonic** (real frequency `β`), with
    `hU` discharged by `lossFlow_norm`. The `lp` direct-sum of `modeFlow_isHarmonic`. -/
theorem lossFlow_isHarmonic (F : HelixChannel) {v : LossSpace} {α β : ℝ}
    (h : HelixSourceFlow.IsDriftingMode (lossFlow F) v α β) :
    HelixSourceFlow.IsHarmonic (lossFlow F) v β :=
  HelixSourceFlow.isHarmonic_of_unitary_drifting (lossFlow F) (fun τ w => lossFlow_norm F τ w) h

end HelixProjected
