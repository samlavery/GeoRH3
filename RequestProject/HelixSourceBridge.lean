import RequestProject.SpectralIdentification
import RequestProject.ExplicitFormulaBridgeOfRH
import RequestProject.ProjectionMidpoint
import RequestProject.RiemannHypothesisBridge

/-!
# Helix Source Bridge

This file keeps the helix-source direction explicit:

`HasSpectralIdentification` for every zeta zero supplies the line placement,
which supplies the Gaussian explicit-formula bridge, which supplies the
pointwise Gaussian Weil bridge used downstream.
-/

open Real Complex

noncomputable section

section SourceLoss

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The higher-dimensional representation is the source of its lower-dimensional
    projection: the lower projection plus saved loss reconstructs the source. -/
theorem higherDimensional_source_of_lowerProjection
    (K : Submodule ℝ F) [K.HasOrthogonalProjection] (x : F) :
    x = K.starProjection x + (x - K.starProjection x) :=
  (green_helmholtz_completeness K x).symm

/-- The Green-Helmholtz projection does not destroy source information:
    the retained projection plus the saved loss reconstructs the source, and
    the retained channel has zero drift against the saved loss. -/
theorem source_projection_plus_saved_loss_no_drift
    (K : Submodule ℝ F) [K.HasOrthogonalProjection] (x : F) :
    K.starProjection x + (x - K.starProjection x) = x ∧
    @inner ℝ F _ (K.starProjection x) (x - K.starProjection x) = 0 :=
  ⟨green_helmholtz_completeness K x, green_helmholtz_no_drift K x⟩

/-- One Green-Helmholtz projection audit: the projection/loss split has
    no drift, the dual loss operator is self-adjoint, and the source
    reconstructs exactly from projection plus saved loss. -/
theorem green_helmholtz_operator_drift_audit
    (K : Submodule ℝ F) [K.HasOrthogonalProjection] (x y : F) :
    @inner ℝ F _ (K.starProjection x) (x - K.starProjection x) = 0 ∧
    @inner ℝ F _ (x - K.starProjection x) (K.starProjection x) = 0 ∧
    @inner ℝ F _ (x - K.starProjection x) y =
      @inner ℝ F _ x (y - K.starProjection y) ∧
    x = K.starProjection x + (x - K.starProjection x) :=
  ⟨green_helmholtz_no_drift K x,
   green_helmholtz_no_drift_symm K x,
   green_helmholtz_loss_self_adjoint K x y,
   (green_helmholtz_completeness K x).symm⟩

end SourceLoss

/-- Dimensional projection audit: both 3D→2D and 2D→1D Green-Helmholtz
    projections have zero projection/loss drift and exact reconstruction. -/
theorem dimensional_projection_no_drift_audit
    (K₃ : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))
    (x₃ : EuclideanSpace ℝ (Fin 3))
    (K₂ : Submodule ℝ (EuclideanSpace ℝ (Fin 2)))
    (x₂ : EuclideanSpace ℝ (Fin 2)) :
    (@inner ℝ _ _ (K₃.starProjection x₃) (x₃ - K₃.starProjection x₃) = 0 ∧
      K₃.starProjection x₃ + (x₃ - K₃.starProjection x₃) = x₃) ∧
    (@inner ℝ _ _ (K₂.starProjection x₂) (x₂ - K₂.starProjection x₂) = 0 ∧
      K₂.starProjection x₂ + (x₂ - K₂.starProjection x₂) = x₂) :=
  ⟨⟨green_helmholtz_3d_no_drift K₃ x₃, green_helmholtz_completeness K₃ x₃⟩,
   ⟨green_helmholtz_2d_no_drift K₂ x₂, green_helmholtz_completeness K₂ x₂⟩⟩

/-- Concrete helix projection audit: `G₁` and the cascade do not invent
    a radial coordinate; the dropped radial coordinate is saved in `loss`
    and recombines exactly with the lower-dimensional projection. -/
theorem helix_projection_loss_tracking_audit (σ γ x : ℝ) :
    let v := zero_embed σ γ x
    v.radial = ProjectionMidpoint.radial_at Layer1.U σ ∧
    (apply_G1 v).radial = 0 ∧
    (apply_cascade v).radial = 0 ∧
    (loss v).radial = v.radial ∧
    v.radial = (apply_cascade v).radial + (loss v).radial ∧
    v.proj = (apply_cascade v).proj + (loss v).proj ∧
    v.angular = (apply_cascade v).angular + (loss v).angular := by
  dsimp
  refine ⟨ProjectionMidpoint.zero_embed_radial_eq_radial_at σ γ x, rfl, rfl, rfl,
    ?_, ?_, ?_⟩ <;> simp [apply_cascade, loss]

/-- The concrete dimensional projections do not create radial drift: after
    the 3D→2D projection, after the 2D→1D projection, and after the
    combined cascade, the retained radial coordinate is zero. -/
theorem dimensional_projections_create_no_radial_drift (v : HelixVector) :
    (apply_G1 v).radial = 0 ∧
    (apply_G2 (apply_G1 v)).radial = 0 ∧
    (apply_cascade v).radial = 0 := by
  simp [apply_G1, apply_G2, apply_cascade]

/-- If the source radial coordinate is zero, the whole concrete helix
    projection/loss pipeline has zero radial drift in every retained and
    saved radial slot. -/
theorem source_no_radial_drift_propagates_through_helix
    (v : HelixVector) (hv : v.radial = 0) :
    (apply_G1 v).radial = 0 ∧
    (apply_G2 (apply_G1 v)).radial = 0 ∧
    (apply_cascade v).radial = 0 ∧
    (loss v).radial = 0 := by
  simp [apply_G1, apply_G2, apply_cascade, loss, hv]

/-- Native full-turn radial growth `x ↦ e^6 x` does not change the source
    radial coordinate stored by the zero embedding. -/
theorem zero_embed_radial_exp_six_mul (σ γ x : ℝ) :
    (zero_embed σ γ (Real.exp 6 * x)).radial = (zero_embed σ γ x).radial :=
  rfl

/-- Equivalently, native `e^6` growth creates zero radial drift in the
    source embedding. -/
theorem zero_embed_exp_six_growth_creates_no_radial_drift (σ γ x : ℝ) :
    (zero_embed σ γ (Real.exp 6 * x)).radial - (zero_embed σ γ x).radial = 0 := by
  rw [zero_embed_radial_exp_six_mul]
  ring

section CombinedDriftAudit

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Dual Green-Helmholtz cascade audit: aligned self-adjoint idempotent
    projections have zero combined drift, self-adjoint saved loss, exact
    reconstruction, and radial-plus-angular loss decomposition. -/
theorem dual_helmholtz_green_cascade_drift_audit
    (G₁ G₂ : F →ₗ[ℝ] F)
    (hG₁_sa : ∀ x y, @inner ℝ F _ (G₁ x) y = @inner ℝ F _ x (G₁ y))
    (hG₂_sa : ∀ x y, @inner ℝ F _ (G₂ x) y = @inner ℝ F _ x (G₂ y))
    (hG₁_idem : ∀ x, G₁ (G₁ x) = G₁ x)
    (hG₂_idem : ∀ x, G₂ (G₂ x) = G₂ x)
    (hcomm : ∀ x, G₁ (G₂ x) = G₂ (G₁ x))
    (x y : F) :
    @inner ℝ F _ ((G₂ ∘ₗ G₁) x) (x - (G₂ ∘ₗ G₁) x) = 0 ∧
    @inner ℝ F _ (x - (G₂ ∘ₗ G₁) x) y =
      @inner ℝ F _ x (y - (G₂ ∘ₗ G₁) y) ∧
    x = (G₂ ∘ₗ G₁) x + (x - (G₂ ∘ₗ G₁) x) ∧
    x - (G₂ ∘ₗ G₁) x = (x - G₁ x) + (G₁ x - (G₂ ∘ₗ G₁) x) :=
  ⟨combined_no_drift G₁ G₂ hG₁_sa hG₂_sa hG₁_idem hG₂_idem hcomm x,
   combined_loss_self_adjoint G₁ G₂ hG₁_sa hG₂_sa hcomm x y,
   signal_eq_projection_plus_loss G₁ G₂ x,
   combined_loss_decomp G₁ G₂ x⟩

end CombinedDriftAudit

/-- Zero radial drift in the helix source coordinate places the zero at the
    source unit midpoint. -/
theorem helix_radial_no_drift_forces_unit_midpoint {σ γ x : ℝ}
    (h : (zero_embed σ γ x).radial = 0) :
    σ = Layer1.U / 2 :=
  ((ProjectionMidpoint.cascade_midpoint_is_unit_half σ γ x).2.1).mp h

/-- At the repo normalization `Layer1.U = 1`, zero radial drift is the
    half-unit readout. -/
theorem helix_radial_no_drift_forces_half {σ γ x : ℝ}
    (h : (zero_embed σ γ x).radial = 0) :
    σ = (1 : ℝ) / 2 := by
  have hmid : σ = Layer1.U / 2 := helix_radial_no_drift_forces_unit_midpoint h
  rwa [ProjectionMidpoint.midpoint_eq_half] at hmid

/-- Source-side radial drift impossibility: every zero embedding has zero
    radial component at every source scale. -/
def RadialDriftImpossibleOnZeros : Prop :=
  ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → ∀ x : ℝ,
    (zero_embed ρ.re ρ.im x).radial = 0

/-- A source-side audit failure: some zeta zero has nonzero helix radial
    component at some source scale. -/
def RadialDriftCreatedOnZero : Prop :=
  ∃ ρ : ℂ, ρ ∈ ZD.NontrivialZeros ∧ ∃ x : ℝ,
    (zero_embed ρ.re ρ.im x).radial ≠ 0

/-- Full concrete helix audit: the source radial coordinate, retained
    projection coordinates, and saved radial loss are all zero on every
    nontrivial zeta zero. -/
def HelixConstructionNoRadialDriftOnZeros : Prop :=
  ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → ∀ x : ℝ,
    let v := zero_embed ρ.re ρ.im x
    v.radial = 0 ∧
    (apply_G1 v).radial = 0 ∧
    (apply_G2 (apply_G1 v)).radial = 0 ∧
    (apply_cascade v).radial = 0 ∧
    (loss v).radial = 0

/-- A concrete audit failure: a zeta zero has source radial drift, or the
    saved loss channel contains radial drift. The retained dimensional
    projections themselves are excluded by `dimensional_projections_create_no_radial_drift`. -/
def HelixConstructionRadialDriftCreatedOnZero : Prop :=
  ∃ ρ : ℂ, ρ ∈ ZD.NontrivialZeros ∧ ∃ x : ℝ,
    let v := zero_embed ρ.re ρ.im x
    v.radial ≠ 0 ∨ (loss v).radial ≠ 0

/-- Mathlib's `RiemannHypothesis` gives zero radial drift for every
    nontrivial zero embedding. -/
theorem radial_drift_impossible_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    RadialDriftImpossibleOnZeros := by
  intro ρ hρ x
  have hline : ρ.re = (1 : ℝ) / 2 := by
    apply hRH ρ hρ.2.2
    · intro htriv
      rcases htriv with ⟨n, hn⟩
      have hre : ρ.re = (-2 * ((n : ℂ) + 1)).re := by rw [hn]
      simp [Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im] at hre
      linarith [hρ.1]
    · intro hρone
      have hlt : (1 : ℂ).re < 1 := by simpa [hρone] using hρ.2.1
      norm_num at hlt
  rw [radial_loss_eq, hline]
  ring

/-- If the helix source creates radial drift on a zeta zero, Mathlib's
    `RiemannHypothesis` is false. -/
theorem not_riemannHypothesis_of_radial_drift_created
    (hdrift : RadialDriftCreatedOnZero) :
    ¬ RiemannHypothesis := by
  intro hRH
  rcases hdrift with ⟨ρ, hρ, x, hx⟩
  exact hx (radial_drift_impossible_of_riemannHypothesis hRH ρ hρ x)

/-- The concrete helix no-drift audit is exactly the source radial
    no-drift statement plus the projection/loss propagation identities. -/
theorem helix_construction_no_radial_drift_iff :
    HelixConstructionNoRadialDriftOnZeros ↔ RadialDriftImpossibleOnZeros := by
  constructor
  · intro h ρ hρ x
    exact (h ρ hρ x).1
  · intro h ρ hρ x
    dsimp
    have hsrc : (zero_embed ρ.re ρ.im x).radial = 0 := h ρ hρ x
    exact ⟨hsrc, (source_no_radial_drift_propagates_through_helix
      (zero_embed ρ.re ρ.im x) hsrc).1,
      (source_no_radial_drift_propagates_through_helix
        (zero_embed ρ.re ρ.im x) hsrc).2.1,
      (source_no_radial_drift_propagates_through_helix
        (zero_embed ρ.re ρ.im x) hsrc).2.2.1,
      (source_no_radial_drift_propagates_through_helix
        (zero_embed ρ.re ρ.im x) hsrc).2.2.2⟩

/-- A concrete helix audit failure gives a source radial-drift witness. -/
theorem radial_drift_created_of_helix_construction_radial_drift
    (hdrift : HelixConstructionRadialDriftCreatedOnZero) :
    RadialDriftCreatedOnZero := by
  rcases hdrift with ⟨ρ, hρ, x, hx⟩
  refine ⟨ρ, hρ, x, ?_⟩
  dsimp at hx
  rcases hx with hsrc | hloss
  · exact hsrc
  · simpa [loss] using hloss

/-- Radial drift impossibility places every nontrivial zero at the source
    half-unit readout. -/
theorem nontrivialZeros_on_line_of_radial_drift_impossible
    (hdrift : RadialDriftImpossibleOnZeros) :
    ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → ρ.re = CoshBalance := by
  intro ρ hρ
  have hhalf : ρ.re = (1 : ℝ) / 2 :=
    helix_radial_no_drift_forces_half (hdrift ρ hρ 1)
  rw [CoshBalance_eq_half]
  exact hhalf

/-- Radial drift impossibility supplies the pointwise Gaussian Weil bridge. -/
theorem weilGaussianBridge_of_radial_drift_impossible
    (hdrift : RadialDriftImpossibleOnZeros) :
    ZD.WeilGaussianBridge :=
  ZD.weilGaussianBridge_of_nontrivialZeros_on_line
    (nontrivialZeros_on_line_of_radial_drift_impossible hdrift)

/-- Radial drift impossibility proves Mathlib's `RiemannHypothesis`. -/
theorem riemannHypothesis_of_radial_drift_impossible
    (hdrift : RadialDriftImpossibleOnZeros) :
    RiemannHypothesis :=
  RHBridge.no_offline_zeros_implies_rh
    (nontrivialZeros_on_line_of_radial_drift_impossible hdrift)

/-- The audited no-drift branch closes the chain to Mathlib's
    `RiemannHypothesis`. -/
theorem helix_audit_no_radial_drift_implies_riemannHypothesis
    (hdrift : RadialDriftImpossibleOnZeros) :
    RiemannHypothesis :=
  riemannHypothesis_of_radial_drift_impossible hdrift

/-- The yes/no source radial-drift audit. -/
theorem radial_drift_audit_consequence :
    (RadialDriftImpossibleOnZeros → RiemannHypothesis) ∧
    (RadialDriftCreatedOnZero → ¬ RiemannHypothesis) :=
  ⟨helix_audit_no_radial_drift_implies_riemannHypothesis,
   not_riemannHypothesis_of_radial_drift_created⟩

/-- The full concrete helix audit closes the same yes/no branch:
    no source/saved radial drift gives Mathlib's `RiemannHypothesis`; any
    source/saved radial drift witness gives its negation. -/
theorem helix_construction_radial_drift_audit_consequence :
    (HelixConstructionNoRadialDriftOnZeros → RiemannHypothesis) ∧
    (HelixConstructionRadialDriftCreatedOnZero → ¬ RiemannHypothesis) :=
  ⟨fun h => helix_audit_no_radial_drift_implies_riemannHypothesis
      (helix_construction_no_radial_drift_iff.mp h),
   fun h => not_riemannHypothesis_of_radial_drift_created
      (radial_drift_created_of_helix_construction_radial_drift h)⟩

/-- Universal helix spectral identification on the zero set places every
    nontrivial zero at the unit midpoint. -/
theorem nontrivialZeros_on_line_of_helix_spectral_identification
    (hsource : ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros →
      HasSpectralIdentification ρ.re ρ.im) :
    ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → ρ.re = CoshBalance := by
  intro ρ hρ
  have hhalf : ρ.re = (1 : ℝ) / 2 :=
    (spectral_identification_complete ρ.re ρ.im hρ.1 hρ.2.1).mp (hsource ρ hρ)
  rw [CoshBalance_eq_half]
  exact hhalf

/-- The helix-source spectral identification supplies the Gaussian
    explicit-formula bridge. -/
theorem explicitFormulaBridge_gaussianKernel_of_helix_spectral_identification
    (hsource : ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros →
      HasSpectralIdentification ρ.re ρ.im) :
    ZD.ExplicitFormulaBridge ZD.gaussianKernel := by
  refine ⟨?_⟩
  intro ρ hρ
  have hline : ρ.re = CoshBalance :=
    nontrivialZeros_on_line_of_helix_spectral_identification hsource ρ hρ
  rw [hline, CoshBalance_eq_half]
  exact ZD.averageEnergyDefect_zero_on_line ZD.gaussianKernel

/-- The helix-source spectral identification supplies the pointwise Gaussian
    Weil bridge. -/
theorem weilGaussianBridge_of_helix_spectral_identification
    (hsource : ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros →
      HasSpectralIdentification ρ.re ρ.im) :
    ZD.WeilGaussianBridge :=
  ZD.weilGaussianBridge_of_explicitFormulaBridge
    (explicitFormulaBridge_gaussianKernel_of_helix_spectral_identification hsource)

end
