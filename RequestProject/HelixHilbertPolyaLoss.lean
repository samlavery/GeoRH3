import Mathlib
import RequestProject.SpectralIdentification
import RequestProject.HelixHalfUnit

/-!
# Hilbert-Polya Instantiation on Helix Loss Modes

This file keeps the operator construction concrete:

* the loss space is a real Hilbert subspace;
* the Green-Helmholtz projection is `K.starProjection`;
* the projection family is self-adjoint, idempotent, and self-dual for every
  mode index, independently of any zero location.
-/

noncomputable section

open scoped BigOperators Real
open Real Complex

/-- The helix loss space is a real Hilbert subspace equipped with its
Green-Helmholtz orthogonal projection. -/
abbrev HelixLossSpace (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] :=
  Submodule ℝ H

/-- The Green-Helmholtz loss projection attached to the helix loss space. -/
abbrev helixLossProjection {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (K : HelixLossSpace H) [K.HasOrthogonalProjection] : H →ₗ[ℝ] H :=
  K.starProjection

/-- The helix loss projection is self-adjoint. -/
theorem helixLossProjection_self_adjoint {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (K : HelixLossSpace H) [K.HasOrthogonalProjection]
    (x y : H) :
    @inner ℝ H _ (helixLossProjection K x) y =
      @inner ℝ H _ x (helixLossProjection K y) :=
  Submodule.inner_starProjection_left_eq_right K x y

/-- The helix loss projection is idempotent. -/
theorem helixLossProjection_idempotent {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (K : HelixLossSpace H) [K.HasOrthogonalProjection]
    (x : H) :
    helixLossProjection K (helixLossProjection K x) = helixLossProjection K x :=
  Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem K x)

/-- The dual loss operator `I - P` is self-adjoint when `P` is the helix
loss projection. -/
theorem helixLossProjection_loss_self_adjoint {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (K : HelixLossSpace H) [K.HasOrthogonalProjection]
    (x y : H) :
    @inner ℝ H _ (x - helixLossProjection K x) y =
      @inner ℝ H _ x (y - helixLossProjection K y) := by
  calc
    @inner ℝ H _ (x - helixLossProjection K x) y
        = @inner ℝ H _ x y - @inner ℝ H _ (helixLossProjection K x) y := by
          rw [inner_sub_left]
    _ = @inner ℝ H _ x y - @inner ℝ H _ x (helixLossProjection K y) := by
          rw [helixLossProjection_self_adjoint K x y]
    _ = @inner ℝ H _ x (y - helixLossProjection K y) := by
          rw [inner_sub_right]

/-- The helix loss projection is self-dual: the projection and the loss channel
are both self-adjoint. -/
theorem helixLossProjection_self_dual {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (K : HelixLossSpace H) [K.HasOrthogonalProjection]
    (x y : H) :
    @inner ℝ H _ (helixLossProjection K x) y =
        @inner ℝ H _ x (helixLossProjection K y) ∧
      @inner ℝ H _ (x - helixLossProjection K x) y =
        @inner ℝ H _ x (y - helixLossProjection K y) :=
  ⟨helixLossProjection_self_adjoint K x y, helixLossProjection_loss_self_adjoint K x y⟩

/-- Every concrete helix loss mode has nonnegative projected energy. -/
theorem helix_loss_mode_energy_nonneg {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (K : HelixLossSpace H) [K.HasOrthogonalProjection]
    (x : ℕ → H) (n : ℕ) :
    0 ≤ ‖K.starProjection (x n)‖ ^ 2 := by
  positivity

/-- The sigma > 1 EF spectral vector supplies a norm-square anchor. -/
theorem ef_spectral_vector_anchor (σ : ℝ) (hσ : 1 < σ)
    (ρ : ℂ) (hρ : ρ ∈ VMEFStandalone.NontrivialZeros) :
    (VMEFStandalone.zeroTerm (σ : ℂ) ρ).re =
      ‖ef_spectral_vector σ ρ‖ ^ 2 :=
  ef_spectral_is_norm_sq σ hσ ρ hρ

/-- The mode-indexed Polya projection family built from the helix loss space. -/
def helixLossPolyaProjectionFamily {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (K : HelixLossSpace H) [K.HasOrthogonalProjection] :
    ℕ → H →ₗ[ℝ] H :=
  fun _ => helixLossProjection K

/-- The Polya projection family is self-adjoint for every mode index. -/
theorem helixLossPolyaProjectionFamily_self_adjoint {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (K : HelixLossSpace H) [K.HasOrthogonalProjection]
    (k : ℕ) (x y : H) :
    @inner ℝ H _ ((helixLossPolyaProjectionFamily K k) x) y =
      @inner ℝ H _ x ((helixLossPolyaProjectionFamily K k) y) :=
  helixLossProjection_self_adjoint K x y

/-- The Polya projection family is idempotent for every mode index. -/
theorem helixLossPolyaProjectionFamily_idempotent {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (K : HelixLossSpace H) [K.HasOrthogonalProjection]
    (k : ℕ) (x : H) :
    helixLossPolyaProjectionFamily K k ((helixLossPolyaProjectionFamily K k) x) =
      (helixLossPolyaProjectionFamily K k) x :=
  helixLossProjection_idempotent K x

/-- The dual loss channel of the Polya projection family is self-adjoint for
every mode index. -/
theorem helixLossPolyaProjectionFamily_loss_self_adjoint {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (K : HelixLossSpace H) [K.HasOrthogonalProjection] (k : ℕ) (x y : H) :
    @inner ℝ H _ (x - (helixLossPolyaProjectionFamily K k) x) y =
      @inner ℝ H _ x (y - (helixLossPolyaProjectionFamily K k) y) :=
  helixLossProjection_loss_self_adjoint K x y

/-- The Polya projection family is self-dual for every mode index: projection
and loss are both self-adjoint. -/
theorem helixLossPolyaProjectionFamily_self_dual {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (K : HelixLossSpace H) [K.HasOrthogonalProjection]
    (k : ℕ) (x y : H) :
    @inner ℝ H _ ((helixLossPolyaProjectionFamily K k) x) y =
        @inner ℝ H _ x ((helixLossPolyaProjectionFamily K k) y) ∧
      @inner ℝ H _ (x - (helixLossPolyaProjectionFamily K k) x) y =
        @inner ℝ H _ x (y - (helixLossPolyaProjectionFamily K k) y) :=
  ⟨helixLossPolyaProjectionFamily_self_adjoint K k x y,
    helixLossPolyaProjectionFamily_loss_self_adjoint K k x y⟩

/-- Any `HilbertPolyaOperator` carries self-adjoint projections modewise by
its structure field. -/
theorem hilbertPolyaOperator_proj_self_adjoint {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (HP : HilbertPolyaOperator H) (k : ℕ) (x y : H) :
    @inner ℝ H _ (HP.proj k x) y = @inner ℝ H _ x (HP.proj k y) :=
  HP.proj_sa k x y

/-- Any `HilbertPolyaOperator` carries idempotent projections modewise by its
structure field. -/
theorem hilbertPolyaOperator_proj_idempotent {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (HP : HilbertPolyaOperator H) (k : ℕ) (x : H) :
    HP.proj k (HP.proj k x) = HP.proj k x :=
  HP.proj_idem k x

/-- The dual loss channel of any `HilbertPolyaOperator` is self-adjoint
modewise. -/
theorem hilbertPolyaOperator_loss_self_adjoint {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (HP : HilbertPolyaOperator H) (k : ℕ) (x y : H) :
    @inner ℝ H _ (x - HP.proj k x) y =
      @inner ℝ H _ x (y - HP.proj k y) := by
  calc
    @inner ℝ H _ (x - HP.proj k x) y
        = @inner ℝ H _ x y - @inner ℝ H _ (HP.proj k x) y := by
          rw [inner_sub_left]
    _ = @inner ℝ H _ x y - @inner ℝ H _ x (HP.proj k y) := by
          rw [HP.proj_sa k x y]
    _ = @inner ℝ H _ x (y - HP.proj k y) := by
          rw [inner_sub_right]

/-- Any `HilbertPolyaOperator` is self-dual modewise: projection and loss are
both self-adjoint. -/
theorem hilbertPolyaOperator_self_dual {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (HP : HilbertPolyaOperator H) (k : ℕ) (x y : H) :
    @inner ℝ H _ (HP.proj k x) y = @inner ℝ H _ x (HP.proj k y) ∧
      @inner ℝ H _ (x - HP.proj k x) y =
        @inner ℝ H _ x (y - HP.proj k y) :=
  ⟨hilbertPolyaOperator_proj_self_adjoint HP k x y,
    hilbertPolyaOperator_loss_self_adjoint HP k x y⟩

/-- The helix scaling data supplies the Polya half-unit coordinate. The
hypotheses are only the helix dilation-energy invariance and nonzero energy. -/
theorem helixScalingData_forces_polya_half_unit
    (c : ℝ) (f : ℝ → ℝ)
    (hE : 0 < ∫ x in Set.Ioi (0 : ℝ), (f x) ^ 2)
    (hIso : ∀ lam : ℝ, 0 < lam →
      (∫ x in Set.Ioi (0 : ℝ), (lam ^ c * f (lam * x)) ^ 2)
        = ∫ x in Set.Ioi (0 : ℝ), (f x) ^ 2) :
    c = 1 / 2 :=
  (HelixHalfUnit.helix_forces_half c f hE).mp hIso

end
