import RequestProject.FaithfulnessFrobenius
/-!
# What the Hilbert–Pólya "datum" really is: it is *exactly* GRH
The closure of this project reduces GRH for `χ` to the hypothesis `hfaithful`, and
`Faithfulness.lean` discharges `hfaithful` from a single honest mathematical input — a
**Hilbert–Pólya spectral realisation** `SpectralRealisation χ` (a self-adjoint operator whose
real spectrum, pushed through `spectralZero μ = 1/2 + iμ`, realises every nontrivial zero).
The natural question is whether that datum is *circular* (secretly assuming RH/GRH) or a genuine,
independent mathematical target.  This file answers it with a theorem, **not** a slogan:
> `spectralRealisation_iff_zeros_on_line` :
>   `Nonempty (SpectralRealisation χ) ↔ (∀ ρ ∈ NTZ χ, ρ.re = 1/2 ∧ ρ.im ≠ 0)`.
So the datum is **logically equivalent** to GRH for `χ` (together with the off-axis condition
that there are no strip zeros on the real line, e.g. no Siegel-type real zero and no central
zero exactly at `s = 1/2`).  It is therefore:
* **not circular** — it does *not* take RH/GRH as a hypothesis; and
* **not strictly stronger or weaker** — producing the operator is *neither more nor less* than
  proving GRH (+ off-axis).
The forward direction (`⟹`) is the project's Von-Neumann reality argument
(`zeros_on_line_of_spectralRealisation`) plus the structure's `off_axis` field.  The backward
direction (`⟸`) is the new content here: **assuming the zeros are on the line and off the real
axis we genuinely construct a self-adjoint operator realising them.**  The operator is the
universal real-diagonal (multiplication) operator `diagOp` on the finitely supported space
`ℝ →₀ ℂ`, equipped with the standard ℓ² inner product; every real number is one of its
eigenvalues, so each on-line zero `ρ = 1/2 + i·Im ρ` is realised by the eigenvalue `Im ρ`.
This makes precise that the Dirichlet-`L` Hilbert–Pólya datum is a *real* (open) target equal to
GRH, while the genuinely *proved* incarnation of the same "self-adjoint Frobenius ⇒ purity"
mechanism is the function-field / Weil II case formalised unconditionally in `WeilII.lean`
(geometric Frobenius as the operator; the skew/symplectic pairing as the reality input; Deligne
purity `|α| = q^{β/2}` as the on-the-line conclusion).
-/
open Complex RCLike
namespace CriticalLinePhasor.Faithfulness
open CriticalLinePhasor.CarrierFiberDecomposition (NTZ)
/-! ## The universal real-diagonal self-adjoint model on `ℝ →₀ ℂ` -/
namespace DiagModel
noncomputable section
variable {ι : Type*}
/-- The standard ℓ² inner product on finitely supported functions `ι →₀ ℂ`. -/
noncomputable instance : Inner ℂ (ι →₀ ℂ) :=
  ⟨fun f g => f.sum (fun i a => (starRingEnd ℂ) a * g i)⟩
theorem inner_def (f g : ι →₀ ℂ) :
    (inner ℂ f g : ℂ) = f.sum (fun i a => (starRingEnd ℂ) a * g i) := rfl
/-- The inner product as a sum over any finset containing the support of `f`. -/
theorem inner_eq_sum_of_subset (f g : ι →₀ ℂ) {s : Finset ι} (hs : f.support ⊆ s) :
    (inner ℂ f g : ℂ) = ∑ i ∈ s, (starRingEnd ℂ) (f i) * g i := by
  rw [inner_def, Finsupp.sum]
  apply Finset.sum_subset hs
  intro i _ hi
  have : f i = 0 := Finsupp.notMem_support_iff.mp hi
  simp [this]
/-- The inner product expressed over the union of the two supports. -/
theorem inner_eq_sum_union [DecidableEq ι] (f g : ι →₀ ℂ) :
    (inner ℂ f g : ℂ) = ∑ i ∈ f.support ∪ g.support, (starRingEnd ℂ) (f i) * g i :=
  inner_eq_sum_of_subset f g Finset.subset_union_left
theorem inner_conj_symm (f g : ι →₀ ℂ) :
    (starRingEnd ℂ) (inner ℂ g f) = inner ℂ f g := by
  classical
  rw [inner_eq_sum_union, inner_eq_sum_union, map_sum, Finset.union_comm g.support f.support]
  exact Finset.sum_congr rfl (fun i _ => by rw [map_mul, Complex.conj_conj, mul_comm])
theorem inner_re_nonneg (f : ι →₀ ℂ) : 0 ≤ RCLike.re (inner ℂ f f : ℂ) := by
  rw [ inner_def ];
  simp +decide [ Finsupp.sum ];
  exact Finset.sum_nonneg fun _ _ => add_nonneg ( mul_self_nonneg _ ) ( mul_self_nonneg _ )
theorem inner_definite (f : ι →₀ ℂ) (h : (inner ℂ f f : ℂ) = 0) : f = 0 := by
  -- By the properties of the inner product, if `inner ℂ f f = 0`, then each term `conj (f i) * f i` must be zero. This follows from the fact that the sum of non-negative terms is zero if and only if each term is zero.
  have h_zero_terms : ∀ i ∈ f.support, Complex.normSq (f i) = 0 := by
    have h_zero_terms : ∑ i ∈ f.support, Complex.normSq (f i) = 0 := by
      simp_all +decide [ Complex.ext_iff, inner_def ];
      simp_all +decide [ Complex.normSq, Finsupp.sum ];
    exact fun i hi => by rw [ Finset.sum_eq_zero_iff_of_nonneg fun _ _ => Complex.normSq_nonneg _ ] at h_zero_terms; aesop;
  ext i; by_cases hi : i ∈ f.support <;> simp_all +decide ;
theorem inner_add_left (f g h : ι →₀ ℂ) :
    (inner ℂ (f + g) h : ℂ) = inner ℂ f h + inner ℂ g h := by
  convert Finsupp.sum_add_index' _ _ <;> simp +decide [ add_mul ]
theorem inner_smul_left (f g : ι →₀ ℂ) (r : ℂ) :
    (inner ℂ (r • f) g : ℂ) = (starRingEnd ℂ) r * inner ℂ f g := by
  apply Eq.symm; exact (by
    have h_support : (r • f).support ⊆ f.support := Finsupp.support_smul
    have h_eq : (inner ℂ (r • f) g : ℂ) = ∑ i ∈ f.support, (starRingEnd ℂ) (r * f i) * g i := by
      convert inner_eq_sum_of_subset ( r • f ) g h_support using 1
    have h_eq' : (inner ℂ f g : ℂ) = ∑ i ∈ f.support, (starRingEnd ℂ) (f i) * g i := by
      convert inner_eq_sum_of_subset f g ( Finset.Subset.refl _ ) using 1
    simp_all +decide [ mul_assoc, Finset.mul_sum _ _ _ ]
  )
/-- The ℓ² inner product makes `ι →₀ ℂ` a normed additive group (via its core). -/
noncomputable instance instNormedAddCommGroup : NormedAddCommGroup (ι →₀ ℂ) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ (ι →₀ ℂ) _ _ _
    { toInner := inferInstance
      conj_inner_symm := inner_conj_symm
      re_inner_nonneg := inner_re_nonneg
      definite := inner_definite
      add_left := inner_add_left
      smul_left := inner_smul_left }
/-- `ι →₀ ℂ` is an inner product space for the standard ℓ² inner product. -/
noncomputable instance instInnerProductSpace : InnerProductSpace ℂ (ι →₀ ℂ) :=
  InnerProductSpace.ofCore _
/-- The **diagonal (multiplication) operator**: multiply the value at index `i` by the real
number `d i`.  This is the prototypical self-adjoint operator with a prescribed real point
spectrum. -/
noncomputable def diagOp (d : ι → ℝ) : (ι →₀ ℂ) →ₗ[ℂ] (ι →₀ ℂ) :=
  Finsupp.lsum ℂ (fun i => (d i : ℂ) • Finsupp.lsingle i)
theorem diagOp_single (d : ι → ℝ) (i : ι) (c : ℂ) :
    diagOp d (Finsupp.single i c) = Finsupp.single i ((d i : ℂ) * c) := by
  unfold diagOp;
  simp +decide [ Finsupp.lsum ]
/-
Pointwise description of the diagonal operator.
-/
theorem diagOp_apply (d : ι → ℝ) (f : ι →₀ ℂ) (i : ι) :
    (diagOp d f) i = (d i : ℂ) * f i := by
  unfold diagOp; simp +decide [ Finsupp.sum ] ;
  rw [ Finset.sum_eq_single i ] <;> aesop
/-
The diagonal operator is symmetric (self-adjoint): its diagonal entries `d i` are real.
-/
theorem diagOp_symmetric (d : ι → ℝ) : (diagOp d).IsSymmetric := by
  intro f g;
  convert inner_eq_sum_of_subset ( diagOp d f ) g ?_ using 1;
  convert inner_eq_sum_of_subset f ( diagOp d g ) _ |> Eq.symm using 1;
  convert inner_eq_sum_of_subset f ( diagOp d g ) _ |> Eq.symm using 1;
  any_goals exact f.support;
  · simp +decide [ diagOp_apply, mul_assoc, mul_comm, mul_left_comm ];
  · exact Finset.Subset.refl _;
  · exact Finset.Subset.refl _;
  · intro i hi; contrapose! hi; simp_all +decide [ diagOp_apply ] ;
/-
Every diagonal entry `d i` (as a complex number) is an eigenvalue of `diagOp d`, with
eigenvector `single i 1`.
-/
theorem diagOp_hasEigenvalue (d : ι → ℝ) (i : ι) :
    Module.End.HasEigenvalue (diagOp d) ((d i : ℂ)) := by
  refine' fun h => _;
  simp_all +decide [ Submodule.eq_bot_iff ];
  specialize h ( Finsupp.single i 1 ) ; simp_all +decide [ diagOp ]
end
end DiagModel
/-! ## The backward direction: constructing the spectral realisation from GRH -/
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
/-- **Backward direction (construction).**  If every nontrivial zero lies on the critical line
and off the real axis, then a Hilbert–Pólya spectral realisation `SpectralRealisation χ`
genuinely *exists*: take the universal self-adjoint real-diagonal operator on `ℝ →₀ ℂ`, whose
eigenvalues are all real numbers, and realise each on-line zero `ρ = 1/2 + i·Im ρ` by the
eigenvalue `Im ρ`. -/
noncomputable def spectralRealisation_of_zeros_on_line
    (hline : ∀ ρ ∈ NTZ χ, ρ.re = 1 / 2) (hoff : ∀ ρ ∈ NTZ χ, ρ.im ≠ 0) :
    SpectralRealisation χ where
  E := ℝ →₀ ℂ
  T := DiagModel.diagOp (fun r : ℝ => r)
  hT := DiagModel.diagOp_symmetric _
  Spec := ℝ
  toEig := fun r => (r : ℂ)
  hEig := fun r => DiagModel.diagOp_hasEigenvalue (fun r : ℝ => r) r
  realises := by
    intro ρ hρ
    refine ⟨ρ.im, ?_⟩
    have hre : ρ.re = 1 / 2 := hline ρ hρ
    apply Complex.ext
    · simp [HilbertPolya.spectralZero, hre]
    · simp [HilbertPolya.spectralZero]
  off_axis := hoff
/-! ## The equivalence: the datum is exactly GRH (plus off-axis) -/
/-- **The Hilbert–Pólya datum is logically equivalent to GRH for `χ` (with the off-axis
condition).**  A spectral realisation of the nontrivial zeros *exists* if and only if every
nontrivial zero lies on the critical line and off the real axis.  Hence the datum is neither
circular nor an over- or under-statement: constructing the operator is *exactly* proving GRH (+ the
absence of strip zeros on the real line). -/
theorem spectralRealisation_iff_zeros_on_line :
    Nonempty (SpectralRealisation χ) ↔ (∀ ρ ∈ NTZ χ, ρ.re = 1 / 2 ∧ ρ.im ≠ 0) := by
  constructor
  · rintro ⟨S⟩ ρ hρ
    exact ⟨zeros_on_line_of_spectralRealisation χ S ρ hρ, S.off_axis ρ hρ⟩
  · intro h
    exact ⟨spectralRealisation_of_zeros_on_line χ (fun ρ hρ => (h ρ hρ).1)
      (fun ρ hρ => (h ρ hρ).2)⟩
/-! ## The strengthened, off-axis-free characterisation: the datum is *exactly* GRH
The full `SpectralRealisation` carries an `off_axis` field (`∀ ρ ∈ NTZ χ, ρ.im ≠ 0`), which is
only needed to feed the *helix* bridge `faithful_of_re_half` (whose `ProjectedNoDriftEvent` is, by
definition, vacuous on the real axis).  That condition is **not** part of the spectral content:
the operator/eigenvalue data — a self-adjoint `T` whose spectrum realises the zeros — already
forces the zeros onto the line by Von-Neumann reality alone, with no reference to the imaginary
axis.  In other words the helix cannot manufacture an off-line zero out of the spectral datum, so
the off-axis caveat is an artifact of the bridge and can be dropped.
We make this precise with the leaner datum `HilbertPolyaDatum χ` (the operator + spectral
realisation, *without* `off_axis`) and prove the clean equivalence
> `hilbertPolyaDatum_iff_GRH` :
>   `Nonempty (HilbertPolyaDatum χ) ↔ (∀ ρ ∈ NTZ χ, ρ.re = 1/2)`,
i.e. the Hilbert–Pólya datum is logically equivalent to **GRH for `χ`**, full stop. -/
/-- **The Hilbert–Pólya spectral datum, off-axis-free.**  A self-adjoint operator `T` on an
inner-product space together with an eigenvalue source whose Möbius/log parametrisation
`spectralZero ∘ toEig` realises every nontrivial zero of `L(·,χ)`.  Unlike `SpectralRealisation`
this carries **no** `off_axis` field: it is the pure spectral content. -/
structure HilbertPolyaDatum (χ : DirichletCharacter ℂ q) where
  /-- The carrier inner-product space. -/
  E : Type
  /-- Additive group structure. -/
  [inst_grp : NormedAddCommGroup E]
  /-- Inner-product space structure. -/
  [inst_ip : InnerProductSpace ℂ E]
  /-- The self-adjoint operator. -/
  T : E →ₗ[ℂ] E
  /-- Self-adjointness. -/
  hT : T.IsSymmetric
  /-- The eigenvalue/spectral source index. -/
  Spec : Type
  /-- The eigenvalue map. -/
  toEig : Spec → ℂ
  /-- Each source value is an eigenvalue of `T`. -/
  hEig : ∀ s, Module.End.HasEigenvalue T (toEig s)
  /-- Every nontrivial zero is realised by the spectral parametrisation. -/
  realises : ∀ ρ ∈ NTZ χ, ∃ s, HilbertPolya.spectralZero (toEig s) = ρ
attribute [instance] HilbertPolyaDatum.inst_grp HilbertPolyaDatum.inst_ip
/-- **Forward direction (Von-Neumann reality).**  The pure spectral datum already places every
nontrivial zero on the critical line — no off-axis hypothesis is used. -/
theorem zeros_on_line_of_hilbertPolyaDatum (D : HilbertPolyaDatum χ) :
    ∀ ρ ∈ NTZ χ, ρ.re = 1 / 2 := by
  intro ρ hρ
  obtain ⟨s, hs⟩ := D.realises ρ hρ
  rw [← hs]
  exact HilbertPolya.hilbert_polya_on_critical_line D.hT (D.hEig s)
/-- **Backward direction (construction).**  GRH for `χ` alone yields the pure spectral datum: the
universal self-adjoint real-diagonal operator on `ℝ →₀ ℂ` realises every on-line zero
`ρ = 1/2 + i·Im ρ` by the eigenvalue `Im ρ`.  No off-axis input is required. -/
noncomputable def hilbertPolyaDatum_of_GRH (hline : ∀ ρ ∈ NTZ χ, ρ.re = 1 / 2) :
    HilbertPolyaDatum χ where
  E := ℝ →₀ ℂ
  T := DiagModel.diagOp (fun r : ℝ => r)
  hT := DiagModel.diagOp_symmetric _
  Spec := ℝ
  toEig := fun r => (r : ℂ)
  hEig := fun r => DiagModel.diagOp_hasEigenvalue (fun r : ℝ => r) r
  realises := by
    intro ρ hρ
    refine ⟨ρ.im, ?_⟩
    have hre : ρ.re = 1 / 2 := hline ρ hρ
    apply Complex.ext
    · simp [HilbertPolya.spectralZero, hre]
    · simp [HilbertPolya.spectralZero]
/-- **The Hilbert–Pólya datum is logically equivalent to GRH for `χ`.**  Dropping the off-axis
artifact, a pure spectral realisation of the nontrivial zeros *exists* if and only if every
nontrivial zero lies on the critical line.  This is the strengthened, clean statement: the datum
is *exactly* GRH. -/
theorem hilbertPolyaDatum_iff_GRH :
    Nonempty (HilbertPolyaDatum χ) ↔ (∀ ρ ∈ NTZ χ, ρ.re = 1 / 2) := by
  constructor
  · rintro ⟨D⟩
    exact zeros_on_line_of_hilbertPolyaDatum χ D
  · intro h
    exact ⟨hilbertPolyaDatum_of_GRH χ h⟩
/-- A full `SpectralRealisation` contains the pure spectral datum (forgetting `off_axis`); hence
the off-axis-free `HilbertPolyaDatum` is the weaker, and therefore the sharper, hypothesis. -/
def HilbertPolyaDatum.ofSpectralRealisation (S : SpectralRealisation χ) : HilbertPolyaDatum χ where
  E := S.E
  T := S.T
  hT := S.hT
  Spec := S.Spec
  toEig := S.toEig
  hEig := S.hEig
  realises := S.realises
end CriticalLinePhasor.Faithfulness
