import RequestProject.ClosedFormFrobenius
/-!
# Faithfulness extracted and applied to discharge `hfaithful`
This file does three things, in increasing order of number-theoretic strength.
## 1. The extracted faithfulness result (unconditional, no RH content)
The *loss-ledger / reconstruction-bijection* faithfulness (ported here from the peer
development): a 3D conical-helix "harmonic fiber" `(radial, phase, height)` is projected to a
1D height channel **via the Möbius/log readout**, with an exact two-sided reconstruction.  The
projection itself is lossy (phase and radius are destroyed), but once the destroyed channels
are *booked in a ledger* the map `fiber ↦ (height, ledger)` is a genuine bijection
(`record_bijective`), and the end-to-end `3D → height → exp → log` pipeline is the identity
(`pipeline_id`, `pipeline_bijective`).  The 2D→1D step *is literally the log*
(`log_recovers_height`) and the Möbius readout `w ρ = 1 - 1/ρ` lands on the unit circle exactly
on the critical line (`w_unit_iff_half`).  All of this is unconditional and, by design, carries
**no** number-theoretic content: it is a statement about coordinates and information flow.
## 2. The new on-line bridge (unconditional)
We connect that faithful Möbius readout to *this project's* GRH-strength predicate
`FaithfulMobiusLogProjection` (the `hfaithful` hypothesis of
`CriticalLinePhasor.HelixFrobeniusPurity.RH_from_helix_frobenius_purity`).  The Möbius-projected
carrier readout `y ↦ 1 - 1/(Re ρ + i y)` has **constant** modulus `1` precisely when
`Re ρ = 1/2` (`projectedReadout_norm_one_of_re_half`), so on the critical line, off the real
axis, the projected no-drift event holds (`projectedNoDrift_of_re_half`) and hence
`FaithfulMobiusLogProjection` holds (`faithful_of_re_half`).  This is the genuine, unconditional
converse to the project's `projectedNoDrift_imp_re_half`.
## 3. Discharging `hfaithful` (honest reduction to the spectral source)
`FaithfulMobiusLogProjection χ C ρ` at *every* nontrivial zero is, by
`projectedNoDrift_imp_re_half`, logically **equivalent to GRH for `χ`**
(`hfaithful_iff_zeros_on_line`): a `sorry`-free unconditional discharge would *be* a proof of
GRH.  We therefore discharge `hfaithful` from a single honestly-named, non-circular mathematical
input — a **Hilbert–Pólya spectral realisation** of the zeros (a self-adjoint operator whose
eigenvalue spectrum, pushed through the Möbius/log parametrisation `spectralZero μ = 1/2 + iμ`,
realises the nontrivial zeros).  Von Neumann reality of the spectrum
(`symmetric_eigenvalue_real`) then forces every realised zero onto `Re = 1/2`
(`hilbert_polya_on_critical_line`), which the on-line bridge converts into `hfaithful`
(`hfaithful_of_spectralRealisation`), and the project's closure
`RH_from_helix_frobenius_purity` into GRH (`RH_of_spectralRealisation`).
The spectral-realisation hypothesis is *not* the conclusion restated: it is the (open)
Hilbert–Pólya program.  No `axiom` is introduced and the GRH-strength step is never fabricated.
-/
namespace CriticalLinePhasor.Faithfulness
open Complex
open CriticalLinePhasor.CarrierFiberDecomposition (NTZ radial_drift)
open CriticalLinePhasor.ComputedSourceCrossingFix
  (projectedReadoutLine ProjectedNoDriftEvent projectedNoDrift_imp_re_half)
open CriticalLinePhasor.HelixFrobeniusPurity
  (FaithfulMobiusLogProjection SourceNoDrift RH_from_helix_frobenius_purity
   HelixFrobeniusEigenstate NTZ_imp_HelixFrobeniusEigenstate
   helix_vanishing_energy_conservation)
/-! ## 1. The extracted faithfulness result (loss-ledger reconstruction bijection) -/
namespace ConeProjection
noncomputable section
/-- A harmonic fiber recorded in the cylindrical coordinate system `(radial, phase, height)`. -/
abbrev Fiber := ℝ × ℝ × ℝ
/-- The radial channel. -/
def radial (f : Fiber) : ℝ := f.1
/-- The phase channel. -/
def phase (f : Fiber) : ℝ := f.2.1
/-- The height channel. -/
def height (f : Fiber) : ℝ := f.2.2
/-- The projection keeps only the **retained** channel: the height. -/
def project (f : Fiber) : ℝ := height f
/-- The **loss ledger**: the two channels destroyed by `project`, namely radial and phase. -/
def ledger (f : Fiber) : ℝ × ℝ := (radial f, phase f)
/-- The full **record**: the retained channel together with the loss ledger. -/
def record (f : Fiber) : ℝ × (ℝ × ℝ) := (project f, ledger f)
/-- **Reconstruction** of a fiber from a record `(height, (radial, phase))`. -/
def reconstruct (d : ℝ × (ℝ × ℝ)) : Fiber := (d.2.1, d.2.2, d.1)
/-- **Faithfulness.** Reconstruction from the record returns the original fiber exactly. -/
theorem reconstruct_record (f : Fiber) : reconstruct (record f) = f := by
  unfold reconstruct record; aesop
/-- Records determine fibers: `record` is injective. -/
theorem record_injective : Function.Injective record :=
  fun x y h => by simpa [reconstruct_record] using congr_arg reconstruct h
/-- Every record is realised: `record` is surjective. -/
theorem record_surjective : Function.Surjective record :=
  fun x => ⟨reconstruct x, reconstruct_record _⟩
/-- **The reconstruction bijection.** -/
def reconstructionBijection : Fiber ≃ ℝ × (ℝ × ℝ) where
  toFun := record
  invFun := reconstruct
  left_inv := reconstruct_record
  right_inv := fun _ => rfl
/-- The reconstruction is bijective. -/
theorem record_bijective : Function.Bijective record :=
  ⟨record_injective, record_surjective⟩
/-! ### The 2D→1D log projection (the projection "is literally the log") -/
/-- The strictly-positive height encoding. -/
def heightEncode (h : ℝ) : ℝ := Real.exp h
/-- The 2D→1D projection "is literally taking the log". -/
def lineProj (z : ℝ) : ℝ := Real.log z
/-- The log step faithfully recovers the height from its positive encoding. -/
theorem log_recovers_height (h : ℝ) : lineProj (heightEncode h) = h := by
  unfold lineProj heightEncode; simp
/-- The log projection is injective on positive encodings (faithful 2D→1D step). -/
theorem lineProj_faithful : Function.Injective (lineProj ∘ heightEncode) :=
  fun x y h => Real.exp_injective <| Real.log_injOn_pos (Real.exp_pos x) (Real.exp_pos y) h
/-- The cone's radial growth rate. -/
def coneSlope : ℝ := 2
/-- The conical helix (harmonic fiber): grows up and out. -/
def coneFiber (t : ℝ) : Fiber := (coneSlope * t, t + Real.pi / 3, t)
/-- The end-to-end 3D → height → encode → 1D(log) pipeline. -/
def pipeline (t : ℝ) : ℝ := lineProj (heightEncode (project (coneFiber t)))
/-- **Faithfulness of the pipeline.** It recovers the parameter exactly. -/
theorem pipeline_id (t : ℝ) : pipeline t = t := by
  unfold pipeline project coneFiber heightEncode lineProj; simp [height]
/-- The pipeline is a bijection of `ℝ`. -/
theorem pipeline_bijective : Function.Bijective pipeline := by
  rw [show pipeline = id from funext pipeline_id]; exact Function.bijective_id
/-! ### The Möbius readout on the unit circle ⟺ on the critical line -/
/-- The Möbius/Li spectral readout of a zero `ρ` — the helix operation `w = 1 − 1/ρ`. -/
def w (ρ : ℂ) : ℂ := 1 - 1 / ρ
/-- Spectral value on the unit circle ⟺ the zero on the critical line. -/
theorem w_unit_iff_half (ρ : ℂ) (hρ : ρ ≠ 0) :
    Complex.normSq (w ρ) = 1 ↔ ρ.re = 1 / 2 := by
  unfold w; simp +decide [Complex.normSq]
  by_cases h : ρ.re * ρ.re + ρ.im * ρ.im = 0 <;> simp_all +decide [← sq]
  · exact False.elim <| hρ <| by refine Complex.ext ?_ ?_ <;> norm_num <;> nlinarith
  · grind
end
end ConeProjection
/-! ## 1b. The Hilbert–Pólya spectral parametrisation (Von Neumann reality) -/
namespace HilbertPolya
open scoped ComplexConjugate
/-- The **spectral parametrisation**: a spectral harmonic `μ` (an eigenvalue) is sent to the
zero candidate `1/2 + iμ`. -/
noncomputable def spectralZero (mu : ℂ) : ℂ := 1 / 2 + Complex.I * mu
/-- **Von Neumann reality of the spectrum.** An eigenvalue of a symmetric (self-adjoint) complex
operator is **real** (`μ.im = 0`). -/
theorem symmetric_eigenvalue_real {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) {mu : ℂ} (hmu : Module.End.HasEigenvalue T mu) :
    mu.im = 0 := by
  have h := hT.conj_eigenvalue_eq_self hmu
  rwa [Complex.conj_eq_iff_im] at h
/-- The real part of the spectral parametrisation: `Re (1/2 + iμ) = 1/2 - Im μ`. -/
theorem spectralZero_re (mu : ℂ) : (spectralZero mu).re = 1 / 2 - mu.im := by
  simp only [spectralZero, Complex.add_re, Complex.mul_re]; simp; ring
/-- The imaginary ordinate of the spectral parametrisation is the eigenvalue itself. -/
theorem spectralZero_im (mu : ℂ) : (spectralZero mu).im = mu.re := by
  simp [spectralZero, Complex.add_im, Complex.mul_im]
/-- **Hilbert–Pólya places the zeros on the critical line.** -/
theorem hilbert_polya_on_critical_line {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) {mu : ℂ}
    (hmu : Module.End.HasEigenvalue T mu) :
    (spectralZero mu).re = 1 / 2 := by
  rw [spectralZero_re, symmetric_eigenvalue_real hT hmu]; ring
end HilbertPolya
/-! ## 2. The on-line bridge (unconditional converse to `projectedNoDrift_imp_re_half`) -/
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (C : ℝ)
/-
**On the critical line the Möbius-projected carrier readout has constant unit modulus.**
For `Re ρ = 1/2`, `‖1 - 1/(Re ρ + i y)‖ = 1` for *every* height `y`: the projected modulus
squared `((Re ρ - 1)² + y²)/((Re ρ)² + y²)` collapses to `(y² + 1/4)²/(y² + 1/4)² = 1`.
-/
theorem projectedReadout_norm_one_of_re_half (ρ : ℂ) (hre : ρ.re = 1 / 2) (y : ℝ) :
    ‖projectedReadoutLine ρ y‖ = 1 := by
  unfold projectedReadoutLine;
  norm_num [ Complex.normSq, Complex.norm_def, hre ];
  grind
omit [NeZero q] in
/-- **On-line projected no-drift.**  Off the real axis (`Im ρ ≠ 0`), on the critical line
(`Re ρ = 1/2`), the Möbius-projected carrier readout has vanishing radial drift: its modulus is
the constant `1`, so its derivative is `0`.  This is the genuine converse of the project's
`projectedNoDrift_imp_re_half`. -/
theorem projectedNoDrift_of_re_half (ρ : ℂ) (hre : ρ.re = 1 / 2) (him : ρ.im ≠ 0) :
    ProjectedNoDriftEvent χ C ρ := by
  refine ⟨him, ?_⟩
  have : (fun y : ℝ => ‖projectedReadoutLine ρ y‖) = fun _ => (1 : ℝ) :=
    funext fun y => projectedReadout_norm_one_of_re_half ρ hre y
  unfold radial_drift
  rw [this]
  simp
omit [NeZero q] in
/-- **Faithful Möbius/log projection on the critical line.**  On the critical line, off the real
axis, `FaithfulMobiusLogProjection` holds unconditionally: the (always-true) source-no-drift and
energy-match premises yield the on-line projected no-drift event. -/
theorem faithful_of_re_half (ρ : ℂ) (hre : ρ.re = 1 / 2) (him : ρ.im ≠ 0) :
    FaithfulMobiusLogProjection χ C ρ :=
  fun _ _ => projectedNoDrift_of_re_half χ C ρ hre him
/-! ## 3. Discharging `hfaithful` and the honest equivalence to GRH -/
/-- **`hfaithful` is equivalent to GRH for `χ`.**  Assuming nontrivial zeros are nonzero and off
the real axis, the GRH-strength hypothesis `∀ ρ ∈ NTZ χ, FaithfulMobiusLogProjection χ C ρ`
holds **iff** every nontrivial zero lies on the critical line.  The forward direction is the
project's no-drift forcing; the backward direction is the on-line bridge above.  This records,
honestly, that an unconditional discharge of `hfaithful` would *be* a proof of GRH. -/
theorem hfaithful_iff_zeros_on_line (hC : 0 < C) (hax : ∀ ρ ∈ NTZ χ, ρ.im ≠ 0) :
    (∀ ρ ∈ NTZ χ, FaithfulMobiusLogProjection χ C ρ) ↔ (∀ ρ ∈ NTZ χ, ρ.re = 1 / 2) := by
  constructor
  · intro h ρ hρ
    have hstate : HelixFrobeniusEigenstate χ C ρ :=
      NTZ_imp_HelixFrobeniusEigenstate χ C hC ρ hρ
    exact projectedNoDrift_imp_re_half χ C ρ
      (h ρ hρ hstate.source_no_drift (helix_vanishing_energy_conservation χ C ρ hstate))
  · intro h ρ hρ
    exact faithful_of_re_half χ C ρ (h ρ hρ) (hax ρ hρ)
/-- **A Hilbert–Pólya spectral realisation of the nontrivial zeros of `L(·,χ)`.**  A self-adjoint
operator `T` on an inner-product space, together with an eigenvalue source `toEig` landing in
its spectrum, whose Möbius/log parametrisation `spectralZero ∘ toEig` *realises* every
nontrivial zero (and lands off the real axis).  This is the (open) Hilbert–Pólya program, stated
as an honest hypothesis — not the conclusion `Re ρ = 1/2` restated. -/
structure SpectralRealisation (χ : DirichletCharacter ℂ q) where
  /-- The carrier Hilbert/inner-product space. -/
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
  /-- The realised zeros lie off the real axis. -/
  off_axis : ∀ ρ ∈ NTZ χ, ρ.im ≠ 0
attribute [instance] SpectralRealisation.inst_grp SpectralRealisation.inst_ip
/-- **The spectral realisation puts every nontrivial zero on the critical line.** -/
theorem zeros_on_line_of_spectralRealisation (S : SpectralRealisation χ) :
    ∀ ρ ∈ NTZ χ, ρ.re = 1 / 2 := by
  intro ρ hρ
  obtain ⟨s, hs⟩ := S.realises ρ hρ
  rw [← hs]
  exact HilbertPolya.hilbert_polya_on_critical_line S.hT (S.hEig s)
/-- **Discharge of `hfaithful` from the spectral realisation.**  Given a Hilbert–Pólya spectral
realisation of the zeros, the GRH-strength hypothesis `hfaithful` of
`RH_from_helix_frobenius_purity` is supplied: Von Neumann reality forces each zero onto the line,
and the on-line bridge `faithful_of_re_half` converts that into the faithful Möbius/log
projection at every nontrivial zero. -/
theorem hfaithful_of_spectralRealisation (S : SpectralRealisation χ) :
    ∀ ρ ∈ NTZ χ, FaithfulMobiusLogProjection χ C ρ :=
  fun ρ hρ =>
    faithful_of_re_half χ C ρ (zeros_on_line_of_spectralRealisation χ S ρ hρ) (S.off_axis ρ hρ)
/-- **GRH for `χ` from a Hilbert–Pólya spectral realisation.**  Combining the discharge of
`hfaithful` with the project's closure `RH_from_helix_frobenius_purity`: for `C > 0`, a spectral
realisation of the nontrivial zeros forces every nontrivial zero onto the critical line. -/
theorem RH_of_spectralRealisation (hC : 0 < C) (S : SpectralRealisation χ) :
    ∀ ρ ∈ NTZ χ, ρ.re = 1 / 2 :=
  RH_from_helix_frobenius_purity χ C hC (hfaithful_of_spectralRealisation χ C S)
end CriticalLinePhasor.Faithfulness
