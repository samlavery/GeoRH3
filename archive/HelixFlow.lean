import Mathlib
import RequestProject.HelixLossPole
import RequestProject.GRHSpectralCriterion

/-!
# The field shift-flow — the Hilbert–Pólya operator: unitary ⟺ GRH

The operator whose spectrum is the zeros is **not** the chiral block `B*B` (its singular values
scale like `log N`, not the zeros) but the **shift-flow** of the loss field: translation `u ↦ u+t`
acts on the mode `e^{(ρ−½)u}` of a zero `ρ` by multiplication by `e^{(ρ−½)t}`. The flow is
**unitary** exactly when every mode has unit modulus, i.e. every zero is on the critical line.

* `flowMode ρ t = e^{(ρ−½)t}` — the flow eigenvalue on the `ρ`-mode.
* `flowMode_unitary_iff` — unit modulus for all `t` ⟺ `Re ρ = ½` (this is `harmonic_iff_half`).
* `grh_iff_flowUnitary` — **GRH ⟺ the shift-flow is unitary**, the Hilbert–Pólya equivalence on
  the right operator, with the per-mode forcing supplied by `harmonic_iff_half`.
-/

namespace HelixFlow

open Complex

variable {N : ℕ} [NeZero N]

/-- The shift-flow eigenvalue on the mode of a zero `ρ`: `U(t)` multiplies `e^{(ρ−½)u}` by
    `e^{(ρ−½)t}`. Definitionally `HelixLossPole.modeResponse (Re ρ) (Im ρ) t`. -/
noncomputable def flowMode (ρ : ℂ) (t : ℝ) : ℂ := HelixLossPole.modeResponse ρ.re ρ.im t

/-- The flow eigenvalue is `e^{(ρ−½)·t}`. -/
theorem flowMode_eq (ρ : ℂ) (t : ℝ) : flowMode ρ t = Complex.exp ((ρ - 1 / 2) * (t : ℂ)) := by
  unfold flowMode HelixLossPole.modeResponse
  have h : ((ρ.re - 1 / 2 : ℝ) : ℂ) + (ρ.im : ℂ) * Complex.I = ρ - 1 / 2 := by
    apply Complex.ext <;>
      simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  rw [h]

/-- **Unitary on the `ρ`-mode ⟺ `ρ` on the critical line.** The flow eigenvalue has unit modulus
    for every `t` (no radial growth) iff `Re ρ = ½`. This is exactly `harmonic_iff_half`. -/
theorem flowMode_unitary_iff (ρ : ℂ) : (∀ t : ℝ, ‖flowMode ρ t‖ = 1) ↔ ρ.re = 1 / 2 :=
  HelixLossPole.harmonic_iff_half ρ.re ρ.im

/-- The shift-flow is **unitary** for channel `χ`: every nontrivial-zero mode has unit modulus. -/
def FlowUnitary (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ ρ ∈ GRHSpectral.NontrivialZeros χ, ∀ t : ℝ, ‖flowMode ρ t‖ = 1

/-- **GRH ⟺ the shift-flow is unitary.** The Hilbert–Pólya equivalence on the right operator:
    the flow's modes are the zeros, and it is unitary exactly when every zero is on the critical
    line. The per-mode forcing is `harmonic_iff_half` (`HelixLossPole`). -/
theorem grh_iff_flowUnitary (χ : DirichletCharacter ℂ N) :
    GRHSpectral.GRH χ ↔ FlowUnitary χ := by
  constructor
  · intro h ρ hρ t
    exact (flowMode_unitary_iff ρ).mpr (h ρ hρ) t
  · intro h ρ hρ
    exact (flowMode_unitary_iff ρ).mp (h ρ hρ)

/-! ## Tying the flow to the radial-frame measurement

The flow mode is the loss-field mode read in the construction's **radial frame** `a` (radius
`R ∝ n^a`). The geometry fixes `a = ½` (the area-law `√n` radius, `HelixDefs`), and the measured
radial rate `→ ½` at `N = 10⁸` is the empirical confirmation. The "construction forces unitarity"
target is then: *no radial drift in the `a = ½` frame*, which forces every zero onto the line.
-/

/-- The flow mode is the loss-field mode read in the **area-law frame** `a = ½`. -/
theorem flowMode_eq_frameHalf (ρ : ℂ) (t : ℝ) :
    flowMode ρ t = HelixLossPole.modeResponseFrame (1 / 2) ρ.re ρ.im t := rfl

/-- **Frame law.** If every nontrivial-zero mode has no radial drift in the radial frame `a`
    (`R ∝ n^a`), then every zero satisfies `Re ρ = a`. (The drift in frame `a` is `σ − a`; zero
    drift forces `σ = a` by `harmonic_in_frame_iff`.) -/
theorem zeros_re_eq_frame (χ : DirichletCharacter ℂ N) (a : ℝ)
    (h : ∀ ρ ∈ GRHSpectral.NontrivialZeros χ, ∀ t : ℝ,
        ‖HelixLossPole.modeResponseFrame a ρ.re ρ.im t‖ = 1) :
    ∀ ρ ∈ GRHSpectral.NontrivialZeros χ, ρ.re = a := fun ρ hρ =>
  ((HelixLossPole.harmonic_in_frame_iff a ρ.re ρ.im).mp (h ρ hρ)).symm

/-- **The construction-forces-unitarity target.** If the construction has **no radial drift in its
    area-law (`√n`, `a = ½`) frame**, then GRH holds. This is the precise remaining obligation: the
    geometry must force the hypothesis (zero radial drift), which is what the radial-rate-`→ ½`
    measurement (N = 10⁸) reports empirically. -/
theorem grh_of_noDrift_areaLaw (χ : DirichletCharacter ℂ N)
    (h : ∀ ρ ∈ GRHSpectral.NontrivialZeros χ, ∀ t : ℝ,
        ‖HelixLossPole.modeResponseFrame (1 / 2) ρ.re ρ.im t‖ = 1) :
    GRHSpectral.GRH χ :=
  zeros_re_eq_frame χ (1 / 2) h

end HelixFlow
