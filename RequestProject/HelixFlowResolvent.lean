import RequestProject.HelixFlowUnitaryGroup
import RequestProject.HelixResolventCapture

/-!
# The unitary flow's resolvent readout

The one-parameter unitary group `HelixFlow.flowHom` (step 2) realized as a path of unitaries in the
**diagonal C\*-algebra** `l∞ = lp (fun _ : ℕ => ℂ) ⊤`, with its resolvent readout. No on/off-line, no
strip continuation, no Weil energy — just the unitary flow and the resolvent of the diagonal operator.

* `flowUnit t` — `U(t)` as an element of `lp (fun _ : ℕ => ℂ) ⊤` (the bounded modulus-1 diagonal).
* `flowUnit_mem_unitary` — it is **unitary** (`star u · u = 1`, since each entry has modulus 1).
* `flowResolvent_regular_off_spectrum` — its resolvent readout `z ↦ φ(resolvent (U t) z)` is regular
  off the **spectrum** (no circle, no line invoked) — `regular_off_spectrum_of_resolvent`.
* `flowResolvent_isUnitaryReceiver` — the same readout, noting the unitary spectrum sits on the unit
  circle (`isUnitaryReceiver_resolventReadout`).
-/

open HelixFlow HelixLimit Complex

namespace HelixFlowResolvent

/-- The flow `U(t)` as an element of the diagonal C\*-algebra `l∞`: the bounded modulus-1 sequence
    `n ↦ phasorFlow t n` (`‖·‖ = 1`, so it is in `lp _ ∞`). -/
noncomputable def flowUnit (t : ℝ) : lp (fun _ : ℕ => ℂ) ⊤ :=
  ⟨fun n => (phasorFlow t n : ℂ),
    memℓp_infty ⟨1, by rintro _ ⟨n, rfl⟩; exact (phasorFlow_norm t n).le⟩⟩

@[simp] theorem flowUnit_coe (t : ℝ) (n : ℕ) :
    (flowUnit t : ℕ → ℂ) n = (phasorFlow t n : ℂ) := rfl

/-- **The flow is unitary in `l∞`.** `star (U t) · U t = 1` (and the mirror), because each diagonal
    entry has modulus 1: `conj z · z = ‖z‖² = 1`. -/
theorem flowUnit_mem_unitary (t : ℝ) :
    flowUnit t ∈ unitary (lp (fun _ : ℕ => ℂ) ⊤) := by
  have key : star (flowUnit t) * flowUnit t = 1 := by
    apply lp.ext
    funext n
    simp only [lp.infty_coeFn_mul, lp.coeFn_star, lp.infty_coeFn_one, Pi.mul_apply, Pi.star_apply,
      Pi.one_apply, flowUnit_coe]
    rw [mul_comm, ← starRingEnd_apply, Complex.mul_conj]
    norm_cast
    rw [Complex.normSq_eq_norm_sq, phasorFlow_norm]
    norm_num
  exact ⟨key, by rw [mul_comm]; exact key⟩

/-- **The resolvent readout of the unitary flow is regular off its spectrum.** For any continuous
    readout `φ`, `z ↦ φ(resolvent (U t) z)` has a finite limit at every `z ∉ spectrum (U t)` — the
    resolvent is analytic on the resolvent set. No circle, no line. -/
theorem flowResolvent_regular_off_spectrum (t : ℝ) {φ : lp (fun _ : ℕ => ℂ) ⊤ → ℂ}
    (hφ : Continuous φ) :
    ∀ z, z ∉ spectrum ℂ (flowUnit t) →
      ∃ L, Filter.Tendsto (fun w => φ (resolvent (flowUnit t) w)) (nhdsWithin z {z}ᶜ) (nhds L) :=
  regular_off_spectrum_of_resolvent (flowUnit t) hφ

/-- **The resolvent readout is a unitary receiver.** The same readout, with the unitary spectrum located
    on the unit circle: `z ↦ φ(resolvent (U t) z)` has a finite limit at every `z` with `‖z‖ ≠ 1`. -/
theorem flowResolvent_isUnitaryReceiver (t : ℝ) {φ : lp (fun _ : ℕ => ℂ) ⊤ → ℂ}
    (hφ : Continuous φ) :
    IsUnitaryReceiver (fun z => φ (resolvent (flowUnit t) z)) :=
  isUnitaryReceiver_resolventReadout (flowUnit_mem_unitary t) hφ

end HelixFlowResolvent

#print axioms HelixFlowResolvent.flowUnit_mem_unitary
#print axioms HelixFlowResolvent.flowResolvent_regular_off_spectrum
#print axioms HelixFlowResolvent.flowResolvent_isUnitaryReceiver
