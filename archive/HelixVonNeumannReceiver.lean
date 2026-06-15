import RequestProject.HelixCompatibilitySquare

/-!
# The von Neumann receiver: `hVN` discharged concretely, spine collapsed to one identity

The self-adjoint reality (`hVN`) is realized **concretely**, not hypothesized. Take a real spectrum
`μ : ℕ → ℝ` — the von Neumann / `T⋆T` reality: each eigenvalue is real, so each source mode is
`SourceMode.ofReal (μ n)` with `rate = i·μ`, `Re rate = 0`. The receiver is its regularized resolvent
trace on the critical line,

  `vonNeumannReceiver μ z = −∑ₙ [ 1/((½+iz) − (½+iμₙ)) + 1/(½+iμₙ) ]`.

Because the spectrum is **real**, every pole `½+iμₙ` sits at a **real** `z = μₙ`; so off the real axis
the trace is regular — `IsSelfAdjointReceiver` (`isSelfAdjointReceiver_vonNeumannReceiver`) is a
**theorem**, proven from the resolvent M-test (escape + trace-class summability of the spectrum),
*never* from the zeros. The separation constant is just `|Im z|`: a point off ℝ is `|Im z|`-far from
every real pole.

With `hVN` discharged, the compatibility-square spine collapses to a **single equation**, `hCompat`:
the constructed trace equals `−L'/L(½+i·)` — i.e. the real von Neumann spectrum `μ` IS the imaginary
heights of the zeros. That is the trace identity / explicit-formula wall, and now the only thing left.
-/

open Complex Filter Topology HelixSource HelixLimit

namespace HelixVonNeumannReceiver

variable {N : ℕ} [NeZero N]

/-- **The von Neumann receiver**: the regularized resolvent trace of a real spectrum `μ`, read on the
critical line `½ + i·`. Real spectrum = von Neumann self-adjoint reality (`SourceMode.ofReal`). -/
noncomputable def vonNeumannReceiver (μ : ℕ → ℝ) (z : ℂ) : ℂ :=
  -sourceTrace (fun n => SourceMode.ofReal (μ n)) (1 / 2 + Complex.I * z)

/-- **`hVN` discharged concretely.** The von Neumann receiver is a self-adjoint receiver — regular off
the real axis — because its spectrum is real: a point `z` with `Im z ≠ 0` is `|Im z|`-separated from
every (real) pole `½+iμₙ`, and the resolvent M-test (escape + trace-class summability of the spectrum)
gives a finite limit there. Earned from reality, not from the zeros. -/
theorem isSelfAdjointReceiver_vonNeumannReceiver (μ : ℕ → ℝ)
    (hesc : Tendsto (fun n => ‖(SourceMode.ofReal (μ n)).poleCoord‖) atTop atTop)
    (hsum : Summable (fun n => ‖(SourceMode.ofReal (μ n)).poleCoord‖⁻¹ ^ 2)) :
    IsSelfAdjointReceiver (vonNeumannReceiver μ) := by
  intro z hz
  have hδpos : 0 < |z.im| := abs_pos.mpr hz
  have hsep : ∀ n, |z.im| ≤
      ‖(1 / 2 + Complex.I * z) - (SourceMode.ofReal (μ n)).poleCoord‖ := by
    intro n
    rw [SourceMode.ofReal_poleCoord]
    have he : (1 / 2 + Complex.I * z) - (1 / 2 + Complex.I * (μ n : ℂ))
        = Complex.I * (z - (μ n : ℂ)) := by ring
    rw [he, norm_mul, Complex.norm_I, one_mul]
    have him : (z - (μ n : ℂ)).im = z.im := by simp [Complex.sub_im]
    calc |z.im| = |(z - (μ n : ℂ)).im| := by rw [him]
      _ ≤ ‖z - (μ n : ℂ)‖ := Complex.abs_im_le_norm _
  have hmtest := hasLocalMtest_resolvent (fun n => SourceMode.ofReal (μ n)) hδpos hsep hesc hsum
  have hcont_st : ContinuousAt (sourceTrace (fun n => SourceMode.ofReal (μ n)))
      (1 / 2 + Complex.I * z) :=
    continuousAt_sourceTrace_of_localMtest (fun n => SourceMode.ofReal (μ n)) hmtest
  have haff_t : Tendsto (fun w : ℂ => (1 / 2 : ℂ) + Complex.I * w) (𝓝 z)
      (𝓝 (1 / 2 + Complex.I * z)) :=
    (continuous_const.add (continuous_const.mul continuous_id)).continuousAt
  have hcomp_t := (hcont_st.tendsto.comp haff_t).neg
  exact ⟨vonNeumannReceiver μ z, hcomp_t.mono_left nhdsWithin_le_nhds⟩

/-- **GRH from the von Neumann receiver + the single trace identity.** The spine is now collapsed:
self-adjoint reality (`hVN`) is a theorem for the concrete `vonNeumannReceiver μ`; the prime foothold
(winding → `−L'/L`) and the Hadamard edge (`−L'/L` → actual zeros) are theorems. **The only remaining
hypothesis is `hCompat`** — the constructed real-spectrum trace equals `−L'/L(½+i·)` — together with
the standard spectral conditions (the von Neumann spectrum escapes to ∞ and is trace-class). GRH then
follows: real spectrum ⟹ zeros at `½+iμₙ` ⟹ `Re ρ = ½`. -/
theorem grh_of_vonNeumannReceiver_traceIdentity (χ : DirichletCharacter ℂ N) (μ : ℕ → ℝ)
    (hesc : Tendsto (fun n => ‖(SourceMode.ofReal (μ n)).poleCoord‖) atTop atTop)
    (hsum : Summable (fun n => ‖(SourceMode.ofReal (μ n)).poleCoord‖⁻¹ ^ 2))
    (hCompat : ∀ z, vonNeumannReceiver μ z
        = -logDeriv (DirichletCharacter.LFunction χ) (1 / 2 + Complex.I * z)) :
    GRHSpectral.GRH χ :=
  HelixCompatibilitySquare.grh_of_winding_vonNeumann_primeFoothold
    (isSelfAdjointReceiver_vonNeumannReceiver μ hesc hsum) hCompat

end HelixVonNeumannReceiver
