import RequestProject.OfflineAmplitudeMethods
import RequestProject.DirichletLHadamardComplete

/-!
# Amplitude defect = excess cosine energy; the accumulating spectral energy defect; no second ledger

Two unconditional AM-GM facts (no RH, no zero-location assumption anywhere), plus the structural
**no second ledger**:

1. **Amplitude defect IS excess cosine energy.** The AM-GM amplitude defect
   `r^β + r^{1−β} − 2r^{1/2}` equals `2 r^{1/2} · (cosh((β−½)·log r) − 1)` — the balanced
   amplitude baseline `2r^{1/2}` times the *excess cosine energy* `cosh(·) − 1 ≥ 0`. The rpow
   amplitude excess and the hyperbolic-cosine excess are the same quantity.

2. **Spectral energy defect accumulates and is non-cancellable.** Summing the per-zero defect
   over a finite zero set gives `SpectralEnergyDefect`, a sum of non-negative terms. It vanishes
   **iff every zero is on the line**; one off-line zero forces a strictly positive total that no
   other zero can cancel (all terms `≥ 0`); and it is monotone in the zero set (more off-line
   zeros ⇒ more defect).

3. **No second ledger.** The defect rides the *same* zeros the trace balance `globalTraceBalance`
   (`= DirichletLHadamard.hadamardPartialFraction`) couples to the primes: each summand is one of
   those poles, and its defect is exactly the cosh-face of that pole (`no_second_ledger`). One
   accounting, two readings — no hidden ledger. (Structural; the substance is the proved coupling.)

Honest scope: items 1–2 are the unconditional **detector**; item 3 is the **one-ledger** structural
fact. None of this proves GRH. The *forcing* — `globalTraceBalance ⟹ SpectralEnergyDefect = 0`,
which `SpectralEnergyDefect_eq_zero_iff` would then collapse onto the line — is a separate step, not
in this file.
-/

open Real Finset BigOperators ZetaDefs

namespace AMGMDefect

variable {r : ℝ} {N : ℕ} [NeZero N]

/-- **Amplitude defect = excess cosine energy.** `r^β + r^{1−β} − 2r^{1/2}` is exactly the balanced
amplitude baseline `2r^{1/2}` times the excess cosine energy `cosh((β−½)·log r) − 1`. Pure algebra
(`r^x = exp(x·log r)`, `2cosh = exp + exp(−·)`), unconditional, for `r > 0`. -/
theorem amplitudeDefect_eq_cosh_excess (hr : 0 < r) (β : ℝ) :
    amplitudeDefect r β
      = 2 * r ^ (1 / 2 : ℝ) * (Real.cosh ((β - 1 / 2) * Real.log r) - 1) := by
  unfold amplitudeDefect zeroPairEnvelope balancedEnvelope
  rw [Real.rpow_def_of_pos hr, Real.rpow_def_of_pos hr, Real.rpow_def_of_pos hr, Real.cosh_eq]
  have e1 : Real.log r * β = (β - 1 / 2) * Real.log r + Real.log r * (1 / 2 : ℝ) := by ring
  have e2 : Real.log r * (1 - β)
      = -((β - 1 / 2) * Real.log r) + Real.log r * (1 / 2 : ℝ) := by ring
  rw [e1, e2, Real.exp_add, Real.exp_add]
  ring

/-- The **excess cosine energy** `cosh x − 1` is non-negative (and `0` iff `x = 0`). -/
theorem cosh_excess_nonneg (x : ℝ) : 0 ≤ Real.cosh x - 1 := by
  have := Real.one_le_cosh x; linarith

/-- Re-derivation of amplitude-defect non-negativity through the **cosine** side: a positive
baseline `2r^{1/2}` times the non-negative cosine excess. -/
theorem amplitudeDefect_nonneg_via_cosh (hr : 0 < r) (β : ℝ) : 0 ≤ amplitudeDefect r β := by
  rw [amplitudeDefect_eq_cosh_excess hr]
  have hbase : 0 ≤ 2 * r ^ (1 / 2 : ℝ) := by positivity
  exact mul_nonneg hbase (cosh_excess_nonneg _)

/-- **Spectral energy defect** of a finite zero set `S` at scale `r`, with multiplicity weight `m`:
the sum of per-zero excess cosine energies `m ρ · amplitudeDefect r (Re ρ)`. -/
noncomputable def SpectralEnergyDefect (m : ℂ → ℝ) (r : ℝ) (S : Finset ℂ) : ℝ :=
  ∑ ρ ∈ S, m ρ * amplitudeDefect r ρ.re

/-- **Non-negative**: a sum of non-negative weighted defects (`r > 0`, `m ≥ 0`). -/
theorem SpectralEnergyDefect_nonneg {m : ℂ → ℝ} (hr : 0 < r) {S : Finset ℂ}
    (hm : ∀ ρ ∈ S, 0 ≤ m ρ) : 0 ≤ SpectralEnergyDefect m r S :=
  Finset.sum_nonneg fun ρ hρ => mul_nonneg (hm ρ hρ) (amplitudeDefect_nonneg hr ρ.re)

/-- **Non-cancellable / coercive: the total defect is `0` iff every zero is on the line.** With
strictly positive multiplicities and `r ≠ 1`, the sum of non-negative excess-cosine energies is `0`
exactly when each term is — i.e. every `Re ρ = ½`. A single off-line zero cannot be hidden: its
positive excess cannot be cancelled by any other zero, since all terms are `≥ 0`. -/
theorem SpectralEnergyDefect_eq_zero_iff {m : ℂ → ℝ} (hr : 0 < r) (hr1 : r ≠ 1)
    {S : Finset ℂ} (hm : ∀ ρ ∈ S, 0 < m ρ) :
    SpectralEnergyDefect m r S = 0 ↔ ∀ ρ ∈ S, ρ.re = 1 / 2 := by
  unfold SpectralEnergyDefect
  rw [Finset.sum_eq_zero_iff_of_nonneg
        (fun ρ hρ => mul_nonneg (hm ρ hρ).le (amplitudeDefect_nonneg hr ρ.re))]
  refine ⟨fun h ρ hρ => ?_, fun h ρ hρ => ?_⟩
  · have hd : amplitudeDefect r ρ.re = 0 :=
      (mul_eq_zero.mp (h ρ hρ)).resolve_left (hm ρ hρ).ne'
    have := (amplitudeDefect_eq_zero_iff hr hr1).mp hd
    rwa [CoshBalance_eq_half] at this
  · have hd : amplitudeDefect r ρ.re = 0 := by
      rw [amplitudeDefect_eq_zero_iff hr hr1, CoshBalance_eq_half]; exact h ρ hρ
    rw [hd, mul_zero]

/-- **Accumulation (monotone in the zero set).** Adding zeros never decreases the defect. -/
theorem SpectralEnergyDefect_mono {m : ℂ → ℝ} (hr : 0 < r) {S T : Finset ℂ}
    (hST : S ⊆ T) (hm : ∀ ρ ∈ T, 0 ≤ m ρ) :
    SpectralEnergyDefect m r S ≤ SpectralEnergyDefect m r T :=
  Finset.sum_le_sum_of_subset_of_nonneg hST
    (fun ρ hρT _ => mul_nonneg (hm ρ hρT) (amplitudeDefect_nonneg hr ρ.re))

/-- **One off-line zero strictly raises the defect — non-cancellable accumulation.** Inserting an
off-line zero (`Re ρ ≠ ½`, positive multiplicity) strictly increases the spectral energy defect: its
excess cosine energy is `> 0` and adds to a non-negative total. The more off-line zeros, the more
defect accumulates, and none of it cancels. -/
theorem SpectralEnergyDefect_lt_insert_offline {m : ℂ → ℝ} (hr : 0 < r) (hr1 : r ≠ 1)
    {S : Finset ℂ} {ρ : ℂ} (hρS : ρ ∉ S) (hmρ : 0 < m ρ) (hoff : ρ.re ≠ 1 / 2)
    (hm : ∀ τ ∈ S, 0 ≤ m τ) :
    SpectralEnergyDefect m r S < SpectralEnergyDefect m r (insert ρ S) := by
  unfold SpectralEnergyDefect
  rw [Finset.sum_insert hρS]
  have hpos : 0 < m ρ * amplitudeDefect r ρ.re :=
    mul_pos hmρ (offline_amplitude_defect_pos hr hr1 (by rw [CoshBalance_eq_half]; exact hoff))
  have hge : 0 ≤ ∑ τ ∈ S, m τ * amplitudeDefect r τ.re :=
    Finset.sum_nonneg fun τ hτ => mul_nonneg (hm τ hτ) (amplitudeDefect_nonneg hr τ.re)
  linarith

/-! ## No second ledger: the defect rides the trace's zeros, entry for entry

The cosine-energy defect and the prime-field trace are **one accounting**, not two. The single
explicit-formula identity `globalTraceBalance` (`= DirichletLHadamard.hadamardPartialFraction`) is
indexed by the whole `NontrivialZeros χ`, and `SpectralEnergyDefect` sums those same zeros — each
entry's defect being the excess cosine energy of that very pole. -/

/-- **No second ledger.** For a primitive `χ ≠ 1`:

* the trace balance `DirichletLHadamard.hadamardPartialFraction` is the single explicit-formula
  identity, indexed by the *whole* `NontrivialZeros χ`; and
* every zero summed by `SpectralEnergyDefect` is one of *those very poles* (`ρ ∈ NontrivialZeros χ`),
  and its defect contribution is exactly the **excess cosine energy of that same pole**:
  `m ρ · 2r^{1/2}(cosh((Re ρ − ½)·log r) − 1)`.

So the cosine-energy ledger is the cosh-face of the trace's pole ledger, **entry for entry** — one
set of zeros, two readings. No zero contributes to the defect outside the single trace coupling.

Not RH: the substance is the proved trace coupling; the *forcing* (`SpectralEnergyDefect = 0`) is a
separate step (`SpectralEnergyDefect_eq_zero_iff` is the on-line indicator on these zeros). -/
theorem no_second_ledger {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (hχp : χ.IsPrimitive)
    {S : Finset ℂ} (hS : ↑S ⊆ GRHSpectral.NontrivialZeros χ) {m : ℂ → ℝ} (hr : 0 < r) :
    DirichletLHadamard.HadamardPartialFraction χ ∧
      ∀ ρ ∈ S, ρ ∈ GRHSpectral.NontrivialZeros χ ∧
        m ρ * amplitudeDefect r ρ.re
          = m ρ * (2 * r ^ (1 / 2 : ℝ) * (Real.cosh ((ρ.re - 1 / 2) * Real.log r) - 1)) :=
  ⟨DirichletLHadamard.hadamardPartialFraction hχ hχp,
   fun ρ hρ => ⟨hS (Finset.mem_coe.mpr hρ), by rw [amplitudeDefect_eq_cosh_excess hr ρ.re]⟩⟩

/-- **The shared ledger is the on-line indicator.** On the *same* zeros the trace couples (any
`S ⊆ NontrivialZeros χ`), the single defect ledger reads `0` exactly when every one of those poles is
on the line. (Forcing the `0` is the open step; this only records that the one ledger *is* the on-line
test.) -/
theorem shared_ledger_is_online_indicator {χ : DirichletCharacter ℂ N}
    {S : Finset ℂ} (_hS : ↑S ⊆ GRHSpectral.NontrivialZeros χ) {m : ℂ → ℝ}
    (hr : 0 < r) (hr1 : r ≠ 1) (hm : ∀ ρ ∈ S, 0 < m ρ) :
    SpectralEnergyDefect m r S = 0 ↔ ∀ ρ ∈ S, ρ.re = 1 / 2 :=
  SpectralEnergyDefect_eq_zero_iff hr hr1 hm

end AMGMDefect
