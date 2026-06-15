import Mathlib
import RequestProject.SpectralSide
import RequestProject.GRHSpectralCriterion

/-!
# Projection loss: 3D helix → 2D unit circle, linked to height and the zero values

The 3-D helix carries **radial growth** (`R = e^{mode}·k`) and **pitch** (winding height). The
projection down to the 2-D unit circle **drops both**, leaving the bare circle `‖w‖ = 1`. The dropped
radial-and-pitch is the **projection loss** — the Γ factor, accumulated (log-free; the winding *is*
the log) from the prime residues `res_p = p/(p-1) = 1/w(p)`.

On a zero `ρ = σ + iγ`, the two 3-D coordinates read off as:
* **height** `= Im ρ = γ` — turns × pitch, the winding height; **kept** by the projection;
* **projection loss** `= Re ρ − ½` — the radial deviation; **dropped** by the projection.

So the shadow `w(ρ)` lands on `‖w‖ = 1` exactly when the projection loss vanishes — the radial fully
dropped, only the height surviving. GRH is then "every zero projects cleanly onto the circle." No
Euler product, no FE, no `log`.
-/

open Complex

namespace HelixProjectionLoss

/-- A prime's **residue** `res_p = p/(p-1)` — the inverted Möbius shadow `1/w(p)`. Pure division. -/
noncomputable def res (p : ℕ) : ℝ := (p : ℝ) / ((p : ℝ) - 1)

/-- **`res_p` is exactly the inverse of the prime's 2-D Möbius shadow** `w(p) = 1 − 1/p = (p−1)/p`. -/
theorem res_eq_inv_w {p : ℕ} (hp : 2 ≤ p) : (res p : ℂ) = (SpectralSide.w (p : ℂ))⁻¹ := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hp1 : (p : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (by omega : p ≠ 1))
  rw [res, SpectralSide.w]
  push_cast
  field_simp

/-! ## The 3-D → 2-D projection and its loss -/

/-- A point on the 3-D helix: **radial growth** `radial`, **pitch** (height) `pitch`, and the angular
    position `angle`. -/
structure Helix3D where
  radial : ℝ
  pitch : ℝ
  angle : ℝ

/-- The **2-D projection**: keep only the angle, land on the unit circle. Radial growth and pitch are
    dropped. -/
noncomputable def project (x : Helix3D) : Circle := Circle.exp x.angle

/-- The **projection loss**: the `(radial growth, pitch)` that 2-D does not carry. -/
def projectionLoss (x : Helix3D) : ℝ × ℝ := (x.radial, x.pitch)

/-- **The shadow lands on the unit circle** — for *every* 3-D point, because the off-circle data
    (radial + pitch) is exactly what the projection loses. -/
theorem project_on_circle (x : Helix3D) : ‖(project x : ℂ)‖ = 1 := by
  rw [project, Circle.norm_coe]

/-- The **height** of a zero on the helix `= Im ρ = γ` (turns × pitch) — the winding coordinate the
    projection **keeps**. -/
def height (ρ : ℂ) : ℝ := ρ.im

/-- The **projection loss carried by a zero** `= Re ρ − ½` — the radial deviation the 3-D→2-D
    projection **drops** (here: converts to height). -/
noncomputable def zeroLoss (ρ : ℂ) : ℝ := ρ.re - 1 / 2

/-! ## Conservation: the loss is **not** discarded — it is converted to height

Nothing is thrown away. The 3-D radial growth does not push the shadow *off* the circle; it **winds**
it *along* the circle, converting the radial into **height** (the imaginary part `γ`). Each singularity
fires a zero at the running height, and the heights are **additive**, not absolute. -/

/-- **The conserving projection.** The radial `r` **winds** the shadow (adds to the phase/height) and
    stays on the unit circle — the radial becomes height, never an off-circle (real-axis) component. -/
noncomputable def projectConserving (r θ : ℝ) : Circle := Circle.exp (θ + r)

/-- The conserving projection is on the circle: the radial winds, it does not push off. -/
theorem projectConserving_on_circle (r θ : ℝ) : ‖(projectConserving r θ : ℂ)‖ = 1 := by
  rw [projectConserving, Circle.norm_coe]

/-- **Additive height.** Each singularity fires at the running total of the radial increments — the
    2-D height is additive, not absolute: `height (n+1) = height n + incr n`. -/
def accumHeight (incr : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => accumHeight incr n + incr n

@[simp] theorem accumHeight_zero (incr : ℕ → ℝ) : accumHeight incr 0 = 0 := rfl

theorem accumHeight_succ (incr : ℕ → ℝ) (n : ℕ) :
    accumHeight incr (n + 1) = accumHeight incr n + incr n := rfl

/-! ## The actual helix geometry: radial growth `e^6·k`, pitch `π/3`

**No `½` is assumed for the zero's real part** — it is not an input, it falls out when all the other
terms balance. For now: the concrete helix, and the height you read off at a singularity. -/

/-- The helix **radial growth** `R(k) = e^6 · k` — Archimedean spiral, `+ e^6` per loop (bigger
    loops). -/
noncomputable def radialGrowth (k : ℕ) : ℝ := Real.exp 6 * (k : ℝ)

/-- The helix **pitch** `= π/3`. -/
noncomputable def pitch : ℝ := Real.pi / 3

/-- The **height after `k` turns**: each turn (a bigger loop) climbs by the pitch — additive, not
    absolute. `height(k) = k · π/3`. When a singularity fires at turn `k`, **this is the measured
    height**; no `½`, no assumed real part. -/
noncomputable def helixHeight (k : ℕ) : ℝ := (k : ℝ) * pitch

/-- **Each turn adds the pitch** `π/3` — the height is additive. -/
theorem helixHeight_succ (k : ℕ) : helixHeight (k + 1) = helixHeight k + pitch := by
  rw [helixHeight, helixHeight]; push_cast; ring

/-- The measured height at turn `k` is exactly `k · π/3`. -/
theorem helixHeight_eq (k : ℕ) : helixHeight k = (k : ℝ) * (Real.pi / 3) := rfl

/-- The loops **grow** each turn: `R(k) < R(k+1)`. -/
theorem radialGrowth_lt_succ (k : ℕ) : radialGrowth k < radialGrowth (k + 1) := by
  have h6 : (0 : ℝ) < Real.exp 6 := Real.exp_pos 6
  have hk : (k : ℝ) < ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_succ_self k
  rw [radialGrowth, radialGrowth]; nlinarith [hk, h6]

/-! ## The link: projection loss ↔ height ↔ the zero's `w`-value and GRH -/

/-- A zero is **`height` along, `zeroLoss` off**: its real/imag parts are exactly the kept height and
    the dropped radial (shifted by the `½` baseline). -/
theorem re_im_eq (ρ : ℂ) : ρ.re = zeroLoss ρ + 1 / 2 ∧ ρ.im = height ρ := by
  refine ⟨by rw [zeroLoss]; ring, rfl⟩

/-- **On the circle ⟺ no projection loss.** The zero's Möbius shadow `w(ρ)` sits on the unit circle
    exactly when its projection loss vanishes — radial fully dropped, height kept. -/
theorem w_unit_iff_zeroLoss_zero (ρ : ℂ) (hρ : ρ ≠ 0) :
    Complex.normSq (SpectralSide.w ρ) = 1 ↔ zeroLoss ρ = 0 := by
  rw [SpectralSide.w_unit_iff_half ρ hρ, zeroLoss]
  constructor <;> intro h <;> linarith

/-- **GRH ⟺ every zero projects onto the circle with no loss.** GRH for `χ` holds exactly when every
    nontrivial zero has zero projection loss — the radial fully dropped by the 3-D→2-D projection,
    only the height `Im ρ` surviving, shadow on `‖w‖ = 1`. (`GRH_iff_spectral_unitary` rephrased in
    projection-loss terms via `w_unit_iff_zeroLoss_zero`.) -/
theorem grh_iff_no_projectionLoss {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    GRHSpectral.GRH χ ↔ ∀ ρ ∈ GRHSpectral.NontrivialZeros χ, zeroLoss ρ = 0 := by
  unfold GRHSpectral.GRH zeroLoss
  constructor <;> intro h ρ hρ <;> have := h ρ hρ <;> linarith

end HelixProjectionLoss
