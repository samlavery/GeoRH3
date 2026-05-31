import Mathlib

/-!
# Core Definitions: The 1D Unit and the Critical Line

## The key idea

The critical strip has width 1 in the standard parameterization: Re(s) ∈ [0, 1].
We make this explicit by defining `UNIT := 1` — the width of the 1D projection
of the critical strip.

The critical line is then at `UNIT / 2`, the **midpoint** of [0, UNIT].
This is not a coincidence — it is forced by the functional equation's
reflection symmetry σ ↦ UNIT − σ, whose unique fixed point is UNIT / 2.

### Why this matters for scaling

When we rescale the strip by a positive factor `u` (e.g. u = log 7):
- The strip becomes [0, u · UNIT] = [0, u]
- The midpoint moves to u · UNIT / 2 = u / 2
- In the log(7) system: midpoint = log(7) · UNIT / 2 = log(7) / 2

The number "1/2" in the Riemann Hypothesis is **UNIT / 2**, not an
intrinsic constant. The geometric content is: zeros lie at the midpoint
of the strip, and "midpoint" means "half the unit".

### Connection to the scaling proof

In the scaling proof (`ScalingCoherence.lean`), we show that:
- On-line zeros (σ = UNIT/2) have growth rate u · UNIT/2 = u/2 in any system
- Off-line zeros (σ ≠ UNIT/2) have imbalance u · (2σ − UNIT) ≠ 0
- The log(7) system has midpoint log(7) · UNIT/2 = log(7)/2

Using UNIT/2 throughout makes these relationships transparent.
-/

noncomputable section

open Real Complex

/-! ## The 1D Unit -/

/-- The width of the critical strip in the standard parameterization.
    The strip is [0, UNIT] = [0, 1]. -/
def UNIT : ℝ := 1

/-- UNIT = 1. -/
@[simp] theorem UNIT_eq : UNIT = 1 := rfl

/-- UNIT is positive. -/
theorem UNIT_pos : (0 : ℝ) < UNIT := by simp [UNIT]

/-- UNIT is nonzero. -/
theorem UNIT_ne_zero : UNIT ≠ 0 := ne_of_gt UNIT_pos

/-! ## The Critical Line as UNIT / 2 -/

/-- The critical-line abscissa: the midpoint of [0, UNIT].
    In standard coordinates this is 1/2.
    Named `CriticalLineRe` for clarity. -/
def CriticalLineRe : ℝ := UNIT / 2

/-- The critical-line abscissa equals 1/2 in standard coordinates. -/
@[simp] theorem CriticalLineRe_eq : CriticalLineRe = 1 / 2 := by
  simp [CriticalLineRe]

/-- The critical-line abscissa is UNIT / 2. -/
theorem CriticalLineRe_eq_unit_div_two : CriticalLineRe = UNIT / 2 := rfl

/-- `CoshBalance` — backward-compatible alias for the critical-line abscissa.
    Named for the `cosh` Mellin transform characterization. -/
def CoshBalance : ℝ := UNIT / 2

/-- `CoshBalance` is 1/2. -/
@[simp] theorem CoshBalance_eq : CoshBalance = 1 / 2 := by
  simp [CoshBalance]

/-- `CoshBalance` equals `CriticalLineRe`. -/
theorem CoshBalance_eq_CriticalLineRe : CoshBalance = CriticalLineRe := rfl

/-- `CoshBalance` is UNIT / 2. -/
theorem CoshBalance_eq_unit_div_two : CoshBalance = UNIT / 2 := rfl

/-! ## Nontrivial Zeros -/

/-- A nontrivial zero of the Riemann zeta function (predicate form):
    `ζ(s) = 0` with `s` in the critical strip `0 < Re(s) < UNIT`.
    Uses Mathlib's `riemannZeta`. -/
def IsNontrivialZetaZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < UNIT

/-- Nontrivial zeros of the Riemann zeta function:
    `{s : ℂ | 0 < Re(s) ∧ Re(s) < UNIT ∧ ζ(s) = 0}`.
    Uses Mathlib's `riemannZeta`. -/
def NontrivialZeros : Set ℂ :=
  { s : ℂ | 0 < s.re ∧ s.re < UNIT ∧ riemannZeta s = 0 }

/-- Alias for `NontrivialZeros` for backward compatibility. -/
def NontrivialZetaZeros : Set ℂ := NontrivialZeros

/-- `NontrivialZetaZeros` is definitionally equal to `NontrivialZeros`. -/
theorem NontrivialZetaZeros_eq : NontrivialZetaZeros = NontrivialZeros := rfl

/-- Off-line nontrivial zeros: those with `Re(s) ≠ UNIT/2`. -/
def OffLineZeros : Set ℂ :=
  { s ∈ NontrivialZeros | s.re ≠ CriticalLineRe }

/-- On-line nontrivial zeros: those with `Re(s) = UNIT/2`. -/
def OnLineZeros : Set ℂ :=
  { s ∈ NontrivialZeros | s.re = CriticalLineRe }

/-- An offline nontrivial zeta zero (predicate form). -/
def IsOfflineZetaZero (s : ℂ) : Prop :=
  s ∈ NontrivialZeros ∧ s.re ≠ CriticalLineRe

/-- Membership in `NontrivialZeros`. -/
theorem mem_NontrivialZeros_iff {s : ℂ} :
    s ∈ NontrivialZeros ↔ 0 < s.re ∧ s.re < UNIT ∧ riemannZeta s = 0 := Iff.rfl

/-- Membership in `OffLineZeros`. -/
theorem mem_OffLineZeros_iff {s : ℂ} :
    s ∈ OffLineZeros ↔ s ∈ NontrivialZeros ∧ s.re ≠ CriticalLineRe := Iff.rfl

/-- Membership in `OnLineZeros`. -/
theorem mem_OnLineZeros_iff {s : ℂ} :
    s ∈ OnLineZeros ↔ s ∈ NontrivialZeros ∧ s.re = CriticalLineRe := Iff.rfl

/-! ## Scaling the Unit -/

/-- The midpoint of the strip [0, u · UNIT] under scaling by u. -/
def scaled_midpoint (u : ℝ) : ℝ := u * UNIT / 2

/-- The scaled midpoint equals u/2 in standard coordinates. -/
@[simp] theorem scaled_midpoint_eq (u : ℝ) : scaled_midpoint u = u / 2 := by
  simp [scaled_midpoint]

/-- The standard midpoint is CriticalLineRe. -/
theorem scaled_midpoint_one : scaled_midpoint 1 = CriticalLineRe := by
  simp [scaled_midpoint, CriticalLineRe]

/-- The log(7) midpoint is log(7)/2. -/
theorem scaled_midpoint_log7 : scaled_midpoint (Real.log 7) = Real.log 7 / 2 := by
  simp [scaled_midpoint]

/-- log(7) is positive. -/
theorem log7_pos : (0 : ℝ) < Real.log 7 := by positivity

/-- log(7)/2 ≠ 1/2 — the midpoint depends on the coordinate unit. -/
theorem log7_midpoint_ne_half : scaled_midpoint (Real.log 7) ≠ CriticalLineRe := by
  simp [scaled_midpoint, CriticalLineRe]
  linarith [show 1 < Real.log 7 by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    exact Real.exp_one_lt_d9.trans_le (by norm_num)]

/-- The scaled midpoint is always u · (UNIT/2) = u · CriticalLineRe. -/
theorem scaled_midpoint_eq_u_times_critical (u : ℝ) :
    scaled_midpoint u = u * CriticalLineRe := by
  simp [scaled_midpoint, CriticalLineRe]; ring

/-! ## The Reflection Involution -/

/-- The functional equation's reflection on [0, u · UNIT]: σ ↦ u · UNIT − σ.
    In standard coordinates (u = 1): σ ↦ 1 − σ. -/
def fe_involution (u σ : ℝ) : ℝ := u * UNIT - σ

/-- The involution is an involution. -/
theorem fe_involution_involution (u σ : ℝ) :
    fe_involution u (fe_involution u σ) = σ := by
  simp [fe_involution]

/-- The unique fixed point of the involution is u · UNIT / 2 = scaled_midpoint u. -/
theorem fe_involution_fixed_iff (u σ : ℝ) :
    fe_involution u σ = σ ↔ σ = scaled_midpoint u := by
  simp [fe_involution, scaled_midpoint]; constructor <;> intro h <;> linarith

/-- In standard coordinates, the fixed point is UNIT/2 = 1/2. -/
theorem fe_standard_fixed (σ : ℝ) :
    fe_involution 1 σ = σ ↔ σ = CriticalLineRe := by
  simp [fe_involution, CriticalLineRe]; constructor <;> intro h <;> linarith

/-- In log(7) coordinates, the fixed point is log(7) · UNIT / 2 = log(7)/2. -/
theorem fe_log7_fixed (σ : ℝ) :
    fe_involution (Real.log 7) σ = σ ↔ σ = Real.log 7 / 2 := by
  simp [fe_involution]; constructor <;> intro h <;> linarith

/-! ## Growth Imbalance via UNIT -/

/-- The growth imbalance of a zero pair (σ, UNIT−σ) scaled by u.
    Imbalance = u·σ − u·(UNIT−σ) = u·(2σ − UNIT). -/
def growth_imbalance_unit (u σ : ℝ) : ℝ := u * (2 * σ - UNIT)

/-- Imbalance is zero iff σ = UNIT/2. -/
theorem growth_imbalance_unit_zero_iff (u σ : ℝ) (hu : u ≠ 0) :
    growth_imbalance_unit u σ = 0 ↔ σ = UNIT / 2 := by
  simp [growth_imbalance_unit, UNIT, hu]
  constructor <;> intro h <;> linarith

/-- In standard coordinates, imbalance = 0 iff σ = 1/2. -/
theorem growth_imbalance_unit_standard (u σ : ℝ) (hu : u ≠ 0) :
    growth_imbalance_unit u σ = 0 ↔ σ = CriticalLineRe := by
  rw [growth_imbalance_unit_zero_iff u σ hu]
  simp [CriticalLineRe]

end
