import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace HarmonicProjection

open Real

/-!
# Projection of a harmonic event from 3D → 2D circle → 1D line

We model the chain of projections described informally as follows.

* **3D harmonic value.**  The harmonic/vertical component of the spiral helix is a real
  number `t : ℝ`.  Its *midline* (the value a harmonic returns to after a sign flip with
  no drift) is `t = 0`.

* **Möbius projection onto the unit circle (2D).**  The Cayley / stereographic map
  `t ↦ 2 * arctan t` sends the whole real line bijectively onto the principal arc
  `(-π, π)` of the unit circle.  This is a Möbius transformation of the line onto the
  circle.  The midline `t = 0` maps to the angle `0`, i.e. the point `(1, 0)` which is the
  *midpoint of the arc*.

* **"Taking logs" projection onto the 1D line.**  For a unit–circle point `e^{iθ}` the
  principal logarithm is `i θ`; normalising the resulting coordinate `θ ∈ (-π, π)` to the
  unit interval gives `u = (θ + π) / (2 π) ∈ (0, 1)`.  The circle's midpoint `θ = 0` maps
  to `u = 1/2`, the *midpoint of the line segment* `(0,1)`.

* **"Sign flip forcing to the midline, no drift".**  The harmonic sits exactly at its
  midline, `t = 0`.  *No drift* is the statement that the maps carry no additive offset,
  i.e. they are odd–symmetric (`toCircleAngle`) / midpoint–preserving (`toLine`), so the
  midpoint is genuinely sent to the midpoint at each stage.

The final theorem `projection_midline` is the requested unconditional statement:
the projected image of the 3D midline is exactly `1/2`.
-/

/-- **Möbius / stereographic projection** of a 3D harmonic value `t` onto an angle on the
unit circle, valued in the principal arc `(-π, π)`. -/
noncomputable def toCircleAngle (t : ℝ) : ℝ := 2 * arctan t

/-- **"Taking logs" projection** of a circle angle `θ` onto a normalized 1D coordinate.
For `θ ∈ (-π, π)` the result lies in `(0, 1)`, with the arc midpoint `θ = 0` sent to `1/2`. -/
noncomputable def toLine (θ : ℝ) : ℝ := (θ + π) / (2 * π)

/-- The **full projection** from a 3D harmonic value to a 1D coordinate. -/
noncomputable def projection (t : ℝ) : ℝ := toLine (toCircleAngle t)

/-! ## No drift: the symmetries that pin the midpoint -/

/-
**No drift in the Möbius stage.**  The circle projection is odd, so it carries no
additive offset: the midline `t = 0` is the unique fixed centre of symmetry.
-/
theorem toCircleAngle_odd (t : ℝ) : toCircleAngle (-t) = - toCircleAngle t := by
  unfold HarmonicProjection.toCircleAngle; rw [ Real.arctan_neg ] ; ring;

/-
**The Möbius image of the 3D midline is the circle's midpoint.**
-/
theorem toCircleAngle_midline : toCircleAngle 0 = 0 := by
  -- By definition of toCircleAngle, we have toCircleAngle 0 = 2 * arctan 0.
  simp [HarmonicProjection.toCircleAngle]

/-
**No drift in the log stage.**  The log projection is affine, hence preserves
midpoints: the midpoint of any chord `[a, b]` maps to the midpoint of the images.
-/
theorem toLine_midpoint (a b : ℝ) :
    toLine ((a + b) / 2) = (toLine a + toLine b) / 2 := by
  unfold HarmonicProjection.toLine; ring;

/-
The two ends of the principal arc (`θ = ±π`, the crest/trough of the harmonic on the
circle) map to the two ends `0` and `1` of the line segment.
-/
theorem toLine_neg_pi : toLine (-π) = 0 := by
  grind +locals

theorem toLine_pi : toLine π = 1 := by
  -- By definition of `toLine`, we have `toLine π = (π + π) / (2 * π)`.
  unfold HarmonicProjection.toLine
  field_simp
  ring

/-
**The log image of the circle's midpoint is the midpoint `1/2` of the line.**
-/
theorem toLine_midline : toLine 0 = 1 / 2 := by
  unfold HarmonicProjection.toLine; ring_nf; norm_num [ Real.pi_ne_zero ] ;

/-
Consistency: the line midpoint `1/2` is exactly the midpoint of the two arc–endpoint
images, confirming `1/2` is the genuine midpoint and not an arbitrary value.
-/
theorem toLine_midpoint_of_endpoints :
    toLine ((-π + π) / 2) = (toLine (-π) + toLine π) / 2 := by
  convert toLine_midpoint ( -Real.pi ) Real.pi using 1

/-! ## Main theorem -/

/-
**Unconditional projection theorem.**
A harmonic event whose sign flip forces it to the 3D midline (`t = 0`), with no drift
introduced anywhere, projects through the Möbius map onto the circle's midpoint and then
through the log map onto the 1D midpoint, which equals `1/2`.
-/
theorem projection_midline : projection 0 = 1 / 2 := by
  convert toLine_midline using 1;
  exact congr_arg _ ( toCircleAngle_midline )

end HarmonicProjection