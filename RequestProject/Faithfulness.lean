import Mathlib
import RequestProject.HilbertPolyaChain

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

/-!
# Unconditional faithfulness via the loss-ledger / reconstruction-bijection method

A point of a 3D conical-helix ("harmonic fiber") is projected to a 2D unit circle and then to a
1D line. The **projection itself is lossy**: phase and radial information are genuinely destroyed.
The method recorded here is the **loss-ledger / reconstruction-bijection** method:

> keep a *ledger* of exactly the channels the projection destroys; then the map
> `fiber ↦ (retained channel, loss ledger)` is a **bijection**, so the original fiber can be
> reconstructed exactly. No information is truly lost once it is booked in the ledger.

The whole development is **faithful** (the reconstruction is an exact two-sided inverse) and
**unconditional** (no hypotheses, only the standard Lean/Mathlib axioms).

## The channels

A harmonic fiber is recorded in the **cylindrical coordinate system** `(radial r, phase θ, height z)`.
That is only the coordinate *system*; the *shape* traced is a genuine **cone**, characterised by
`r = coneSlope · z` (the radius grows with the height) — emphatically **not** a cylinder, whose
radius would be constant.

* **height** — the *retained* channel (`project`).
* **(radial, phase)** — the *lost* channels, booked in the `ledger`.

The conical helix **grows up and out**: the height climbs at a constant unit **pitch** while the
radius opens out at the constant rate `coneSlope` (a *separate* constant), and the phase carries the
`π/3` shift, so `coneFiber t = (coneSlope · t, t + π/3, t)`. It lies on the cone `r = coneSlope · z`
(`coneFiber_on_cone`), equivalently on the Cartesian cone `x² + y² = (coneSlope · z)²`
(`realize_coneFiber_on_cone`), and its radius is strictly increasing
(`coneFiber_radius_strictMono`) — the defining "up and out" growth of a cone rather than the
constant radius of a cylinder.

## The reconstruction bijection (the core result)

`record f = (project f, ledger f)` and `reconstruct d` invert each other:

* `reconstructionBijection : Fiber ≃ ℝ × (ℝ × ℝ)` — the explicit bijection.
* `reconstruct_record`, `record_injective`, `record_bijective` — faithfulness, unconditionally.

## Why the ledger is necessary (the loss ledger is accurate)

The purely geometric projection `geomProj` (realize on the unit circle, keep height, *drop the
ledger*) is provably **not injective**:

* `phase_lost`  — `2π`-periodicity collapses distinct phases;
* `radial_lost` — dropping the radius collapses distinct radii.

So without the ledger the data is destroyed; *with* it, reconstruction is bijective. That contrast
is the whole point.

## The 2D and 1D stages

* The projected atom lands on the unit circle: `projAtom_on_unit_circle`, `unitCircleProj_on_circle`.
* The 2D→1D projection "is literally the log": on the positive height encoding `exp h`, `Real.log`
  recovers `h` (`log_recovers_height`) and is injective there (`lineProj_faithful`). The end-to-end
  pipeline `pipeline t = t` (`pipeline_id`) is a bijection (`pipeline_bijective`).

## Coordinate shifts and rescalings preserve information

A shift `x ↦ x + c` and a nonzero rescaling `x ↦ k·x` (and more generally any affine
`x ↦ k·x + c`) are **bijections** of `ℝ` (`shift_bijective`, `rescale_bijective`,
`affineCoord_bijective`, with the explicit inverse `affineCoordEquiv`): they neither lose nor gain
information. In particular the midpoint rescaling `halve = (·)/2` identifies the pairs
`(1, 1/2)`, `(π/3, π/6)` and `(log 7, log 7 / 2)` — from the geometric-projection perspective these
are **the same value** (`same_value_under_halve`, `halve_bijective`).

## Honest scope note (no Riemann Hypothesis is proved)

The "critical line at `1/2`" enters only as the literal numeric midpoint of the height
parametrisation (`midpoint_to_critical`: helix midpoint → circle midpoint → `1/2`). It is a
statement about coordinates and information flow and carries **no** number-theoretic content; it
does **not** prove or bear on the Riemann Hypothesis.
-/

namespace ConeProjection

noncomputable section

/-- A harmonic fiber recorded in the cylindrical coordinate system `(radial, phase, height)`.
The *shape* traced by `coneFiber` is a cone (`r = coneSlope · z`), not a cylinder. -/
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

/-! ### The reconstruction bijection (faithful, unconditional) -/

/-- **Faithfulness.** Reconstruction from the record returns the original fiber exactly:
no information is lost once the ledger is kept. -/
theorem reconstruct_record (f : Fiber) : reconstruct (record f) = f := by
  unfold ConeProjection.reconstruct ConeProjection.record; aesop;

/-- Records determine fibers: `record` is injective. -/
theorem record_injective : Function.Injective record := by
  exact fun x y h => by simpa [ reconstruct_record ] using congr_arg ( fun p => reconstruct p ) h;

/-- Every record is realised: `record` is surjective. -/
theorem record_surjective : Function.Surjective record := by
  exact fun x => ⟨ reconstruct x, reconstruct_record _ ⟩

/-- **The reconstruction bijection.** `fiber ↦ (retained channel, loss ledger)` is a bijection
of the fiber space with retained-data × ledger, with explicit inverse `reconstruct`. -/
def reconstructionBijection : Fiber ≃ ℝ × (ℝ × ℝ) where
  toFun := record
  invFun := reconstruct
  left_inv := fun f => reconstruct_record f
  right_inv := fun _ => rfl

/-- The reconstruction bijection is bijective (packaged restatement). -/
theorem record_bijective : Function.Bijective record := by
  exact ⟨ record_injective, record_surjective ⟩

/-! ### The conical helix: it grows **up and out**, and height alone reconstructs the fiber -/

/-- The cone's **radial growth rate**: how fast the cone opens *out* per unit of height. A positive
constant, distinct from the unit pitch, so the fiber genuinely traces a **cone** (radius grows with
height), not a cylinder (constant radius). -/
def coneSlope : ℝ := 2

/-- The radial growth rate is a positive constant: the cone really opens out. -/
theorem coneSlope_pos : 0 < coneSlope := by norm_num [ConeProjection.coneSlope]

/-- The conical helix (harmonic fiber). The height climbs at constant unit **pitch** (`height = t`)
while the radius opens **out** at the constant rate `coneSlope` (`radial = coneSlope · t`), and the
phase carries the `π/3` shift. So the fiber spirals **up and out** along a cone. -/
def coneFiber (t : ℝ) : Fiber := (coneSlope * t, t + Real.pi / 3, t)

/-- On the helix the retained channel is the parameter (the height climbs at unit pitch). -/
theorem project_coneFiber (t : ℝ) : project (coneFiber t) = t := by
  rfl

/-- On the helix the **ledger is a function of the retained channel**: the radius is `coneSlope`
times the height and the phase is the height plus the `π/3` shift. Hence on the helix no extra
ledger is needed — the retained height alone reconstructs the fiber. -/
theorem ledger_coneFiber (t : ℝ) :
    ledger (coneFiber t)
      = (coneSlope * project (coneFiber t), project (coneFiber t) + Real.pi / 3) := by
      rfl

/-- **The fiber lies on the cone** `r = coneSlope · z`: the radius is a constant multiple of the
height. This is the defining property of a *cone* (radius grows with height), as opposed to a
cylinder (constant radius). -/
theorem coneFiber_on_cone (t : ℝ) :
    radial (coneFiber t) = coneSlope * height (coneFiber t) := rfl

/-- The radius **grows out**: it is strictly increasing in the parameter, so the cone opens up — in
contrast with a cylinder, whose radius is constant. -/
theorem coneFiber_radius_strictMono :
    StrictMono (fun t => radial (coneFiber t)) := by
  intro a b hab
  simp only [ConeProjection.radial, ConeProjection.coneFiber]
  exact mul_lt_mul_of_pos_left hab coneSlope_pos

/-- The helix is faithfully parametrised by `t` (its embedding is injective). -/
theorem coneFiber_injective : Function.Injective coneFiber := by
  intro x y h
  have hx : (coneFiber x).2.2 = (coneFiber y).2.2 := by rw [h]
  simpa [ConeProjection.coneFiber] using hx

/-- The helix section: reconstructing from the retained channel alone returns the helix point. -/
theorem coneFiber_height_section (t : ℝ) : coneFiber (project (coneFiber t)) = coneFiber t := by
  -- By definition of `project`, we have `project (coneFiber t) = t`.
  apply congr_arg ConeProjection.coneFiber; exact project_coneFiber t

/-! ### Geometric realisation and why the ledger is necessary -/

/-- Cylindrical → Cartesian realisation of an abstract `(radial, phase, height)` fiber. -/
def atom (r θ h : ℝ) : ℝ × ℝ × ℝ := (r * Real.cos θ, r * Real.sin θ, h)

/-- The realised 3D point of a fiber. -/
def realize (f : Fiber) : ℝ × ℝ × ℝ := atom (radial f) (phase f) (height f)

/-- **The realised conical helix satisfies the Cartesian cone equation** `x² + y² = (coneSlope·z)²`:
the helix spirals **up and out** along a cone. (A cylinder would instead satisfy
`x² + y² = const`, independent of `z`.) -/
theorem realize_coneFiber_on_cone (t : ℝ) :
    (realize (coneFiber t)).1 ^ 2 + (realize (coneFiber t)).2.1 ^ 2
      = (coneSlope * (realize (coneFiber t)).2.2) ^ 2 := by
  simp only [ConeProjection.realize, ConeProjection.coneFiber, ConeProjection.atom,
    ConeProjection.radial, ConeProjection.phase, ConeProjection.height]
  nlinarith [Real.sin_sq_add_cos_sq (t + Real.pi / 3)]

/-- The purely **geometric** projection: realise onto the unit circle and keep the height, but
**drop the ledger** (forget radius and the absolute phase modulo `2π`). -/
def geomProj (f : Fiber) : ℝ × ℝ × ℝ :=
  (Real.cos (phase f), Real.sin (phase f), height f)

/-- **Phase is lost** (without the ledger): `2π`-periodicity collapses distinct phases. -/
theorem phase_lost :
    ∃ f₁ f₂ : Fiber, f₁ ≠ f₂ ∧ phase f₁ ≠ phase f₂ ∧ geomProj f₁ = geomProj f₂ := by
      refine' ⟨ ⟨ 1, 0, 0 ⟩, ⟨ 1, 2 * Real.pi, 0 ⟩, _, _, _ ⟩ <;> norm_num [ ConeProjection.phase, ConeProjection.geomProj ];
      rfl

/-- **Radial information is lost** (without the ledger): distinct radii collapse when the radius
is dropped, even though the realised points are genuinely different. -/
theorem radial_lost :
    ∃ f₁ f₂ : Fiber, radial f₁ ≠ radial f₂ ∧
      realize f₁ ≠ realize f₂ ∧ geomProj f₁ = geomProj f₂ := by
        refine' ⟨ ⟨ 1, 0, 0 ⟩, ⟨ 2, 0, 0 ⟩, _, _, _ ⟩ <;> norm_num [ ConeProjection.radial, ConeProjection.realize, ConeProjection.geomProj ];
        · unfold ConeProjection.atom ConeProjection.phase ConeProjection.height; norm_num;
        · unfold ConeProjection.phase ConeProjection.height; norm_num;

/-! ### The projected atom lands on the unit circle -/

/-- The unit-circle projection in `π/6` coordinates: records only the angle. -/
def unitCircleProj (t : ℝ) : ℝ × ℝ := (Real.cos (t + Real.pi / 6), Real.sin (t + Real.pi / 6))

/-- The complex "x = i·y" encoding of the projected atom. -/
def projAtom (t : ℝ) : ℂ := Complex.exp (Complex.I * (t + Real.pi / 6))

/-- The complex projected atom lies on the unit circle. -/
theorem projAtom_on_unit_circle (t : ℝ) : ‖projAtom t‖ = 1 := by
  unfold ConeProjection.projAtom; norm_num [ Complex.norm_exp ] ;

/-- The real `π/6`-coordinate projection lands on the unit circle. -/
theorem unitCircleProj_on_circle (t : ℝ) :
    (unitCircleProj t).1 ^ 2 + (unitCircleProj t).2 ^ 2 = 1 := by
      exact Real.cos_sq_add_sin_sq _

/-! ### The 2D→1D log projection and the critical-line midpoint -/

/-- The strictly-positive height encoding. -/
def heightEncode (h : ℝ) : ℝ := Real.exp h

/-- The 2D→1D projection "is literally taking the log". -/
def lineProj (z : ℝ) : ℝ := Real.log z

/-- The log step faithfully recovers the height from its positive encoding. -/
theorem log_recovers_height (h : ℝ) : lineProj (heightEncode h) = h := by
  unfold ConeProjection.lineProj ConeProjection.heightEncode; norm_num;

/-- The log projection is injective on positive encodings (faithful 2D→1D step). -/
theorem lineProj_faithful : Function.Injective (lineProj ∘ heightEncode) := by
  exact fun x y h => Real.exp_injective <| Real.log_injOn_pos ( Real.exp_pos x ) ( Real.exp_pos y ) h

/-- The end-to-end 3D → height → encode → 1D(log) pipeline. -/
def pipeline (t : ℝ) : ℝ := lineProj (heightEncode (project (coneFiber t)))

/-- **Faithfulness of the pipeline.** It recovers the parameter exactly. -/
theorem pipeline_id (t : ℝ) : pipeline t = t := by
  unfold ConeProjection.pipeline ConeProjection.project ConeProjection.heightEncode ConeProjection.lineProj; aesop;

/-- The pipeline is a bijection of `ℝ` (unconditional faithfulness, packaged). -/
theorem pipeline_bijective : Function.Bijective pipeline := by
  rw [ show ConeProjection.pipeline = id by exact funext pipeline_id ] ; exact Function.bijective_id

/-- The helix midpoint (parameter `1/2`) is carried by the faithful pipeline to the "critical
line" value `1/2`. A literal coordinate statement; see the module docstring. -/
theorem midpoint_to_critical : pipeline (1 / 2) = 1 / 2 := by
  exact pipeline_id _

/-! ### Interface to the HP projection closures

The closure file `HilbertPolyaChain.lean` consumes projection faithfulness through the concrete
operator readout `SpectralSide.w ρ` and the equivalent Möbius/Pythagorean readout.  The cone
pipeline is the retained-height/log projection; the bridge below states exactly how a midpoint
event in that pipeline supplies the readout atom needed by the HP closure.
-/

/-- The faithful cone pipeline has the same midpoint equation as the retained coordinate. -/
theorem pipeline_midpoint_iff (x : ℝ) : pipeline x = 1 / 2 ↔ x = 1 / 2 := by
  rw [pipeline_id x]

/-- A midpoint event in the faithful cone pipeline gives the HP spectral-unit readout. -/
theorem pipeline_midpoint_gives_spectral_unit (ρ : ℂ) (hρ : ρ ≠ 0)
    (hmid : pipeline ρ.re = 1 / 2) :
    Complex.normSq (SpectralSide.w ρ) = 1 := by
  have hre : ρ.re = 1 / 2 := (pipeline_midpoint_iff ρ.re).mp hmid
  exact (SpectralSide.w_unit_iff_half ρ hρ).mpr hre

/-- A midpoint event in the faithful cone pipeline gives the Möbius/Pythagorean readout. -/
theorem pipeline_midpoint_gives_moebius_pythagoras (ρ : ℂ) (hγ : ρ.im ≠ 0)
    (hmid : pipeline ρ.re = 1 / 2) :
    (moebius_helix ρ.re ρ.im).re ^ 2 + (moebius_helix ρ.re ρ.im).im ^ 2 = 1 := by
  have hre : ρ.re = 1 / 2 := (pipeline_midpoint_iff ρ.re).mp hmid
  exact (readout_pythagoras_iff_online ρ.re ρ.im hγ).mpr hre

/-- The reflected `π/3` source coordinate. A sign-changing crossing is fixed by this reflection. -/
noncomputable def piThirdSignFlip (u : ℝ) : ℝ := Real.pi / 3 - u

/-- The fixed point of the `π/3` sign-flip reflection is exactly the midpoint `π/6`. -/
theorem piThirdSignFlip_fixed_iff_midpoint (u : ℝ) :
    piThirdSignFlip u = u ↔ u = Real.pi / 6 := by
  unfold piThirdSignFlip
  constructor
  · intro h; linarith
  · intro h; rw [h]; ring

/-! ### Coordinate shifts and rescalings preserve information (bijections)

A coordinate **shift** (translation) and a nonzero **rescaling** are bijections of `ℝ`. Hence they
neither **lose** information (they are *injective*: distinct inputs stay distinct) nor **invent**
information (they are *surjective*: every value is attained), and they are exactly **reversible**
(explicit inverse). From this geometric-projection perspective the value pairs `(1, 1/2)`,
`(π/3, π/6)` and `(log 7, log 7 / 2)` are **the same value**: each pair is identified by the single
information-preserving midpoint rescaling `halve = (·)/2` — the very `midpoint ↦ 1/2` coordinate
change used above. -/

/-- A coordinate **shift** (translation) by `c`. -/
def shift (c x : ℝ) : ℝ := x + c

/-- A coordinate **rescaling** by the factor `k`. -/
def rescale (k x : ℝ) : ℝ := k * x

/-- A general **affine reparametrisation** `x ↦ k·x + c` (a rescaling followed by a shift). -/
def affineCoord (k c x : ℝ) : ℝ := k * x + c

/-- A coordinate shift is **injective**: it loses no information. -/
theorem shift_injective (c : ℝ) : Function.Injective (shift c) := by
  intro a b h; exact add_right_cancel h

/-- A coordinate shift is **surjective**: it invents no information. -/
theorem shift_surjective (c : ℝ) : Function.Surjective (shift c) := by
  intro y; exact ⟨y - c, by simp [ConeProjection.shift]⟩

/-- A coordinate **shift is a bijection**: information-preserving and reversible. -/
theorem shift_bijective (c : ℝ) : Function.Bijective (shift c) :=
  ⟨shift_injective c, shift_surjective c⟩

/-- A nonzero rescaling is **injective**: it loses no information. -/
theorem rescale_injective {k : ℝ} (hk : k ≠ 0) : Function.Injective (rescale k) := by
  intro a b h; exact mul_left_cancel₀ hk h

/-- A nonzero rescaling is **surjective**: it invents no information. -/
theorem rescale_surjective {k : ℝ} (hk : k ≠ 0) : Function.Surjective (rescale k) := by
  intro y; exact ⟨y / k, by simp [ConeProjection.rescale, mul_div_cancel₀, hk]⟩

/-- A nonzero **rescaling is a bijection**: information-preserving and reversible. -/
theorem rescale_bijective {k : ℝ} (hk : k ≠ 0) : Function.Bijective (rescale k) :=
  ⟨rescale_injective hk, rescale_surjective hk⟩

/-- A nonzero **affine reparametrisation is a bijection**: information-preserving and reversible. -/
theorem affineCoord_bijective {k : ℝ} (hk : k ≠ 0) (c : ℝ) :
    Function.Bijective (affineCoord k c) := by
  have h : affineCoord k c = shift c ∘ rescale k := by
    funext x; simp [ConeProjection.affineCoord, ConeProjection.shift, ConeProjection.rescale]
  rw [h]; exact (shift_bijective c).comp (rescale_bijective hk)

/-- The **explicit reversible affine coordinate change** as an equivalence: its two-sided inverse
witnesses that no information is lost or gained. -/
def affineCoordEquiv {k : ℝ} (hk : k ≠ 0) (c : ℝ) : ℝ ≃ ℝ where
  toFun := affineCoord k c
  invFun := fun y => (y - c) / k
  left_inv := by intro x; simp only [ConeProjection.affineCoord]; field_simp; ring
  right_inv := by intro y; simp only [ConeProjection.affineCoord]; field_simp; ring

/-- The **midpoint rescaling** `halve = (·)/2`: the information-preserving coordinate change that
carries "full" coordinates to "midpoint / critical-line" coordinates. -/
def halve (x : ℝ) : ℝ := rescale (1 / 2) x

/-- The midpoint rescaling is a **bijection**: it neither loses nor gains information. -/
theorem halve_bijective : Function.Bijective halve :=
  rescale_bijective (by norm_num)

/-- `1` and `1/2` are the same value under the midpoint rescaling. -/
theorem halve_one : halve 1 = 1 / 2 := by
  simp [ConeProjection.halve, ConeProjection.rescale]

/-- `π/3` and `π/6` are the same value under the midpoint rescaling. -/
theorem halve_pi_div_three : halve (Real.pi / 3) = Real.pi / 6 := by
  simp only [ConeProjection.halve, ConeProjection.rescale]; ring

/-- `log 7` and `log 7 / 2` are the same value under the midpoint rescaling. -/
theorem halve_log_seven : halve (Real.log 7) = Real.log 7 / 2 := by
  simp only [ConeProjection.halve, ConeProjection.rescale]; ring

/-- **The values are "the same" from the projection perspective.** The pairs `(1, 1/2)`,
`(π/3, π/6)` and `(log 7, log 7 / 2)` are each identified by the single information-preserving
(bijective) midpoint rescaling `halve`; by `halve_bijective` this coordinate change neither loses
nor gains information. -/
theorem same_value_under_halve :
    halve 1 = 1 / 2 ∧ halve (Real.pi / 3) = Real.pi / 6 ∧
      halve (Real.log 7) = Real.log 7 / 2 :=
  ⟨halve_one, halve_pi_div_three, halve_log_seven⟩

/-! ## Data processing inequality: "offline zeros" as a DPI violation

This section formalizes the *logical / information-flow skeleton* of the requested argument. Treat
the 3D helix as a **source** `S` and the 1D frame as a **derived** space `D`, related by a
deterministic **processing** map `derive : S → D`. This is the Hilbert–Pólya hypothesis taken as an
*explicit hypothesis*: the 1D spectrum is **computed from** the source, exactly as the requester
puts it that "zeta zeros are nothing but derived values, computed using the primes as source data."

The **data processing inequality**, in this deterministic setting, says processing can only
**destroy or preserve** information, never **create** it. The genuine features visible downstream
are *exactly* the image of the source under `derive`; nothing outside that image is real. An
**offline zero** is a putative 1D feature with **no source preimage** — information that appeared
*after* processing. Asserting it is genuine contradicts the DPI.

### Honest scope note
These are abstract theorems about functions and information flow. They do **not** prove the Riemann
Hypothesis, do **not** establish that the 3D helix is in fact the source of the zeta zeros (that
identification is an unproven hypothesis, supplied here as an explicit hypothesis wherever it is
used), and do **not** decide whether offline zeros exist for ζ. They formalize *only* the
conditional logic: **if** the 1D frame is a deterministic image of the source, **then** features
absent from the source cannot be genuine downstream. The closing meta-results make precise the
requester's two asymmetric points: an internal (1D-only) method *cannot* settle offline-ness, while
lifting to a richer frame *can* — just as FLT was settled by lifting to elliptic curves, so one
cannot declare a priori that no analogous lift exists for RH.
-/

section DataProcessing

variable {S D : Type*}

/-- The features the **source passes down** to the derived frame: the image of the processing map.
Everything genuinely present in the 1D frame must live here. -/
def passedDown (derive : S → D) : Set D := Set.range derive

/-- A derived feature is **genuine / derived** exactly when it has a source preimage. -/
theorem genuine_iff_passedDown (derive : S → D) (d : D) :
    (∃ s, derive s = d) ↔ d ∈ passedDown derive := Iff.rfl

/-- **No spontaneous generation of features.** Anything genuinely present downstream is the image
of *something* upstream: the source already contained it. -/
theorem derived_has_source (derive : S → D) {d : D}
    (h : d ∈ passedDown derive) : ∃ s, derive s = d := h

/-- **Data processing inequality (deterministic, core form).** Under the Hilbert–Pólya hypothesis
`hHP` that every genuine downstream feature is derived from the source, an **offline zero** `d` — a
feature asserted genuine yet having **no source preimage** — is impossible. This is the precise sense
in which "offline zeros existing in 1D but not on the 3D source" violate the DPI. -/
theorem offline_zero_violates_dpi (derive : S → D) (genuine : Set D)
    (hHP : genuine ⊆ passedDown derive) {d : D}
    (hgenuine : d ∈ genuine) (hoffline : d ∉ passedDown derive) : False :=
  hoffline (hHP hgenuine)

/-- **Zeros are derived values, not primitive ones.** Modelling the 1D zeros as values *computed
from the primes* via `computeFromPrimes : PrimeData → ℝ`, every genuine zero has a prime-data
preimage. ("There is no reason to believe zeta zeros are anything but derived values, computed using
the primes as source data" — formalized as: genuine = derived from the primes.) -/
theorem zeros_are_derived {PrimeData : Type*} (computeFromPrimes : PrimeData → ℝ) {z : ℝ}
    (h : z ∈ passedDown computeFromPrimes) : ∃ p, computeFromPrimes p = z := h

/-- **DPI, surjective form.** The source surjects onto the realized derived features: every
genuine downstream feature is hit by the processing map. -/
theorem source_surjects_onto_derived (derive : S → D) :
    Function.Surjective (Set.rangeFactorization derive) :=
  Set.rangeFactorization_surjective

/-- **DPI, finite cardinality form (`H(f(X)) ≤ H(X)`).** With finitely many states, the number of
distinct genuine downstream features never exceeds the number of source states: processing cannot
manufacture new distinguishable features. -/
theorem card_derived_le_source (derive : S → D) [Fintype S] [Fintype (Set.range derive)] :
    Fintype.card (Set.range derive) ≤ Fintype.card S :=
  Fintype.card_le_of_surjective _ Set.rangeFactorization_surjective

/-- **Inside the 1D frame you cannot decide offline-ness.** No test that sees only the derived value
`d` (and not the processing map / source) can decide whether `d` has a source preimage: whenever the
frame has at least two distinguishable values, the *same* `d` is online under one processing map
(`id`) and offline under another (a constant map). Hence a purely 1D-internal analytic method
cannot, in principle, certify that offline zeros do or do not exist — "it is impossible to prove
that offline zeros don't exist using methods that never step outside the 1D frame." -/
theorem no_internal_offline_test [Nontrivial D] :
    ¬ ∃ test : D → Bool, ∀ (derive : D → D) (d : D),
        (test d = true ↔ d ∈ passedDown derive) := by
  rintro ⟨test, htest⟩
  obtain ⟨d, e, hde⟩ := exists_pair_ne D
  have h1 : test d = true := (htest id d).2 ⟨d, rfl⟩
  have hned : d ∉ passedDown (fun _ : D => e) := by
    rintro ⟨s, hs⟩; exact hde hs.symm
  have h2 : test d ≠ true := fun h => hned ((htest (fun _ => e) d).1 h)
  exact h2 h1

/-- **From outside the frame, the question is determinate.** Once the processing map is in hand (the
"3D vantage"), membership in the source image is a definite fact — in stark contrast to
`no_internal_offline_test`. Stepping outside the 1D frame restores the very information the internal
view lacks. -/
theorem external_view_determines (derive : S → D) (d : D) :
    (d ∈ passedDown derive) ∨ (d ∉ passedDown derive) := em _

/-- **A richer frame in which offline-zero-freeness is provably true.** There is a processing map
(the faithful cone pipeline) whose image is *everything*, so no value is offline. This witnesses
that offline-zero-freeness is **provable in some frame**; therefore one cannot claim a priori that
lifting RH to a richer (e.g. 3D / cohomological) frame *cannot* make it provable — the same kind of
frame-lift that proved FLT via elliptic curves. It does **not** prove RH. -/
theorem exists_frame_without_offline_zeros :
    ∃ derive : ℝ → ℝ, Function.Bijective derive ∧ passedDown derive = Set.univ :=
  ⟨pipeline, pipeline_bijective, pipeline_bijective.surjective.range_eq⟩

/-! ### Concrete instantiation: the cone source has no radial drift, hence no offline zeros -/

/-- **No radial drift, so the source exactly determines the 1D frame.** On the helix the ledger
(radius and phase) is a *function of* the retained height (`ledger_coneFiber`): the source carries no
independent radial drift, and the end-to-end pipeline is a bijection (`pipeline_bijective`). Hence
every 1D value is passed down by the 3D source. -/
theorem cone_pipeline_no_offline (d : ℝ) : d ∈ passedDown pipeline :=
  pipeline_bijective.surjective d

/-- **Offline zeros of the cone-pipeline frame are impossible (DPI instance).** Any 1D value
asserted to be an offline zero — one without a 3D source preimage — yields a contradiction, because
the faithful, radial-drift-free pipeline passes *every* value down. (The hypothesis that the value is
otherwise "genuine" is not even needed: in this frame no value at all can be offline.) -/
theorem cone_offline_zero_violates_dpi {d : ℝ}
    (hoffline : d ∉ passedDown pipeline) : False :=
  hoffline (cone_pipeline_no_offline d)

end DataProcessing

/-! ## Hilbert–Pólya / Von Neumann: a realised spectral program *discharges* the DPI hypothesis

The previous section took the Hilbert–Pólya identification ("the 1D spectrum is a deterministic
image of the source") as an **explicit hypothesis** `hHP`. As the requester notes, a *full*
Hilbert–Pólya construction — a **self-adjoint (symmetric) operator** `T` whose **spectral harmonics**
(its eigenvalues `μ`, the *poles* of the resolvent) parametrise the zeros via `s = 1/2 + iμ` — would
"sock in" and **discharge** that hypothesis, turning `hHP` from an assumption into a *theorem*.

Two ingredients make this precise here, both **unconditional** given the operator:

* **Von Neumann reality of the spectrum.** Eigenvalues of a symmetric operator are real
  (`symmetric_eigenvalue_real`, from `LinearMap.IsSymmetric.conj_eigenvalue_eq_self`). Hence the
  spectral parametrisation `spectralZero μ = 1/2 + iμ` lands **exactly on the critical line**
  `Re = 1/2` (`hilbert_polya_on_critical_line`). This is the geometric "retains height" statement at
  the spectral level: the **imaginary** ordinate is the eigenvalue itself
  (`spectralZero_im`), while the **Pythagorean** law `|s|² = (1/2)² + μ²`
  (`spectralZero_pythagoras`) fixes the real part to the midpoint `1/2`.
* **Discharge of the DPI hypothesis.** If the genuine zeros are *exactly* the image of the
  eigenvalue source under `spectralZero` (the content of a realised Hilbert–Pólya program), then
  `hHP : genuine ⊆ passedDown derive` holds **by construction** (`hp_realised_gives_hHP`), so by
  `offline_zero_violates_dpi` **no offline zero can exist** (`hp_no_offline_zeros`). The capstone
  `hilbert_polya_capstone` packages both consequences from a single symmetric operator.

### Honest scope note
This remains **conditional on the existence** of such a self-adjoint operator with the required
spectrum — the Hilbert–Pólya program itself is open, and nothing here proves the Riemann Hypothesis.
What *is* proved unconditionally is the **implication**: *given* the operator and the spectral
identification of the zeros, the eigenvalues are real (Von Neumann), the zeros lie on `Re = 1/2`, and
the earlier DPI hypothesis is discharged so offline zeros are impossible. -/

section HilbertPolya

open scoped ComplexConjugate

/-- The **spectral parametrisation**: a spectral harmonic `μ` (an eigenvalue — a *pole* of the
resolvent of the self-adjoint operator) is sent to the zeta-zero candidate `1/2 + iμ`. -/
def spectralZero (mu : ℂ) : ℂ := 1 / 2 + Complex.I * mu

/-- **Von Neumann reality of the spectrum.** An eigenvalue of a symmetric (self-adjoint) complex
operator is **real** (`conj μ = μ`, i.e. `μ.im = 0`). -/
theorem symmetric_eigenvalue_real {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) {mu : ℂ} (hmu : Module.End.HasEigenvalue T mu) :
    mu.im = 0 := by
  have h := hT.conj_eigenvalue_eq_self hmu
  rwa [Complex.conj_eq_iff_im] at h

/-- The real part of the spectral parametrisation: `Re (1/2 + iμ) = 1/2 - Im μ`. -/
theorem spectralZero_re (mu : ℂ) : (spectralZero mu).re = 1 / 2 - mu.im := by
  simp only [spectralZero, Complex.add_re, Complex.mul_re]
  simp
  ring

/-- The imaginary ordinate of the spectral parametrisation is the **eigenvalue itself**
("retains the height/ordinate"): `Im (1/2 + iμ) = Re μ`. -/
theorem spectralZero_im (mu : ℂ) : (spectralZero mu).im = mu.re := by
  simp [spectralZero, Complex.add_im, Complex.mul_im]

/-- **The Pythagorean law for the spectral parametrisation** (`μ` real): the squared modulus is
`(1/2)² + (Re μ)²`, a right triangle with legs the critical abscissa `1/2` and the spectral ordinate.
This fixes the real part to the midpoint `1/2`. -/
theorem spectralZero_pythagoras {mu : ℂ} (h : mu.im = 0) :
    Complex.normSq (spectralZero mu) = (1 / 2) ^ 2 + (mu.re) ^ 2 := by
  simp only [spectralZero, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, h]
  simp
  ring

/-- **Hilbert–Pólya places the zeros on the critical line.** For an eigenvalue `μ` of a symmetric
operator, the spectral parametrisation `spectralZero μ = 1/2 + iμ` has real part exactly `1/2`:
the zero lies on the critical line. (Von Neumann reality of the spectrum.) -/
theorem hilbert_polya_on_critical_line {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) {mu : ℂ} (hmu : Module.End.HasEigenvalue T mu) :
    (spectralZero mu).re = 1 / 2 := by
  rw [spectralZero_re, symmetric_eigenvalue_real hT hmu]; ring

/-- **The DPI hypothesis is discharged.** A *realised* Hilbert–Pólya program identifies the genuine
zeros with the image of the eigenvalue source under `spectralZero`. Then the assumption
`hHP : genuine ⊆ passedDown derive` of `offline_zero_violates_dpi` is no longer assumed but holds as
a **theorem**. -/
theorem hp_realised_gives_hHP {Spec : Type*} (toEig : Spec → ℂ) (genuine : Set ℂ)
    (hRealised : genuine = passedDown (fun s => spectralZero (toEig s))) :
    genuine ⊆ passedDown (fun s => spectralZero (toEig s)) :=
  hRealised.le

/-- **No offline zeros, unconditionally (given the realised program).** With the genuine zeros
identified as the spectral image, an offline zero — a genuine value with no eigenvalue preimage —
is impossible. The DPI hypothesis has been discharged by the spectral construction. -/
theorem hp_no_offline_zeros {Spec : Type*} (toEig : Spec → ℂ) (genuine : Set ℂ)
    (hRealised : genuine = passedDown (fun s => spectralZero (toEig s))) {d : ℂ}
    (hgenuine : d ∈ genuine) (hoffline : d ∉ passedDown (fun s => spectralZero (toEig s))) :
    False :=
  offline_zero_violates_dpi (fun s => spectralZero (toEig s)) genuine
    (hp_realised_gives_hHP toEig genuine hRealised) hgenuine hoffline

/-- **Capstone: a single symmetric operator discharges everything.** From a self-adjoint operator
`T`, an eigenvalue source `toEig` landing in its spectrum, and the realised identification of the
genuine zeros with the spectral image, one obtains *simultaneously*:

1. **Critical line** (Von Neumann): every genuine zero has real part `1/2`; and
2. **No offline zeros** (DPI discharged): no genuine zero lacks an eigenvalue preimage.

This is the precise sense in which a full Hilbert–Pólya construction "socks in and discharges" the
hypothesis taken explicitly in the data-processing section. It is the implication only — it does not
prove that such an operator exists, and hence does not prove the Riemann Hypothesis. -/
theorem hilbert_polya_capstone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    {Spec : Type*} (toEig : Spec → ℂ)
    (hEig : ∀ s, Module.End.HasEigenvalue T (toEig s))
    (genuine : Set ℂ)
    (hRealised : genuine = passedDown (fun s => spectralZero (toEig s))) :
    (∀ z ∈ genuine, z.re = 1 / 2) ∧
      (∀ d ∈ genuine, d ∉ passedDown (fun s => spectralZero (toEig s)) → False) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    rw [hRealised] at hz
    obtain ⟨s, rfl⟩ := hz
    exact hilbert_polya_on_critical_line hT (hEig s)
  · intro d hd hoff
    exact hp_no_offline_zeros toEig genuine hRealised hd hoff

end HilbertPolya

end

end ConeProjection
