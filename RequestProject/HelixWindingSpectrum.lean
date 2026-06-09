import RequestProject.HelixVonNeumannReceiver
import RequestProject.HelixLogFreeFTA

/-!
# The spectrum extracted from the log-free winding (not from the zeros)

The honest Hilbert–Pólya direction. The von Neumann receiver's real spectrum is **not** taken to be
the zero heights `Im ρ` (which would be parasitic on the zeros). It is **extracted from the log-free
winding**: `μₙ = windAngle θ n`, the geometric angular frequency of the prime-fiber winding `wind θ`.

* **No-drift reality, earned from the geometry.** Each winding mode `windMode θ n = ofReal (windAngle θ n)`
  has `Re rate = 0` (`windMode_noDrift`) — the *same fact* as the winding sitting on the unit circle,
  `‖wind θ n‖ = 1` (`wind_unitModulus`): purely angular, no radial drift. This is the σ-free
  conservation that forces reality, read straight off the log-free geometry — no `σ`, no `ρ`.
* **The spectrum is geometric and independent of the zeros.** `windingReceiver θ` is the resolvent
  trace of this geometric spectrum; its self-adjoint reality is free.

GRH then follows from the winding spectrum escaping + being trace-class + **`hCompat`** — the winding
trace equals `−L'/L(½+i·)`. Now `hCompat` is a *genuine* identity (geometric spectrum vs. analytic
zeros), not a tautology: it asserts the log-free winding frequencies ARE the zero heights. That is the
trace-formula wall — but the construction no longer reads the answer off the zeros.
-/

open Complex Filter Topology HelixSource HelixLimit HelixLogFree

namespace HelixWindingSpectrum

variable {N : ℕ} [NeZero N]

/-- **The winding mode** at integer `n` with angle data `θ`: a source mode whose rate is the
purely-imaginary winding frequency `i·windAngle θ n`. Extracted from the log-free winding geometry. -/
noncomputable def windMode (θ : ℕ → ℝ) (n : ℕ) : SourceMode :=
  SourceMode.ofReal (windAngle θ n)

/-- **No drift** of the winding mode: `Re rate = 0`, σ-free. -/
theorem windMode_noDrift (θ : ℕ → ℝ) (n : ℕ) : (windMode θ n).rate.re = 0 :=
  SourceMode.noDrift _

/-- **No-drift = unit-modulus winding (the geometric reality).** The log-free winding sits on the unit
circle, `‖wind θ n‖ = 1` — purely angular, no radial drift. This is the conservation that forces
`Re rate = 0`, read off the geometry with no `σ`/`ρ`/critical line. -/
theorem wind_unitModulus (θ : ℕ → ℝ) (n : ℕ) : ‖(wind θ n : ℂ)‖ = 1 :=
  Circle.norm_coe _

/-- The pole-coordinate of the winding mode is on the critical line (`Re = ½`), inherited from the
no-drift — the geometric `½` (`√`-of-planar-packing), not a coordinate `σ−½`. -/
theorem windMode_poleCoord_re (θ : ℕ → ℝ) (n : ℕ) : (windMode θ n).poleCoord.re = 1 / 2 :=
  SourceMode.poleCoord_re _

/-- **The winding receiver**: the von Neumann resolvent trace of the geometric winding spectrum
`μₙ = windAngle θ n`, read on the critical line. The spectrum is real (no-drift), so the receiver is
self-adjoint — earned from the log-free winding, not from the zeros. -/
noncomputable def windingReceiver (θ : ℕ → ℝ) : ℂ → ℂ :=
  HelixVonNeumannReceiver.vonNeumannReceiver (windAngle θ)

/-- **GRH from the log-free winding spectrum + the trace identity.** The spectrum is extracted from the
log-free winding (geometric, no-drift reality), independent of the zeros. GRH follows once the winding
spectrum escapes, is trace-class, and `hCompat` holds — the winding trace equals `−L'/L(½+i·)`, i.e.
the geometric winding frequencies ARE the imaginary heights of the zeros. -/
theorem grh_of_windingSpectrum_traceIdentity (χ : DirichletCharacter ℂ N) (θ : ℕ → ℝ)
    (hesc : Tendsto (fun n => ‖(SourceMode.ofReal (windAngle θ n)).poleCoord‖) atTop atTop)
    (hsum : Summable (fun n => ‖(SourceMode.ofReal (windAngle θ n)).poleCoord‖⁻¹ ^ 2))
    (hCompat : ∀ z, windingReceiver θ z
        = -logDeriv (DirichletCharacter.LFunction χ) (1 / 2 + Complex.I * z)) :
    GRHSpectral.GRH χ :=
  HelixVonNeumannReceiver.grh_of_vonNeumannReceiver_traceIdentity χ (windAngle θ) hesc hsum hCompat

end HelixWindingSpectrum
