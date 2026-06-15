import RequestProject.HelixWindBridge
import RequestProject.HelixResolventCapture
import RequestProject.DirichletLHadamardComplete

/-!
# The compatibility square: log-free winding ⟷ self-adjoint receiver ⟷ actual zero peaks

```
   log-free winding ──prime foothold──▶ −L'/L
        │                                  │
     no drift                          Hadamard
        │                                  │
        ▼                                  ▼
 self-adjoint receiver ───hCompat───▶ actual zero peaks
```

Three of the four edges are now **theorems**:

* **top (prime foothold)** — the log-free winding twist of the von Mangoldt prime field equals `−L'/L`
  shifted by the winding parameter (`HelixWindBridge.windedVonMangoldt_eq_neg_logDeriv_shift`), and the
  receiver target `−L'/L(½+i·)` IS that prime/Euler field where it converges
  (`receiverTarget_eq_primeField`, below). `log` lives only on this bridge edge.
* **right (Hadamard)** — `−L'/L`'s poles are the actual nontrivial zeros, globally
  (`DirichletLHadamard.hadamardPartialFraction`).
* **left (no drift) + reality** — the von Neumann self-adjoint receiver has real singular support
  (`HelixLimit.real_absorption_of_selfAdjoint`), earned, not defined from the zeros.

The **bottom edge `hCompat`** — *the receiver's boundary trace equals `−L'/L(½+i·)`* — is the single
load-bearing remaining theorem: continuing the proven convergent-region prime field across the bridge
to the boundary `Re = ½` so that its resonances meet the Hadamard zero peaks on the receiver's real
spectrum. That continuation is the explicit-formula wall; everything else commutes.
-/

open Complex ArithmeticFunction HelixLimit

namespace HelixCompatibilitySquare

variable {N : ℕ} [NeZero N]

/-- **Prime-foothold edge (PROVEN), convergent region.** Where `Im z < −½` (so `Re(½+iz) > 1`), the
receiver target `−L'/L(½+iz)` is exactly the von Mangoldt prime/Euler field — the helix's prime
fibers with Mangoldt weights (prime powers included). The geometric winding family generates its
imaginary translates (`HelixWindBridge.windedVonMangoldt_eq_neg_logDeriv_shift`). -/
theorem receiverTarget_eq_primeField {χ : DirichletCharacter ℂ N} {z : ℂ} (hz : z.im < -(1 / 2 : ℝ)) :
    -logDeriv (DirichletCharacter.LFunction χ) (1 / 2 + Complex.I * z)
      = LSeries ((fun n : ℕ => χ ↑n) * fun n => (vonMangoldt n : ℂ)) (1 / 2 + Complex.I * z) := by
  apply HelixSource.neg_logDeriv_LFunction_eq_vonMangoldt
  have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
  have hre : (1 / 2 + Complex.I * z).re = 1 / 2 - z.im := by
    rw [hhalf, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im]
    ring
  rw [hre]; linarith

/-- **The winding realizes the receiver target in the convergent region.** Combining the prime
foothold with the bridge: for `Im z < −½`, the receiver target `−L'/L(½+iz)` equals the `γ=0` member
of the log-free winding family — and the bridge translates it across all winding parameters. This is
the top edge of the square meeting the bottom-left corner, log-free in the geometry. -/
theorem receiverTarget_eq_windedField_at_zero {χ : DirichletCharacter ℂ N} {z : ℂ}
    (hz : z.im < -(1 / 2 : ℝ)) :
    -logDeriv (DirichletCharacter.LFunction χ) (1 / 2 + Complex.I * z)
      = LSeries (fun n => (χ ↑n * (vonMangoldt n : ℂ)) *
          ((HelixLogFree.wind (fun p => (0 : ℝ) * Real.log p) n : Circle) : ℂ))
          (1 / 2 + Complex.I * z) := by
  rw [receiverTarget_eq_primeField hz]
  apply LSeries_congr
  intro n _
  rw [Pi.mul_apply]
  by_cases hn : n = 0
  · simp [hn]
  · rw [HelixWindBridge.wind_glog_eq_cpow 0 hn]
    simp

/-- **Compatibility-square capstone — `grh_of_winding_vonNeumann_primeFoothold`.** GRH from exactly two
inputs:
* `hVN` — the **von Neumann self-adjoint receiver** (reality: a finite boundary limit at every `z` off
  the real axis, i.e. resolvent regular off `ℝ`). Earned from self-adjointness, *not* from putting the
  zeros on `ℝ`.
* `hCompat` — the **bottom edge**: the receiver's boundary trace equals `−L'/L(½+i·)`.

The top edge (winding → `−L'/L`, prime foothold) is `receiverTarget_eq_windedField_at_zero` +
`HelixWindBridge`; the right edge (`−L'/L` → actual zero peaks, global Hadamard) is
`DirichletLHadamard.hadamardPartialFraction`. The whole remaining content is `hCompat`. -/
theorem grh_of_winding_vonNeumann_primeFoothold {χ : DirichletCharacter ℂ N} {T : ℂ → ℂ}
    (hVN : IsSelfAdjointReceiver T)
    (hCompat : ∀ z, T z = -logDeriv (DirichletCharacter.LFunction χ) (1 / 2 + Complex.I * z)) :
    GRHSpectral.GRH χ :=
  grh_of_harmonicTraceReceiver_traceIdentity hVN hCompat

/-- **The right edge is discharged.** `−L'/L`'s pole structure is the actual nontrivial zeros,
globally and unconditionally — the Hadamard partial fraction. So the square's `−L'/L → actual zero
peaks` arrow is a theorem, not a hypothesis. -/
theorem hadamardEdge {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (hχp : χ.IsPrimitive) :
    DirichletLHadamard.HadamardPartialFraction χ :=
  DirichletLHadamard.hadamardPartialFraction hχ hχp

end HelixCompatibilitySquare
