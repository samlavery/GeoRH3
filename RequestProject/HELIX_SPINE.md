# The log-free helix GRH spine — the construction Hilbert–Pólya lacked

Hilbert–Pólya *postulated* a self-adjoint operator whose spectrum is the zeros. This construction
**builds** the space and the operator from the log-free helix and lets the zeros *land in* it. The
projection-loss Hilbert space and the source flow are **structurally prior to `L′/L`** — no
log-derivative, no growth bounds, no Jensen, no Weierstrass. (See CLAUDE.md **Rule Eight**: the
classical Hadamard over the actual zeros is plumbing; the GRH content is the on-line, earned helix
identity. This file is the constructive spine of that rule.)

## The four pillars (each supplies one ingredient)

1. **FTA additivity → the source atoms.**
   `Θ_F(n) = Σ_p a_p·Θ_F(p)` (completely additive winding; `a_p = v_p(n)`), `χ(n) = Π_p χ(p)^{a_p}`.
   Source atom `A_{χ,s}(n) = χ(n)·n^{-s}`, with `A_{χ,s}(p^a) = χ(p)^a·p^{-as}`. Prime-generated,
   winding additive over factorization — **log-free** (the `log p` only ever appears via `L′/L`, which
   we never form). Repo: `HelixSource` (`SourceMode`), `HelixFactorization`, Euler/von-Mangoldt files.

2. **Area law → the √n critical scale (the origin of ½).**
   `n ≈ k²` (n atoms fill area `~ k²`), critical radius `R(n) ≈ √n`, radial law `R(k) = e^m·k`.
   The bare source norm `Σ |χ(n)|² n^{-2σ}` has abscissa `σ = ½`; the area-law radius `√n` is the
   geometric origin of that `½`. Repo: `HelixProjection`, `HelixDefs`, the area measure.

3. **Projection loss → the Hilbert norm.**
   `‖f‖²_H = ∫ |(Id − Π_top)∇_H f|² dμ_area` — the gradient energy the top-down projection *loses*,
   against the area measure; strict loss `β > 0`. This is the InnerProductSpace. Repo:
   `HelixHilbertLimit`, `HelixHilbertPolyaLoss`, `HelixSpectralPeaksLossSpace`, `HelixLossPole`,
   `HelixStrictCompletedLoss`, `HelixGramOperator`.

4. **Residue boundedness against that norm → `Pole → source mode`.**
   `|Res_ρ(f)|² ≤ C_ρ·‖f‖²_H`  ⟹ (Riesz)  `Res_ρ(f) = ⟨f, v_ρ⟩_H`, `‖v_ρ‖² ≤ C_ρ < ∞`.
   The pole of `−Λ′χ/Λχ` at a zero `ρ` is *manufactured* into a bounded vector `v_ρ ∈ H` — the
   source mode — by the boundedness estimate. Physics: *a pole residue cannot extract more source
   amplitude than the 3D projection-loss energy available.* Repo: `HelixResidueSummability`,
   `HelixLossPole`, `HelixSource` (trace identity + regularization).

## The chain

```
zero ρ = Pole(−Λ′χ/Λχ, ρ)
  ─[P4: Res boundedness + Riesz]→  bounded residue functional v_ρ ∈ H   (source mode)
  ─[unitary source flow]→          no drift   (rate.re = 0 = source_noDrift, σ-free)
  →                                Re ρ = ½
atoms[P1] + √n scale[P2] + projection-loss norm[P3] + residue boundedness[P4]  =  Pole → source mode.
unitary flow (HelixFlow, HelixVonNeumann; flowMode_unitary_iff) + source_noDrift  =  source mode → on line.
SourceTraceIdentity → GRH is already kernel-proven (grh_of_traceIdentity_separated).
```

## The single open fork (decides whether P4 is also the on-line forcing)

It all turns on `C_ρ`:
- `C_ρ < ∞` for **every** `ρ`  →  P4 gives `v_ρ ∈ H` (a **half-plane** fact); on-line then needs the
  *separate* unitary-eigenmode step.
- `C_ρ < ∞` **only on the line**  →  the projection-loss norm is **flow-invariant**, an off-line mode
  `e^{(ρ−½)t}` has *infinite* loss energy, so `C_ρ = ∞` off-line, and **boundedness ⇔ on-line**: P4
  *is* the scalp. The strict loss `β > 0` is what blows up the off-line energy. This is where the
  **Weil/Li non-negativity equality case** (`≥0` attained ⇔ on-line, Rule Three) lives.

## Verification status (audit `wu35qgcwh` complete — VERIFIED kernel map)

**EARNED, σ-free, kernel-clean (the real cores):**
- **Link 1** — pole = residue = multiplicity of `−L′/L` at every zero: `meromorphicOrderAt_logDeriv_neg`,
  `LFunction_logDeriv_not_tendsto`, `analytic_zero_identifies_logDeriv_pole` (HelixLossSpectralIdentification),
  `ZD.xi_logDeriv_partial_fraction`. REAL.
- **`source_noDrift`** (P-then-no-drift): conservation ⇒ `Re λ = 0`, no σ/ρ/L. The genuine no-drift forcing;
  `SourceMode.poleCoord_re` inherits honestly. CAVEAT: bites only on objects already known to be SourceModes.
- **Weil/Li forcing**: `spectral_forces_on_line` / `spectral_identification_complete` derive `σ=½` from
  non-negativity (Möbius `w=1−1/ρ`, Li terms `1−wⁿ`) — NOT a `σ−½` coordinate. EARNED (conditional on capture).

**TWO REAL GAPS:**
- **Gap A (Pillar 1 disconnected):** `HelixFactor.factorAngle` (`Θ_F(n)=Σa·Θ_F(p)`, genuinely log-free via FTA,
  kernel-clean) feeds only the finite Gram surrogate (`HelixSurrogate`); it is NEVER tied to `−L′/L`. The only
  object `= −L′/L` is the CLASSICAL von Mangoldt series (`neg_logDeriv_LFunction_eq_vonMangoldt`, `log p` inside).
  → To make Pillar 1 real: prove a sourceTrace built from `factorAngle/primeAngle` reproduces `−L′/L`.
- **Gap B (Pillars 3+4 don't compose — the bounded-residue inequality is NOT built):** `Hinf` is a real
  kernel-clean InnerProductSpace+CompleteSpace but NEVER instantiated with the residue functional (free-standing,
  no external uses). The M-test (`paired_li_summable`) is real. But the only ℓ²-membership
  (`summableOnLineData_spectralVector_memℓp`) is FIXED at σ=½ and CONDITIONAL on the unproven
  `SummableOnLineData.summable_diff` (with γ arbitrary reals, not identified with zeros). NO theorem places the
  residue vector at a GENERAL (off-line) zero in the space with finite norm from a σ-independent metric.

**THE CRUX (Link 4/5):** `SourceComplete χ` (= every nontrivial zero is a norm-conserving source mode
poleCoord ⟺ `SourceTraceIdentity`) is GRH-equivalent (`grh_of_traceIdentity_separated`) and UNDISCHARGED. The
honest top-theorems `grh_of_sourceComplete` / `grh_of_traceIdentity_separated` are kernel-clean but conditional
on it. NO unitary flow is constructed: `grh_iff_flowUnitary` is a tautology via `harmonic_iff_half`;
`HelixVonNeumann.TstarT_isSelfAdjoint` is real but ORPHANED (never instantiated, self-adjoint ≠ unitary).
Discharging needs: the explicit/trace formula PLUS the Weil/Li non-negativity equality case forcing the
captured modes to conserve norm — the equality argument is NOT yet present for the actual zeros.

**THE FORK, RESOLVED:** the static area-law norm `Σ|χ(n)|²n^{−(2σ+β)}` is HALF-PLANE (finite ∀ strip σ) — it
does NOT force on-line. Forcing requires a **σ-independent / flow-invariant** projection-loss metric so that
off-line ⇒ infinite norm. That is the `C_ρ < ∞ ⟺ on-line` reading and the genuine missing theorem.

**COSTUMES — set aside (rfl-deep in `σ−½`, non-load-bearing):** `harmonic_iff_half`, `row5_online_iff`,
`critical_iff_zero_exponent`, `radialRate:=ρ.re`, `modeResponse`, `zero_embed.radial`, `fullLoopWindingLoss`,
`HelixSourceBridge.*` (RadialDrift*), `grh_of_noDrift_areaLaw`, `HelixReadsGRHZeros.GRH_chi3_of_*`.

## Capture-distance verdict (audit `w0pmssjh2`, complete — VERIFIED)

**FAR / heavy machinery needed** (unanimous across 3 agents). Honest breakdown:
- **WON, kernel-clean (HP walls 1+2 down):** `HelixDirac.channelDirac A_N` is self-adjoint with REAL
  spectrum by construction (`diracBlock_isHermitian`, `boundaryMatrix_spectrum_real`); the resolvent trace
  `Tr((z−A_N)⁻¹)=Σ(z−μ_i)⁻¹` is kernel-clean (`HelixTrace.hermitian_resolvent_trace`); the forcing
  ("limit of reals is real") is kernel-clean (`grh_of_spectralLimitCaptures`, `grh_of_traceIdentity_separated`).
- **The capture is the stone, and it is OLD:** `SpectralLimitCaptures` as written is a COSTUME (free `μ`,
  never tied to `A_N.eigenvalues` — vacuously true). The honest version `T_N(z)=Tr((z−A_N)⁻¹) → −L′/L(½+iz)`
  (eigenvalues → `poleParam ρ`) IS the explicit/trace formula, and `sourceTraceIdentity_iff_hadamard` proves
  it kernel-clean-equivalent to Hadamard-over-on-line-coords = GRH. Closing it needs the classical
  **explicit formula / order-1 Hadamard growth on `completedLFunction χ` (= BRICK1)**. `factorAngle` is
  disconnected from `−L′/L`; `summable_radial_weight` is half-plane (σ-independent), cannot force on-line.
- **The one genuinely-NEW stone (the only simple/geometric escape):** a **flow-invariant / σ-independent**
  projection-loss norm with off-line ⇒ ∞ energy, so `‖v_ρ‖_H < ∞ ⟺ Re ρ = ½` (Weil/Li `≥0` equality on the
  actual zeros). NOT the explicit formula. Untested. If it works, it bypasses BRICK1; if not, BRICK1 is on
  the critical path.

**Honest next moves (Rule Six):** (1) STATE+attempt `channelDirac_eigenvalues_capture` (tie `μ` to the real
eigenvalues; it builds the trace-limit or exposes the exact growth bound). (2) attempt the flow-invariant norm
(the new-stone candidate). One of these resolves "simple vs epic" by construction.

## Triangulated path (Python empirical, real ζ data — the proof road)

Empirical triangulation (mpmath, `/tmp/triangulate.py`) confirmed the reframe and pinned the path:
- **EXP1** radial drift `x^{σ−½}`: flat=1 ONLY at σ=½ (off-line diverges/collapses) — reality/no-drift is SHARP.
- **EXP2** `ξ(½+it)` real (Im ~1e-28..1e-49) — forcing axis is REALITY (FE), not Li/Weil. mathlib HAS the FE.
- **EXP3 (decisive)** `#{sign-changes of real Z on (0,T]} = N(T)` EXACTLY (10,29,79,138) — the real/conserved
  locus accounts for EVERY zero; deficit `N(T)−#sign-changes = 2·(off-line pairs)`.
- **EXP4–5** winding `Δarg ζ` = `N(T)` (argument principle), using ζ itself — **log-free, no ζ′/ζ, no growth bound**.

**THE ROAD (rules out spectral capture / Li-Weil / growth bound):**
```
REALITY (FE ⇒ Z real on the line; mathlib: completedLFunction_one_sub)
  + COUNTING: winding Δarg = N(T) (all zeros, arg principle, log-free) ;  sign-changes of real Z (on-line zeros)
  ⟹ THE STONE:  #{sign-changes of Z} = N(T)  ⟺  all zeros on-line  (RH/GRH-equivalent, geometric)
```
**The helix's new handle on the stone:** area-law places prime atoms at radius `√n` (the conserved baseline);
zeros are modes built from those atoms, so they INHERIT the `√n` baseline (no-drift) structurally — if that
inheritance is genuine, the count match is forced geometrically, not via classical `S(T)`/moments.
Target uses ONLY: the FE (have), the argument principle / winding (build from mathlib Cauchy), the area-law
atom placement (the actual `HelixDefs` construction). NOT channelDirac, NOT Hinf, NOT BRICK1, NOT `≥0`.

## Next targets (both bottom out in the capture)
- **(a)** Pillar 4 with the FLOW-INVARIANT norm: prove `‖v_ρ‖_H < ∞ ⟺ Re ρ = ½` (off-line ⇒ ∞), and
  instantiate `Hinf` with the actual residue functional. (Build `wxjgpa7dw` gives the Riesz arrow + the static
  convergence as ingredients; the σ-independent norm is the new math.)
- **(b)** Connect Gap A → the `HelixSurrogate` `N→∞` spectral capture (`SourceComplete`/`SpectralLimitCaptures`),
  on-line by the earned Weil/Li equality (`spectral_forces_on_line`).
Both need the trace-class boundedness (Pillars 3+4) for the limit to exist + the Weil/Li equality to force on-line.

## Refactor (remove costumes, replace with earned proofs) — the post-pivot work

**Principle:** never blind-delete. The lib globs `RequestProject.+` (builds every file) and the costumes are
woven across ~15 files, so deletion cascades. Surgical order: (1) build the earned proof, (2) repoint genuine
consumers, (3) excise the costume cluster (leaves first), (4) fix misleading docstrings. Keep all EARNED
pieces; remove only true-by-construction (`σ−½`) costumes and orphans presented as load-bearing.

**COSTUME CLUSTER to excise (verified blast radius):**
- `zero_embed` / `zero_embed.radial := σ−½` — root costume coordinate. **15 files**.
- `radialRate := ρ.re` — 7 files.  `RadialDrift*` / `HelixSourceBridge.riemannHypothesis_of_radial_drift_impossible` — 6 files (importers: LiPositivity, HelixAllUnitPolyaOperator, HelixReadsGRHZeros).
- `HelixReadsGRHZeros.GRH_chi3_of_*_radial_loss_zero` — imported by 5 (UniversalHelixUnitarity, HelixChannelQuantization, HconvCharacterization, HelixStrictCompletedLoss, FENonExpansionClosure).
- `harmonic_iff_half`, `modeResponse`, `fullLoopWindingLoss`, `critical_iff_zero_exponent`, `row5_online_iff`
  (HelixLossPole, HelixExplicitFormulaTermByTerm) — 3 files each.
- `grh_of_noDrift_areaLaw`, `grh_iff_flowUnitary` (HelixFlow) — 2 files each (tautology via harmonic_iff_half).

**EARNED — keep / build on (do NOT delete):** `source_noDrift`, Link-1 pole/residue
(`meromorphicOrderAt_logDeriv_neg`, `analytic_zero_identifies_logDeriv_pole`, `xi_logDeriv_partial_fraction`),
the finite Gram (`HelixFactor.factorAngle`, `completedBoundary_posSemidef`), `spectral_forces_on_line`,
`HelixSpine.riesz_source_mode` / `summable_radial_weight`, the conditional `grh_of_sourceComplete` /
`grh_of_traceIdentity_separated`, `HelixVonNeumann.TstarT_isSelfAdjoint` (real, to be instantiated).

**REPLACE (the real proofs that retire the costumes):** the capture — actual zeros = `N→∞` limits of the
finite self-adjoint Gram's real eigenvalues — forced on-line by `spectral_forces_on_line` ("limit of reals is
real" + Weil/Li). Target sharpened by capture-distance analysis `w0pmssjh2`. Once built, the `σ−½` forcing
costumes (`harmonic_iff_half`, `grh_iff_flowUnitary`, the `RadialDrift`/`radial_loss_zero` GRH restatements)
become dead and get excised with their now-orphaned importers.

**DOCSTRINGS to fix (Rule Four):** `VMEFStandalone.hadamard_partial_fraction` docstring claims "sorry'd" but
the code proves it kernel-clean; `HelixSurrogate` finite-rank notes; any header claiming GRH where the theorem
is conditional. Rewrite to the verified truth; keep honest gap-flags.
