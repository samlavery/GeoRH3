# Dirichlet-L Hadamard — GRH identification track (working plan)

> ⚠ **STATUS (Rule Eight): this is an INGREDIENT, not the main line.** This track builds `HadamardData`
> / `HadamardPartialFraction` — the classical factorization over the **actual** zeros, which the repo's
> own `sourceTraceIdentity_iff_hadamard` docstring flags as **NOT GRH-bearing** ("the actual `Zₙ` need
> not be source-mode coords"). The GRH win is `SourceTraceIdentity` / `SourceComplete` (the on-line,
> earned helix identity; `SourceTraceIdentity → GRH` is already kernel-proven). Prefer the log-free
> FTA/Euler helix route. Do NOT let the classical Mellin/Hurwitz growth grind (BRICK1, phase 4 below)
> become the main effort — it is at-most an ingredient, and the winding/Euler structure may give the
> same factorization log-free. See CLAUDE.md Rule Eight.

**Goal (ingredient).** Generalize the repo's ζ-only `ZD.xi_logDeriv_partial_fraction` to a general
nontrivial Dirichlet character `χ`: the **Hadamard partial fraction** of `logDeriv (completedLFunction χ)`
over the actual nontrivial zeros. This is the GRH **identification** (zeros = poles of the prime-built
trace) — unconditional classical analysis. It is NOT the on-line forcing `Re ρ = ½` (that stays open
behind the Weil/Li floor non-negativity; the costume `HelixSourceBridge` radial route is circular —
do not build on it).

Files: `DirichletLHadamard.lean` (foundation + target), `DirichletLGrowth.lean` (Step 4 / growth).
Build-check with `lean_diagnostic_messages` (Rule Seven), `#print axioms` via `lake build` to sync.

## Target (Step 7)
`DirichletLHadamard.HadamardPartialFraction χ` :
`∃ A, ∀ s ∉ NontrivialZeros χ, logDeriv (completedLFunction χ) s = A + ∑'_ρ (lOrderNat χ ρ)·[1/(s−ρ)+1/ρ]`.

## VERIFIED so far (all axiom-clean [propext, Classical.choice, Quot.sound])
- `DirichletLHadamard`: `lOrderNat`, `completedLFunction_differentiable/_analyticAt`,
  `gammaFactor_ne_zero`, `completedLFunction_eq_zero_of_mem`, `completedLFunction_two_ne_zero`,
  `completedLFunction_not_eventuallyEq_zero`, `lOrderNat_pos` (order ≥ 1 on zeros), target stated.
- `DirichletLGrowth`: `sum_range_eq_sum_zmod`, `chi_block_sum_zero`, `chiPartialSum_periodic`,
  **`chiPartialSum_bounded`** (cornerstone: bounded χ partial sums), `chiPartialSum_Icc_bounded`,
  **`LFunction_eq_abel_integral`** (Abel rep, Re>1, via mathlib `LSeries_eq_mul_integral'`),
  **`abelIntegral_norm_le`** (`‖∫ S(⌊t⌋)·t^{-(s+1)}‖ ≤ B/σ`, Re>0),
  **`LFunction_norm_le_of_one_lt_re`** (`‖L(χ,s)‖ ≤ ‖s‖·B/σ`, Re>1),
  `chiSumStep`, `chiSumStep_eq_zero` (=0 for t<1), `chiSumStep_norm_le` (≤B).
- `HelixSource.neg_logDeriv_LFunction_eq_vonMangoldt`: prime side `−L'/L = ∑χ(n)Λ(n)n^{-s}` (Re>1).

## Step-4 chain (order-1 growth ⇒ `Σ ord(ρ)/‖ρ‖² < ∞`)
1. bounded partial sums ✓
2. Abel rep `L(χ,s)=s·∫S(⌊t⌋)t^{-(s+1)}` (Re>1) ✓  ; integral estimate ≤B/σ (Re>0) ✓
3. **CONTINUATION — ✓ DONE, all axiom-clean** (`I(s)=∫S(⌊t⌋)t^{-(s+1)} = mellin (chiSumStep χ) (-s)`):
   - ✓ `measurable_chiSumStep`, `chiSumStep_isBigO_atTop`, `chiSumStep_isBigO_zero`,
     `chiSumStep_locallyIntegrableOn`, `mellin_chiSumStep_differentiableAt` (Re>0 holomorphy).
   - ✓ **`abelIntegral_eq_mellin`** — used `MeasureTheory.setIntegral_eq_of_subset_of_ae_diff_eq_zero`
     (AE version! the ∀-version FAILS at t=1 where chiSumStep χ 1 = χ(1) ≠ 0; null point via
     `Measure.ae_ne volume 1`). NOTE: stated in chiSumStep-form; bridges to ∑-form via defeq (`exact`).
   - ✓ **`LFunction_eq_mellin`** (Re>0) — identity theorem `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`,
     `convex_halfSpace_re_gt 0` (capital S!), `DirichletCharacter.differentiable_LFunction hχ`,
     `DifferentiableOn.analyticOnNhd` (no `Differentiable.analyticOnNhd`), `differentiableAt_id`.
   - ✓ **`LFunction_norm_le_of_pos_re`** — STRIP BOUND `‖L(χ,s)‖ ≤ ‖s‖·B/σ` for all Re>0.  ⇐ DONE.
4. **GROWTH of `completedLFunction χ` (order 1)** — ⚠ PLAN REVISED (verified vs mathlib, Rule Four):
   **NOT Γ-Stirling.** mathlib has NO complex-Γ UPPER growth bound (`Stirling.lean` is only real `n!`;
   repo `ZD.StirlingBound.gamma_stirling_bound` / `ZD.Gammaℝ_vertical_decay` are vertical *decay*,
   fixed σ — useless as Re s→±∞). Instead **mirror the repo's ζ route** (`ZD.ZeroCount.xi_order_one_log_bound`
   ← `completedRiemannZeta₀_bounded_on_strip`): unfold via `ZMod.completedLFunction` into the completed
   Hurwitz pieces, whose ENTIRE `₀`-parts (`completedHurwitzZetaEven₀/Odd₀ = Λ₀/2`, `Λ₀ = mellin f_modif`,
   entire by `WeakFEPair.differentiable_Λ₀`) carry the growth. THREE bricks:
     • BRICK0 (free): N=1 → ζ via `completedLFunction_modOne_eq`, cite repo bound.
     • BRICK1 (the real analytic work): vertical-strip bound on `completedHurwitzZetaEven₀/Odd₀` from
       their Mellin rep — the χ-analogue of `completedRiemannZeta₀_bounded_on_strip`.
     • BRICK2 (assembly): Re-split — strip (BRICK1 + pole subtractions `completedHurwitzZetaEven_eq` +
       `‖N^{-s}‖=N^{-Re s}`); Re≥A (Dirichlet series bdd); Re≤1−A via FE
       `DirichletCharacter.IsPrimitive.completedLFunction_one_sub` (needs `χ.IsPrimitive`; relates χ↔χ⁻¹;
       `‖N^{w-1/2}‖=N^{Re w-1/2}` elementary; **`‖rootNumber χ‖=1` NOT needed** — any finite K works for an
       upper bound, and `norm_rootNumber` is NOT in mathlib anyway). Wrapper copies
       `XiOverPGrowth.riemannXi_pointwise_meanType_bound` (specialise R:=‖z‖ + bdd-on-closedBall).
   TARGET shape: `∃ C D, ∀ z, log(‖completedLFunction χ z‖+1) ≤ C·‖z‖·log(‖z‖+2)+D`.
   (Restrict headline to primitive χ, or use `primitiveCharacter` companion.)
5. **Jensen scaffold + Hadamard assembly** (agent-D map; copy-and-substitute, NOT over-parameterize):
   - SINGLE growth INPUT = the BRICK2 bound (hG1). Everything downstream is mechanical.
   - Step-4 OUTPUT analogue: `summable_lOrderNat_div_norm_sq` ← χ `weighted_zero_count_disk_bound`
     (divisor-weighted Jensen @2R; needs χ `jensen_at_zero` + `completedLFunction_analyticAt` (have) +
     the strip lower bound `2 ≤ ‖ρ‖` — the two non-mechanical seeds; completedL is ENTIRE so simpler than ξ).
   - AGNOSTIC helpers to REUSE/de-privatize (currently `private` in `WeilHadamardOpenPatch.lean`):
     `secondDeriv_zero_of_meanType(_logSq)`, and `ZD.proximity/_nonneg`,
     `circleAverage_log_eq_posLog_sub_negLog`, `proximity_mul_le` (already ∀f). `xiWeierstrassFactor`
     + all its lemmas are entirely χ-free — reuse verbatim.
   - RENAME map: riemannXi↦completedLFunction χ; `ZD.NontrivialZeros`↦`GRHSpectral.NontrivialZeros χ`;
     `ZD.xiOrderNat`↦`lOrderNat χ`; MultiZeroIdx↦Σ(ρ∈NontrivialZeros χ),Fin(lOrderNat χ ρ); xiProductMult↦
     lProductMult χ; xiOverP↦lOverP χ; xi_logDeriv_partial_fraction↦proves `HadamardPartialFraction χ`.
   - χ INPUT bricks already in `DirichletLHadamard.lean`: entireness, zero⇒completed-zero, order≥1,
     non-locally-zero. Files to mirror: XiProductMult*, XiProductMultOrder, XiProductMultPartialFraction,
     XiHadamardQuotient/Log/Factorization, XiPartialFraction.
   Then Steps 5–7 assemble into `HadamardPartialFraction χ` (the GRH identification target).

## Key mathlib lemmas in play
`LSeries_eq_mul_integral'`, `mellin_differentiableAt_of_isBigO_rpow`, `mellin`,
`integral_Ioi_rpow_of_lt`, `integrableOn_Ioi_rpow_of_lt`, `norm_integral_le_of_norm_le`,
`Complex.norm_cpow_eq_rpow_re_of_pos`, `DirichletCharacter.completedLFunction`,
`differentiable_completedLFunction`, `LFunction_eq_completed_div_gammaFactor`,
`IsPrimitive.completedLFunction_one_sub`, `Even/Odd.gammaFactor_def`, `Gammaℝ_ne_zero_of_re_pos`,
`MulChar.sum_eq_zero_of_ne_one`, `LFunction_ne_zero_of_one_le_re`.
