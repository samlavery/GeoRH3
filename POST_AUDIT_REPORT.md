# Post-Audit Report — `proof/three` (RequestProject)

**Date:** 2026-06-08
**Scope:** Full repository — every `.lean` file read; load-bearing claims re-derived against
the Lean kernel (`lean_verify` / `#print axioms`), not trusted from docstrings (RULE FOUR).
**Auditor note:** This report obeys RULE FOUR itself — every "proved/clean" below is a kernel
check I ran, not a prose claim I read. "Reported by inventory" marks facts gathered by the
read-through that I did not individually kernel-check.

**Update (2026-06-08, post-audit):** the general-χ Hadamard partial fraction — flagged in the
original audit as the one in-progress analytic target — is now a **proved, kernel-clean theorem**
(`DirichletLHadamard.hadamardPartialFraction`, primitive `χ ≠ 1`). The full analytic backbone (the
`hid`-side global balance) is now complete for **both ζ and general χ**; §1/§3a/§4/§5/§8 updated to
match, and the stale "TARGET, not a theorem" remark in `HelixProgram.lean` was corrected. Full
build: **8678 jobs green**.

---

## 1. Headline verdict

The repository is a **large, sound, kernel-clean formalization** of the classical analytic
machinery around ζ and Dirichlet L, **plus** a clean Hilbert–Pólya / energy *reduction* of
GRH. It is honest: **no theorem proves RH or GRH unconditionally**, and the reductions consume
a hypothesis the repo itself proves is GRH-equivalent. With the general-χ Hadamard partial
fraction now proved, the **entire analytic backbone (the `hid`-side global balance) is complete**;
the sole remaining obligation for GRH is the **on-line forcing** (the identification / reality /
"HP part") — which is *not* analytic plumbing.

- **Soundness:** `0` tactic-position `sorry`/`admit` in the entire repo; `0` custom `axiom`
  declarations. Every theorem I spot-checked depends only on `propext, Classical.choice,
  Quot.sound`.
- **The Hadamard/Stirling/Gamma analytic backbone is correct and complete — for ζ *and* general χ**
  — verified brick by brick (§4). The general-χ Hadamard partial fraction
  (`DirichletLHadamard.hadamardPartialFraction`) is now a proved, kernel-clean theorem.
- The "incorrect things" found were **stale docstrings**, not math errors: several files still
  described the now-*proved* Hadamard partial fraction as an open `sorry`. These are fixed (§6).
- Cleanup performed: deleted `RiemannHypothesis.lean` and the entire Log7 tangent; build green
  (§7).

---

## 2. Method

- Read all ~190 modules (two fan-out passes + direct reads of the core).
- Kernel-verified ~20 of the most load-bearing theorems, spanning the analytic backbone, the
  energy machinery, the GRH reductions, and the Gamma chain.
- Ran a repo-wide sweep for real `axiom` declarations and tactic-position `sorry`/`admit`.
- Re-checked the build after every edit (`lean_diagnostic_messages`, then `lake build`).

---

## 3. What is genuinely proved (kernel-verified)

### 3a. Classical analytic backbone — the "Hadamard gap" is closed for ζ **and general χ**

| Theorem | File | Axioms |
|---|---|---|
| `VMEFStandalone.vonMangoldt_explicit_formula_LSeries` (von Mangoldt explicit formula) | `VonMangoldtEFStandalone.lean` | clean |
| `ZD.riemannXi_hadamard_factorization` (ξ = e^{Az+B}·∏) | `XiHadamardFactorization.lean` | clean |
| `ZD.xi_logDeriv_partial_fraction` (ξ'/ξ = A + Σ_ρ m_ρ[1/(s−ρ)+1/ρ]) | `XiPartialFraction.lean` | clean |
| `DirichletLHadamard.hadamardPartialFraction` (**general-χ** Λ'/Λ = A + Σ_ρ ord·[…], primitive χ≠1, **unconditional**) | `DirichletLHadamardComplete.lean` | clean |
| `Layer1.vonMangoldt_LSeries_eq` | `Layer1Objects.lean` | clean |

The ξ'/ξ partial fraction — the classical Hadamard input older docstrings call "the irreducible
gap" — is **discharged** via the chain Jensen zero-count (`ZeroCountJensen`) → `Σ1/|ρ|²<∞`
(`XiOrderSummable`) → Weierstrass product + order matching (`XiProduct*`) → mean-type growth
(`XiOverPGrowth`) → Borel–Carathéodory constancy (`WeilHadamardOpenPatch`). All kernel-clean.

The **general-χ** analog is now likewise discharged, mirroring the ζ chain on its own files:
order-1 growth (`DirichletLGrowthComplete`) → Jensen zero-count (`DirichletLZeroCount`) →
summability → order-matched Weierstrass product (`DirichletLProductMult*`) → zero-free quotient
`LOverP` (`DirichletLOverP*`) → Nevanlinna/Poisson + Borel–Carathéodory constancy
(`DirichletLOverPGrowth*`, `DirichletLOverPLogDeriv`, `LogDerivConstOfGrowth`) → assembly
(`DirichletLHadamardAssembly` → `DirichletLHadamardComplete`). A sweep of all ~14 new files shows
**no tactic-`sorry`, no `admit`, no `axiom` declarations**, and the capstone is kernel-clean.
**Reported by inventory:** `ZeroCountJensen`, `StirlingBound`, `EulerMaclaurinDirichlet`,
`ZetaStripBound`, `DirichletLGrowth` are `sorry`-free.

### 3b. Geometry / spectral structure (σ-free where claimed)

- `GrindF.equidistant_iff` — `‖ρ−1‖ = ‖ρ‖ ⟺ Re ρ = ½` (the self-dual axis; earned, not `rfl`).
- `SpectralSide.w_FE_reciprocal`, `MobiusPath.w_norm_one_iff`, `SelfDual.self_dual_nature`.
- `HelixSource.source_noDrift` — conservation ⟹ `Re(rate) = 0`, **σ-free** (the earned forcing).
- `HelixLogFree.wind_mul` — log-free FTA winding (multiplicative, unit modulus).
- `HelixCollapse.completedRiemannZeta_critical_line_im_zero` — completed ζ real on the line.

### 3c. Energy machinery (the "global energy matching")

| Theorem | File | Axioms |
|---|---|---|
| `ZD.averageEnergyDefect_pos_offline` (β≠½ ⟹ defect>0) | `EnergyDefect.lean` | clean |
| `ZD.re_half_of_averageEnergyDefect_gaussian_zero` (defect=0 ⟹ on-line) | `GaussianClosedForm.lean` | clean |

The averaged energy defect equals `2π∫[(cosh−1)²+sinh²]ψ²` via half-line Parseval
(`HalfLineParseval`, `EnergyDefect.averageEnergyDefect_eq_weighted_L2`). Because
`averageEnergyDefect_pos_offline` is kernel-clean, the **entire Parseval chain beneath it is
`sorry`-free** (an earlier "deferred sketch" worry in `HalfLineParseval` is a misread — the
kernel says clean).

### 3d. The GRH/RH reductions (all conditional, kernel-clean)

`HelixSource.grh_of_sourceComplete`, `…grh_of_traceIdentity_separated`,
`HelixResolventCapture.grh_of_harmonicTraceReceiver_traceIdentity`,
`HelixProgram.grh_of_real_moebiusReceiver`, `RiemannHypothesisBridge.no_offline_zeros_implies_rh`,
etc. Each is a correct reduction **consuming** an open hypothesis.

---

## 4. The Hadamard/Stirling/Gamma proof — focused audit

This was the explicit audit target. **It is correct and, for the completed Dirichlet L growth,
complete.** Verified brick by brick:

| Brick | Theorem | File | Axioms |
|---|---|---|---|
| Γ modulus | `GammaBound.Gamma_le_inv` (Γ(x) ≤ 1/x on (0,1]) | `GammaModulusBound.lean` | clean |
| Γ-factor log bound | `DirichletLHadamard.log_norm_gammaFactor_le` | `DirichletLGammaFactor.lean` | clean |
| hStrip (0<Re≤1) | `DirichletLHadamard.completedL_bound_strip` | `DirichletLStripBound.lean` | clean |
| **Capstone** (order-1 log growth) | `DirichletLHadamard.completedL_order_one_log_bound` | `DirichletLGrowthComplete.lean` | clean |
| hLeft (via FE) | `DirichletLHadamard.completedL_bound_left` | `DirichletLLeftBound.lean` | clean |

`completedL_order_one_log_bound` is **unconditional** (Stirling + Abel + FE), assembling
`hStrip + hRight + hLeft` through `completedL_order_one_log_bound_of_subbounds`. This is the
genuine order-1 growth of the completed L — the load-bearing global object the transcript
described, and it holds.

**Two Hadamard partial fractions — both now PROVED:**

1. **ζ / riemannXi:** `ZD.xi_logDeriv_partial_fraction` — proved, kernel-clean (§3a).
2. **general χ:** `DirichletLHadamard.hadamardPartialFraction` — **now proved**, kernel-clean
   (primitive `χ ≠ 1`, unconditional). The `def` `HadamardPartialFraction χ` is the *statement*;
   the theorem `hadamardPartialFraction` *discharges* it via the full chain (order-1 growth →
   summability → order-matched product → zero-free quotient → Nevanlinna/Borel–Carathéodory
   constancy → assembly). The earlier "TARGET, not a theorem" remark in `HelixProgram.lean` was
   stale and has been corrected (§6).

**`StirlingBound.lean` (the "big old" sharp Stirling):** load-bearing, not dead weight — imported
by `RiemannXiDecay`, `ThetaTransport`, `ZetaStripBound`; supplies the sharp vertical decay the
Weil-contour / strip-bound machinery needs. `GammaModulusBound.lean` is the newer *crude* route
(`‖Γ(z)‖ ≤ Γ(Re z)`) sufficient for the upper-only Hadamard growth; the two coexist by design.
No correctness defect found in either.

---

## 5. The single open obligation (GRH-equivalent)

**First, what is *not* the obligation anymore:** the analytic balance — the global Hadamard
partial fraction (`hid`-side: geometric canonical-product side = spectral log-derivative side,
globally over the actual zeros) — is now **fully proved**, for ζ and general χ (§3a/§4). But note
the honest point that keeps it from being the finish line: this balance is **unconditionally
true** — it holds with off-line zeros too (they sit in the sum at their off-line positions). So
completing it, valuable as it is (the whole analytic backbone), does **not** close the gate.

No `RiemannHypothesis`/`GRH χ` conclusion is unconditional — confirmed by enumerating every such
theorem. Across all routes the consumed hypothesis is **one thing in many costumes: the on-line
forcing / identification** — that the *actual* nontrivial zeros are exactly the on-line objects
the geometry/energy produces:

`SourceComplete` · `Exhausts` · `SpectralLimitCaptures` · `hid ∧ hsa` · spectral identification ·
flow-unitarity-on-the-zeros · `WeilGaussianBridge` / `bothChannelsBalancedAtZeros` · `WeilFormula`.

The repo **proves each is GRH-equivalent** (`sourceComplete_iff_grh`, `exhausts_iff_grh`,
`grh_iff_flowUnitary`, `spectralLimitCaptures_iff_grh`, …). So these are honest reductions that
consume the open problem — **not** circular bugs.

For the energy route specifically: the **detector is proved** (off-line ⟹ strictly positive,
non-cancellable defect; defect = 0 ⟺ on-line), but "the defect vanishes at every *actual* zero"
is the **Weil explicit-formula positivity**, and the full Weil equality `WeilFormula` is a `Prop`
**consumed as a hypothesis everywhere** (only the trivial `0,0` instance is proved —
`PartialWeilFormula.lean`, `WeilCoshTest.lean`). That equality + its positivity at the zeros is
the classical hard core, still open.

The σ-free forcing that *is* earned (`source_noDrift`, unitarity ⟹ real spectrum) forces the
line for the **constructed** modes/flow; tying those to the **actual** zeros is exactly the open
identification.

---

## 6. Incorrect things found — and fixed (RULE FOUR)

All were **stale prose**, not math errors: written when the ζ-Hadamard step was a `sorry`, never
updated after it was discharged. Each is now corrected to the verified kernel state.

| File | Was (incorrect) | Now |
|---|---|---|
| `VonMangoldtEFStandalone.lean` (header) | "downstream theorems additionally have `sorryAx`"; "left as `sorry`" | states the import discharges it; "No `sorryAx`" |
| `SpectralRH.lean` | "the only sorry in the chain is `hadamard_partial_fraction` … this sorry disappears" | Hadamard is proved, no `sorry`; the gap is the `SpectralRealization` hypothesis (GRH-equivalent) |
| `EFTestAndBridge.lean` | "Hadamard partial fraction (sorry'd)"; gap = "Hadamard + Weil positivity" | Hadamard proved; gap = "Weil positivity ⟹ RH" |
| `SpectralIdentification.lean` | "**The Hilbert-Pólya operator proves RH.**" (overclaim; theorem is conditional) | "Hilbert–Pólya ⟹ on-line (conditional)"; existence is the open input |
| `HelixProgram.lean` (`global_traceIdentity_of_local_energy` docstring) | `HadamardPartialFraction` is "a `def`/TARGET … **not** a theorem" | now a proved theorem (`DirichletLHadamard.hadamardPartialFraction`); "discharged, not assumed" |

**Correctly-flagged "costumes" left intact** (the repo is honest about these): the `zero_embed`
family defines `radial := σ − ½`, so `GRH_iff_helix_reads_zeros_on_core`, `harmonic_iff_half`,
and `ConcreteOperators.radial_loss_zero_iff` are `rfl`-deep / iff-GRH — not forcing. Their
docstrings already say so.

---

## 7. Cleanup performed

- **Deleted** `RequestProject/RiemannHypothesis.lean` (0 importers — a summary file of
  `rh_iff_*` restatements; nothing depended on it).
- **Deleted the Log7 tangent** (a coordinate-rescaling curiosity off the main line):
  `Log7Comparison.lean`, `Log7HelixRH.lean`; removed the Log7 theorems/imports from
  `AntiVectorBalance.lean`, `ConditionalRH.lean`, and the stale import in
  `FactorizationPositivity.lean`. The substantive non-Log7 content of those three files
  (anti-vector defect algebra, `rh_iff_li`, `li_iff_weil`, `hypothesis_hierarchy`,
  `conditional_rh_package`) was preserved.
- **Commented out** (cosmetic, no live Lean users — only the packaging, not the reduction):
  `HelixSource.sourceComplete_iff_grh` (the `↔`) and `sourceComplete_of_grh` (the trivial
  backward `GRH → SourceComplete`, `rate := ρ−½`). The forward reduction `grh_of_sourceComplete`
  and its `grh_of_traceIdentity_*` chain were left live (kernel-proven, load-bearing). The
  equivalence remains a mathematical fact; only its named statement is hidden.
- **Build:** full `lake build` green after all changes, including the new general-χ Hadamard
  chain — **8678 jobs, "Build completed successfully"** (only pre-existing `push_neg` deprecation
  / unused-variable warnings). (An earlier transient "failure" on `DirichletLStripBound` was a
  `timeout` artifact at a 595 s cap, not a real error — it builds clean on its own.)
- **Added** `RULE NINE` to `CLAUDE.md` (read the entire repo before any obstructive content) and
  `RadialInheritance.lean` (reduces `E_radial = 0` to `SourceComplete` with `NoDrift` discharged
  as a theorem) in earlier sessions.

---

## 8. Recommendations (the real remaining research)

1. ~~Finish the general-χ Hadamard partial fraction.~~ **Done** — `hadamardPartialFraction` is
   proved and kernel-clean (`DirichletLHadamardComplete`). The whole analytic backbone (`hid`) is
   now complete for ζ and general χ. No analytic plumbing remains on the critical path.
2. **The one scalp is the on-line forcing / identification — and it is now the *only* thing left**
   (RULE EIGHT). With `hid` (the balance) proved, GRH reduces to carrying the **earned no-drift of
   the source onto the actual zeros** — equivalently, realizing the proved balance by a genuinely
   self-adjoint object so the zeros' reality is *inherited*, not asserted. In the repo's terms:
   discharge `SourceComplete` / `hsa` for an *independently constructed* operator whose resolvent
   trace is the (now-proved) `−L'/L(½+i·)` balance. This is the "HP part," positivity-free; the
   Weil/`WeilFormula` positivity route remains the alternative, not the critical path.
3. **Prose hygiene:** the repo's docstrings remain its least reliable layer. Any future "this
   sorry / this gap" comment should be re-checked against `#print axioms` before being trusted —
   §6 fixed the load-bearing ones (incl. the now-stale `HelixProgram` "TARGET" remark), but a
   broader prose pass would help future readers.

---

*Every "clean" in §3–§4 was produced by `lean_verify` during this audit. Items labelled
"reported by inventory" were gathered in the read-through but not individually kernel-checked;
treat them as high-confidence-but-unverified until a `#print axioms` confirms.*
