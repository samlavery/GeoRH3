# RequestProject Lean Catalog

Purpose: catalog every `RequestProject/*.lean` file by its possible usefulness toward an
actual RH proof chain, separating unconditional Lean content from conditional interfaces,
diagnostic files, and compatibility scaffolding.

## Inventory Commands Used

```bash
find RequestProject -maxdepth 1 -name '*.lean' -type f | sort
rg -n '^import ' RequestProject/*.lean
rg -n '^\s*(sorry|admit|exact\?|axiom\b)|:=\s*by\s+sorry|by\s+sorry|exact\?' RequestProject/*.lean
rg -n '^(theorem|lemma|def|structure|class|inductive|abbrev|opaque|noncomputable def)\b' RequestProject/*.lean
```

## Current Compile Prerequisites

Several moved files currently import modules that are still in `tmp/`, not in
`RequestProject/`:

- `RequestProject.VonMangoldtEFStandalone` is imported by `EFTestAndBridge`,
  `HelixExplicitFormula`, `HelixGreedyResidue`, `HelixPositivityGap`,
  `HelixResidueSummability`, `RiemannHypothesis`, `SpectralIdentification`,
  and `SpectralRH`.
- `RequestProject.JensenStandalone` is imported by `HelixExplicitFormula`.

Current source locations:

- `tmp/VonMangoldtEFStandalone.lean`
- `tmp/JensenStandalone.lean`

Direct checks observed:

- `lake env lean RequestProject/XiPartialFraction.lean` exits 0 and prints clean
  axiom footprints for `ZD.logDeriv_xiProductMult_partial_fraction` and
  `ZD.xi_logDeriv_partial_fraction`.
- `lake env lean RequestProject/RHFromEF.lean` exits 0 with one declaration using
  `sorry`.
- `lake env lean RequestProject/RiemannHypothesis.lean` fails at import resolution
  until `VonMangoldtEFStandalone` exists under `RequestProject/`.

Actual proof placeholders in `RequestProject/*.lean`:

- `RequestProject/RHFromEF.lean:96`
- `RequestProject/WeilExplicitBridge.lean:175`

Interactive-search tactics still present:

- `RequestProject/LiPositivity.lean:70`
- `RequestProject/HelixProjectionEigenvalue.lean:548`
- `RequestProject/HelixProjectionEigenvalue.lean:550`

## High-Value Chains

### A. Active Helix / Spectral Chain

These files are the most relevant new path after the `tmp` move.

- `ForcedAlignment.lean` proves the key single-pair Möbius/Li forcing facts:
  reciprocal pairing, bounded paired Li forcing `σ = 1/2`, and projection/loss
  algebra. Unconditional, no source placeholders found.
- `NoOfflineZeros.lean` formalizes finite zero data, partial Li sums, one-offline
  forcing, and uniform-boundedness conditions. Unconditional local theorems plus
  explicit bridge assumptions.
- `HelixConvergence.lean` handles finite-to-infinite summability interfaces for
  on-line paired terms and Möbius norm-square estimates. Unconditional local
  content, but it depends on `NoOfflineZeros`.
- `HelixGreedyResidue.lean` connects the helix cascade, Euler/product residues,
  projection positivity, and EF-shaped positivity summaries. It depends on the
  missing `VonMangoldtEFStandalone`.
- `HelixResidueSummability.lean` connects Möbius residue size, summability, and
  Li coefficients. It depends on the missing `VonMangoldtEFStandalone`.
- `SpectralIdentification.lean` is a central interface: paired Li coefficients as
  norm-squares and spectral identification forcing line placement. It depends on
  the missing `VonMangoldtEFStandalone`.
- `SpectralRH.lean` packages the `SpectralRealization` structure and proves that
  realization data forces every indexed zero onto the line. Conditional on the
  realization structure; depends on the missing `VonMangoldtEFStandalone`.
- `RiemannHypothesis.lean` is the new top-level spectral wrapper using Mathlib's
  `RiemannHypothesis`. Conditional on spectral realization; depends on the missing
  `VonMangoldtEFStandalone`.
- `HelixProjectionEigenvalue.lean` proves self-adjoint idempotent projection
  facts, eigenvalue/loss tracking, reconstruction, and projection constraints.
  Mostly unconditional projection algebra; replace the two `exact?` calls for
  stable source.
- `HelixPositivityGap.lean` summarizes unconditional projection positivity,
  sigma-greater-than-one nonnegativity, off-line energy violation lemmas, and
  Mathlib RH connection theorems. Depends on the missing `VonMangoldtEFStandalone`.
- `TwoFieldSpectral.lean`, `InversionDestruction.lean`, and
  `PipelineArchitecture.lean` provide the two-channel/two-stage geometric
  architecture and the inversion/unit-circle mechanism. Useful as explanatory and
  algebraic infrastructure.

### B. Analytic / Xi / Hadamard / Explicit-Formula Chain

These files are the strongest analytic infrastructure currently in
`RequestProject`.

- `XiWeierstrassFactor.lean`, `XiProduct.lean`, `XiProductZeros.lean`,
  `XiOrder.lean`, `XiOrderSummable.lean`, `XiProductMult.lean`,
  `XiProductMultOrder.lean`, `XiLogDerivTerms.lean`,
  `XiProductMultPartialFraction.lean`, `XiHadamardQuotient.lean`,
  `XiHadamardLog.lean`, `XiOverPGrowth.lean`, `WeilHadamardOpenPatch.lean`,
  `XiHadamardFactorization.lean`, and `XiPartialFraction.lean` form a coherent
  ξ product / partial-fraction stack. `XiPartialFraction.lean` currently checks
  cleanly and is a high-value source of analytic input.
- `VonMangoldtExplicitFormula.lean`, `Layer1Objects.lean`,
  `LogDerivIdentity.lean`, and `OperatorCoupling.lean` are the older explicit
  formula track using the xi partial fraction infrastructure.
- `EulerMaclaurinDirichlet.lean`, `SpiralInduction.lean`,
  `StirlingBound.lean`, `RiemannXiDecay.lean`, `ZetaStripBound.lean`,
  `ZeroCountJensen.lean`, `ZetaBound.lean`, and `ZetaBoundHelpers.lean` provide
  analytic estimates: continuation/Dirichlet series, Stirling, strip bounds,
  Jensen zero counting, and lower bounds on zero height.
- `RHFromEF.lean` is a conditional wrapper from explicit formula style input to
  `RiemannHypothesis`; it contains one actual `sorry`.

### C. Weil / Gaussian / Cosh Detector Chain

These files are useful for test functions, positivity interfaces, and zero-side
detectors.

- `WeilPositivity.lean` proves von Mangoldt nonnegativity, prime-power weights,
  diagonal positivity, projection positivity, and related Weil-form algebra.
  No source placeholders found.
- `WeilExplicitBridge.lean` is a new bridge from explicit formula data to Li
  positivity and finite zero conclusions. It has one actual `sorry` at the
  finite-on-line extraction step.
- `WeilBridge.lean`, `PartialWeilFormula.lean`, `WeilCoshTest.lean`,
  `WeilCoshPairPositivity.lean`, and `WeilCoshPairPositivity_RouteBeta.lean`
  package the partial Weil formula and cosh/Gaussian test-function side.
- `GaussianAdmissible.lean`, `GaussianClosedForm.lean`, and
  `GaussianDetectorPair.lean` provide concrete Gaussian kernels, closed forms,
  and pair detectors. Useful when a proof chain needs an explicit positive test.
- `WeilContour.lean` and `WeilContourMultiplicity.lean` are large contour-side
  analytic files. Useful for residue, Mellin, Gaussian pair-test, and multiplicity
  versions of the contour argument.
- `ExplicitFormulaBridgeOfRH.lean` is legacy compatibility scaffolding. Its
  current value is reference/backward imports, not the preferred bridge.
- `t.lean` duplicates the `XiHadamardFactorization.lean` content and appears to be
  scratch or a renamed copy; use the named file instead.

## File-by-File Catalog

Legend:

- `Unconditional`: local Lean statements have no actual `sorry` in this source.
- `Conditional`: proves implications from named hypotheses, structures, or bridge
  assumptions.
- `Placeholder`: contains actual `sorry` or interactive `exact?` source.
- `Auxiliary`: definitions, estimates, diagnostics, or compatibility support.

| File | Status | Useful contribution |
| --- | --- | --- |
| `AntiVectorBalance.lean` | Unconditional / conditional summary | Prime residual and anti-vector defect algebra; supports log-scale imbalance and factorization-residue arguments. |
| `BridgeToZeroFree.lean` | Unconditional / conditional bridge | Mertens trigonometric nonnegativity and a `weil_positivity_full` bridge proposition feeding zero-free style conclusions. |
| `CombinedLoss.lean` | Unconditional operator algebra | Self-adjoint/idempotent combined loss, no-drift, positivity, Pythagorean decomposition. Useful for projection-cascade bookkeeping. |
| `ConcreteOperators.lean` | Unconditional finite model | Concrete finite spectral values, helix vectors, diagonal spectral unit-circle criteria, and cascade reconstruction. |
| `ConditionalRH.lean` | Conditional packaging | Packages Li positivity, Weil bridge, and scaling-rate conditions into RH-style conclusions. Useful for dependency tracing. |
| `CoordinateInvariance.lean` | Unconditional geometry | Shows half-unit as fixed point of strip involution and handles rescaled coordinates. Useful for interpreting the `1/2` readout. |
| `CoshBalance.lean` | Auxiliary | Minimal definition of `CoshBalance = cosh 0 / 2`. |
| `Defs.lean` | Core definitions | Unit-width critical-line definitions, nontrivial zeta zero sets, field markers, drift, and geometric readout notions. |
| `Dichotomy.lean` | Conditional finite/set dichotomy | All-on-line/all-off-line split, infection/no-dilution style finite-set lemmas, and Weil-positivity consequences. |
| `DoubleCoshResidue.lean` | Unconditional detector algebra | Double-cosh residue classifier: balanced iff on-line, unbalanced grows. |
| `DoubleCoshValidation.lean` | Unconditional/conditional classifier | Validates double-cosh classifier against zeta zero predicates and packages classifier versions of RH. |
| `EFTestAndBridge.lean` | Conditional; missing import | Tests explicit formula at `s=2,3`, proves sigma-greater-than-one zero-term nonnegativity, and bridges to conditional RH summaries. Needs `VonMangoldtEFStandalone`. |
| `EnergyDefect.lean` | Conditional energy API | Quadratic energy defect, centered excess, cosine/sine transforms, and closure lemmas. Depends on parseval interfaces. |
| `EulerMaclaurinDirichlet.lean` | Unconditional analytic infrastructure | Euler-Maclaurin/Dirichlet continuation objects and bounds for zeta in `0 < Re(s)`. Useful upstream of strip estimates. |
| `ExplicitFormulaBridgeOfRH.lean` | Legacy compatibility | Older Gaussian/Weil bridge factorization API. Keep for imports, but prefer newer Weil/cosh and xi-partial-fraction tracks. |
| `FactorizationPositivity.lean` | Conditional bridge | Connects factorization residue and Li positivity through a bridge proposition. Useful as a specification of the factorization-to-Li step. |
| `FiniteRH.lean` | Unconditional finite extension | Extends single-pair Li forcing to finite sets with synchronization/recurrence support. |
| `ForcedAlignment.lean` | High-value unconditional core | Reciprocal Möbius pairing, bounded paired Li forcing `σ = 1/2`, self-adjoint/loss embedding, and Euler residual positivity. |
| `GapAnalysis.lean` | Diagnostic | Classifies geometric half-unit facts versus analytic target facts; useful for avoiding bookkeeping mistakes. |
| `GapAudit.lean` | Diagnostic | Narrative audit of proved layers and remaining bridge interfaces. No declarations. |
| `GaussianAdmissible.lean` | Mostly auxiliary analytic kernel | Gaussian admissibility and domination lemmas for Weil bridge kernels. |
| `GaussianClosedForm.lean` | Unconditional closed forms | Closed forms for Gaussian theta observables and energy defect. Useful for explicit detector calculations. |
| `GaussianDetectorPair.lean` | Unconditional detector algebra | Left/right Gaussian detectors, ratio/square-difference formulas, and positivity off the line. |
| `GreenHelmholtz.lean` | High-value unconditional operator core | Orthogonal projection/self-adjoint/no-drift/positivity/Pythagorean facts for 3D and 2D cascades. |
| `HalfLineParseval.lean` | Auxiliary analytic infrastructure | Derives half-line parseval identities from Plancherel-style statements; useful for energy-defect discharge. |
| `HarmonicDiagnostics.lean` | Diagnostic/API consumer | Packages detector memberships, online/offline diagnostics, and RH-style summaries over bridge definitions. |
| `HelixConvergence.lean` | High-value unconditional convergence interface | Paired Li norm-square identities and summability conditions for finite-to-infinite passage. |
| `HelixExplicitFormula.lean` | Conditional; missing imports | Helix amplitude/winding, helix zero contribution, Li coefficient, envelope, and five-way critical-line characterizations. Needs `VonMangoldtEFStandalone` and `JensenStandalone`. |
| `HelixForcing.lean` | Conditional architecture | Functional-equation anti-symmetry, spectral consistency, and structural forcing summaries over helix operators. |
| `HelixGreedyResidue.lean` | Conditional; missing import | Greedy residue/additive Euler product view and positivity-chain summaries. Needs `VonMangoldtEFStandalone`. |
| `HelixIdentity.lean` | Unconditional algebra | Master identities, two-channel decomposition, additive operator loss/rhs identities, midpoint and growth sign facts. |
| `HelixNonClosure.lean` | Conditional number-theoretic geometry | Log-prime non-closure facts, Lindemann-style hypothesis interface, helix remainder and projection-loss positivity for primes. |
| `HelixPositivityGap.lean` | Conditional; missing import | Projection positivity, off-line energy violation, constraints forcing line placement, and Mathlib RH bridge summaries. Needs `VonMangoldtEFStandalone`. |
| `HelixProjectionEigenvalue.lean` | Placeholder cleanup needed | Self-adjoint projection eigenvalue/loss/reconstruction theorems and helix projection summaries. Replace two `exact?` calls. |
| `HelixProjectionZeros.lean` | Unconditional geometry/model | Roots of unity, helix angle/point operations, projection losses, Möbius map, and Li-term on-line nonnegativity. |
| `HelixResidueSummability.lean` | Conditional; missing import | Möbius residue equals reciprocal, summability interfaces, and Li coefficient boundedness/unboundedness. Needs `VonMangoldtEFStandalone`. |
| `HelixRoundTrip.lean` | High-value unconditional core | Round-trip projection energy, involutions, Möbius helix map, unit criterion, Li helix terms, recurrence, and status summary. |
| `HelixSelfDual.lean` | Unconditional operator algebra | Self-adjointness of `G^2`, loss, rhs, channel duality, and real projection loss identities. |
| `InversionDestruction.lean` | Unconditional geometry | Unit-circle/inversion facts, off-unit growth/decay, and positivity destruction lemmas. |
| `Layer1Objects.lean` | Auxiliary explicit-formula layer | Von Mangoldt, L-series, and log-derivative identity objects for the older explicit formula track. |
| `LiPositivity.lean` | Placeholder cleanup needed | Li coefficient positivity interface importing `HelixExplicitFormula` and `RHFromEF`; contains an `exact?` tactic. |
| `Log7Comparison.lean` | Unconditional coordinate comparison | Compares standard unit and log-7 scale, including midpoint and defect-rate transformations. |
| `Log7HelixRH.lean` | Conditional coordinate package | Log-7 helix version of line placement, Li boundedness, and factorization interfaces. |
| `LogDerivIdentity.lean` | Analytic explicit-formula support | Log-derivative identities and theta transport input for the older von Mangoldt explicit formula. |
| `Main.lean` | Project options only | Imports Mathlib and sets options; does not import the library files. |
| `MellinPathToXi.lean` | Analytic bridge | Mellin/theta path toward ξ and completed zeta identities. Useful upstream of Weil/cosh tests. |
| `MirrorPairDefect.lean` | Unconditional pair algebra | Mirror-pair defect and off-line/on-line pair behavior used by dichotomy and concrete operator files. |
| `NoOfflineZeros.lean` | High-value conditional bridge | Finite Li sums, one-offline forcing, abstract zero data, convergence and uniform-boundedness interfaces. |
| `NontrivialZeros.lean` | Core definitions | Thin wrapper around nontrivial zero predicates from `Defs`. |
| `OfflineAmplitudeMethods.lean` | Detector support | Offline amplitude, cosh/sinh, and growth diagnostics consumed by harmonic files. |
| `OperatorCoupling.lean` | Auxiliary placeholder API | Small operator-coupling file for the older explicit formula stack. |
| `PNTDichotomy.lean` | Auxiliary scale/coherence | Prime-number-theorem style dichotomy over coordinate/scaling coherence. |
| `PairCoshGaussTest.lean` | Gaussian/cosh support | Pair test functions and small Gaussian/cosh facts used by contour files. |
| `PartialWeilFormula.lean` | Conditional Weil API | Defines a partial Weil formula object and zero/prime side summands. Useful as an interface. |
| `PipelineArchitecture.lean` | Unconditional/conditional architecture | Two channels by two projection stages, channel energy, merge loss, and master dichotomy packaging. |
| `PrimeNormScaling.lean` | Auxiliary coordinate scaling | Prime norm scaling and coherence facts for log-scaled interpretations. |
| `ProjectionSelfAdjoint.lean` | High-value unconditional operator core | Orthogonal projections and self-adjointness for concrete subspaces in real inner product spaces. |
| `RHFromEF.lean` | Placeholder | Conditional route from explicit-formula envelope bounds to Mathlib RH; contains one actual `sorry`. |
| `RiemannHypothesis.lean` | Conditional; missing import | New top-level spectral package using Mathlib `RiemannHypothesis`. Needs `VonMangoldtEFStandalone`. |
| `RiemannHypothesisBridge.lean` | Compatibility bridge | Connects cosh-balance/double-cosh validation to RH-style statements. |
| `RiemannXiDecay.lean` | Analytic estimates | Decay/bounds for ξ using Stirling/theta transport; used by Jensen and contour tracks. |
| `RoundTripForcing.lean` | Conditional helix/RH wrapper | Uses helix explicit formula and RH-from-EF interface to package round-trip forcing. |
| `ScalingCoherence.lean` | Unconditional coordinate algebra | Scale/unscale coherence and unit-width readout facts. |
| `SimulRecurrence.lean` | Recurrence support | Simultaneous recurrence lemmas used by finite zero-set arguments. |
| `SpectralConvergence.lean` | Conditional spectral bridge | Spectral convergence and bridge assumptions tying operators to zero data. |
| `SpectralIdentification.lean` | High-value conditional; missing import | Paired Li coefficient spectral identification and norm-square bridge. Needs `VonMangoldtEFStandalone`. |
| `SpectralRH.lean` | High-value conditional; missing import | `SpectralRealization` structure and proof that realization data places every indexed zero on the line. Needs `VonMangoldtEFStandalone`. |
| `SpiralInduction.lean` | Analytic/geometric support | Spiral and induction lemmas for zeta/Euler-Maclaurin work. |
| `StirlingBound.lean` | High-value analytic estimates | Stirling and gamma-ratio bounds used by strip, Jensen, and ξ decay files. |
| `ThetaCenteredExcess.lean` | Theta detector support | Centered theta excess and zero-side detector facts. |
| `ThetaTransport.lean` | Analytic transport | Theta/Mellin transport infrastructure feeding log-derivative and Gaussian closed-form files. |
| `TwoFieldSpectral.lean` | Unconditional geometry/model | Two-field spectral architecture, mirror pair defects, unit-circle and spiral behavior, two-stage energy split. |
| `UniversalRH.lean` | Conditional universal packaging | Universal finite-to-set summaries over concrete operators and Green-Helmholtz pieces. |
| `VonMangoldtExplicitFormula.lean` | High-value analytic bridge | Older explicit formula using `XiPartialFraction`, layer objects, and operator coupling. |
| `WeilBridge.lean` | Conditional bridge API | Defines Weil bridge/admissible kernel interfaces and closure facts. |
| `WeilContour.lean` | High-value analytic contour file | Mellin/Gaussian identities, zeta log-derivative, contour/residue infrastructure, and pair-test assembly. |
| `WeilContourMultiplicity.lean` | Analytic multiplicity support | Multiplicity-aware residue/log-derivative contour support. |
| `WeilCoshPairPositivity.lean` | Conditional detector bridge | Cosh separation and `WeilVanishesOnZeros` interface yielding line placement. |
| `WeilCoshPairPositivity_RouteBeta.lean` | Conditional detector bridge | Even/odd channel formalization and bridge from balanced channels to zero-side vanishing. |
| `WeilCoshTest.lean` | Unconditional/conditional test functions | Cosh/Gaussian test functions, prime-side summands, and zero-side closed forms. |
| `WeilExplicitBridge.lean` | Placeholder | Explicit-formula bridge from prime positivity to Li positivity; one actual `sorry` remains. |
| `WeilHadamardOpenPatch.lean` | High-value analytic support | Local open-patch partial-fraction identities used in the Hadamard factorization path. |
| `WeilPositivity.lean` | High-value unconditional positivity | Von Mangoldt weights, Euler product/prime-power survival, Weil diagonal positivity, and projection positivity. |
| `XiHadamardFactorization.lean` | High-value analytic theorem | Hadamard factorization of ξ via product quotient and partial-fraction-on-open machinery. |
| `XiHadamardLog.lean` | High-value analytic support | Entire zero-free quotient `ξ / xiProductMult`. |
| `XiHadamardQuotient.lean` | High-value analytic support | Zero equivalence between ξ/completed zeta and nontrivial zeta zeros. |
| `XiLogDerivTerms.lean` | High-value analytic support | Per-factor log-derivative and summability for Weierstrass factors. |
| `XiOrder.lean` | High-value analytic support | Defines finite zero orders of ξ at nontrivial zeros. |
| `XiOrderSummable.lean` | High-value analytic support | Multiplicity-weighted summability of zero orders over inverse norm squared. |
| `XiOverPGrowth.lean` | High-value analytic estimates | Mean-type growth bound for `xiOverP = ξ / xiProductMult`. |
| `XiPartialFraction.lean` | High-value analytic bridge | Clean partial fraction for `ξ'/ξ` from product and factorization tracks. Verified by direct Lean check. |
| `XiProduct.lean` | High-value analytic support | Locally uniform Weierstrass product over nontrivial zeros. |
| `XiProductMult.lean` | High-value analytic support | Multiplicity-indexed Weierstrass product and zero-set equivalence. |
| `XiProductMultOrder.lean` | High-value analytic support | Order matching for `xiProductMult` at each nontrivial zero. |
| `XiProductMultPartialFraction.lean` | High-value analytic support | Product-side multiplicity-weighted partial fraction. |
| `XiProductZeros.lean` | High-value analytic support | Entire product and zero-set coincidence with nontrivial zeros. |
| `XiWeierstrassFactor.lean` | High-value analytic support | Genus-1 Weierstrass factor, derivative, and norm bounds. |
| `ZeroCountJensen.lean` | High-value analytic estimates | Jensen zero-count bound and summability infrastructure for nontrivial zeros. |
| `ZetaBound.lean` | Analytic estimates | Lower bound on imaginary part of nontrivial zeta zeros and completed-zeta nonzero facts. |
| `ZetaBoundHelpers.lean` | Analytic estimates | Mellin and completed-zeta norm helper bounds. |
| `ZetaConnection.lean` | Conditional bridge | Connects abstract helix/Möbius statements to Mathlib `riemannZeta` and Mathlib RH. |
| `ZetaStripBound.lean` | High-value analytic estimates | Polynomial bound for zeta in the critical strip via regularization and strip estimates. |
| `ZetaZeroDefs.lean` | Core definitions | Canonical zero predicates, online/offline sets, witness structures, and many membership lemmas. |
| `t.lean` | Scratch duplicate | Duplicate of `XiHadamardFactorization.lean`; useful only as a scratch comparison file. |

## Most Useful Files To Prioritize

1. Move or recreate the two missing imported modules if the new helix/spectral
   chain is the target:
   `tmp/VonMangoldtEFStandalone.lean` and `tmp/JensenStandalone.lean`.
2. Stabilize source placeholders:
   `RHFromEF.lean`, `WeilExplicitBridge.lean`, `LiPositivity.lean`,
   and `HelixProjectionEigenvalue.lean`.
3. For analytic input, prioritize:
   `XiPartialFraction.lean`, `XiHadamardFactorization.lean`,
   `XiOverPGrowth.lean`, `XiProductMultPartialFraction.lean`,
   `ZeroCountJensen.lean`, `ZetaStripBound.lean`, and `StirlingBound.lean`.
4. For geometric/operator input, prioritize:
   `ForcedAlignment.lean`, `HelixRoundTrip.lean`, `GreenHelmholtz.lean`,
   `ProjectionSelfAdjoint.lean`, `HelixConvergence.lean`,
   `SpectralIdentification.lean`, and `SpectralRH.lean`.
5. For bridge/test-function input, prioritize:
   `WeilPositivity.lean`, `WeilExplicitBridge.lean`, `WeilContour.lean`,
   `WeilCoshTest.lean`, `GaussianDetectorPair.lean`, and
   `PartialWeilFormula.lean`.

