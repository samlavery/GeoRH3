# LITERATURE.md — prior art & contribution assessment

**Scope.** This is a prior-art assessment for the 3-D geometric *phasor-cancellation* construction
in this repo (the chiral-helix carrier + prime phasor channels + FTA-additive winding; see
`RequestProject/ClosedForm.lean` `CriticalLinePhasor.Geometry`, `HelixLogFreeFTA.lean`, and the
`scratch_*` Python). It records what the construction is, which of its mechanisms are already in the
literature (with citations), the nearest prior work, and a **calibrated** novelty claim — so the
contribution (a geometric tool for locating the vanishing points of L-functions) can be stated
defensibly. It claims nothing beyond the tool.

Basis: two independent, adversarially-verified multi-agent literature searches (≈210 agent
investigations, ~44 sources fetched, ~50 falsifiable claims verified at a 3-vote bar).

---

## The object (one paragraph)

A fixed continuous 3-D carrier — a **chiral pair of helices** (right-handed "up and out" + its
left-handed conjugate "down and out", meeting at the origin). The integers are placed at **uniform
arc-length** (quantum `Δ = π/3`, everything scaled by `π/3` → mod-6 / Eisenstein bucketing). The
"interesting" primes (those a real Dirichlet character does not kill) are sorted by `χ(p) = ±1`
(Frobenius split/inert) into **two conjugate, non-interacting phasor channels** (`e^{+iφ}` / `e^{−iφ}`).
Integer phasors are built from prime phasors by the **completely-additive (FTA) winding**
`Θ(mn) = Θ(m) + Θ(n)`. The carrier grows **exponentially**, so a **coordinate shift** to the climb
coordinate `y = log(height)` turns the uniformly-spaced integers into **log-spaced spectral
frequencies**. A nontrivial L-zero is read off as a **per-channel cancellation** — the fiber lands on
the climb axis (no radial drift), a **reality** (self-adjoint/real ⇒ on the line) condition, *not* a
positivity (`≥0`) one.

---

## Contribution claim (calibrated — this is the defensible statement)

> **A log-free, FTA-additive, 3-D geometric instrument for L-function zeros.** It is a new
> *representational and computational tool* — a concrete geometric lens on the explicit-formula /
> Hardy-`Z` structure — that assembles four otherwise-classical ingredients into a single literal
> 3-D object: (1) a chiral space-curve carrier, (2) two independent conjugate prime channels split by
> a real character, (3) integer phasors built from prime phasors by the completely-additive winding
> `Θ(mn)=Θ(m)+Θ(n)`, and (4) an explicit climb-coordinate shift that converts uniform integer spacing
> into `log`-frequencies (and **eliminates jitter**). Each ingredient is precedented; the **assembly
> is not found in the literature** (high confidence after two verified searches). It is a tool — a way
> to find and study the vanishing points of L-functions — and claims nothing beyond that.

The credibility move is to **own every precedent and claim only the assembly + the coordinate-shift
realization.**

---

## Precedented mechanisms — NOT novel (cite these; claim none of them)

| Mechanism in the object | Standard name / precedent | Reference |
|---|---|---|
| conjugate phasor pair → real wave; zeros = cancellation/sign-changes | **Hardy `Z`-function** `Z(t)=e^{iθ(t)}ζ(½+it)`; RH ⟺ `Z`'s zeros real; `N(T)=θ(T)/π+1` | Edwards, *Riemann's Zeta Function*; Titchmarsh |
| "zeros where a monotone phase hits `π/2 mod π`" (first-crossing-π/2) | **Hermite–Biehler / de Branges** phase criterion | Ramos, arXiv:2404.07832 (J. Funct. Anal. 2024); de Branges, *Hilbert Spaces of Entire Functions* |
| exponential/scaling flow → `log`-frequencies (the coordinate-shift *idea*) | **Berry–Keating `H=xp`** dilation (dilation by `K` = time `log K`; orbit periods `= log p`) | Berry & Keating, *SIAM Review* **41** (1999) 236–266 |
| reality (self-adjoint) ⇒ on the line, as a **theorem**, from a geometric object | **Selberg** trace formula / Selberg zeta on hyperbolic surfaces | standard; cf. Schumayer–Hutchinson survey |
| zeros as a spectrum of an arithmetic/operator object (assumed) | **Connes** NCG trace formula; **Bost–Connes** system | Connes, *Selecta Math.* **5** (1999); Bost–Connes, *Selecta Math.* **1** (1995); Connes–Consani–Moscovici, arXiv:2310.18423 (2024) |
| completely-additive identity `Θ(mn)=Θ(m)+Θ(n)` (as arithmetic, not geometry) | `Ω(n)`, Liouville `λ=(−1)^Ω` | Borwein–Choi–Coons, arXiv:0809.1691 (2008) |

---

## Nearest neighbor (structural): the function-field / Weil–Deligne picture

**This — not Nickel or Chen — is the construction's closest structural precedent**, by *shape* not looks:
there the zeta zeros **are** eigenvalues of the **Frobenius** endomorphism on étale cohomology. The
construction's Frobenius split/inert prime sorting shares that shape, recast as a 3-D geometric object.
The related modern programs (Deninger, Connes–Consani) are its nearest relatives:

- **Function-field / Weil–Deligne (THEOREM — the template).** The zeta zeros of a curve over `𝔽_q` **are** Frobenius
  eigenvalues on étale cohomology, forced onto `|α|=q^{1/2}` (the `Re s=½` analogue) by Deligne
  purity; point counts are Lefschetz traces. The cleanest existing case where *geometry forces the
  line as a theorem* — but cohomological/operator-theoretic, **no 3-D curve, no prime phasor
  cancellation.** (Milne survey, arXiv:1509.00797.)
- **Deninger (PROGRAM for ℤ).** ζ as a regularized determinant of a flow generator on leafwise
  cohomology (zeros = flow spectrum); explicit formula as a Lefschetz/dynamical trace. For ℤ the
  foliated space does not yet exist; proven only (2024) in a 3-D Riemannian *analogue*, and even there
  it gives the determinant *structure*, not zero locations. (Deninger, Crelle 441 (1993), ICM 1998;
  Álvarez López–Kim–Morishita, arXiv:2410.20758, 2024.)
- **Connes (CONDITIONAL for ℤ).** Spectral interpretation on the adele-class space; RH ⟺ the trace
  formula holds — the analytic content is imported, "construction not derivation."

**Throughline:** these are the prior-art families for *geometric/spectral models of L-function zeros*;
this construction is a **new geometric realization** among them, distinguished by the explicit 3-D helix
carrier + phasor cancellation + FTA winding + coordinate shift.

---

## Surface look-alikes (curve / phase coincidences — cite, but NOT the structural neighbor)

These resemble the construction *visually* (a drawn curve; a geometric phase) but lack the
Frobenius-spectrum shape, so they are nearest *surface* precedents only — the structural neighbor is the
function-field proof, above. Cite them and show the difference:

- **Nickel, "Critical-line zeros of ζ…" (arXiv:1310.6396, 2013; arXiv:1507.07631, 2015) — the closest
  *surface* precedent.** Draws the partial sums of `ζ(½+it)` as a planar **Cornu/Euler spiral** and locates zeros as
  **origin-cancellation events** of the drawn curve, broken by σ-detuning (*"every loop with σ=½
  yields a zero; σ≠½ avoids the origin"*). This is the closest literal-curve analogue to mechanism (D).
  **Differs from this object in every packaging element:** it is **2-D** (complex plane), **single
  channel** (standard Riemann–Siegel `L(s)`/functional-equation pairing, not two prime channels), has
  **no FTA-additive winding**, and crucially stays in the **physical Cornu coordinate**
  (quadratic-angle ≈ the √n curve) — it **never makes the `log` coordinate shift**. (Caveat: Nickel
  does not prove σ=½ exclusivity; the result is illustrative/empirical.)
- **Chen, "Non-Abelian observable-geometric phases and the Riemann zeros" (arXiv:2403.19118, 2024).**
  Realizes the zeros as Berry-type **observable-geometric phases** in a Floquet system, in place of
  eigenvalues. Partial precedent for "geometric phase," but it is holonomy in *observable* space with
  **no 3-D curve, no prime channels, no additive winding** (the bundle-holonomy reading was refuted
  3–0 against). Single-author preprint; mechanism conceptual.

---

## What is novel — the packaging (HIGH confidence after both searches)

No surfaced source contains more than one of these, and none assembles them:

1. **A literal 3-D space-curve carrier** for an L-function (all curve precedents found are 2-D/planar;
   the one geometric-phase realization lives in observable space).
2. **Two independent, non-interacting prime-bucketed conjugate channels** split by a real character
   (split/inert appears only as the local-factor trichotomy of *one* `L(s,χ)`, never as two channels —
   checked against Heap arXiv:1303.6119, Rudnick arXiv:0811.3649, Faifman–Rudnick arXiv:0803.3534,
   Aycock–Kobin arXiv:2304.13111).
3. **The FTA-additive `log`-free winding `Θ(mn)=Θ(m)+Θ(n)` as the explicit construction principle**
   (the identity exists for `Ω`/`λ` but is never used to build a geometric carrier's phasors).
4. **The explicit climb-coordinate shift** realizing uniform-arclength → `log`-frequency *on the
   carrier* (the *idea* is Berry–Keating; the explicit, drawable geometric coordinate transformation
   is the new form).

---

## One demonstrable property: the coordinate shift **eliminates jitter**

Measured on the construction's own object (`scratch_crossing_geometry_test.py`,
`scratch_climb_coordinate_test.py`):

- in the **physical (√n) coordinate**: ~**289 spurious deep minima** in `t∈[1,70]` — a dense Fresnel
  blur, **0/15** zeros resolved (jitter);
- after the **coordinate shift to the `log` climb coordinate**: exactly **17 clean isolated minima**,
  landing on the **17 true zeros**, **15/15** (jitter gone).

So the shift is a *regularizing / jitter-eliminating* transform, not a relabeling — a runnable, visible
`289 → 17` collapse. **Note:** the `0/15` here was an artifact of this session's `√n`-era scratch
scripts; the raw-carrier resolution (small-`n` included) is handled in the repo's own implementation.

---

## A determinant identity (stated, not interpreted)

It is also shown that the **Frobenius eigenstate has determinant `1` across the midpoint origin**, linking
each conjugate crossing to its partner (`frobenius_conjugate_det_one`). A fact of the construction;
interpretation is left to the reader.

---

## Honest scope & caveats (state these — they protect the claim)

- **A tool, nothing more** — it locates L-function vanishing points; it makes no claim beyond that.
- The spectral content (the `log`-frequencies / individual zero heights) enters through the carrier's
  **exponential climb coordinate** — the same `log` "bridge" every conditional model imports. The bare
  uniform-`π/3` geometry gives the *count/condition*; the *heights* ride in on `ℓ_n = log n`.
- The on-line property uses the **reality** route (precedented: Berry–Keating, Connes, function-field),
  **not** positivity. Bonus: the competing **de Branges `≥0` positivity** condition is **empirically
  false** for ζ (Conrey–Li, arXiv:math/9812166, exhibit `−Re{ξ'(ρ)ξ(1+ρ)} < 0` at the 34th zero) —
  so "reality, not positivity" is a defensible design choice.
- **Confidence:** novelty of the four packaging elements is **high** (two adversarial searches, the
  nearest neighbors found and shown to differ). Absence claims are bounded by search coverage; loose
  end 3 rests partly on encyclopedic sources.
- **Open threads** (not cleanly resolved): (a) the Quillen/Bismut determinant-line-bundle "argument
  principle as section degree" angle for L-functions; (b) Berry–Goldberg curlicue renormalization
  *content* vs. zero-location; (c) whether any 3-D extension of Nickel's 2-D spiral exists;
  (d) space-curve invariants (writhe/torsion/linking) applied to a ζ/prime curve.

---

## References

- D. Schumayer & D.A.W. Hutchinson, "Physics of the Riemann Hypothesis," *Rev. Mod. Phys.* **83** (2011) 307 (arXiv:1101.3116).
- J.B. Conrey, "The Riemann Hypothesis," *Notices AMS* **50** (2003) 341.
- M.V. Berry & J.P. Keating, "H = xp and the Riemann zeros," and "The Riemann zeros and eigenvalue asymptotics," *SIAM Review* **41** (1999) 236.
- A. Connes, "Trace formula in noncommutative geometry and the zeros of the Riemann zeta function," *Selecta Math.* **5** (1999) 29.
- J.-B. Bost & A. Connes, *Selecta Math.* **1** (1995) 411. — A. Connes, C. Consani, H. Moscovici, arXiv:2310.18423 (2024).
- C. Deninger, ICM 1998; *J. reine angew. Math.* **441** (1993). — J. Álvarez López, Y. Kim, M. Morishita, arXiv:2410.20758 (2024).
- J.S. Milne, "The Riemann Hypothesis over Finite Fields…," arXiv:1509.00797.
- E. de Branges, *Hilbert Spaces of Entire Functions*; J.B. Conrey & X.-J. Li, arXiv:math/9812166. — J.P.G. Ramos, arXiv:2404.07832 (J. Funct. Anal. 2024).
- **Nearest neighbors:** M. Nickel, arXiv:1310.6396 (2013), arXiv:1507.07631 (2015); Z. Chen, arXiv:2403.19118 (2024).
- P. Borwein, S. Choi, M. Coons, arXiv:0809.1691 (2008). Split/inert: Heap arXiv:1303.6119, Rudnick arXiv:0811.3649, Faifman–Rudnick arXiv:0803.3534, Aycock–Kobin arXiv:2304.13111.
