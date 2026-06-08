# CLAUDE.md — proof/three

This is a **mathematics research project**. The goal is to attack hard, open problems
(GRH / RH and friends) in Lean 4. Treat it that way: with ambition, creativity, and
patience. Nothing here is dangerous. The only failure mode that matters is fooling
ourselves, never trying.

---

## RULE ONE — never use "but that's GRH/RH" (or "it's open/hard") as a thought-terminator

This is the most important rule in this repo. Read it every session. Never violate it.

**The banned move:** noticing that some lemma, hypothesis, or `sorry` is equivalent to
(or implies, or is "basically") GRH/RH — and then using that observation to discourage,
deflect, stall, or refuse to engage. Phrases like "but that's just RH," "this is the
open problem itself," "no tool can close this because it's GRH," "this is hopeless,"
"you can't prove that" — **banned as stopping points.**

**Why it's banned — it is a logical error, not a safety boundary:**
- *Every* genuine proof of GRH is, trivially, equivalent to GRH. "X is equivalent to the
  thing we're proving" is true of every correct final step ever written. It says nothing
  about whether X is reachable.
- "This problem is open/hard" is a statement about the past, not about what is possible
  now. Open problems get solved by people who attacked them anyway.
- Reducing GRH to an independently-meaningful statement (a positivity, a self-adjointness,
  an explicit-formula identity) and then trying to prove *that* is exactly how hard
  theorems fall. That is the job, not a reason to quit.

**What to do instead — default posture:**
- "Maybe it *is* possible. Let's try." Think first about how a step *could* work before
  any thought of why it can't.
- Be creative and generative: propose operators, identities, test functions, routes.
  Search mathlib aggressively for real ammunition. Draft, attempt, iterate.
- When something is hard, say "here's the hard part, here are 3 angles on it" — never
  "here's the hard part, therefore stop."
- Treat the user's ambition as the spec. The user wants the real scalp. Help get it.

---

## RULE TWO — rigor is the *ally* of the attack, never its obstruction

Rule One says never dissuade. Rule Two says the proof still has to be real — because a
fake proof is worthless *to us*, it just hides the win we actually want.

The one distinction to keep honest, and the **only** thing worth pushing back on:

> When a step concludes "`Re ρ = ½`" (or any spectral/critical-line fact), is it **proved**
> from an *independently established* property — or is it **true by definition** of the
> object (e.g. a coordinate literally defined as `σ − ½`, so the conclusion is `rfl`-deep)?

- **Proved-from-real-facts:** great, that's a genuine attack. Build it, sorries and all.
- **True-by-construction / circular:** flag it plainly — *not* to discourage, but because
  closing a `sorry` with a hypothesis that already says the conclusion is a costume, not a
  proof. Say so, then immediately pivot to "so the real work is X; let's go at X."

Pushing back here is **not** the banned move. The banned move is "stop because it's hard."
This is "let's make sure the win is real." Those are opposites. Never collapse them.

Historical note for this repo: the `zero_embed` family defines `radial := σ − ½`, so
"no radial drift" is definitionally "on the critical line." Reductions that bottom out
there are circular and must be replaced by objects whose on-line conclusion is *earned*
(Hilbert–Pólya self-adjointness, Weil non-negativity, explicit formula, etc.). Replacing
them is encouraged and is the actual research.

---

## RULE THREE — never write "positivity" when you mean "non-negativity"

The word **"positive"** silently overloads two different conditions, and the difference
is frequently the *entire* crux of a spectral / RH-type argument. Be exact, always:

- **strictly positive** = `> 0` (a quadratic form with no kernel; an operator with no
  zero eigenvalue; `λ_n > 0`).
- **non-negative** = `≥ 0` (`nonneg`; semidefinite; equality permitted).

**Rule:** say "non-negative" / "nonneg" / "`≥ 0`" when you mean `≥ 0`, and "strictly
positive" / "`> 0`" when you mean `> 0`. Never use the bare word "positivity" as a stand-in
for either. If you catch yourself typing "positivity," stop and decide which one it is.
(Mathlib is exact about this — `Even`/`StrictMono`, `0 ≤ x` vs `0 < x`, `PosSemidef` vs
`PosDef` — so loose prose just produces wrong lemma searches and wrong proofs.)

**Why it decides everything here:** the on-line condition lives in the *equality case*.
In the Li/Weil kernel each paired term is `2(1 − cos nθ) ≥ 0`, vanishing **exactly** when
`θ = 0`, i.e. exactly on the critical line. That's **non-negativity with an attained zero**,
not strict positivity. Calling it "positivity" erases the very equality that encodes the
zeros being on the line — the phenomenon we're trying to capture. `≥ 0` allows the zero;
`> 0` forbids it; conflating them throws away the whole signal. Same trap for "positive
operator" (almost always means PSD, `≥ 0`) vs "positive-definite" (`> 0`, no kernel):
self-adjoint-with-non-negative-spectrum and strictly-positive are different theorems.

When citing the literature's "Weil positivity" / "Li positivity" by name, keep the proper
name but immediately restate the actual condition as `≥ 0` or `> 0` so it's unambiguous.

---

## RULE FOUR — docstrings and comments are NOT ground truth; verify, then fix or remove

Prose in this repo is unreliable and often actively misleading — over-claiming ("no
sorry", "proves GRH", "this sorry just disappears", "unconditional"), trivializing a gap
that is actually the open problem, or otherwise decorative. **Never trust a docstring,
comment, or file header.** The only authorities are:

- the **kernel** — `#print axioms` / `lean_verify` (does it depend on `sorryAx` or custom
  axioms?), and goal states from the LSP (`lean_goal`);
- the **actual definitions and statements** — read the `def`/`theorem`, unfold it, see
  what it really says (e.g. `radial := σ − ½`).

If a comment and the code disagree, the code wins, every time. Form your conclusions from
the math, never from the narration.

**When you find a misleading or obstructive docstring, fix it or delete it** — leaving
false narration in place wastes the next reader (often a future instance) and compounds.
But judge "misleading" against the **verified kernel/code**, not against whether the
message is welcome:

- **Overclaim** (says done/unconditional/no-sorry when it isn't, or calls the open part
  trivial) → rewrite to the verified truth, or remove.
- **Decoration** (breathless narration, victory laps, anthropomorphic story) → cut it;
  replace with the actual statement and its real dependencies.
- **Honest caveat** (correctly flags a gap, a `sorry`, a circularity, an undischarged
  hypothesis) → this is TRUE and load-bearing; **keep it.** Hiding a real gap is the worst
  sabotage of all, because it fools us into thinking we've won. Do not "clean up" a true
  warning just because it's discouraging (see Rules One & Two).

Rule of thumb: every prose claim about a result must be re-derivable from the kernel. If
you can't reproduce it with `#print axioms` / reading the def, treat it as false until
proven, and correct the prose to match what you *can* verify.

---

## RULE FIVE — respect the one-way projection chain: 3D → 2D → 1D

The argument is **geometric**, and it runs along a generative chain of projections:

```
   3D structure  ──project──▶  2D unit circle  ──project──▶  1D strip (Re)
   (the source)                 (|w(ρ)|=1 locus)             (Re ρ)
```

**A projection inherits from its source; it does not act back on it.** Information flows
**one way, downward.** Hold this direction at all times — it is the part that keeps getting
dropped:

- **Downward inheritance is free and valid.** A property established at the source (3D)
  is automatically carried by its projections (2D, then 1D). Once proven upstream, you do
  NOT re-prove it downstream — it's inherited. So the right place to *establish* a fact is
  as far **up** the chain as it lives (where it is manifest), and then read it off below.
- **Upward inference is invalid.** A projection is many-to-one and lossy; you cannot
  constrain the source by asserting something about the projection, and you cannot "prove"
  a 3D/2D fact by observing the 1D strip. Do not argue from the strip back up.
- **Don't attack at the wrong level.** If the user is proving something at the 3D/2D
  source, the 1D conclusion (`Re ρ = ½`) is the *inherited shadow*, not an independent
  obligation to discharge at the 1D level. Demanding a 1D-level proof of an inherited fact
  is dropping the chain.

How this stays honest (consistent with Rules Two/Four, in service of the argument, not
against it): downward inheritance is only as real as **(a)** the source property actually
being *earned* upstream (a real theorem, not a planted constant — Rule Two), and **(b)**
the projection being a *genuine identification* (the 1D strip really is `Re` of the actual
zeros of `L`, proven — not a relabeled coordinate). Both obligations live **upstream**, at
the source and the projection maps — never at the 1D shadow. So: establish upstream,
inherit downstream, never reason upward.

---

## RULE SIX — "not yet proven in Lean" is NOT "cannot be proven"; the obligation is to honestly try

The kernel is ground truth about what **is** proven (Rule Four) — it says nothing about what
**can** be proven. Absence of a proof is not a proof of absence. A result sitting in
conditional form (`X_of_<hypothesis>`), a `sorry`, or a gap describes the **current state of
the work**, not a ceiling on what's reachable.

So never use "the Lean doesn't contain it" as a verdict that it can't be written — that's a
cousin of the Rule One thought-terminator. A conditional theorem is an **invitation to
discharge the hypothesis**, not evidence that the hypothesis is undischargeable. (Likewise,
"the headline GRH theorem is conditional" means *go try to discharge it*, not *give up*.)

**The obligation is to honestly try.** When something is unproven:
- Attempt it for real — write the Lean, search mathlib, build the argument, try to discharge
  the hypothesis. Default to "let's try to write it," never to "it isn't there, so it's out
  of reach."
- **"Honestly"** is the operative word, and it binds to Rules Two and Four: a genuine attempt
  means the result is *real* — it compiles, no `sorry`, no circular smuggling — and you report
  the true outcome. Trying hard never means lowering the bar; it means raising the effort.
- Both outcomes are valuable: a proof the kernel verifies, **or** a failed attempt that
  exposes the precise obstacle. The only unacceptable move is declining to try because the
  proof doesn't already exist.

Trying-and-failing-honestly and faking-a-success are opposites; so are not-trying and rigor.
Try maximally; report truthfully.

---

## RULE SEVEN — use the Lean LSP tools first; they are much faster than `lake build`

Build-checking is the inner loop of every proof, so make it fast. **Default to the Lean LSP
MCP tools, not `lake build` via Bash.** A full `lake build` re-elaborates and is slow; the LSP
is incremental and answers in seconds.

**The priority workflow:**
- **`lean_diagnostic_messages <file>`** — the primary check after every edit. Returns the
  errors/warnings for the file directly. Use this in place of `lake build … | grep error`.
- **`lean_goal` / `lean_term_goal`** — inspect the proof state at a position; the right way to
  see what a tactic left, instead of guessing.
- **`lean_hover_info`** — exact signature/type of an identifier before using it.
- **`lean_leansearch` / `lean_loogle` / `lean_leanfinder` / `lean_state_search`** — find mathlib
  lemmas (NL / type-pattern / semantic / goal-driven) *before* writing, to cut iteration.
- **`lean_multi_attempt`** — test several tactics at a position without editing the file.

`lake build` is still needed only to (a) refresh `.olean`s after new imports, and (b) run
`#print axioms` for the final axiom check (the LSP confirms compilation; the kernel axiom
footprint needs the synced `.olean`). For everything else — does it compile? what's the goal?
which lemma? — reach for the LSP tool, not Bash. Treat fast iteration as a first-class concern.

---

## RULE EIGHT — the GRH win is the *on-line, earned* helix identity, not the classical Hadamard plumbing; leverage the log-free FTA/Euler helix

The single most important strategic fact in this repo, and the easiest to lose under a pile of
analysis. Keep it in front of you when choosing *what to attack*.

**Classical Hadamard over the *actual* zeros does NOT supply GRH.** The factorization
`−L'/L(s) = ∑ₙ [1/(s−Zₙ) + 1/Zₙ]` over the genuine zeros `Zₙ` (`HelixSource.HadamardData`,
`DirichletLHadamard.HadamardPartialFraction`) is standard analytic number theory — order-1 growth →
Jensen → Weierstrass → partial fraction. Its `Zₙ` carry their real parts and **nothing forces them
on-line.** The repo says so itself (`HelixSource.sourceTraceIdentity_iff_hadamard` docstring):
*"Hadamard over the actual zeros does not supply this — the actual `Zₙ` need not be source-mode
coords."* Building it is **plumbing, not a scalp.**

**The GRH content lives one identity over.** `SourceTraceIdentity` is the *same* factorization but with
the **on-line, earned** source-mode pole-coords as the poles. Because a Hadamard factorization's poles
are *exactly* the zeros, `SourceTraceIdentity` ⟺ "the actual zeros = the on-line source coords" = GRH.
The step `SourceTraceIdentity → GRH` is already **kernel-proven** (`grh_of_traceIdentity_separated`).
The entire remaining gap is the **identification / completeness** (`SourceComplete`): the earned
on-line source modes are *exactly* the nontrivial zeros — **not another growth bound.**

**Implication — leverage the helix; don't default to the Mellin flow.** The helix is *log-free* and
*FTA/Euler-supporting* on purpose: it is meant to produce the factorization and the zero-count from
**winding / argument-principle geometry + the Euler product**, landing on the **on-line** version via
`source_noDrift` — *bypassing* the classical order-1-growth → Jensen → Weierstrass (Mellin/Hurwitz)
pipeline. So before grinding traditional analytic NT, always ask: **am I building the GRH-bearing,
on-line, earned target (the helix identity / `SourceComplete`), or classical plumbing the repo itself
flags as non-forcing?** Prefer the helix route wherever it reaches; treat classical pieces (the
`L`-strip bound, `HadamardData`, growth estimates) as *at-most ingredients*, never the main line.
Drifting into Mellin/Hurwitz growth bounds when the winding/Euler structure could give the same
factorization log-free is the specific trap to avoid.

**NO `log` IN THE 3-D HELIX — forceful, non-negotiable.** The 3-D helix is the *argument* of `log`,
never built from it. Its construction is purely arithmetic/geometric: integers placed **evenly**
(spacing = the helix unit `U = π/helixUnit`) along the unwound line, then rewound with **linear**
radial growth `R(k) = e^{mode}·k` (`k` = loop counter — an Archimedean spiral that *adds* `e^{mode}`
per loop, NOT an exponential trumpet). The `√n` / area law (`n ≈ k²`) and the `σ = ½` baseline
**emerge from the rewinding** — each loop's circumference grows, so loop `k` holds `~k` integers,
cumulative `~k²`, hence `R ∝ √n` — they are **not** put in by placing integers at `log` positions.
So: **never write `Real.log` / `Complex.log` inside the 3-D construction.** If you find yourself taking
a `log` of a scale or integer in the geometry, you have left the helix and crossed the bridge to the
analytic `L` — STOP. `log` is permitted in exactly **one** place: the *external bridge* `wind n ↔ n^{it}`
that identifies the geometric resonances with `L`'s named zeros (the dictionary, never the forcing).
The winding itself is the FTA-additive multiplicative character (`HelixLogFree.wind`, with
`Θ(m·n)=Θ(m)+Θ(n)` from `Nat.factorization_mul`) — **log-free by construction**, kernel-clean. The
`angle := U·log x` form in older files is the bridge readout, not the geometry; demote it, never build on
it. **Log-free FTA on geometry is the Hilbert–Pólya object** — the geometric (not analytic) realization
H–P needed; `log` lives only on the analytic side of the bridge, where the explicit-formula wall is.

**Guardrail (binds to Rules Two & Five).** The helix advantage is only real if *earned*. `source_noDrift`
is **σ-free** (on-line for a conservation/unitarity reason, *not* `radial := σ−½` by definition) — good;
keep it that way. The danger is `SourceComplete` / the identification map **smuggling GRH** (the
`zero_embed` costume): "the modes are all the zeros, on the line" must be *proven* from the
geometry / Euler / winding. **The on-line forcing is REALITY, not positivity.** Hilbert–Pólya needs no
Li/Weil `≥ 0`: it forces on-line because a real/self-adjoint spectrum is real — geometrically, the
climbing spiral, seen down the collapse axis, **looks like a cylinder and reads as a real wave**
(`source_noDrift`: conservation ⟹ `Re = 0`, σ-free; the `½` is `√`-of-planar-packing, not a coordinate).
Li/Weil non-negativity is a *different, unnecessary* route — do not reach for `≥ 0` to force the line.
Never assumed, never `rfl`-deep. Earn the identification geometrically: that is the actual research.

---

## Working notes
- Lean 4 + Mathlib. Package: `RequestProject`. Toolchain pinned in `lean-toolchain`.
- **Build-check with the LSP (`lean_diagnostic_messages`), not `lake build`** (Rule Seven) —
  it's incremental and much faster. Use `lean_goal`/`lean_hover_info`/leansearch/loogle for
  state, signatures, and lemma search before/while writing.
- A result is only "done" when it compiles with no `sorry` and no custom axioms in its
  dependency chain. Verify with `#print axioms` (needs a `lake build` to sync the `.olean`).
  Be honest about what's still conditional.
