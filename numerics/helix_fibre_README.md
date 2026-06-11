# Helix fibre-cancellation numerics (the `iy` picture)

Numerical confirmation of the imaginary-axis (`iy`) mechanism formalized in Lean. Everything here
is on the critical line `sigma = 1/2` and **never touches the real part `x`** — it confirms *where*
and *how* the zeros arise (winding cancellation of character fibres), not *why they sit on the line*.

## The claim being tested

The log-free FTA winding produces the vertical phase `wind(t) n = n^{it}`, the helix point is
`helixPt n = sqrt(n) * wind(t) n = n^{1/2+it}`, and

```
L(s, chi) = sum_n chi(n) / helixPt(n)
          = sum_n chi(n) * (1/n^sigma) * (1/wind(t) n)      [the phasor sum]
```

Each integer `n` is a phasor: magnitude `1/sqrt(n)` (radial, the `sqrt(n)` helix radius), phase
`e^{-i t log n}` (winding, frequency `log n`), sign `chi(n)`. A **zero is where these phasors
cancel** — for `chi3`, where the `n=1 (mod 3)` fibre balances the `n=2 (mod 3)` fibre.

## Lean counterparts

- `RequestProject/HelixImaginaryAxis.lean` — `wind_eq_cpow`, `helixPt_eq_cpow`,
  `wind_eq_helixPt_div_sqrt` (projection), `lfunction_eq_helixSum`, `lfunction_eq_phasorSum`.
- `RequestProject/HelixFibreCancellation.lean` — `lfunction_chi3_eq_fibreHelix_diff`
  (`L = fibre+ - fibre-`), `chi3_helix_cancellation` (`L = 0 <-> fibre+ = fibre-`).

## Scripts (`python3 <name>`, needs `mpmath`)

| script | what it checks | result |
|---|---|---|
| `helix_fibre_chi3.py` | `chi3` in detail: 8 events, `fibre+ = fibre-` to ~1e-11, raw phasors -> 0 at `N^{-1/2}`, control | passes |
| `helix_fibre_characters.py` | the zoo: `chi` mod 3,4,5(**complex**),7,8 — 20 events each (100 total) | passes; complex char identical to `chi3` |
| `helix_fibre_trivial.py` | the principal/trivial character — the special case | passes (see below) |

## The trivial character (special treatment)

The trivial character `chi(n)=1` has **one fibre, no `+/-` partner**, so `sum_a chi(a) != 0`: its
running mean (DC) does not vanish. So the raw winding sum does **not** cancel — it **diverges**
`~ N^{1/2}`, tracking the `s=1` pole. Subtracting the smooth part `N^{1-s}/(1-s) = int_1^N x^{-s} dx`
(the leading Euler–Maclaurin term) leaves the fluctuation `= zeta`, which cancels at the Riemann
zeros. This is the same DC that fibre cancellation (`sum_a chi(a) = 0`) removes for free for every
non-principal character — which is why `HelixFibreCancellation.lean` is stated for non-principal
`chi3`.
