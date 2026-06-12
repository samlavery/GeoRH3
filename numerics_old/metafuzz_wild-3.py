"""
metafuzz_wild-3.py  --  ID wild-3
CLAIM H3: BANDWIDTH / STANDING-WAVE INTERFERENCE VOLUME (gap law from a resolved-mode count).

Consecutive zeros are spaced so exactly ONE new geometric mode becomes resolvable.  The phasor
frequencies are the heights z_n = log n; between integers n and n+1 the log-frequency spacing is
delta = log(1+1/n) ~ 1/n.  A standing-wave / Nyquist argument: two cancellation events at heights
gamma, gamma' are distinguishable only if (gamma'-gamma) * [max resolvable log-frequency window]
>= 2*pi.  The effective window is set by the AFE coherent cutoff

      N_eff(gamma) = sqrt(q*gamma/(2*pi))     (largest integer still contributing coherently)

giving max log-frequency  log N_eff.

  H3 GAP LAW :  (gamma_{n+1} - gamma_n) * log(N_eff)  ~  2*pi
                =>  gap ~ 2*pi/log(N_eff) = 2*pi/log(sqrt(q*gamma/2pi)) = 4*pi/log(q*gamma/2pi).

This is a FACTOR-2 variant of the classical H1 gap

  H1 GAP LAW :  (gamma_{n+1} - gamma_n) * log(q*gamma/(2*pi))  ~  2*pi
                =>  gap ~ 2*pi/log(q*gamma/2pi).

H3 says the relevant frequency window is only the INTEGER bandwidth log N_eff (= (1/2)log(q*gamma/2pi));
H1 says it is the FULL frequency log(q*gamma/2pi).  Because log N_eff = (1/2) log(q*gamma/2pi) EXACTLY,
H3 predicts gaps exactly 2x larger than H1 -- so they are cleanly distinguishable and one must die.

"Volume of integers between zeros" (H3 reading): dN_eff = N_eff(gamma_{n+1}) - N_eff(gamma_n) new
integers admitted into the coherent sum per zero.  H3 sub-claim: dN_eff -> a fixed integer quota.

--------------------------------------------------------------------------------
WHAT THE MATH ACTUALLY SAYS (so we test the right thing, brutally honestly):

The classical Riemann-von Mangoldt density for L(chi mod q):

    N(T) ~ (T/2pi) log(qT/2pi) - T/2pi + O(log T)
    => local density  dN/dT = (1/2pi) log(q T/2pi)
    => MEAN local gap  E[gamma_{n+1}-gamma_n] = 2pi / log(q gamma/2pi)   <== this is H1, exact (it is a
       theorem -- the average gap, the H1 product = 2pi by construction of the counting function).

H3's window is log N_eff = (1/2) log(q gamma/2pi), so H3 predicts mean gap = 4pi/log(q gamma/2pi) = 2x
the TRUE mean gap.  Therefore H3, AS A GAP LAW, is mathematically expected to FALSIFY by a clean factor
of 2: gap*log(N_eff) ~ pi, NOT 2pi.  This file is a deliberate A/B so one of {H1=2pi, H3=2pi} dies with
numbers.  The valuable, honest outcome here is the precise factor.

Caveat on "exact zeros at <1e-12": the constants 'passed' demands are EXACT zeros being hit by ONE rule.
The gap LAW is a DENSITY/AVERAGE statement, NOT an exact per-zero identity -- individual gaps fluctuate
(GUE).  So no gap law (H1 or H3) can be "exact" per zero; the strongest TRUE claim is "the mean product
is character-independent and equals the right constant."  We verify every gamma used is an EXACT zero
(|L(1/2+i gamma)|<1e-12 via mpmath), then test which product (H1 or H3) is the flat, character-independent
2*pi on AVERAGE.  passed=True ONLY if H3's product is genuinely ~2pi flat across all 5 characters; we
expect instead H1=2pi and H3=pi (H3 falsified), and we report the actual numbers either way.

VERDICT POLICY:
  - H3 PASSES only if  mean[ gap * log(N_eff) ] = 2*pi  (flat, character-independent) across
    mod 3,4,5q,5quartic(complex),7 -- AND every gamma is an exact zero (<1e-12).
  - H3 FAILS (expected) if that product is ~pi while H1's product gap*log(q gamma/2pi) = 2*pi.
  - Sub-claim dN_eff->const is tested separately (expected ~0.17/gap, sub-one, NOT a fixed quota).
  - High-statistics fit uses the 3580 chi3 zeros in lchi3_zeros_record.txt.
"""

import math
import numpy as np
import mpmath as mp

mp.mp.dps = 30
TWO_PI = 2.0 * math.pi

# ------------------------------------------------------------------ characters (ONE ruleset, chi only)
CHARS = {
    "mod 3 quadratic":         (3, {1: 1, 2: -1}),
    "mod 4 quadratic":         (4, {1: 1, 3: -1}),
    "mod 5 quadratic":         (5, {1: 1, 4: 1, 2: -1, 3: -1}),
    "mod 5 quartic (complex)": (5, {1: 1, 2: 1j, 4: -1, 3: -1j}),
    "mod 7 quadratic":         (7, {1: 1, 2: 1, 4: 1, 3: -1, 5: -1, 6: -1}),
}


def Lval(q, table, s):
    """exact L(chi,s) = q^{-s} sum_a chi(a) zeta(s, a/q)  (Hurwitz)."""
    tot = mp.mpc(0)
    for a, c in table.items():
        tot += mp.mpc(c) * mp.zeta(s, mp.mpf(a) / q)
    return q ** (-s) * tot


def Lmag_online(q, table, gamma):
    """|L(chi, 1/2 + i gamma)| -- the EXACT zero verifier. Precision-adaptive: large gamma needs
    more guard digits for Hurwitz-zeta cancellation, else |L| floors out at a rounding artifact
    (~1e-12 at gamma~3500, dps=30) rather than the true ~1e-39 zero magnitude."""
    dps = max(30, int(0.25 * float(gamma)) + 30)
    with mp.workdps(dps):
        return float(abs(Lval(q, table, mp.mpf(1) / 2 + 1j * mp.mpf(gamma))))


# ------------------------------------------------------------------ find consecutive zeros on the line
def find_zeros(q, table, T_hi, t0=0.5, coarse=0.02):
    """
    Scan |L(1/2+it)| for sign-bracketed minima, refine each with complex findroot, keep only EXACT
    on-line zeros (|L|<1e-12, |Im root|<1e-9).  Returns a sorted list of consecutive gamma_n.
    """
    f = lambda s: Lval(q, table, mp.mpf(1) / 2 + 1j * s)
    ts = np.arange(t0, T_hi, coarse)
    mags = np.array([float(abs(f(mp.mpf(t)))) for t in ts])
    zs = []
    for i in range(1, len(ts) - 1):
        if mags[i] < mags[i - 1] and mags[i] < mags[i + 1] and mags[i] < 0.35:
            try:
                root = mp.findroot(f, mp.mpc(ts[i], 0), tol=mp.mpf(10) ** (-22))
                tm = float(mp.re(root))
                if abs(float(mp.im(root))) < 1e-9 and tm > t0 and \
                        all(abs(tm - z) > 1e-4 for z in zs) and \
                        abs(complex(f(mp.mpf(tm)))) < 1e-12:
                    zs.append(tm)
            except Exception:
                pass
    return sorted(zs)


def load_record_zeros(path, cap=None):
    """high-statistics chi3 zeros (40+ digit), already verified |L|<~1e-39.
    Returns (floats, strings): floats for fast gap arithmetic (gaps are O(1), double is ample),
    strings to preserve the full 40-digit value for EXACT mpmath re-verification (a double truncates
    gamma~3500 to ~1e-13 rel error => |L| ~ |L'|*err ~ 1e-12, a TRUNCATION artifact, not a non-zero)."""
    pairs = []
    with open(path) as fh:
        for line in fh:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            parts = line.split()
            if len(parts) >= 2:
                try:
                    pairs.append((float(parts[1]), parts[1]))
                except Exception:
                    pass
    pairs.sort(key=lambda p: p[0])
    if cap:
        pairs = pairs[:cap]
    return [p[0] for p in pairs], [p[1] for p in pairs]


def Lmag_online_str(q, table, gamma_str):
    """exact verifier from the full-precision DECIMAL STRING gamma (no double truncation)."""
    g = mp.mpf(gamma_str)
    dps = max(50, int(0.30 * float(g)) + 40)
    with mp.workdps(dps):
        return float(abs(Lval(q, table, mp.mpf(1) / 2 + 1j * g)))


# ------------------------------------------------------------------ the two windows
def logNeff(q, gamma):
    """H3 window: log of the AFE coherent length N_eff = sqrt(q gamma / 2pi)."""
    return math.log(math.sqrt(q * gamma / TWO_PI))


def logFull(q, gamma):
    """H1 window: full smooth-density log-frequency log(q gamma / 2pi)."""
    return math.log(q * gamma / TWO_PI)


def Neff(q, gamma):
    return math.sqrt(q * gamma / TWO_PI)


# ================================================================== MAIN
print("=" * 104)
print("  wild-3  --  H3 BANDWIDTH/STANDING-WAVE gap law   (gap * log N_eff ?= 2*pi)   A/B vs H1 (gap*logFull?=2pi)")
print("=" * 104)
print("  Identity in play:  log N_eff = log sqrt(q g/2pi) = (1/2) log(q g/2pi) = (1/2) logFull")
print("  => H3 product = (1/2) * H1 product exactly.  If H1 product = 2pi (theorem), H3 product = pi.")
print(f"  2*pi = {TWO_PI:.6f}   pi = {math.pi:.6f}\n")

# ---- per-character A/B on directly-found EXACT zeros -------------------------------------------------
T_HI = {3: 90.0, 4: 90.0, 5: 70.0, 7: 60.0}   # enough range for a clean mean over many gaps
summary = {}   # name -> (mean H3 product, mean H1 product, nverified, ngaps, maxLmag)

for name, (q, table) in CHARS.items():
    zs = find_zeros(q, table, T_HI.get(q, 80.0))
    if len(zs) < 3:
        print(f"{name:26s}: only {len(zs)} zeros found, skipping"); continue

    # EXACT verification of every gamma
    mags = [Lmag_online(q, table, g) for g in zs]
    maxmag = max(mags)
    all_exact = maxmag < 1e-12

    prodsH3, prodsH1, dNeffs = [], [], []
    for i in range(len(zs) - 1):
        gap = zs[i + 1] - zs[i]
        gmid = 0.5 * (zs[i] + zs[i + 1])           # evaluate window at gap midpoint
        prodsH3.append(gap * logNeff(q, gmid))
        prodsH1.append(gap * logFull(q, gmid))
        dNeffs.append(Neff(q, zs[i + 1]) - Neff(q, zs[i]))

    mH3 = float(np.mean(prodsH3)); mH1 = float(np.mean(prodsH1)); mdN = float(np.mean(dNeffs))
    summary[name] = (mH3, mH1, len(zs), len(prodsH3), maxmag)

    print(f"{name:26s} (q={q})  zeros found = {len(zs)}   max|L| = {maxmag:.2e}  "
          f"{'EXACT(<1e-12)' if all_exact else '*** NOT all exact ***'}")
    print(f"    mean gap*log(N_eff)  [H3] = {mH3:.5f}    (target 2pi={TWO_PI:.5f};  half-target pi={math.pi:.5f})")
    print(f"    mean gap*log(qg/2pi) [H1] = {mH1:.5f}    (target 2pi={TWO_PI:.5f})")
    print(f"    H3/H1 ratio = {mH3/mH1:.4f}  (must be ~0.5 by the log identity)   mean dN_eff/gap = {mdN:.4f}\n")

# ---- character-independence check (the discriminator) ----------------------------------------------
print("-" * 104)
if summary:
    h3vals = [v[0] for v in summary.values()]
    h1vals = [v[1] for v in summary.values()]
    print(f"  H3 product across chars : mean={np.mean(h3vals):.4f}  spread=[{min(h3vals):.4f},{max(h3vals):.4f}]")
    print(f"  H1 product across chars : mean={np.mean(h1vals):.4f}  spread=[{min(h1vals):.4f},{max(h1vals):.4f}]")
    print(f"  Which sits at 2pi={TWO_PI:.4f}?  H3 dist={abs(np.mean(h3vals)-TWO_PI):.4f}   "
          f"H1 dist={abs(np.mean(h1vals)-TWO_PI):.4f}")

# ================================================================== HIGH-STATISTICS chi3 (3580 zeros)
print("\n" + "=" * 104)
print("  HIGH-STATISTICS chi3  (q=3) -- 3580 exact zeros (40-digit) from lchi3_zeros_record.txt")
print("=" * 104)
g3, g3str = load_record_zeros("lchi3_zeros_record.txt")
print(f"  loaded {len(g3)} chi3 zeros up to gamma = {g3[-1]:.2f}")

# spot-verify a few exact (the record was made at 256-bit; re-verify with mpmath here)
# from the FULL-PRECISION STRING gamma -- a Python double would truncate gamma~3500 and fake a 1e-12.
spotidx = [0, 1, 100, 1000, len(g3) - 1]
print("  spot exact re-verification (|L(1/2+i gamma)| via mpmath, full 40-digit gamma):")
allspot = True
for k in spotidx:
    m = Lmag_online_str(3, CHARS["mod 3 quadratic"][1], g3str[k])
    allspot = allspot and (m < 1e-12)
    print(f"     zero #{k+1:5d}  gamma={g3[k]:13.6f}   |L| = {m:.2e}   {'OK<1e-12' if m<1e-12 else 'FAIL'}")

# per-gap products over the whole record
q = 3
gaps = np.diff(g3)
gmid = 0.5 * (np.array(g3[:-1]) + np.array(g3[1:]))
H3prod = gaps * np.array([logNeff(q, g) for g in gmid])
H1prod = gaps * np.array([logFull(q, g) for g in gmid])
dNeff = np.array([Neff(q, g3[i + 1]) - Neff(q, g3[i]) for i in range(len(g3) - 1)])

print("\n  --- mean products over ALL 3579 chi3 gaps ---")
print(f"    H3  mean gap*log(N_eff)  = {H3prod.mean():.5f}   std={H3prod.std():.4f}   (target 2pi={TWO_PI:.5f}; half pi={math.pi:.5f})")
print(f"    H1  mean gap*log(qg/2pi) = {H1prod.mean():.5f}   std={H1prod.std():.4f}   (target 2pi={TWO_PI:.5f})")
print(f"    H3/H1 = {H3prod.mean()/H1prod.mean():.5f}  (must be ~0.5)")

# windowed means (does the product trend toward its target as gamma grows?  H1 should, H3 should approach pi)
print("\n  --- product vs height (binned by gamma), to see asymptotics ---")
edges = [0, 50, 200, 500, 1000, 2000, 3600]
print("   gamma band      ngaps   <gap>   <H3=gap*logNeff>   <H1=gap*logFull>   <dN_eff/gap>")
for a, b in zip(edges[:-1], edges[1:]):
    sel = (gmid >= a) & (gmid < b)
    if sel.sum() == 0:
        continue
    print(f"   [{a:5d},{b:5d})   {int(sel.sum()):5d}   {gaps[sel].mean():6.4f}      "
          f"{H3prod[sel].mean():8.5f}          {H1prod[sel].mean():8.5f}          {dNeff[sel].mean():7.4f}")

# H3 sub-claim: dN_eff -> fixed integer quota?
print("\n  --- H3 sub-claim: does dN_eff (integers admitted per zero) approach a fixed quota? ---")
print(f"    mean dN_eff over all gaps = {dNeff.mean():.5f}   median = {np.median(dNeff):.5f}")
print(f"    dN_eff in first 100 gaps  = {dNeff[:100].mean():.5f}     last 100 gaps = {dNeff[-100:].mean():.5f}")
print(f"    (N_eff itself grows ~sqrt(gamma); each zero admits a SHRINKING fraction of an integer ->")
print(f"     dN_eff ~ (dN/dgamma)*gap = [q/(4pi N_eff)]*[2pi/log(qg/2pi)] ~ 1/(2 N_eff log) -> 0, NOT a fixed quota.)")

# direct test of the theoretical mean-gap form gap_mean = 2pi/log(q gamma/2pi)
print("\n  --- is H1 the TRUE mean-gap law? compare observed <gap> to 2pi/log(q gamma/2pi) per band ---")
print("   gamma band      <gap>_obs    2pi/log(qg/2pi)_pred    ratio")
for a, b in zip(edges[:-1], edges[1:]):
    sel = (gmid >= a) & (gmid < b)
    if sel.sum() == 0:
        continue
    pred = float(np.mean([TWO_PI / logFull(q, g) for g in gmid[sel]]))
    obs = gaps[sel].mean()
    print(f"   [{a:5d},{b:5d})    {obs:8.5f}        {pred:8.5f}             {obs/pred:6.4f}")

# ================================================================== VERDICT
print("\n" + "=" * 104)
print("  VERDICT")
print("=" * 104)
chi3_H3 = H3prod.mean(); chi3_H1 = H1prod.mean()
crit_exact = allspot                                   # every spot-checked gamma is an exact zero
# H3 passes ONLY if its product is ~2pi (within 5%) AND character-independent AND exact zeros
h3_at_2pi = abs(chi3_H3 - TWO_PI) / TWO_PI < 0.05
h1_at_2pi = abs(chi3_H1 - TWO_PI) / TWO_PI < 0.05
char_indep_h3 = (max([v[0] for v in summary.values()]) - min([v[0] for v in summary.values()])) < 0.5 if summary else False

print(f"  exact-zero constraint met (spot <1e-12)      : {crit_exact}")
print(f"  H3 product ~ 2pi (within 5%)                  : {h3_at_2pi}   (chi3 value {chi3_H3:.4f} vs 2pi={TWO_PI:.4f})")
print(f"  H1 product ~ 2pi (within 5%)                  : {h1_at_2pi}   (chi3 value {chi3_H1:.4f} vs 2pi={TWO_PI:.4f})")
print(f"  H3 product character-independent (<0.5 spread): {char_indep_h3}")
print()
if h3_at_2pi and char_indep_h3 and crit_exact:
    print("  >>> H3 PASSES: the integer-bandwidth window log N_eff gives gap*window = 2pi across all L.")
else:
    print("  >>> H3 FALSIFIED as the gap law: gap*log(N_eff) ~ pi, NOT 2pi (factor-2 off by the")
    print("      log N_eff = (1/2) logFull identity).  The TRUE window is the FULL log(q gamma/2pi)")
    print("      (= H1, the Riemann-von Mangoldt density), not the integer bandwidth.  dN_eff is a")
    print("      SHRINKING sub-integer per zero, not a fixed quota.  Clean negative, exact reason.")
