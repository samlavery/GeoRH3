#!/usr/bin/env python3
"""Canonical reference zeros for the first six primitive Dirichlet L-functions.

Computes the first 100 nontrivial zeros (ordinates t > 0 on the critical line
Re(s) = 1/2, in increasing order) of:

    L1  Riemann zeta                  (q = 1, trivial character)
    L2  L(s, chi_3)   chi_3 = unique primitive character mod 3 (odd quadratic)
    L3  L(s, chi_4)   chi_4 = unique primitive character mod 4 (odd quadratic)
    L4  L(s, chi_5)   even quadratic (Legendre) character mod 5
    L5  L(s, chi_5')  order-4 character mod 5 with chi(2) = i (odd, complex)
    L6  L(s, chi_7)   odd quadratic (Legendre) character mod 7

Moduli 2 and 6 have no primitive non-principal characters (every character mod
2 or mod 6 is induced from modulus 1 or 3, so its L-function is that of zeta or
chi_3 up to finitely many Euler factors).  Hence the list above is exactly the
first six primitive L-functions ordered by conductor.

Method
------
zeta:  mpmath's mp.zetazero(n) (Riemann-Siegel based, library-certified
       ordering of the zeros), n = 1..100.

Dirichlet L:  Hurwitz-zeta evaluation

    L(s, chi) = q^(-s) * sum_{a=1}^{q-1} chi(a) * zeta(s, a/q),

combined into the Hardy Z-function (real on the real t-axis):

    Z(t)     = eps^(-1/2) * omega(t) * L(1/2 + i t, chi),
    omega(t) = (q/pi)^(i t/2) * G/|G|,  G = Gamma(((1/2 + i t) + a)/2),
    eps      = tau(chi) / (i^a * sqrt(q)),
    tau(chi) = sum_{a mod q} chi(a) * e^(2 pi i a / q),

with parity a = 0 for even chi (chi(-1) = 1) and a = 1 for odd chi
(chi(-1) = -1).  The functional equation makes eps^(-1/2) * Lambda(1/2 + it)
real, so Z is real and its sign changes are exactly the on-line zeros.  The
branch of eps^(-1/2) is fixed once, verified by a reality test at several
points (relative |Im| residual below REALITY_TOL), before any scanning.

Zeros are located by a sign-change scan (step SCAN_STEP from T_START), refined
by bracketed Anderson-Bjorck root finding, and each root is certified by a
sign change across [root - 5e-14, root + 5e-14], guaranteeing 12+ correct
decimals (bisection fallback if the fast path fails).

Completeness checks (missed close pairs are the failure mode):
  1. The bottom segment [T_START, first zero] is unconditionally re-swept at
     step 0.01.
  2. Smooth zero-count: for every k, |k - N(t_k)| with
     N(T) = (T/(2 pi)) * log(q T / (2 pi e)) must stay <= 2; a violation
     triggers a full-range rescan at step 0.01.
  3. Gap statistics: no gap between consecutive zeros may exceed 4x the local
     mean gap 2 pi / log(q t / (2 pi)); a violation triggers a rescan of that
     gap at step 0.005.

Validation: the first ordinates of L1/L2/L3 are asserted against the known
values 14.134725 / 8.039737 / 6.020949 (tolerance 1e-4).

Usage:  python3 compute_zeros.py
Writes the six files into the zeros/ directory next to this file and prints a
summary report.  Fully deterministic: fixed precision, fixed grids, fixed test
points, no randomness.  No global mutable state beyond the mpmath precision
context (handled via mp.workdps).
"""

from __future__ import annotations

import os
import time
from dataclasses import dataclass
from typing import Callable, Dict, List, Optional, Tuple

from mpmath import mp

# ---------------------------------------------------------------------------
# Fixed configuration (deterministic; stamped into the output files)
# ---------------------------------------------------------------------------

DATE = "2026-06-11"            # generation date written into the file headers
ZERO_COUNT = 100               # zeros per L-function
SCAN_DPS = 30                  # mp.dps during the sign-change scan
REFINE_DPS = 30                # mp.dps during refinement / certification
T_START = "0.1"                # scan starts here
SCAN_STEP = "0.05"             # primary grid step
BOTTOM_STEP = "0.01"           # unconditional fine sweep of [T_START, t_1]
COUNT_RESCAN_STEP = "0.01"     # rescan step when the smooth-count check trips
GAP_RESCAN_STEP = "0.005"      # rescan step for a suspicious gap
COUNT_TOL = 2.0                # allowed |found count - smooth N(T)|
GAP_RATIO_TOL = 4.0            # allowed gap / local mean gap
CERTIFY_HALFWIDTH = "5e-14"    # sign change across +- this certifies the root
DEDUP_TOL = "1e-9"             # two roots closer than this are the same zero
REALITY_TOL = 1e-15            # max allowed relative |Im Z| at test points
REALITY_TEST_POINTS = ("0.7", "1.9", "5.3", "9.6", "14.2", "23.7", "41.5", "77.3")

# Known first ordinates used as hard validation (mission spec).
KNOWN_FIRST_ORDINATES = {
    "L1_zeta_q1": "14.134725",
    "L2_chi3_q3": "8.039737",
    "L3_chi4_q4": "6.020949",
}


# ---------------------------------------------------------------------------
# Character specification
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class CharSpec:
    """A primitive Dirichlet character given by its value table.

    values[a] is chi(a) for a = 0, 1, ..., q-1 (0 whenever gcd(a, q) > 1).
    parity is the 'a' in the Gamma factor: 0 for even chi, 1 for odd chi.
    """
    label: str
    q: int
    values: Tuple[complex, ...]
    parity: int
    description: str

    def chi(self, n: int) -> complex:
        return self.values[n % self.q]


SPECS: Tuple[CharSpec, ...] = (
    CharSpec(
        label="L2_chi3_q3", q=3, values=(0, 1, -1), parity=1,
        description="Dirichlet L of chi_3, the unique primitive character mod 3 (odd quadratic)"),
    CharSpec(
        label="L3_chi4_q4", q=4, values=(0, 1, 0, -1), parity=1,
        description="Dirichlet L of chi_4, the unique primitive character mod 4 (odd quadratic)"),
    CharSpec(
        label="L4_chi5quad_q5", q=5, values=(0, 1, -1, -1, 1), parity=0,
        description="Dirichlet L of the even quadratic character mod 5 (Legendre symbol mod 5)"),
    CharSpec(
        label="L5_chi5c4_q5", q=5, values=(0, 1, 1j, -1j, -1), parity=1,
        description="Dirichlet L of the order-4 character mod 5 with chi(2) = i (odd, complex)"),
    CharSpec(
        label="L6_chi7quad_q7", q=7, values=(0, 1, 1, -1, 1, -1, -1), parity=1,
        description="Dirichlet L of the odd quadratic character mod 7 (Legendre symbol mod 7)"),
)


# ---------------------------------------------------------------------------
# Core arithmetic: Gauss sum, root number, L via Hurwitz zeta, Hardy Z
# ---------------------------------------------------------------------------

def gauss_sum(spec: CharSpec) -> mp.mpc:
    """tau(chi) = sum_{a mod q} chi(a) e^(2 pi i a / q).  |tau| = sqrt(q)."""
    tau = mp.mpc(0)
    for a in range(1, spec.q):
        c = spec.values[a]
        if c:
            tau += mp.mpc(c) * mp.expjpi(mp.mpf(2 * a) / spec.q)
    return tau


def root_number(spec: CharSpec) -> mp.mpc:
    """eps(chi) = tau(chi) / (i^a sqrt(q)); |eps| = 1 for primitive chi."""
    return gauss_sum(spec) / (mp.mpc(0, 1) ** spec.parity * mp.sqrt(spec.q))


def L_chi(spec: CharSpec, s) -> mp.mpc:
    """L(s, chi) = q^(-s) sum_{a=1}^{q-1} chi(a) zeta(s, a/q) (Hurwitz zeta)."""
    acc = mp.mpc(0)
    for a in range(1, spec.q):
        c = spec.values[a]
        if c:
            acc += mp.mpc(c) * mp.zeta(s, mp.mpf(a) / spec.q)
    return mp.power(spec.q, -s) * acc


def hardy_Z_complex(spec: CharSpec, t, branch: int = 1) -> mp.mpc:
    """eps^(-1/2) omega(t) L(1/2 + it, chi) as a complex number.

    Mathematically real for real t; the imaginary part is the numerical
    residual used by the reality check.  branch = +-1 selects the square-root
    branch of eps^(-1/2).
    """
    t = mp.mpf(t)
    s = mp.mpf("0.5") + mp.mpc(0, 1) * t
    G = mp.gamma((s + spec.parity) / 2)
    omega = mp.power(mp.mpf(spec.q) / mp.pi, mp.mpc(0, 1) * t / 2) * G / abs(G)
    return branch * omega * L_chi(spec, s) / mp.sqrt(root_number(spec))


def hardy_Z(spec: CharSpec, t, branch: int = 1) -> mp.mpf:
    """The real Hardy Z-function; its sign changes are the on-line zeros."""
    return hardy_Z_complex(spec, t, branch).real


# ---------------------------------------------------------------------------
# Reality check / branch selection
# ---------------------------------------------------------------------------

def reality_residual(spec: CharSpec, branch: int = 1,
                     points: Tuple[str, ...] = REALITY_TEST_POINTS) -> mp.mpf:
    """Max over the test points of |Im W| / |W| with W = hardy_Z_complex."""
    worst = mp.mpf(0)
    for p in points:
        w = hardy_Z_complex(spec, mp.mpf(p), branch)
        mag = abs(w)
        if mag < mp.mpf("1e-20"):
            continue  # too close to a zero for a meaningful relative residual
        worst = max(worst, abs(w.imag) / mag)
    return worst


def choose_branch(spec: CharSpec) -> Tuple[int, mp.mpf]:
    """Pick the eps^(-1/2) branch that makes Z real; fail loudly otherwise."""
    res_plus = reality_residual(spec, 1)
    if res_plus < mp.mpf(repr(REALITY_TOL)):
        return 1, res_plus
    res_minus = reality_residual(spec, -1)
    if res_minus < mp.mpf(repr(REALITY_TOL)):
        return -1, res_minus
    raise RuntimeError(
        f"{spec.label}: Hardy Z fails the reality test on both eps^(-1/2) "
        f"branches (relative Im residuals: +branch {mp.nstr(res_plus, 5)}, "
        f"-branch {mp.nstr(res_minus, 5)}).  Character table, parity, or root "
        "number must be wrong; refusing to scan.")


# ---------------------------------------------------------------------------
# Smooth zero count and local gap statistics
# ---------------------------------------------------------------------------

def smooth_count(q: int, T) -> mp.mpf:
    """Smooth estimate N(T) ~ (T/(2 pi)) log(q T/(2 pi e)) of the one-sided
    zero count (0 < t <= T).  Accurate up to an O(1) constant + S(T)."""
    T = mp.mpf(T)
    return (T / (2 * mp.pi)) * mp.log(q * T / (2 * mp.pi * mp.e))


def local_mean_gap(q: int, t) -> Optional[mp.mpf]:
    """Local mean zero spacing 2 pi / log(q t/(2 pi)) (d/dT of smooth_count).

    Returns None where the density formula is not yet meaningful
    (q t/(2 pi) <= 1.35); the smooth-count check covers that bottom region.
    """
    x = q * mp.mpf(t) / (2 * mp.pi)
    if x <= mp.mpf("1.35"):
        return None
    return 2 * mp.pi / mp.log(x)


def _completeness(q: int, zeros: List[mp.mpf]) -> Tuple[float, List[int], float]:
    """(max |k - N(t_k)|, indices of gaps > GAP_RATIO_TOL, max gap ratio)."""
    max_dev = max(abs(float((i + 1) - smooth_count(q, z)))
                  for i, z in enumerate(zeros))
    gap_bad: List[int] = []
    max_ratio = 0.0
    for i in range(len(zeros) - 1):
        mg = local_mean_gap(q, (zeros[i] + zeros[i + 1]) / 2)
        if mg is None:
            continue
        ratio = float((zeros[i + 1] - zeros[i]) / mg)
        if ratio > max_ratio:
            max_ratio = ratio
        if ratio > GAP_RATIO_TOL:
            gap_bad.append(i)
    return max_dev, gap_bad, max_ratio


# ---------------------------------------------------------------------------
# Root refinement (certified to 12+ decimals) and scanning
# ---------------------------------------------------------------------------

def _sign_change(f1, f2) -> bool:
    return mp.sign(f1) * mp.sign(f2) < 0


def _bisect(spec: CharSpec, branch: int, lo, hi, f_lo, f_hi, width) -> mp.mpf:
    """Plain bisection of a sign-change bracket down to the given width."""
    while hi - lo > width:
        mid = (lo + hi) / 2
        fm = hardy_Z(spec, mid, branch)
        if fm == 0:
            return mid
        if _sign_change(f_lo, fm):
            hi, f_hi = mid, fm
        else:
            lo, f_lo = mid, fm
    return (lo + hi) / 2


def refine_zero(spec: CharSpec, branch: int, lo, hi, f_lo, f_hi) -> mp.mpf:
    """Refine a sign-change bracket [lo, hi] to a certified root.

    Fast path: bracketed Anderson-Bjorck via mp.findroot, then certification
    by a sign change across [r - h, r + h] with h = CERTIFY_HALFWIDTH (5e-14),
    which pins the zero to within h, i.e. 12+ correct decimals.  Fallback:
    bisection of the original bracket to width 1e-14.
    """
    with mp.workdps(REFINE_DPS):
        lo, hi = mp.mpf(lo), mp.mpf(hi)
        h = mp.mpf(CERTIFY_HALFWIDTH)
        root = None
        try:
            r = mp.findroot(lambda x: hardy_Z(spec, x, branch), (lo, hi),
                            solver="anderson", tol=mp.mpf("1e-26"),
                            maxsteps=200)
            r = mp.mpf(r.real) if isinstance(r, mp.mpc) else mp.mpf(r)
            if lo <= r <= hi and _sign_change(hardy_Z(spec, r - h, branch),
                                              hardy_Z(spec, r + h, branch)):
                root = r
        except (ValueError, ArithmeticError):
            root = None
        if root is None:
            root = _bisect(spec, branch, lo, hi, f_lo, f_hi, mp.mpf("1e-14"))
        return root


def rescan_range(spec: CharSpec, branch: int, lo, hi, step,
                 known: List[mp.mpf]) -> List[mp.mpf]:
    """Fine scan of [lo, hi]; return refined zeros not already in `known`.

    Brackets that contain a known zero are skipped (their sign change is
    accounted for); refined roots within DEDUP_TOL of a known root are
    discarded as duplicates.
    """
    known_sorted = sorted(mp.mpf(z) for z in known)
    dedup = mp.mpf(DEDUP_TOL)
    out: List[mp.mpf] = []
    lo, hi, step = mp.mpf(lo), mp.mpf(hi), mp.mpf(step)
    if hi <= lo:
        return out
    n = int(mp.ceil((hi - lo) / step))
    t_prev = lo
    f_prev = hardy_Z(spec, t_prev, branch)
    for k in range(1, n + 1):
        t_cur = lo + k * step
        if t_cur > hi:
            t_cur = hi
        f_cur = hardy_Z(spec, t_cur, branch)
        if (_sign_change(f_prev, f_cur)
                and not any(t_prev <= z <= t_cur for z in known_sorted)):
            r = refine_zero(spec, branch, t_prev, t_cur, f_prev, f_cur)
            if (all(abs(r - z) > dedup for z in known_sorted)
                    and all(abs(r - z) > dedup for z in out)):
                out.append(r)
        t_prev, f_prev = t_cur, f_cur
    return out


def find_zeros(spec: CharSpec, count: int = ZERO_COUNT,
               progress: Optional[Callable[[str], None]] = None
               ) -> Tuple[List[mp.mpf], Dict]:
    """First `count` ordinates t > 0 of the on-line zeros of L(s, chi).

    Runs the branch-verified Hardy-Z sign scan, refines and certifies every
    root, then applies the completeness protocol (bottom sweep, smooth-count
    check with 0.01 rescan, gap check with 0.005 rescan).

    Returns (zeros, diagnostics).  diagnostics keys: branch, residual, tau,
    eps, rescans (list of str), flags (list of str; empty = all checks pass),
    max_dev, max_gap_ratio.
    """
    say = progress or (lambda _msg: None)
    with mp.workdps(SCAN_DPS):
        # -- pipeline sanity: primitivity (|tau| = sqrt q) and reality of Z.
        tau = gauss_sum(spec)
        if abs(abs(tau) - mp.sqrt(spec.q)) > mp.mpf("1e-20"):
            raise RuntimeError(
                f"{spec.label}: |tau(chi)| != sqrt(q) "
                f"(got {mp.nstr(abs(tau), 20)}); character table is not a "
                "primitive character.  Refusing to scan.")
        eps = root_number(spec)
        branch, residual = choose_branch(spec)
        say(f"{spec.label}: branch {branch:+d}, reality residual "
            f"{mp.nstr(residual, 3)}")

        # -- primary scan upward until `count` sign changes are refined.
        step = mp.mpf(SCAN_STEP)
        t0 = mp.mpf(T_START)
        zeros: List[mp.mpf] = []
        k = 0
        t_prev, f_prev = t0, hardy_Z(spec, t0, branch)
        while len(zeros) < count:
            k += 1
            t_cur = t0 + k * step
            f_cur = hardy_Z(spec, t_cur, branch)
            if _sign_change(f_prev, f_cur):
                zeros.append(refine_zero(spec, branch, t_prev, t_cur,
                                         f_prev, f_cur))
                if len(zeros) % 25 == 0:
                    say(f"{spec.label}: {len(zeros)} zeros, "
                        f"t ~ {mp.nstr(zeros[-1], 10)}")
            t_prev, f_prev = t_cur, f_cur

        # -- unconditional fine sweep of the bottom segment [t0, t_1].
        rescans: List[str] = []
        new = rescan_range(spec, branch, t0, zeros[0], mp.mpf(BOTTOM_STEP),
                           zeros)
        rescans.append(
            f"bottom [{mp.nstr(t0, 6)}, {mp.nstr(zeros[0], 12)}] "
            f"@ {BOTTOM_STEP}: {len(new)} new")
        zeros = sorted(zeros + new)

        # -- completeness loop: check, rescan on failure, re-check.
        for _attempt in range(3):
            zeros = sorted(zeros)[:count]
            max_dev, gap_bad, max_ratio = _completeness(spec.q, zeros)
            if max_dev <= COUNT_TOL and not gap_bad:
                break
            new = []
            if max_dev > COUNT_TOL:
                got = rescan_range(spec, branch, t0, zeros[-1],
                                   mp.mpf(COUNT_RESCAN_STEP), zeros)
                rescans.append(
                    f"count-check rescan [{T_START}, "
                    f"{mp.nstr(zeros[-1], 12)}] @ {COUNT_RESCAN_STEP}: "
                    f"{len(got)} new (max dev was {max_dev:.2f})")
                new += got
            for i in gap_bad:
                got = rescan_range(spec, branch, zeros[i], zeros[i + 1],
                                   mp.mpf(GAP_RESCAN_STEP), zeros)
                rescans.append(
                    f"gap rescan [{mp.nstr(zeros[i], 12)}, "
                    f"{mp.nstr(zeros[i + 1], 12)}] @ {GAP_RESCAN_STEP}: "
                    f"{len(got)} new")
                new += got
            if not new:
                break  # nothing found: deviation is a smooth-term offset
            zeros = sorted(zeros + new)

        zeros = sorted(zeros)[:count]
        max_dev, gap_bad, max_ratio = _completeness(spec.q, zeros)
        flags: List[str] = []
        if max_dev > COUNT_TOL:
            flags.append(
                f"smooth-count deviation {max_dev:.2f} exceeds {COUNT_TOL} "
                "and the 0.01 rescan found nothing (interpreting as an O(1) "
                "offset of the smooth formula, not a missed zero)")
        for i in gap_bad:
            flags.append(
                f"gap [{mp.nstr(zeros[i], 14)}, {mp.nstr(zeros[i + 1], 14)}] "
                f"exceeds {GAP_RATIO_TOL}x local mean gap and the 0.005 "
                "rescan found nothing")

    diag = {
        "branch": branch, "residual": residual, "tau": tau, "eps": eps,
        "rescans": rescans, "flags": flags,
        "max_dev": max_dev, "max_gap_ratio": max_ratio,
    }
    return zeros, diag


def compute_L1(count: int = ZERO_COUNT,
               progress: Optional[Callable[[str], None]] = None
               ) -> Tuple[List[mp.mpf], Dict]:
    """First `count` ordinates of Riemann zeta zeros via mp.zetazero(n).

    The same smooth-count and gap statistics are computed as a sanity report
    (no rescan machinery: zetazero's ordering is library-certified).
    """
    say = progress or (lambda _msg: None)
    with mp.workdps(REFINE_DPS):
        zeros: List[mp.mpf] = []
        for n in range(1, count + 1):
            zeros.append(mp.im(mp.zetazero(n)))
            if n % 25 == 0:
                say(f"L1_zeta_q1: {n} zeros, t ~ {mp.nstr(zeros[-1], 10)}")
        max_dev, gap_bad, max_ratio = _completeness(1, zeros)
    if max_dev > COUNT_TOL or gap_bad:
        raise RuntimeError(
            f"L1_zeta_q1: completeness statistics failed on zetazero output "
            f"(max_dev {max_dev:.2f}, bad gaps {gap_bad}); the smooth-count "
            "tolerances are mis-set.  Stopping.")
    diag = {
        "branch": None, "residual": None, "tau": None, "eps": mp.mpc(1),
        "rescans": ["none (zetazero used directly)"], "flags": [],
        "max_dev": max_dev, "max_gap_ratio": max_ratio,
    }
    return zeros, diag


# ---------------------------------------------------------------------------
# Validation, formatting, file output
# ---------------------------------------------------------------------------

def validate_first_zero(label: str, zeros: List[mp.mpf]) -> None:
    """Assert the first ordinate against the known reference (L1/L2/L3)."""
    ref = KNOWN_FIRST_ORDINATES.get(label)
    if ref is None:
        return
    if abs(zeros[0] - mp.mpf(ref)) >= mp.mpf("1e-4"):
        raise RuntimeError(
            f"{label}: first ordinate {mp.nstr(zeros[0], 16)} does not match "
            f"the known reference {ref} within 1e-4.  Stopping.")


def fmt12(t) -> str:
    """Format a positive mpf with exactly 12 decimal places (no float pass)."""
    with mp.workdps(REFINE_DPS + 10):
        scaled = int(mp.nint(mp.mpf(t) * mp.mpf(10) ** 12))
    return f"{scaled // 10**12}.{scaled % 10**12:012d}"


def _cval(c) -> str:
    """Pretty-print a character value (0, +-1, +-i)."""
    if c == 0:
        return "0"
    if c == 1:
        return "1"
    if c == -1:
        return "-1"
    if c == 1j:
        return "i"
    if c == -1j:
        return "-i"
    return str(c)


def _char_table(spec: CharSpec) -> str:
    return ", ".join(f"chi({a})={_cval(spec.values[a])}"
                     for a in range(spec.q))


def dirichlet_header(spec: CharSpec, zeros: List[mp.mpf],
                     diag: Dict) -> List[str]:
    """Header comment lines (without the leading '# ') for a Dirichlet file."""
    branch_desc = ("principal" if diag["branch"] == 1
                   else "negated principal")
    lines = [
        f"{spec.label}: first {len(zeros)} nontrivial zeros "
        "(ordinates t > 0 on Re s = 1/2, increasing)",
        f"function: {spec.description}",
        f"character table (q = {spec.q}, conductor {spec.q}, primitive): "
        f"{_char_table(spec)}",
        f"parity: a = {spec.parity} "
        f"({'even, chi(-1)=+1' if spec.parity == 0 else 'odd, chi(-1)=-1'})",
        f"gauss sum tau(chi) = {mp.nstr(diag['tau'], 25)}  "
        "(|tau| = sqrt(q) verified)",
        f"root number eps = tau/(i^a sqrt(q)) = {mp.nstr(diag['eps'], 25)}",
        f"Z-branch: eps^(-1/2) = {branch_desc} square root "
        f"(branch {diag['branch']:+d}); max relative reality residual "
        f"|Im W|/|W| = {mp.nstr(diag['residual'], 3)} (tol {REALITY_TOL})",
        "method: L(s,chi) = q^(-s) * sum_(a=1..q-1) chi(a)*zeta(s, a/q) "
        "(Hurwitz zeta, mpmath);",
        "method: Hardy Z(t) = eps^(-1/2) * (q/pi)^(it/2) * "
        "(Gamma((s+a)/2)/|Gamma((s+a)/2)|) * L(1/2+it, chi), s = 1/2+it;",
        f"method: sign-change scan from t = {T_START} step {SCAN_STEP}; "
        f"bottom segment re-swept at step {BOTTOM_STEP}; roots refined by "
        "bracketed Anderson-Bjorck (mp.findroot) and certified by a sign "
        f"change across +-{CERTIFY_HALFWIDTH} (12+ correct decimals)",
        f"precision: mp.dps = {SCAN_DPS} (scan), {REFINE_DPS} (refine)",
        f"completeness: smooth-count max |k - N(t_k)| = "
        f"{diag['max_dev']:.3f} (tol {COUNT_TOL}); max gap/local-mean-gap = "
        f"{diag['max_gap_ratio']:.3f} (tol {GAP_RATIO_TOL})",
        f"rescans: {'; '.join(diag['rescans'])}",
        f"date: {DATE}",
        f"count: {len(zeros)}",
        "columns: index ordinate (12 decimal places)",
    ]
    if spec.label == "L5_chi5c4_q5":
        lines.insert(
            3, "note: complex character, so the zero set is NOT symmetric "
               "under t -> -t; these are the first 100 zeros with t > 0 "
               "(the conjugate character carries the mirrored zeros)")
    if diag["flags"]:
        lines.append("FLAGS: " + "; ".join(diag["flags"]))
    return lines


def zeta_header(zeros: List[mp.mpf], diag: Dict) -> List[str]:
    """Header comment lines (without the leading '# ') for the zeta file."""
    return [
        f"L1_zeta_q1: first {len(zeros)} nontrivial zeros "
        "(ordinates t > 0 on Re s = 1/2, increasing)",
        "function: Riemann zeta (the Dirichlet L-function of the trivial "
        "character mod q = 1)",
        "character table (q = 1, conductor 1): chi(n) = 1 for all n "
        "(trivial character)",
        "parity: a = 0 (even)",
        "root number eps = 1 (exact)",
        "method: mpmath mp.zetazero(n).im for n = 1..100 (Riemann-Siegel "
        "based; zero ordering certified internally by mpmath)",
        f"precision: mp.dps = {REFINE_DPS}",
        "reality residual: n/a (no Hardy-Z scan; zetazero used directly)",
        f"completeness: smooth-count max |k - N(t_k)| = "
        f"{diag['max_dev']:.3f} (tol {COUNT_TOL}); max gap/local-mean-gap = "
        f"{diag['max_gap_ratio']:.3f} (tol {GAP_RATIO_TOL}); "
        "rescans: none (zetazero used directly)",
        f"date: {DATE}",
        f"count: {len(zeros)}",
        "columns: index ordinate (12 decimal places)",
    ]


def write_zeros_file(path: str, header_lines: List[str],
                     zeros: List[mp.mpf]) -> None:
    """Write '# '-prefixed header lines, then 'index ordinate' rows."""
    with open(path, "w") as fh:
        for line in header_lines:
            fh.write("# " + line + "\n")
        for i, z in enumerate(zeros, 1):
            fh.write(f"{i} {fmt12(z)}\n")


def verify_zeros_file(path: str, expected_count: int) -> None:
    """Re-read a written file and check count, format, strict monotonicity."""
    import re
    pat = re.compile(r"^(\d+) (\d+\.\d{12})$")
    rows: List[Tuple[int, float]] = []
    with open(path) as fh:
        for line in fh:
            if line.startswith("#"):
                continue
            m = pat.match(line.strip())
            if not m:
                raise RuntimeError(f"{path}: malformed data line {line!r}")
            rows.append((int(m.group(1)), float(m.group(2))))
    if len(rows) != expected_count:
        raise RuntimeError(
            f"{path}: {len(rows)} data rows, expected {expected_count}")
    if [r[0] for r in rows] != list(range(1, expected_count + 1)):
        raise RuntimeError(f"{path}: indices are not 1..{expected_count}")
    ts = [r[1] for r in rows]
    if any(b <= a for a, b in zip(ts, ts[1:])):
        raise RuntimeError(f"{path}: ordinates not strictly increasing")


# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------

def main() -> None:
    t_all = time.perf_counter()
    out_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           "zeros")
    os.makedirs(out_dir, exist_ok=True)

    def log(msg: str) -> None:
        print(msg, flush=True)

    summary: List[Tuple[str, List[mp.mpf], str, List[str], List[str], float]] = []

    # ----- L1: Riemann zeta via zetazero -----------------------------------
    log("=== L1_zeta_q1 (Riemann zeta, q = 1) ===")
    t0 = time.perf_counter()
    zeros, diag = compute_L1(ZERO_COUNT, progress=log)
    validate_first_zero("L1_zeta_q1", zeros)
    elapsed = time.perf_counter() - t0
    path = os.path.join(out_dir, "L1_zeta_q1.txt")
    write_zeros_file(path, zeta_header(zeros, diag), zeros)
    verify_zeros_file(path, ZERO_COUNT)
    log(f"L1_zeta_q1: done in {elapsed:.1f}s -> {path}")
    summary.append(("L1_zeta_q1", zeros[:3], "n/a", diag["rescans"],
                    diag["flags"], elapsed))

    # ----- L2..L6: Dirichlet L via Hardy-Z scan -----------------------------
    for spec in SPECS:
        log(f"=== {spec.label} ({spec.description}) ===")
        t0 = time.perf_counter()
        zeros, diag = find_zeros(spec, ZERO_COUNT, progress=log)
        validate_first_zero(spec.label, zeros)
        for fl in diag["flags"]:
            log(f"WARNING {spec.label}: {fl}")
        elapsed = time.perf_counter() - t0
        path = os.path.join(out_dir, spec.label + ".txt")
        write_zeros_file(path, dirichlet_header(spec, zeros, diag), zeros)
        verify_zeros_file(path, ZERO_COUNT)
        log(f"{spec.label}: done in {elapsed:.1f}s -> {path}")
        summary.append((spec.label, zeros[:3], mp.nstr(diag["residual"], 3),
                        diag["rescans"], diag["flags"], elapsed))

    # ----- consolidated report ----------------------------------------------
    log("")
    log("==================== SUMMARY ====================")
    for label, firsts, resid, rescans, flags, elapsed in summary:
        log(f"{label}:")
        log("  first three ordinates: "
            + ", ".join(fmt12(z) for z in firsts))
        log(f"  reality residual: {resid}")
        log(f"  rescans: {'; '.join(rescans)}")
        log(f"  flags: {'; '.join(flags) if flags else 'none'}")
        log(f"  elapsed: {elapsed:.1f}s")
    log(f"total runtime: {time.perf_counter() - t_all:.1f}s")
    log("All checks passed." if not any(s[4] for s in summary)
        else "COMPLETED WITH FLAGS (see above).")


if __name__ == "__main__":
    main()
