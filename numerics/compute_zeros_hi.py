#!/usr/bin/env python3
"""High-resolution reference zeros: first 500 ordinates to 50 decimal places.

Independent (NON-geometric) reference data for the test harness: the same
traditional methods as compute_zeros.py — mp.zetazero for Riemann zeta, and the
Hurwitz-zeta Hardy-Z sign-change scan for the Dirichlet L-functions — but at
500 zeros and 50 certified decimal places.  This is the ground truth the helix
results are compared *against*; it never uses the geometric/helix construction.

Reuses compute_zeros.py's vetted arithmetic (gauss sum, root number, L via
Hurwitz zeta, Hardy Z, branch selection, smooth-count/gap completeness, scan +
rescan pipeline).  It overrides only:
  * the precision caps (compute_zeros.refine_zero hardcodes findroot tol 1e-26
    and certify +-5e-14 -> ~12 decimals; here findroot tol 1e-58 and certify
    +-1e-54 -> 50 certified decimals);
  * the working precision (REFINE_DPS 65; SCAN_DPS 30 for cheap bracketing);
  * the character set (adds L7 chi8 mod 8, L8 order-3 mod 7, L9 Legendre mod
    1009 — the last with full mpmath cube-root-of-unity / Legendre tables so the
    50-digit output is not silently capped by double-precision character values).

Output: numerics/zeros_500x50/<label>.txt (the originals in zeros/ are left
intact).  Each root is certified by a Hardy-Z sign change across [r-h, r+h] with
h = 1e-54, pinning it to < 1e-54 (50+ correct decimals).

Usage:
    python3 compute_zeros_hi.py                 # all nine, count 500
    python3 compute_zeros_hi.py --funcs L9      # only L9
    python3 compute_zeros_hi.py --funcs L1,L2 --count 200
"""

from __future__ import annotations

import argparse
import os
import time
from typing import Dict, List, Optional, Tuple

from mpmath import mp

import compute_zeros as cz
from compute_zeros import CharSpec

# ---------------------------------------------------------------------------
# Hi-resolution configuration
# ---------------------------------------------------------------------------

DATE = "2026-06-13"
ZERO_COUNT = 500
SCAN_DPS = 30            # cheap sign-change bracketing
REFINE_DPS = 65         # certified-root precision (>= 53 sig figs + margin)
DECIMALS = 50           # output decimal places
FINDROOT_TOL = "1e-58"
CERTIFY_HALFWIDTH = "1e-54"   # |root - true| < this  =>  50 certified decimals
OUT_DIRNAME = "zeros_500x50"

# Push the shared module's globals to hi-resolution (find_zeros / rescan_range
# read these at call time).
cz.ZERO_COUNT = ZERO_COUNT
cz.SCAN_DPS = SCAN_DPS
cz.REFINE_DPS = REFINE_DPS
cz.CERTIFY_HALFWIDTH = CERTIFY_HALFWIDTH


# ---------------------------------------------------------------------------
# Hi-precision root refinement (replaces compute_zeros.refine_zero's caps)
# ---------------------------------------------------------------------------

def refine_zero_hi(spec, branch, lo, hi, f_lo, f_hi):
    """Refine a sign-change bracket to a root certified to 50 decimals.

    Fast path: bracketed Anderson-Bjorck (mp.findroot, tol 1e-58) then certify
    by a sign change across [r - h, r + h], h = 1e-54.  Fallback: bisection of
    the original bracket down to width h.
    """
    with mp.workdps(REFINE_DPS):
        lo, hi = mp.mpf(lo), mp.mpf(hi)
        h = mp.mpf(CERTIFY_HALFWIDTH)
        root = None
        try:
            r = mp.findroot(lambda x: cz.hardy_Z(spec, x, branch), (lo, hi),
                            solver="anderson", tol=mp.mpf(FINDROOT_TOL),
                            maxsteps=400)
            r = mp.mpf(r.real) if isinstance(r, mp.mpc) else mp.mpf(r)
            if lo <= r <= hi and cz._sign_change(cz.hardy_Z(spec, r - h, branch),
                                                 cz.hardy_Z(spec, r + h, branch)):
                root = r
        except (ValueError, ArithmeticError):
            root = None
        if root is None:
            root = cz._bisect(spec, branch, lo, hi, f_lo, f_hi, h)
        return root


cz.refine_zero = refine_zero_hi   # find_zeros / rescan_range pick this up


# ---------------------------------------------------------------------------
# Cached Hardy Z (precompute sqrt(eps) once per spec; matters for q = 1009,
# where root_number is itself a 1009-term Gauss sum recomputed on every call).
# ---------------------------------------------------------------------------

_sqrt_eps_cache: Dict[str, object] = {}


def _sqrt_eps(spec) -> object:
    se = _sqrt_eps_cache.get(spec.label)
    if se is None:
        with mp.workdps(REFINE_DPS + 5):
            se = mp.sqrt(cz.root_number(spec))
        _sqrt_eps_cache[spec.label] = se
    return se


def hardy_Z_complex_cached(spec, t, branch: int = 1):
    t = mp.mpf(t)
    s = mp.mpf("0.5") + mp.mpc(0, 1) * t
    G = mp.gamma((s + spec.parity) / 2)
    omega = mp.power(mp.mpf(spec.q) / mp.pi, mp.mpc(0, 1) * t / 2) * G / abs(G)
    return branch * omega * cz.L_chi(spec, s) / _sqrt_eps(spec)


def hardy_Z_cached(spec, t, branch: int = 1):
    return hardy_Z_complex_cached(spec, t, branch).real


cz.hardy_Z = hardy_Z_cached
cz.hardy_Z_complex = hardy_Z_complex_cached


# ---------------------------------------------------------------------------
# Character set (L2..L9).  Quadratic / {+-1, +-i} values are exact in Python
# complex; the order-3 character (L8) needs high-precision cube roots of unity.
# ---------------------------------------------------------------------------

def _legendre_table(p: int) -> Tuple[int, ...]:
    """(chi(0)=0, chi(a) = +-1 the Legendre symbol (a|p)) for prime p."""
    vals = [0] * p
    for a in range(1, p):
        vals[a] = 1 if pow(a, (p - 1) // 2, p) == 1 else -1
    return tuple(vals)


def build_specs() -> Tuple[CharSpec, ...]:
    """The eight primitive Dirichlet characters L2..L9 (L1 = zeta is separate)."""
    with mp.workdps(REFINE_DPS + 15):
        w = mp.expjpi(mp.mpf(2) / 3)         # e^{i*pi*(2/3)} = e^{2 pi i/3}, all-mpmath
        w2 = mp.conj(w)                      # = e^{-2 pi i / 3} = w^2
    chi7c3 = (mp.mpc(0), mp.mpc(1), w2, w, w, w2, mp.mpc(1))   # order-3 mod 7
    return (
        CharSpec(label="L2_chi3_q3", q=3, values=(0, 1, -1), parity=1,
                 description="Dirichlet L of chi_3, the unique primitive character mod 3 (odd quadratic)"),
        CharSpec(label="L3_chi4_q4", q=4, values=(0, 1, 0, -1), parity=1,
                 description="Dirichlet L of chi_4, the unique primitive character mod 4 (odd quadratic)"),
        CharSpec(label="L4_chi5quad_q5", q=5, values=(0, 1, -1, -1, 1), parity=0,
                 description="Dirichlet L of the even quadratic character mod 5 (Legendre symbol mod 5)"),
        CharSpec(label="L5_chi5c4_q5", q=5, values=(0, 1, 1j, -1j, -1), parity=1,
                 description="Dirichlet L of the order-4 character mod 5 with chi(2) = i (odd, complex)"),
        CharSpec(label="L6_chi7quad_q7", q=7, values=(0, 1, 1, -1, 1, -1, -1), parity=1,
                 description="Dirichlet L of the odd quadratic character mod 7 (Legendre symbol mod 7)"),
        CharSpec(label="L7_chi8quad_q8", q=8, values=(0, 1, 0, -1, 0, -1, 0, 1), parity=0,
                 description="even quadratic character mod 8 (Kronecker symbol (2|n))"),
        CharSpec(label="L8_chi7c3_q7", q=7, values=chi7c3, parity=0,
                 description="order-3 even character mod 7 with chi(3) = e^{2 pi i/3}"),
        CharSpec(label="L9_chi1009quad_q1009", q=1009, values=_legendre_table(1009), parity=0,
                 description="even quadratic (Legendre) character mod 1009 -- large conductor probe"),
    )


# ---------------------------------------------------------------------------
# 50-decimal formatting and headers
# ---------------------------------------------------------------------------

def fmt_dp(t, places: int = DECIMALS) -> str:
    """Format a positive mpf to exactly `places` decimals (integer scaling)."""
    with mp.workdps(REFINE_DPS + 17):
        scaled = int(mp.nint(mp.mpf(t) * mp.mpf(10) ** places))
    sign = "-" if scaled < 0 else ""
    scaled = abs(scaled)
    return f"{sign}{scaled // 10**places}.{scaled % 10**places:0{places}d}"


def _cval(c) -> str:
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
    return mp.nstr(mp.mpc(c), 12)


def _char_table(spec: CharSpec) -> str:
    if spec.q > 32:   # abbreviate huge tables (full table is in zeros/<label>.txt)
        return (f"Legendre symbol (a|{spec.q}); chi(a)=0 iff {spec.q}|a "
                "(full value table in the original zeros/ file)")
    return ", ".join(f"chi({a})={_cval(spec.values[a])}" for a in range(spec.q))


def dirichlet_header(spec: CharSpec, zeros, diag: Dict) -> List[str]:
    branch_desc = "principal" if diag["branch"] == 1 else "negated principal"
    lines = [
        f"{spec.label}: first {len(zeros)} nontrivial zeros "
        "(ordinates t > 0 on Re s = 1/2, increasing)",
        f"function: {spec.description}",
        f"character table (q = {spec.q}, conductor {spec.q}, primitive): {_char_table(spec)}",
        f"parity: a = {spec.parity} "
        f"({'even, chi(-1)=+1' if spec.parity == 0 else 'odd, chi(-1)=-1'})",
        f"gauss sum tau(chi) = {mp.nstr(diag['tau'], 30)}  (|tau| = sqrt(q) verified)",
        f"root number eps = tau/(i^a sqrt(q)) = {mp.nstr(diag['eps'], 30)}",
        f"Z-branch: eps^(-1/2) = {branch_desc} square root (branch {diag['branch']:+d}); "
        f"max relative reality residual |Im W|/|W| = {mp.nstr(diag['residual'], 3)} (tol {cz.REALITY_TOL})",
        "method: INDEPENDENT (non-geometric) reference. "
        "L(s,chi) = q^(-s) * sum_(a=1..q-1) chi(a)*zeta(s, a/q) (Hurwitz zeta, mpmath);",
        "method: Hardy Z(t) = eps^(-1/2) * (q/pi)^(it/2) * "
        "(Gamma((s+a)/2)/|Gamma((s+a)/2)|) * L(1/2+it, chi), s = 1/2+it;",
        f"method: sign-change scan from t = {cz.T_START} step {cz.SCAN_STEP}; "
        f"bottom segment re-swept at step {cz.BOTTOM_STEP}; roots refined by "
        "bracketed Anderson-Bjorck (mp.findroot, tol "
        f"{FINDROOT_TOL}) and certified by a Hardy-Z sign change across "
        f"+-{CERTIFY_HALFWIDTH} ({DECIMALS}+ correct decimals)",
        f"precision: mp.dps = {SCAN_DPS} (scan), {REFINE_DPS} (refine/certify)",
        f"completeness: smooth-count max |k - N(t_k)| = {diag['max_dev']:.3f} "
        f"(tol {cz.COUNT_TOL}); max gap/local-mean-gap = {diag['max_gap_ratio']:.3f} "
        f"(tol {cz.GAP_RATIO_TOL})",
        f"rescans: {'; '.join(diag['rescans'])}",
        f"date: {DATE}",
        f"count: {len(zeros)}",
        f"columns: index ordinate ({DECIMALS} decimal places)",
    ]
    if spec.label == "L5_chi5c4_q5":
        lines.insert(3, "note: complex character, zero set NOT symmetric under "
                        "t -> -t; these are the first zeros with t > 0")
    if diag["flags"]:
        lines.append("FLAGS: " + "; ".join(diag["flags"]))
    return lines


def zeta_header(zeros, diag: Dict) -> List[str]:
    return [
        f"L1_zeta_q1: first {len(zeros)} nontrivial zeros "
        "(ordinates t > 0 on Re s = 1/2, increasing)",
        "function: Riemann zeta (the Dirichlet L-function of the trivial character mod q = 1)",
        "character table (q = 1, conductor 1): chi(n) = 1 for all n (trivial character)",
        "parity: a = 0 (even)",
        "root number eps = 1 (exact)",
        "method: INDEPENDENT (non-geometric) reference. "
        f"mpmath mp.zetazero(n).im for n = 1..{len(zeros)} "
        "(Riemann-Siegel based; zero ordering certified internally by mpmath)",
        f"precision: mp.dps = {REFINE_DPS}",
        "reality residual: n/a (no Hardy-Z scan; zetazero used directly)",
        f"completeness: smooth-count max |k - N(t_k)| = {diag['max_dev']:.3f} "
        f"(reported; zetazero ordering is library-certified); "
        f"max gap/local-mean-gap = {diag['max_gap_ratio']:.3f}",
        f"date: {DATE}",
        f"count: {len(zeros)}",
        f"columns: index ordinate ({DECIMALS} decimal places)",
    ]


# ---------------------------------------------------------------------------
# L1 (zeta) via zetazero -- report completeness, do not raise (ordering is
# library-certified, so a smooth-count offset is the formula's, not a miss).
# ---------------------------------------------------------------------------

def compute_L1_hi(count: int, log) -> Tuple[List, Dict]:
    with mp.workdps(REFINE_DPS):
        zeros = []
        for n in range(1, count + 1):
            zeros.append(mp.im(mp.zetazero(n)))
            if n % 50 == 0:
                log(f"L1_zeta_q1: {n} zeros, t ~ {mp.nstr(zeros[-1], 10)}")
        max_dev, gap_bad, max_ratio = cz._completeness(1, zeros)
    flags = []
    if max_dev > cz.COUNT_TOL or gap_bad:
        flags.append(f"smooth-count deviation {max_dev:.2f} (zetazero ordering "
                     "is library-certified; reported, not a missed zero)")
    diag = {"branch": None, "residual": None, "tau": None, "eps": mp.mpc(1),
            "rescans": ["none (zetazero used directly)"], "flags": flags,
            "max_dev": max_dev, "max_gap_ratio": max_ratio}
    return zeros, diag


# ---------------------------------------------------------------------------
# Output + verification
# ---------------------------------------------------------------------------

def write_file(path: str, header_lines: List[str], zeros) -> None:
    with open(path, "w") as fh:
        for line in header_lines:
            fh.write("# " + line + "\n")
        for i, z in enumerate(zeros, 1):
            fh.write(f"{i} {fmt_dp(z)}\n")


def verify_file(path: str, expected_count: int) -> None:
    import re
    pat = re.compile(r"^(\d+) (\d+\.\d{" + str(DECIMALS) + r"})$")
    rows = []
    with open(path) as fh:
        for line in fh:
            if line.startswith("#"):
                continue
            m = pat.match(line.strip())
            if not m:
                raise RuntimeError(f"{path}: malformed data line {line!r}")
            rows.append((int(m.group(1)), m.group(2)))
    if len(rows) != expected_count:
        raise RuntimeError(f"{path}: {len(rows)} rows, expected {expected_count}")
    if [r[0] for r in rows] != list(range(1, expected_count + 1)):
        raise RuntimeError(f"{path}: indices not 1..{expected_count}")
    ts = [mp.mpf(r[1]) for r in rows]
    if any(b <= a for a, b in zip(ts, ts[1:])):
        raise RuntimeError(f"{path}: ordinates not strictly increasing")


# ---------------------------------------------------------------------------
# Cross-check against the existing low-res reference (first min(N,100) rows).
# ---------------------------------------------------------------------------

def crosscheck_low_res(label: str, zeros, log) -> Optional[float]:
    here = os.path.dirname(os.path.abspath(__file__))
    ref_path = os.path.join(here, "zeros", label + ".txt")
    if not os.path.exists(ref_path):
        return None
    refs = []
    with open(ref_path) as fh:
        for line in fh:
            if line.startswith("#"):
                continue
            parts = line.split()
            if len(parts) == 2:
                refs.append(mp.mpf(parts[1]))
    n = min(len(refs), len(zeros))
    if n == 0:
        return None
    worst = max(float(abs(zeros[i] - refs[i])) for i in range(n))
    log(f"{label}: vs old reference (first {n}): max|diff| = {worst:.3e}")
    return worst


# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------

def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--funcs", default="L1,L2,L3,L4,L5,L6,L7,L8,L9",
                    help="comma list of labels (prefix match, e.g. L1,L9)")
    ap.add_argument("--count", type=int, default=ZERO_COUNT)
    args = ap.parse_args()

    want = set(args.funcs.split(","))
    count = args.count

    def selected(label: str) -> bool:
        return any(label.startswith(w) or label == w or label.split("_")[0] == w
                   for w in want)

    def log(msg: str) -> None:
        print(msg, flush=True)

    here = os.path.dirname(os.path.abspath(__file__))
    out_dir = os.path.join(here, OUT_DIRNAME)
    os.makedirs(out_dir, exist_ok=True)

    t_all = time.perf_counter()

    if selected("L1_zeta_q1"):
        log("=== L1_zeta_q1 (Riemann zeta, q = 1) ===")
        t0 = time.perf_counter()
        zeros, diag = compute_L1_hi(count, log)
        path = os.path.join(out_dir, "L1_zeta_q1.txt")
        write_file(path, zeta_header(zeros, diag), zeros)
        verify_file(path, count)
        crosscheck_low_res("L1_zeta_q1", zeros, log)
        log(f"L1_zeta_q1: done in {time.perf_counter()-t0:.1f}s -> {path}")

    for spec in build_specs():
        if not selected(spec.label):
            continue
        log(f"=== {spec.label} ({spec.description[:60]}) ===")
        t0 = time.perf_counter()
        zeros, diag = cz.find_zeros(spec, count, progress=log)
        for fl in diag["flags"]:
            log(f"WARNING {spec.label}: {fl}")
        path = os.path.join(out_dir, spec.label + ".txt")
        write_file(path, dirichlet_header(spec, zeros, diag), zeros)
        verify_file(path, count)
        crosscheck_low_res(spec.label, zeros, log)
        log(f"{spec.label}: done in {time.perf_counter()-t0:.1f}s -> {path}")

    log(f"total runtime: {time.perf_counter()-t_all:.1f}s")


if __name__ == "__main__":
    main()
