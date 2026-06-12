#!/usr/bin/env python3
"""One-shot cross-check of the generated reference zero files against LMFDB.

Reads the six files in zeros/ and compares:
  - L1/L2/L3 first ordinates against the classical reference values, and
  - L4/L5/L6 first three ordinates against the zeros listed on LMFDB
    (pages 1-5-5.4-r0-0-0, 1-5-5.2-r1-0-0, 1-7-7.6-r1-0-0, fetched 2026-06-11),
  - all files: 100 rows, strictly increasing, 12-decimal format.

LMFDB digits were transcribed on 2026-06-11; agreement is required to 1e-9
(comfortably inside both sources' precision).
"""

import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ZDIR = os.path.join(HERE, "zeros")

# label -> list of (index, reference ordinate, tolerance)
REFS = {
    # classical value (Riemann zeta first zero):
    "L1_zeta_q1": [(1, "14.134725141734693790", 1e-9)],
    # LMFDB 1-3-3.2-r1-0-0 (quadratic mod 3), fetched 2026-06-11:
    "L2_chi3_q3": [
        (1, "8.03973715568146668171362321417", 1e-9),
        (2, "11.24920620777293524970502567886", 1e-9),
        (3, "15.70461917672162556516555088043", 1e-9),
    ],
    # LMFDB page 1-4-4.3-r1-0-0 was behind a CAPTCHA at fetch time; this is
    # the classical first zero of the Dirichlet beta function from the
    # literature.  L3's primary validation is the in-run certified
    # computation plus the mission constant 6.020949 (tol 1e-4).
    "L3_chi4_q4": [(1, "6.0209489046975965", 1e-9)],
    # LMFDB 1-5-5.4-r0-0-0 (even quadratic mod 5):
    "L4_chi5quad_q5": [
        (1, "6.64845334472771471612327845997", 1e-9),
        (2, "9.831444432886669616348321347458", 1e-9),
        (3, "11.95884562608351453026565868826", 1e-9),
    ],
    # LMFDB 1-5-5.2-r1-0-0 (quartic mod 5, chi(2)=i, root number 0.850+0.525i):
    "L5_chi5c4_q5": [
        (1, "6.18357819545085391437751730970", 1e-9),
        (2, "8.45722917442323072160535286274", 1e-9),
        (3, "12.67494641701135578048229914508", 1e-9),
    ],
    # LMFDB 1-7-7.6-r1-0-0 (odd quadratic mod 7):
    "L6_chi7quad_q7": [
        (1, "4.47573828372868313197462848719", 1e-9),
        (2, "6.84549171249137726783979779478", 1e-9),
        (3, "11.16018454311952965510181826588", 1e-9),
    ],
}

PAT = re.compile(r"^(\d+) (\d+\.\d{12})$")


def read_file(label):
    path = os.path.join(ZDIR, label + ".txt")
    rows = {}
    with open(path) as fh:
        for line in fh:
            if line.startswith("#"):
                continue
            m = PAT.match(line.strip())
            if not m:
                raise SystemExit(f"FAIL {label}: malformed line {line!r}")
            rows[int(m.group(1))] = float(m.group(2))
    if len(rows) != 100 or sorted(rows) != list(range(1, 101)):
        raise SystemExit(f"FAIL {label}: expected indices 1..100")
    ts = [rows[i] for i in range(1, 101)]
    if any(b <= a for a, b in zip(ts, ts[1:])):
        raise SystemExit(f"FAIL {label}: not strictly increasing")
    return rows


def main():
    ok = True
    for label, checks in REFS.items():
        rows = read_file(label)
        for idx, ref, tol in checks:
            got = rows[idx]
            diff = abs(got - float(ref[:18]))
            status = "ok" if diff < tol else "MISMATCH"
            if status != "ok":
                ok = False
            print(f"{label} zero #{idx}: file {got:.12f}  ref {ref[:20]}  "
                  f"|diff| = {diff:.2e}  [{status}]")
    print("CROSS-CHECK " + ("PASSED" if ok else "FAILED"))
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
