"""Self-certifying computation of Riemann zeta zeros to arbitrary precision.

THE TOOL (this project's computational deliverable): every zero is returned with a
three-part certificate from the accounting identity

    m - theta(t)/pi - 3/2 = S(t)        (midpoint convention at the zero)

verified at the working-precision floor:
  * POSITION     -- the identity residual (floor-tracking = the zero is exact);
  * INDEX        -- the integer m in the identity (a missed zero shifts every
                    subsequent residual by ~1: un-fakeable);
  * MULTIPLICITY -- the S-jump across the zero (= order; 1 = simple).

Method: quadratic Newton on zeta(1/2+it) with escalating precision (iteration k
runs at ~2.2x the digits already correct, so only the last iterations pay full
price), seeded from any coarse table (9 decimals suffice).  S is computed
independently by argument continuation along sigma: 3 -> 1/2 (principal branch
safe at sigma = 3).  Nothing in the certificate reuses the Newton computation.

Benchmark output: zeta-evaluations and wall seconds per zero per certified digit.
"""
from __future__ import annotations

import time
from mpmath import mp, mpf, mpc, zeta, loggamma, im as mim, re as mre, arg as marg, \
    log as mlog, pi as mppi, fabs

EVALS = {"n": 0}

def zeta_line(t, dps, derivative=0):
    """zeta(1/2 + i t) (or d/ds) at the given dps."""
    EVALS["n"] += 1
    with mp.workdps(dps):
        return zeta(mpc(mpf(1)/2, t), derivative=derivative)

def theta_zeta(t, dps):
    with mp.workdps(dps):
        return mim(loggamma(mpc(mpf(1)/4, t/2))) - (t/2)*mlog(mppi)

def refine(seed, target_dps, seed_digits=8):
    """Escalating-precision Newton: seed (float ok) -> zero to target_dps digits."""
    t = mpf(seed)
    digits = seed_digits
    while digits < target_dps:
        work = min(int(2.2*digits) + 10, target_dps + 10)
        with mp.workdps(work):
            f = zeta_line(t, work)
            fp = zeta_line(t, work, derivative=1) * mpc(0, 1)   # d/dt = i * zeta'
            t = mre(t - f/fp)
        digits = int(1.9*digits)
    return t

SIGMA_PATH = [mpf(3), mpf(2), mpf('1.4'), mpf(1), mpf('0.8'), mpf('0.65'),
              mpf('0.57'), mpf('0.53'), mpf('0.51'), mpf('0.503'), mpf('0.501'),
              mpf('0.5003'), mpf('0.5001'), mpf('0.50003'), mpf('0.50001'), mpf('0.5')]

def S_cont(t, dps):
    """(1/pi) arg zeta(1/2+it) by continuation from sigma = 3 (principal there)."""
    with mp.workdps(dps):
        EVALS["n"] += 1
        prev = marg(zeta(mpc(SIGMA_PATH[0], t)))
        for s_ in SIGMA_PATH[1:]:
            EVALS["n"] += 1
            cur = marg(zeta(mpc(s_, t)))
            while cur - prev > mppi:  cur -= 2*mppi
            while cur - prev < -mppi: cur += 2*mppi
            prev = cur
        return prev/mppi

def certify(t, m, dps):
    """The three-part certificate at working precision."""
    with mp.workdps(dps):
        d = mpf(10)**(-int(0.4*dps))
        Sm, Sp = S_cont(t - d, dps), S_cont(t + d, dps)
        resid = fabs(mpf(m) - theta_zeta(t, dps)/mppi - mpf(3)/2 - (Sm + Sp)/2)
        mult = Sp - Sm
    return resid, mult

def parse_odlyzko_zeros2(path):
    """Odlyzko's first-100-zeros-to-1000-decimals table (multi-line per zero)."""
    out, cur = [], ""
    for line in open(path):
        s = line.strip()
        if not s:
            continue
        if "." in s:                      # a new zero starts
            if cur:
                out.append(cur)
            cur = s
        else:
            cur += s
    if cur:
        out.append(cur)
    return out

def main(n_deep=3, deep_dps=1020, n_broad=25, broad_dps=220):
    import os
    here = os.path.dirname(os.path.abspath(__file__))
    od = parse_odlyzko_zeros2(os.path.join(here, "results", "odlyzko_zeros2.txt"))
    print(f"Odlyzko zeros2 parsed: {len(od)} zeros, ~{len(od[0])-4} decimals each", flush=True)
    seeds = [float(z[:14]) for z in od]

    for label, count, dps in (("DEEP", n_deep, deep_dps), ("BROAD", n_broad, broad_dps)):
        print(f"\n=== {label}: first {count} zeros at dps {dps} ===", flush=True)
        for m in range(1, count + 1):
            EVALS["n"] = 0
            t0 = time.time()
            z = refine(seeds[m-1], dps)
            ne_newton = EVALS["n"]
            resid, mult = certify(z, m, dps)
            wall = time.time() - t0
            with mp.workdps(dps):
                xref = fabs(z - mpf(od[m-1]))
            print(f"zero {m:3d}: identity residual {mp.nstr(resid, 3)}  "
                  f"|ours - Odlyzko| {mp.nstr(xref, 3)}  mult-1 {mp.nstr(fabs(mult-1), 2)}  "
                  f"[{EVALS['n']} evals ({ne_newton} newton), {wall:.1f}s, "
                  f"{wall/dps*1000:.1f} ms/digit]", flush=True)

if __name__ == "__main__":
    main()


# --- v2: full-precision protocol (no truncated inputs anywhere) -------------
def refine_full(seed_str, target_dps):
    """Newton from a FULL-PRECISION string seed (no float truncation)."""
    digits0 = max(8, len(seed_str) - 4)
    with mp.workdps(target_dps + 10):       # seed parsed at FULL precision
        t = mpf(seed_str)
    digits = digits0
    while digits < target_dps:
        work = min(int(2.2*digits) + 10, target_dps + 10)
        with mp.workdps(work):
            f = zeta_line(t, work)
            fp = zeta_line(t, work, derivative=1) * mpc(0, 1)
            t = mre(t - f/fp)
        digits = int(1.9*digits)
    return t

def certify_v2(zeros, m, dps, gap_hint=None):
    """Full-floor certificate: index at the INTER-ZERO MIDPOINT (|zeta| ~ 1,
    no cancellation), position by the Newton residual, multiplicity by a
    moderate-delta jump.  Residual floor = the working precision itself."""
    t = zeros[m-1]
    with mp.workdps(dps):
        T = (zeros[m-1] + zeros[m])/2 if m < len(zeros) else t + (gap_hint or mpf(2))
        resid_index = fabs(mpf(m) - theta_zeta(T, dps)/mppi - 1 - S_cont(T, dps))
        pos = fabs(zeta_line(t, dps))
        d = mpf(10)**(-20)
        mult = S_cont(t + d, dps//4) - S_cont(t - d, dps//4)
    return resid_index, pos, mult

def supremacy(n_zeros=10, dps=2048):
    """Beyond the canonical: zeros to twice Odlyzko's depth, fully certified."""
    import os, time
    here = os.path.dirname(os.path.abspath(__file__))
    od = parse_odlyzko_zeros2(os.path.join(here, "results", "odlyzko_zeros2.txt"))
    print(f"SUPREMACY RUN: first {n_zeros} zeros at {dps} decimals "
          f"(canonical table: ~1022)", flush=True)
    zs = []
    for m in range(1, n_zeros + 2):              # +1 neighbor for the last midpoint
        t0 = time.time()
        EVALS["n"] = 0
        zs.append(refine_full(od[m-1], dps))
        print(f"  refined zero {m} [{EVALS['n']} evals, {time.time()-t0:.0f}s]", flush=True)
    out = open(os.path.join(here, "results", f"zeta_zeros_{dps}.txt"), "w")
    out.write(f"# Riemann zeta zeros 1..{n_zeros} to {dps} decimals.\n"
              f"# Method: escalating-precision Newton on zeta(1/2+it), full-precision seeds;\n"
              f"# certificates: index at inter-zero midpoint (full floor), position = |zeta| at\n"
              f"# the zero, multiplicity = S-jump. Produced in Python/mpmath on an Apple M3.\n")
    for m in range(1, n_zeros + 1):
        t0 = time.time()
        EVALS["n"] = 0
        ri, pos, mult = certify_v2(zs, m, dps)
        with mp.workdps(dps):
            xref = fabs(zs[m-1] - mpf(od[m-1]))
        print(f"zero {m:3d}: index-resid {mp.nstr(ri, 3)}  |zeta(rho)| {mp.nstr(pos, 3)}  "
              f"mult-1 {mp.nstr(fabs(mult-1), 2)}  vs-canonical {mp.nstr(xref, 3)}  "
              f"[{EVALS['n']} evals, {time.time()-t0:.0f}s]", flush=True)
        out.write(f"{m} {mp.nstr(zs[m-1], dps)}\n")
    out.close()
    print("table written", flush=True)
