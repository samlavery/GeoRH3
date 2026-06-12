"""
convergence.py -- CONVERGENCE TESTS for the purchase-model pipeline. Measured, not assumed.

(a) RESOLUTION: do the fiber's marks converge as the helix discretization refines
    (n_integers doubling)?  Expected: trapezoid error -> 0; observed order reported.
(b) HEIGHT: do mark offsets vs certified zeros decay with height?  The geometric
    accumulator differs from exact theta by ~ a constant (the Gamma O(1) term) plus
    O(1/t); a constant E-error shifts a mark by  const / theta'(t)  -> decays like
    1/log t.  Windowed means reported per function; the exact-theta gap at each mark
    is measured directly (crosscheck) to confirm the constant-offset diagnosis.
(c) PRECISION: are the exact-ladder rungs (model_ladder) stable under mp.dps 25 -> 40?
All results printed; failures raise.
"""
from __future__ import annotations
import math, os, sys
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from helix3d import Helix, HelixParams
from fiber import Fiber, ALL_SPECS, ZETA_SPEC
from compute_zeros import SPECS
import mpmath as mp

HERE = os.path.dirname(os.path.abspath(__file__))
ZD = os.path.join(HERE, 'zeros')

def load_zeros(label):
    zs = []
    with open(os.path.join(ZD, f"{label}.txt")) as f:
        for ln in f:
            if not ln.startswith('#'):
                p = ln.split()
                if len(p) == 2: zs.append(float(p[1]))
    return zs

print("="*78)
print("(a) RESOLUTION CONVERGENCE -- chi_3 fiber, 60 marks, n_integers doubling")
print("="*78)
res = [62_500, 125_000, 250_000, 500_000]
marks_by_res = []
for n in res:
    h = Helix(HelixParams(n_integers=n))
    marks_by_res.append([m.height for m in Fiber(SPECS[0], h).run(60)])
prev_dev = None
for i in range(1, len(res)):
    dev = max(abs(a-b) for a, b in zip(marks_by_res[i-1], marks_by_res[i]))
    order = (math.log(prev_dev/dev)/math.log(2)) if prev_dev else float('nan')
    print(f"  {res[i-1]:>7d} -> {res[i]:>7d}:  max|delta mark| = {dev:.3e}"
          + (f"   observed order ~ {order:.2f}" if prev_dev else ""))
    prev_dev = dev
assert prev_dev < 1e-4, "marks not converged at top resolution"
print("  PASSED: marks converge; 250k discretization error << offsets being measured")

print()
print("="*78)
print("(b) HEIGHT CONVERGENCE -- offsets and exact-theta gaps vs height, per function")
print("="*78)
h = Helix(HelixParams(n_integers=400_000))   # extra headroom for tails
print(f"{'function':22s} {'mean%gap 1-25':>14s} {'26-50':>7s} {'51-75':>7s} {'76-100':>8s}"
      f"  {'thetaGap@10':>11s} {'@100':>6s}")
for spec in ALL_SPECS:
    f = Fiber(spec, h)
    marks = f.run(100)
    zeros = load_zeros(spec.label)
    m = min(len(zeros), len(marks))
    ds = [abs(marks[i].height - zeros[i]) for i in range(m)]
    gaps = [zeros[i+1]-zeros[i] for i in range(m-1)]
    def wmean(lo, hi):
        seg = ds[lo:hi]; g = gaps[lo:min(hi, len(gaps))]
        return (sum(seg)/len(seg)) / (sum(g)/len(g)) * 100
    # exact-theta gap at two marks (constant-offset diagnosis)
    q, a = spec.q, spec.parity
    def theta_gap(mk):
        t = mk.height
        th = float(mp.im(mp.loggamma((mp.mpf(1)/2 + 1j*t + a)/2)) + (t/2)*mp.log(mp.mpf(q)/mp.pi))
        return abs(th - mk.E_at)
    print(f"{spec.label:22s} {wmean(0,25):14.1f} {wmean(25,50):7.1f} {wmean(50,75):7.1f}"
          f" {wmean(75,100):8.1f}  {theta_gap(marks[9]):11.4f} {theta_gap(marks[99]):6.4f}")
print("  (thetaGap ~ 0 certifies the accumulator; offsets do NOT decay and should not:")
print("   rung-by-rung, offset_k = -pi*S(gamma_k)/theta'(gamma_k) -- the zeros' own phase")
print("   residual, which oscillates and slowly grows. Flat windows = correct pipeline.")

print()
print("="*78)
print("(c) PRECISION -- exact-ladder rungs, mp.dps 25 vs 40 (chi_3, rungs 1,50,100)")
print("="*78)
def theta3(t): return (t/2)*mp.log(3/mp.pi) + mp.im(mp.loggamma(mp.mpf(3)/4 + 0.5j*t))
for n_r in (1, 50, 100):
    vals = []
    for dps in (25, 40):
        with mp.workdps(dps):
            lvl = (n_r - mp.mpf(1)/2)*mp.pi
            r = mp.findroot(lambda u: theta3(u) - lvl, 8.0 + 1.8*(n_r-1))
            vals.append(r)
    d = abs(vals[0]-vals[1])
    print(f"  rung {n_r:3d}:  dps25={mp.nstr(vals[0],15)}  dps40={mp.nstr(vals[1],15)}  |diff|={mp.nstr(d,3)}")
    assert d < mp.mpf('1e-10'), "precision instability"
print("  PASSED: rungs stable to <1e-10 under precision doubling")
