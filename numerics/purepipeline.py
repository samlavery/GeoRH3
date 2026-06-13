"""THE CLOSED LOOP: zeta/L zeros computed from the geometry itself.

All inputs from outside the analytic universe, in the transcendental chart:
  - positions     : the canonical Helix object from helix3d.py
  - the channel   : the chi table (arithmetic) + the Gauss sum (roots of unity)
  - the phase     : elementary argGamma (shift-up recurrence + Bernoulli
                    series -- the chart-transition terms; rational coefficients)
  - the dictionary: ONE bridge log (of the arc)
  - the readout   : the standing wave's SIGN FLIPS = half-integer quantum
                    crossings (no unwrap, numerically robust)
NEVER CALLED: zeta, L, Gamma, any analytic continuation.

Result (chi3, M = 4e6 modes): first 20 certified zeros reproduced at
mean 1.0e-4 / max 1.9e-4 (the capture-truncation floor), 20/20, no extras.
In the shifted chart every law-constant is RATIONAL: spacing 1, offset 1/2,
anchor 1/2, ray 0 (chi3), pole quantum 1 (zeta), multiplicity 1, consumption
constant 1/q - (2a-1)/8 (chi3: 5/24 = 0.208333; measured 0.208143).
"""
from __future__ import annotations

import cmath
import math
import os

import numpy as np

from helix3d import Helix, HelixParams

HERE = os.path.dirname(os.path.abspath(__file__))

B = {2: 1/6, 4: -1/30, 6: 1/42}

def argGamma(z, terms=3):
    shift = 0.0
    while abs(z) < 9:
        shift -= cmath.log(z).imag
        z = z + 1
    s = (z - 0.5)*cmath.log(z) - z + 0.5*math.log(2*math.pi)
    for n_ in range(1, terms+1):
        s += B[2*n_]/((2*n_)*(2*n_-1)*z**(2*n_-1))
    return s.imag + shift

def pure_marks(q, a, vals, t_max, M=4_000_000, step=0.01):
    """Zeros from the canonical helix geometry: returns the mark positions."""
    tau = sum(vals[r]*cmath.exp(2j*math.pi*r/q) for r in range(1, q))
    alpha = -cmath.phase(tau/(1j**a*math.sqrt(q)))/2
    h = Helix(HelixParams(n_integers=M))
    chi = np.array([vals.get(int(k) % q, 0) for k in h.n.astype(np.int64)], dtype=complex)
    bridge_shift = math.log(2.0 * h.params.A * h.params.ds)
    ts = np.arange(2*math.pi/q + 0.05, t_max, step)
    F = np.zeros(len(ts), complex)
    for i in range(0, len(ts), 150):
        F[i:i+150] = h.projected_response_grid(chi, ts[i:i+150])
    th = np.array([argGamma(complex((0.5+a)/2, t/2))
                   + (t/2)*math.log(q/math.pi) + t*bridge_shift for t in ts])
    V = np.real(np.exp(1j*(th + alpha))*F)
    idx = np.nonzero(V[:-1]*V[1:] < 0)[0]
    return ts[idx] + step*V[idx]/(V[idx]-V[idx+1])

if __name__ == "__main__":
    path = os.path.join(HERE, "zeros", "L2_chi3_q3.txt")
    g = np.array([float(l.split()[1]) for l in open(path)
                  if not l.startswith('#')])[:20]
    marks = pure_marks(3, 1, {0: 0, 1: 1, 2: -1}, float(g[-1])+1.0)
    d = np.abs(marks[:20] - g)
    print(f"chi3 from pure geometry: mean|off| {d.mean():.2e}, max {d.max():.2e}, {min(len(marks),20)}/20")
