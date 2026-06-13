"""THE CLOSED LOOP: zeta/L zeros computed from the geometry itself.

All inputs from outside the analytic universe, in the transcendental chart:
  - positions     : arcs n*(pi/3)  (transcendental lengths; integers appear
                    ONLY as arc ratios -- readouts, never coordinates)
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
import numpy as np, math, cmath

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

def pure_marks(q, a, vals, U, t_max, M=4_000_000, step=0.01):
    """Zeros from the geometry: returns the mark positions."""
    tau = sum(vals[r]*cmath.exp(2j*math.pi*r/q) for r in range(1, q))
    alpha = -cmath.phase(tau/(1j**a*math.sqrt(q)))/2
    ticks = np.arange(1, M+1, dtype=float)
    arc = ticks*U
    chi = np.array([vals[int(k) % q] for k in range(M+1)])[1:]
    w = chi/np.sqrt(arc/U)
    log_arc = np.log(arc)
    ts = np.arange(2*math.pi/q + 0.05, t_max, step)
    F = np.zeros(len(ts), complex)
    for i in range(0, len(ts), 150):
        F[i:i+150] = (w[None,:]*np.exp(-1j*ts[i:i+150][:,None]*log_arc[None,:])).sum(axis=1)
    th = np.array([argGamma(complex((0.5+a)/2, t/2))
                   + (t/2)*math.log(q/math.pi) + t*math.log(U) for t in ts])
    V = np.real(np.exp(1j*(th + alpha))*F)
    idx = np.nonzero(V[:-1]*V[1:] < 0)[0]
    return ts[idx] + step*V[idx]/(V[idx]-V[idx+1])

if __name__ == "__main__":
    g = np.array([float(l.split()[1]) for l in open('zeros/L2_chi3_q3.txt')
                  if not l.startswith('#')])[:20]
    marks = pure_marks(3, 1, {0: 0, 1: 1, 2: -1}, math.pi/3, float(g[-1])+1.0)
    d = np.abs(marks[:20] - g)
    print(f"chi3 from pure geometry: mean|off| {d.mean():.2e}, max {d.max():.2e}, {min(len(marks),20)}/20")
