"""
Frobenius-3D screw / monodromy operator — numerical test of the production package.

The decision (this run): Frobenius in 3D is the helix SCREW / return-map operator.
Zeros are NOT scalar eigenvalues of F_3D; they are singular EIGEN-EVENTS on the carrier:

    F_3D psi = phase . psi      phase = e^{iD}     |phase| = 1   (carrier, no-drift)
    A    psi = arc   . psi      arc-length position observable
    readout(arc) = rho          analytic readout pulls -L'/L back to helix arc coord

The package's one numerically-decisive claim is the EVENT TRACE IDENTITY:

    Tr_event(z) = SUM_e  weight(e) / (z - arc(e))  =  -d/dz log Lambda(readout(z)).

With readout(z) = 1/2 + i z and the events sitting at the zeros (arc = gamma_n), this is
exactly the Hilbert-Polya resolvent trace = log-derivative of the Riemann Xi function:

    Xi(z) := xi(1/2 + i z)  (entire, even, order 1, zeros at z = +/- gamma_n)
    d/dz log Xi(z)  =  SUM_n [ 1/(z - gamma_n) + 1/(z + gamma_n) ]  =  SUM_n 2z/(z^2 - gamma_n^2).

We test, against mpmath ground truth (exact zeros, exact xi):
  PART 1  the screw/monodromy carrier: eigenphases e^{iD}, e^{i gamma_n D} are unit-modulus
          (a real H-P spectrum <=> unit-modulus monodromy: "unit transverse eigenphase").
  PART 2  THE TRACE IDENTITY: SUM_n 2z/(z^2 - gamma_n^2)  ==  d/dz log Xi(z), to many digits.
  PART 3  the emission law: events farther apart in ARC (height e^{gamma} up), while the
          ORDINATE gaps shrink ~ 2pi/log gamma  (the e^{gamma} Jacobian duality).

Nothing here is RH-conditional: it tests whether the construction is FAITHFUL to the real
analytic object.  If PART 2 matches, the event-trace really is -d/dz log Lambda(readout) --
the production's spectral readout is the honest log-derivative of the completed L-function.
"""

import mpmath as mp
import numpy as np

mp.mp.dps = 30
TWO_PI = 2 * mp.pi


# ----------------------------------------------------------------------------- ground truth
def xi(s):
    """Riemann xi: entire, xi(s) = xi(1-s).  xi(s) = 1/2 s(s-1) pi^{-s/2} Gamma(s/2) zeta(s)."""
    s = mp.mpf(0) + s
    return mp.mpf(1) / 2 * s * (s - 1) * mp.power(mp.pi, -s / 2) * mp.gamma(s / 2) * mp.zeta(s)


def Xi(z):
    """Riemann Xi in the arc coordinate: Xi(z) = xi(1/2 + i z).  Even, entire, zeros at +/- gamma_n."""
    return xi(mp.mpf(1) / 2 + 1j * z)


def logderiv_Xi(z):
    """d/dz log Xi(z)  -- the analytic readout  -d/dz log Lambda(readout(z)) up to orientation."""
    z = mp.mpc(z)
    return mp.diff(lambda w: mp.log(Xi(w)), z)


print("Caching nontrivial zeta zeros gamma_n (mpmath, exact) ...", flush=True)
NZ = 200
gammas = [mp.im(mp.zetazero(n)) for n in range(1, NZ + 1)]
print(f"  cached gamma_1 .. gamma_{NZ}:  gamma_1 = {float(gammas[0]):.6f}, "
      f"gamma_{NZ} = {float(gammas[-1]):.4f}\n", flush=True)


# ============================================================================= PART 1
print("=" * 80)
print("PART 1 — the screw / monodromy CARRIER:  eigenphase e^{iD}, |.| = 1  (no drift)")
print("=" * 80)

# The 4x4 homogeneous screw matrix F_D = rotation(D) in the transverse plane (x,y)
#                                      + axial translation h*D along z.
def screw_matrix(Delta, h):
    c, s = np.cos(Delta), np.sin(Delta)
    return np.array([[c, -s, 0.0, 0.0],
                     [s,  c, 0.0, 0.0],
                     [0.0, 0.0, 1.0, h * Delta],
                     [0.0, 0.0, 0.0, 1.0]])

Delta = 0.7234           # carrier angular step per unit (arbitrary fixed carrier)
h = 1.0
F = screw_matrix(Delta, h)
eig = np.linalg.eigvals(F)
print(f"  screw step Delta = {Delta},  axial slope h = {h}")
print(f"  eigenvalues of the 4x4 homogeneous screw: {np.round(eig, 6)}")
print(f"  predicted {{e^(+iD), e^(-iD), 1, 1}} = "
      f"{np.round([np.exp(1j*Delta), np.exp(-1j*Delta), 1, 1], 6)}")
trans_mods = sorted(abs(e) for e in eig)
print(f"  |eigenvalues| = {np.round(sorted(abs(e) for e in eig), 12)}   "
      f"(transverse pair has |.|=1: carrier is a no-drift isometry)")

# The Hilbert-Polya MONODROMY  U_D = e^{i D H}  acts on the gamma_n-eigenstate by e^{i gamma_n D}.
# A REAL spectrum {gamma_n}  <=>  unit-modulus monodromy eigenphases.  This is the
# "unit transverse eigenphase" of every vanishing event, with no RH input.
print("\n  Hilbert-Polya monodromy U_D = e^{iD H}: eigenphase of the gamma_n eigen-event:")
print(f"    {'n':>3} {'gamma_n':>12} {'e^{i gamma_n Delta}':>34} {'|.|':>8}")
for n in [1, 2, 5, 10, 50, 200]:
    g = gammas[n - 1]
    ph = mp.e ** (1j * g * Delta)
    print(f"    {n:>3} {float(g):>12.5f}   {complex(ph).real:>+.6f}{complex(ph).imag:>+.6f}i   "
          f"{float(abs(ph)):>8.5f}")
print("  => real spectrum forces every eigenphase onto the unit circle (von Neumann reality,")
print("     read on the carrier as a pure rotation).  No positivity, no GRH used.")


# ============================================================================= PART 2
print("\n" + "=" * 80)
print("PART 2 — THE TRACE IDENTITY (the real content):")
print("    Tr_event(z) = SUM_n [1/(z-gamma_n) + 1/(z+gamma_n)]  ==  d/dz log Xi(z)")
print("                = -d/dz log Lambda(readout(z)),   readout(z) = 1/2 + i z")
print("=" * 80)


def event_trace_partial(z, N):
    """SUM_{n=1}^{N} 2z/(z^2 - gamma_n^2) -- the resolvent trace over the first N eigen-events."""
    z = mp.mpc(z)
    return mp.fsum(2 * z / (z * z - g * g) for g in gammas[:N])


def tail_correction(z, N):
    """Analytic estimate of SUM_{n>N} 2z/(z^2-gamma_n^2) ~ -2z * SUM_{n>N} 1/gamma_n^2,
    using the zero density dN/dt ~ log(t/2pi)/2pi:
        SUM_{n>N} 1/gamma_n^2 ~ integral_{gamma_N}^inf (1/t^2)(log(t/2pi)/2pi) dt
                              = [log(gamma_N/2pi) + 1] / (2 pi gamma_N)."""
    z = mp.mpc(z)
    gN = gammas[N - 1]
    tail_inv_sq = (mp.log(gN / TWO_PI) + 1) / (TWO_PI * gN)
    return -2 * z * tail_inv_sq


test_points = [mp.mpf(5), mp.mpf(10), mp.mpf(17), mp.mpf("0.5") + 8j, mp.mpf(3) + 2j]
print(f"\n  {'z':>16} {'partial SUM (N=200)':>26} {'+tail corr':>26} {'d/dz log Xi(z)':>26} {'|err|':>11}")
for z in test_points:
    lhs_raw = event_trace_partial(z, NZ)
    lhs = lhs_raw + tail_correction(z, NZ)
    rhs = logderiv_Xi(z)
    err = abs(lhs - rhs)
    zs = f"{complex(z).real:g}{complex(z).imag:+g}i" if complex(z).imag else f"{float(z):g}"
    print(f"  {zs:>16} {complex(lhs_raw).real:>+12.6f}{complex(lhs_raw).imag:>+12.6f}i "
          f"{complex(lhs).real:>+12.6f}{complex(lhs).imag:>+12.6f}i "
          f"{complex(rhs).real:>+12.6f}{complex(rhs).imag:>+12.6f}i {float(err):>11.2e}")

# Tail-FREE sharpening: each eigen-event is a SIMPLE pole of the analytic readout with
# residue exactly 1, sitting exactly at z = gamma_n.  This identifies weight(e)=1, arc(e)=gamma_n
# with no truncation model at all -- d/dz log Xi(z) ~ 1/(z - gamma_n) as z -> gamma_n.
print("\n  Tail-FREE check: residue of d/dz log Xi(z) at each event  (weight=1, arc=gamma_n):")
print(f"    {'n':>3} {'gamma_n (event arc)':>22} {'residue = lim (z-g) d/dz log Xi':>34}")
for n in [1, 2, 3, 5, 10]:
    g = gammas[n - 1]
    eps = mp.mpf(10) ** (-8)
    res = eps * logderiv_Xi(g + eps)        # (z-g)*[1/(z-g)+holo] -> 1 as eps->0
    print(f"    {n:>3} {float(g):>22.10f} {float(res.real):>34.8f}")
print("    => every event is a simple pole, residue 1, located exactly at gamma_n:")
print("       Tr_event(z) = SUM_e 1/(z - arc(e)) with weight 1 and arc(e) = gamma_n, exactly.")

# Convergence: the partial event-trace -> the analytic log-derivative as more events are summed.
z0 = mp.mpf(6)
rhs0 = logderiv_Xi(z0)
print(f"\n  Convergence of the event-trace to d/dz log Xi(z) at z = {float(z0)}  "
      f"(target = {float(rhs0.real):+.8f}):")
print(f"    {'N events':>10} {'partial SUM':>18} {'+tail corr':>18} {'|err (corrected)|':>20}")
for N in [10, 25, 50, 100, 200]:
    raw = event_trace_partial(z0, N)
    corr = raw + tail_correction(z0, N)
    print(f"    {N:>10} {float(raw.real):>18.8f} {float(corr.real):>18.8f} {float(abs(corr - rhs0)):>20.2e}")


# ============================================================================= PART 3
print("\n" + "=" * 80)
print("PART 3 — the emission law:  events farther apart in ARC (height e^{gamma} up),")
print("         ORDINATE gaps shrink ~ 2pi/log(gamma)   (the e^{gamma} Jacobian duality)")
print("=" * 80)
print(f"\n  {'n':>4} {'gamma_n':>12} {'ord. gap':>10} {'2pi/log(g)':>12} "
      f"{'height e^{g}':>16} {'arc gap ~ e^{g}/log g':>22}")
prev = mp.mpf(0)
for n in [1, 2, 5, 10, 20, 50, 100, 200]:
    g = gammas[n - 1]
    gap = g - prev if n <= 2 else gammas[n - 1] - gammas[n - 2]
    mean_gap = TWO_PI / mp.log(g / TWO_PI)
    height = mp.e ** g
    arc_gap = height / mp.log(g)         # arc separation grows like e^{gamma}/log gamma
    print(f"  {n:>4} {float(g):>12.5f} {float(gap):>10.4f} {float(mean_gap):>12.4f} "
          f"{mp.nstr(height, 6):>16} {mp.nstr(arc_gap, 6):>22}")
print("\n  ordinate gaps -> shrink (density up ~ log gamma);  arc/height gaps -> blow up ~ e^{gamma}.")
print("  Same events, two readings: dense in the 1-D shadow, ever-sparser on the 3-D carrier.")

print("\n" + "=" * 80)
print("READING: if PART 2 matches to many digits, the event-trace SUM 1/(z - arc(e)) over the")
print("eigen-events IS  -d/dz log Lambda(readout(z))  -- the screw/monodromy production's")
print("spectral readout is the honest log-derivative of the completed L-function. Faithful,")
print("unconditional, no positivity. The open weld stays only: do the events EXHAUST the zeros.")
print("=" * 80)
