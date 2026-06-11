"""
radial_step_core.py

The CORE radial-step experiment.  The analytic L is  sum_n chi3(n) n^{-1/2} e^{-i w log n}.
It collapses at the zeros because the PHASE is w*log(n) and the AMPLITUDE is n^{-1/2}.
A genuine blocky helix must MANUFACTURE that phase = w*log(n) and amplitude = n^{-1/2}
from STEPPED geometry -- not put log(n) in by hand.

KEY GEOMETRIC FACT used here (the area law, RULE EIGHT): if integers sit on a cone
with constant ARC spacing and LINEAR radial growth R = A*phi, then arc length
s(phi) ~ (A/2) phi^2, so integer n at arc s_n = n*ds gives phi_n ~ sqrt(n) and
R_n ~ sqrt(n).  The amplitude 1/R_n ~ n^{-1/2} is then EARNED, not imposed.  But the
PHASE the geometry hands you is phi_n ~ sqrt(n), NOT log(n).  So a smooth cone gives
n^{-1/2} but the WRONG phase.  This file builds the stepped fix:

RADIAL-STEP IDEA: make the radius grow GEOMETRICALLY across blocks, R_{k+1} = rho * R_k,
so that the number of integers that fit in loop k (circumference 2pi R_k) is ~ R_k, and
the cumulative count to loop k is ~ rho^k = R_k, i.e. n ~ R_k and loop index k ~ log_rho(n).
Then the HEIGHT (pitch-accumulated) advances by a CONSTANT per loop, so z ~ k ~ log(n).
Using z as the phasor phase gives phase ~ log(n) EARNED from geometric radial stepping.

This is the radial-step blocky helix: each block = one loop, radius steps by factor rho,
the per-loop constant axial rise makes height = log-of-count, and that height drives the
phasor.  We build it as a real 3D solid, hang phasors, and test the collapse at the zeros.
"""
import numpy as np
import mpmath as mp
mp.mp.dps = 30

def chi3(n):
    r = n % 3
    return 1.0 if r == 1 else (-1.0 if r == 2 else 0.0)

def load_zeros(path="lchi3_zeros_1000.txt", k=20):
    g = []
    with open(path) as f:
        for ln in f:
            ln = ln.strip()
            if ln and not ln.startswith("#"):
                g.append(float(ln.split()[1]))
    return np.array(sorted(g))[:k]
GAMMA = load_zeros(k=20)

def L_chi3(s):
    return mp.power(3, -s) * (mp.zeta(s, mp.mpf(1)/3) - mp.zeta(s, mp.mpf(2)/3))


def build_geometric_radial_helix(nloops, rho, base_per_loop, pitch_const):
    """RADIAL-STEP build. Loop k (0-based) has radius R_k = rho^k.  It holds
    m_k = round(base_per_loop * R_k) integers spread evenly around the loop
    (angular spacing 2pi/m_k).  Block boundary = loop boundary.  The axial rise
    is CONSTANT pitch_const per loop, so z_n = pitch_const * (loop index + angle
    fraction).  Returns explicit (x,y,z), phi, R, amp, sign and the per-integer
    height z (the EARNED ~log phase candidate)."""
    xs, ys, zs, phis, Rs, amps, signs, hz = [], [], [], [], [], [], [], []
    n = 0
    running_z = 0.0
    for k in range(nloops):
        R_k = rho ** k
        m_k = max(1, int(round(base_per_loop * R_k)))
        dphi = 2 * np.pi / m_k
        for j in range(m_k):
            n += 1
            ang = j * dphi
            phi_tot = 2 * np.pi * k + ang
            z = running_z + pitch_const * (ang / (2 * np.pi))
            xs.append(R_k * np.cos(ang)); ys.append(R_k * np.sin(ang))
            zs.append(z); phis.append(phi_tot); Rs.append(R_k)
            amps.append(1.0 / np.sqrt(R_k * 1.0))   # amp ~ 1/sqrt(R) ~ n^{-1/2}/... see note
            signs.append(chi3(n))
            hz.append(z)
        running_z += pitch_const
    return (np.array(xs), np.array(ys), np.array(zs), np.array(phis),
            np.array(Rs), np.array(amps), np.array(signs), np.array(hz))


def phasor_resultant(phase, amp, sign, w):
    """REAL phasor vector sum.  Hang unit vector (cos(w*phase),sin(w*phase)),
    weight by chi3*amp, sum the 2D vectors.  Return |resultant| and coherence."""
    a = w * phase
    Vx = np.sum(sign * amp * np.cos(a))
    Vy = np.sum(sign * amp * np.sin(a))
    mag = np.hypot(Vx, Vy)
    denom = np.sum(np.abs(sign) * amp)
    return mag, (mag / denom if denom else 0.0)


def control_L(w, N):
    n = np.arange(1, N + 1)
    s = np.array([chi3(k) for k in n])
    return abs(np.sum(s * n**-0.5 * np.exp(-1j * w * np.log(n))))


if __name__ == "__main__":
    print("=" * 78)
    print("GEOMETRIC RADIAL-STEP HELIX: radius steps by rho per loop -> z ~ log(n)")
    print("=" * 78)

    rho = np.e ** 0.5      # radius multiplies by e^{1/2} per loop
    nloops = 26
    base = 1.0
    pitch = 1.0            # 1 unit of height per loop

    X, Y, Z, PHI, R, AMP, SIGN, HZ = build_geometric_radial_helix(
        nloops, rho, base, pitch)
    Nbuilt = len(X)
    print(f"rho={rho:.4f}  loops={nloops}  built {Nbuilt} integer-points")
    print()
    # Does loop index k = log_rho(n)?  i.e. is z (=k*pitch) proportional to log(n)?
    nidx = np.arange(1, Nbuilt + 1)
    print("--- SAMPLE OF THE BUILT 3D SOLID (radial-step cone) ---")
    print(f"{'n':>5} {'loop':>5} {'phi':>9} {'R':>9} {'z(height)':>10}   (x,y,z)    log(n)")
    seen = {}
    for nn in [1, 2, 3, 5, 10, 30, 100, 300, 1000, 3000]:
        if nn <= Nbuilt:
            i = nn - 1
            loopk = Z[i] / pitch
            print(f"{nn:5d} {loopk:5.2f} {PHI[i]:9.2f} {R[i]:9.3f} {Z[i]:10.4f}  "
                  f"({X[i]:7.2f},{Y[i]:7.2f},{Z[i]:6.2f}) {np.log(nn):6.3f}")
    print()
    # fit z vs log(n)
    m = nidx >= 20
    c = np.polyfit(np.log(nidx[m]), Z[m], 1)
    res = np.std(Z[m] - (c[0]*np.log(nidx[m]) + c[1])) / np.std(Z[m])
    print(f"FIT  z ~ {c[0]:.4f} * log(n) + {c[1]:.4f}   (normalized residual {res:.4f})")
    print(f"  -> height IS proportional to log(n): the EARNED log phase from radial stepping")
    print(f"  -> so use phase = z * (probe), with probe frequency scaled by 1/c[0]")
    print()

    # phasor collapse using the EARNED height z as phase (rescaled so z = log n)
    phase = Z / c[0]    # now phase ~ log(n)
    print("--- PHASOR VECTOR-SUM COLLAPSE at chi3 zeros (phase = earned log-height) ---")
    print(f"{'gamma':>9} {'|resultant|':>12} {'coherence':>10} {'|L control|':>12} {'match?':>7}")
    for g in GAMMA[:10]:
        mag, coh = phasor_resultant(phase, AMP, SIGN, g)
        ctrl = control_L(g, Nbuilt)
        # off-zero reference: midpoint to next zero
        print(f"{g:9.3f} {mag:12.5f} {coh:10.5f} {ctrl:12.5f}")
    print()
    # off-zero probes to check it is NOT collapsing everywhere
    print("--- OFF-ZERO probes (should be LARGE if the object discriminates) ---")
    offs = [9.5, 13.5, 17.0, 22.0]
    for w in offs:
        mag, coh = phasor_resultant(phase, AMP, SIGN, w)
        print(f"w={w:7.3f}  |resultant|={mag:10.5f}  coherence={coh:8.5f}  |L|={control_L(w,Nbuilt):8.4f}")
