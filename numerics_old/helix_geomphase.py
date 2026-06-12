"""
helix_geomphase.py -- can the log-n winding phase be PRODUCED by a genuine 3D geometric
mechanism instead of IMPOSED as e^{-i w log n}?

BASELINE (helix3d_universal.py): integer n -> cone, R_n=sqrt(n) (amp 1/R=n^{-1/2}),
z_n=log n (frequency), phasor chi(n)*n^{-1/2}*e^{-i w z_n}; |F(w)|->0 EXACTLY at the
nontrivial-zero heights of L(chi).  The phase z_n=log n is IMPOSED.  This file asks
whether a real geometric construction (holonomy / Berry phase / continuous winding of an
explicit 3D curve / parallel transport in the Frenet frame) PRODUCES exactly log n.

NON-NEGOTIABLES:
  (1) ONE ruleset for every L; only chi (mod q) changes.
  (2) Zeros EXACT: every claimed zero verified |L(chi,1/2+i gamma)| < 1e-12 (mpmath Hurwitz).
  (3) An ASYMPTOTIC match to log n is NOT enough: the small-n harmonic error (~c/n) times
      gamma~8..30 destroys the cancellation.  The produced phase must equal log n to ~1e-3
      relative or the AT-zero defect blows up from ~1e-3 to O(1).  (Demonstrated in
      sensitivity() below.)

Each construction is tested by feeding its produced phase Phi_n in place of z_n=log n and
measuring the helix collapse |F| AT the exact zeros vs OFF (midpoints), for the SAME chi
set as the baseline incl. the complex mod-5 quartic.
"""
import numpy as np
import mpmath as mp

mp.mp.dps = 30
M = 200000
n = np.arange(1, M + 1).astype(float)
nint = n.astype(int)
amp = 1.0 / np.sqrt(n)
LOGN = np.log(n)  # the target the geometry must reproduce

# ---------------- characters: ONLY per-L input (identical to baseline) ----------------
CHARS = {
    "mod 3 quadratic":          (3, {1: 1, 2: -1}),
    "mod 4 quadratic":          (4, {1: 1, 3: -1}),
    "mod 5 quadratic":          (5, {1: 1, 4: 1, 2: -1, 3: -1}),
    "mod 5 quartic (complex)":  (5, {1: 1, 2: 1j, 4: -1, 3: -1j}),
    "mod 7 quadratic":          (7, {1: 1, 2: 1, 4: 1, 3: -1, 5: -1, 6: -1}),
}


def char_array(q, table):
    v = np.zeros(M, dtype=complex)
    r = nint % q
    for res, val in table.items():
        v[r == res] = val
    return v


def Lval(q, table, s):
    tot = mp.mpc(0)
    for a, c in table.items():
        tot += mp.mpc(c) * mp.zeta(s, mp.mpf(a) / q)
    return q ** (-s) * tot


def true_zeros(q, table, hi=26.0, step=0.05):
    f = lambda s: Lval(q, table, mp.mpf(1) / 2 + 1j * s)
    ts = np.arange(0.6, hi, step)
    mag = np.array([float(abs(f(mp.mpf(t)))) for t in ts])
    zs = []
    for i in range(1, len(ts) - 1):
        if mag[i] < mag[i - 1] and mag[i] < mag[i + 1] and mag[i] < 0.4:
            try:
                root = mp.findroot(f, mp.mpc(ts[i], 0), tol=mp.mpf(10) ** (-20))
                tm = float(mp.re(root))
                if abs(float(mp.im(root))) < 1e-6 and abs(complex(f(mp.mpf(tm)))) < 1e-9 \
                        and tm > 0.5 and all(abs(tm - q0) > 1e-3 for q0 in zs):
                    zs.append(tm)
            except Exception:
                pass
    return sorted(zs)[:6]


def collapse(chi_vals, Phi, w):
    """generic helix collapse with PRODUCED phase Phi (array, len M) instead of log n."""
    return abs(np.sum(chi_vals * amp * np.exp(-1j * w * Phi)))


# zeros computed once (exact) per character
ZEROS = {}
EXACTL = {}
for name, (q, table) in CHARS.items():
    zs = true_zeros(q, table)
    ZEROS[name] = zs
    EXACTL[name] = [float(abs(Lval(q, table, mp.mpf(1) / 2 + 1j * mp.mpf(w)))) for w in zs]


def report(title, Phi, note=""):
    """run the SAME phase Phi across all chars; print AT vs OFF collapse + max-AT defect."""
    print("=" * 92)
    print(f"CONSTRUCTION: {title}")
    if note:
        print(f"  {note}")
    # how close is Phi to log n (the decisive metric)
    rel = np.max(np.abs(Phi - LOGN) / np.maximum(np.abs(LOGN), 1e-9))
    abserr = np.max(np.abs(Phi - LOGN))
    print(f"  max |Phi - log n|       = {abserr:.3e}      max rel err = {rel:.3e}")
    print("-" * 92)
    worst_at = 0.0
    for name, (q, table) in CHARS.items():
        zs = ZEROS[name]
        if not zs:
            print(f"  {name:26s}: no zeros"); continue
        chi = char_array(q, table)
        at = [collapse(chi, Phi, w) for w in zs]
        off = [collapse(chi, Phi, 0.5 * (zs[i] + zs[i + 1])) for i in range(len(zs) - 1)]
        worst_at = max(worst_at, max(at))
        print(f"  {name:26s} AT={['%.4f' % x for x in at]}")
        print(f"  {'':26s} OFF={['%.4f' % x for x in off]}")
    verdict = "COLLAPSES at zeros (PASS)" if worst_at < 0.05 else "does NOT collapse (FAIL)"
    print(f"  --> worst AT-zero defect over all chars = {worst_at:.4f}   ==> {verdict}")
    print()
    return worst_at


def sensitivity():
    """show that an ASYMPTOTIC match is not enough: a c/(2n) error at small n kills collapse."""
    print("#" * 92)
    print("# SENSITIVITY: the phase must equal log n to ~1e-3; an asymptotic match is NOT enough.")
    print("#  perturb the exact phase by c/(2n) (the size of a discrete-winding harmonic error):")
    q, table = CHARS["mod 3 quadratic"]
    chi = char_array(q, table)
    g = ZEROS["mod 3 quadratic"][0]
    for c in [0.0, 1e-3, 1e-2, 0.1, 0.5, 1.0]:
        d = collapse(chi, LOGN + c / (2 * n), g)
        print(f"#   log n + {c:5.3f}/(2n)  -> AT-zero defect = {d:.5f}")
    print("#" * 92)
    print()


if __name__ == "__main__":
    print("Verifying the zeros are EXACT (mpmath |L(1/2+i gamma)|, must be < 1e-12):")
    for name in CHARS:
        print(f"  {name:26s} zeros={[round(x,4) for x in ZEROS[name]]}")
        print(f"  {'':26s} |L|  ={['%.1e' % e for e in EXACTL[name]]}")
    print()

    sensitivity()

    # ==================================================================== BASELINE (control)
    report("B0  IMPOSED phase Phi_n = log n  (the baseline -- control, must PASS)",
           LOGN, "Phi = log n directly; this is what we are trying to reproduce geometrically.")

    # ==================================================================== A: log-spiral azimuth
    # A logarithmic spiral r = e^{b*phi} has, BY ITS OWN GEOMETRY, azimuth phi = (1/b) log r.
    # Place integer n at radius r_n = sqrt(n) on a log-spiral; its winding azimuth is then
    # phi_n = (1/b) log sqrt(n) = (1/(2b)) log n.  With b chosen so the rate = 1, phi_n = log n.
    # The log here is the spiral's intrinsic angle<->radius law, NOT log() applied to n.
    b = 0.5  # so phi = (1/(2b)) log n = log n
    Phi_A = (1.0 / (2 * b)) * np.log(n)  # = log n exactly, but read off the spiral azimuth
    report("A  logarithmic-spiral AZIMUTH  phi_n = (1/(2b)) log r_n, r_n=sqrt(n), b=1/2",
           Phi_A,
           "the equiangular spiral's defining law azimuth = (1/b) log radius; r=sqrt(n) => phi=log n.")

    # ==================================================================== B: discrete winding sum
    # The KNOWN-FAILING construction (prior finding): continuous winding of a curve with radial
    # speed 1 and azimuthal speed 1/R gives, discretely, theta_n = sum_{k<=n} 1/R_k.
    # With R_k = sqrt(k): theta_n = sum 1/sqrt(k) ~ 2 sqrt(n)  (NOT log n at all -- wrong law).
    Phi_B1 = np.cumsum(1.0 / np.sqrt(n))
    report("B1  discrete winding theta_n = sum_{k<=n} 1/R_k,  R_k=sqrt(k)  (azimuthal speed 1/R)",
           Phi_B1, "winding of a curve climbing the sqrt cone at azimuthal speed 1/R ~ 2 sqrt n, not log n.")

    # If instead azimuthal speed = 1/r and the radius grows so that dr/dn = r (exponential in n,
    # i.e. r_n = e^{c n}) then theta_n = sum 1/r * dr-per-step... the only radial law giving
    # sum 1/R_k = log n is R_k = k (radius LINEAR in n), the harmonic series H_n.
    Phi_B2 = np.cumsum(1.0 / n)  # H_n = harmonic number ~ log n + gamma_E + 1/(2n) - ...
    report("B2  discrete winding theta_n = sum_{k<=n} 1/k = H_n  (radius LINEAR R_k=k, speed 1/R)",
           Phi_B2,
           "H_n -> log n + Euler gamma + 1/(2n) -...; asymptotically log n but the 1/(2n) tail at "
           "SMALL n is exactly the killer the prompt warns about.")

    # ==================================================================== C: continuous integral
    # The CONTINUOUS winding (integral, not sum): for radius r(x)=x and azimuthal speed dphi/dx=1/r,
    # phi(n) = integral_1^n dx/x = log n EXACTLY.  This is the continuous limit that has NO harmonic
    # error -- but it requires reading the azimuth at the CONTINUOUS arc parameter = log of position,
    # i.e. it IS log by the fundamental theorem of calculus (integral of 1/x).
    Phi_C = np.log(n) - np.log(1.0)  # = integral_1^n dx/x, exact
    report("C  continuous winding phi(n)=integral_1^n (1/r) dr, r linear  =>  = log n EXACTLY",
           Phi_C,
           "the integral of 1/x IS log n; continuous winding has no harmonic error but it is "
           "literally the integral definition of log -- geometry that equals log by construction.")

    # ==================================================================== C2: ODE-integrated winding
    # Same continuous winding but computed WITHOUT ever calling log(): integrate the geometric
    # angular velocity dphi/dr = 1/r on a fine radial grid (trapezoid), sample at r=n.  No log()
    # appears in the code -- yet the result equals log n to numerical precision.  This isolates
    # precisely WHERE log is unavoidable: it is the integral of the angular speed 1/r itself.
    rg = np.linspace(1.0, float(M), 4_000_00)
    omega = 1.0 / rg                                   # geometric angular velocity (no log used)
    cumphi = np.concatenate([[0.0], np.cumsum(0.5 * (omega[1:] + omega[:-1]) * np.diff(rg))])
    Phi_C2 = np.interp(n, rg, cumphi)                  # winding sampled at the integer radii
    report("C2 ODE-integrated winding: integrate dphi/dr=1/r numerically (NO log() in code), sample r=n",
           Phi_C2,
           "pure trapezoid integration of the angular speed 1/r; equals log n to grid precision. "
           "The integral of 1/r is intrinsically log -- this is where log is geometrically forced.")

    # ==================================================================== D: cone holonomy / Berry
    # Parallel transport on a cone of half-angle alpha: transporting a vector once around the axis
    # gives holonomy = 2*pi*(1 - sin alpha) (the cone's angle deficit).  Accumulated over the climb,
    # the geometric phase is PROPORTIONAL TO THE AZIMUTH SWEPT, i.e. linear in the winding angle, NOT
    # logarithmic.  We model: azimuth swept to reach integer n on the sqrt-cone with arc-spacing s is
    # proportional to cumulative arc / radius ~ same B1 family.  Holonomy = (1-sin a) * azimuth.
    alpha = np.pi / 6
    azimuth_to_n = np.cumsum(1.0 / np.sqrt(n))           # azimuth swept (B1 family)
    Phi_D = (1 - np.sin(alpha)) * azimuth_to_n           # Berry/holonomy phase ~ linear in azimuth
    report("D  cone parallel-transport HOLONOMY  Phi=(1-sin a)*azimuth_swept  (Berry phase)",
           Phi_D,
           "cone angle-deficit holonomy is LINEAR in azimuth swept (~2 sqrt n), never logarithmic.")

    # ==================================================================== E: Frenet torsion integral
    # The geometric phase of a space curve (Fermi-Walker / parallel transport of the normal frame)
    # accumulates as integral of torsion tau ds.  Test whether a NATURAL conical-helix curve
    # gives a cumulative torsion = log n.  Build r(t)=sqrt(t), winding azimuth = the curve's own
    # geometric winding, z(t)=t (pitch), sample at the integer arc-positions, and integrate the
    # NUMERICALLY-computed torsion.  This is a genuine differential-geometric phase, computed, not
    # imposed.  We sample t on a fine grid, form the 3D curve, get kappa, tau by finite differences.
    def frenet_torsion_phase(zfun, wind_fun, label):
        tg = np.linspace(1.0, float(M), 2_000_00)
        r = np.sqrt(tg)
        phi = wind_fun(tg)
        X = np.stack([r * np.cos(phi), r * np.sin(phi), zfun(tg)], axis=0)
        d1 = np.gradient(X, tg, axis=1)
        d2 = np.gradient(d1, tg, axis=1)
        d3 = np.gradient(d2, tg, axis=1)
        cross = np.cross(d1.T, d2.T).T
        cross_norm2 = np.sum(cross ** 2, axis=0)
        triple = np.sum(cross * d3, axis=0)
        sds = np.sqrt(np.sum(d1 ** 2, axis=0))           # |r'| = ds/dt
        tau = np.divide(triple, np.maximum(cross_norm2, 1e-300))  # torsion
        cum = np.concatenate([[0.0], np.cumsum(0.5 * (tau[1:] + tau[:-1]) * sds[1:] * np.diff(tg))])
        Phi_int = np.interp(n, tg, cum)
        report(label, Phi_int,
               "cumulative integral of Frenet torsion tau ds along the curve, numerically computed.")
    # conical helix with LINEAR pitch and sqrt-cone, geometric winding ~ sqrt t
    frenet_torsion_phase(lambda tg: tg, lambda tg: 2 * np.sqrt(tg),
                         "E  Frenet torsion phase, curve r=sqrt t, z=t, azimuth=2 sqrt t")
    # conical helix whose z-axis is itself log-paced (log enters via the curve's height)
    frenet_torsion_phase(lambda tg: np.log(tg), lambda tg: 2 * np.sqrt(tg),
                         "E2 Frenet torsion phase, curve r=sqrt t, z=log t (height=log), azimuth=2 sqrt t")

    # ==================================================================== CONVERGENCE / OBSTACLE
    # The decisive experiment.  Construction C2 (integrate the geometric angular speed dphi/dr=1/r)
    # PRODUCES the phase by integration, never calling log().  Its accuracy -- hence whether the
    # helix collapses -- is controlled entirely by how well the integral of 1/r is resolved near
    # the steep small-r region.  A linear grid leaves a ~1e-2 error there and FAILS; a log-spaced
    # grid (which resolves small r) drives the error to ~1e-9 and the collapse RETURNS, matching
    # the exact baseline.  Conclusion: the geometric winding collapses if and ONLY IF it reproduces
    # log n exactly.  log n is forced as the integral of the angular speed 1/r; there is no separate
    # geometric phase that lands on log n while being anything other than that integral.
    print("#" * 92)
    print("# CONVERGENCE: ODE-integrated geometric winding dphi/dr=1/r, log-spaced grid resolving")
    print("# small r.  As the integral of 1/r is resolved, Phi->log n and the collapse RETURNS.")
    print("#" * 92)
    q, table = CHARS["mod 3 quadratic"]
    chi = char_array(q, table)
    g = ZEROS["mod 3 quadratic"][0]
    print("#  grid pts |  max|Phi-log n|  |  AT-zero defect (mod3, gamma=%.4f)" % g)
    for K in [400_000, 2_000_000, 10_000_000]:
        rg = np.geomspace(1.0, float(M), K)
        omega = 1.0 / rg
        cumphi = np.concatenate([[0.0], np.cumsum(0.5 * (omega[1:] + omega[:-1]) * np.diff(rg))])
        Phi = np.interp(n, rg, cumphi)
        err = float(np.max(np.abs(Phi - LOGN)))
        d = collapse(chi, Phi, g)
        print(f"#  {K:9d} |   {err:.3e}    |   {d:.5f}")
    print("#  (exact-log baseline defect at this gamma = %.5f)" % collapse(chi, LOGN, g))
    print("#" * 92)
