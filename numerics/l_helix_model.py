"""
l_helix_model.py  --  high-precision Dirichlet L(s,chi) + helix-geometry chart.

EVALUATORS (high precision):
  * non-principal chi   : HURWITZ-FREE.  completed Lambda via the theta split (incomplete gamma,
                          Riemann's method).  ~12 terms = 50 digits.  matches Hurwitz to ~1e-52.
  * principal chi0 mod q: L = zeta(s) prod_{l|q}(1 - l^{-s}),  with  zeta(s) = eta(s)/(1-2^{1-s}).
  * eta-acceleration    : for 2 not | q,   L = L_eta / (1 - 2^{1-s} chi(2)),
                          L_eta = sum (-1)^{n-1} chi(n) n^{-s}  (a relation, not the evaluator).

ROBUST ZEROS: the completed Lambda(1/2+iy) is REAL on the line (root number +1 for chi3); zeros are
  its SIGN CHANGES -- not root-finding on Im L.

HELIX GEOMETRY (a CHART -- gauge: it does NOT move the ordinates or heights, verified):
  z = e^y ;  k = z/p (loops) ;  R = r*k ;  3D point gamma(y) = ((r/p)e^y cos(2 pi e^y/p),
  (r/p)e^y sin(2 pi e^y/p), e^y) ;  arc spacing Delta = pi/3 ;  closed-form arclength S(k;p,r).

PRECISION HIERARCHY:  precise y_j (theta-Lambda sign changes) -> z_j = e^{y_j} -> 3D point /
  closed-form arclength -> finite phasor DIAGNOSTIC.   delta z ~ e^y delta y, so y_j must be precise.
"""
import mpmath as mp
import numpy as np

mp.mp.dps = 50


# ============================================================ characters
def chi3(n):
    return {0: 0, 1: 1, 2: -1}[n % 3]

def prime_factors(q):
    fs, d, m = [], 2, q
    while d * d <= m:
        if m % d == 0:
            fs.append(d)
            while m % d == 0:
                m //= d
        d += 1
    if m > 1:
        fs.append(m)
    return fs


# ============================================================ non-principal L -- HURWITZ-FREE (theta)
def Lambda_chi3(s, terms=40):
    """completed Lambda(s, chi3) via the theta split (incomplete gamma).  NO Hurwitz zeta.
       Lambda = (3/pi)^{(s+1)/2} sum chi(n) n^{-s} Gamma((s+1)/2, pi n^2/3)
              + (3/pi)^{(2-s)/2} sum chi(n) n^{s-1} Gamma((2-s)/2, pi n^2/3)."""
    A = mp.power(mp.mpf(3) / mp.pi, (s + 1) / 2)
    B = mp.power(mp.mpf(3) / mp.pi, (2 - s) / 2)
    tot = mp.mpc(0)
    for n in range(1, terms + 1):
        c = chi3(n)
        if c == 0:
            continue
        x = mp.pi * n * n / 3
        tot += c * (A * mp.power(n, -s) * mp.gammainc((s + 1) / 2, x)
                    + B * mp.power(n, s - 1) * mp.gammainc((2 - s) / 2, x))
    return tot

def L_chi3(s):
    """L(s,chi3) recovered from the Hurwitz-free completed Lambda by dividing off the gamma factor."""
    return Lambda_chi3(s) / (mp.power(mp.mpf(3) / mp.pi, (s + 1) / 2) * mp.gamma((s + 1) / 2))


# ============================================================ principal character (sec 4)
def L_principal(s, q):
    """L(s, chi0 mod q) = zeta(s) prod_{l | q}(1 - l^{-s}),  with zeta via Dirichlet eta (mp.altzeta)."""
    zeta = mp.altzeta(s) / (1 - mp.power(2, 1 - s))
    return zeta * mp.fprod((1 - mp.power(mp.mpf(l), -s)) for l in prime_factors(q))


# ============================================================ eta-acceleration identity (sec 6)
def L_eta_from_L(s, Lval, chi2):
    """L_eta(s) = (1 - 2^{1-s} chi(2)) L(s,chi)   for 2 not | q.  (relation; degenerates to L if chi(2)=0.)"""
    return (1 - mp.power(2, 1 - s) * chi2) * Lval


# ============================================================ robust zeros (real completed Lambda)
def Lambda_real(y):
    return mp.re(Lambda_chi3(mp.mpf("0.5") + 1j * mp.mpf(y)))

def chi3_zeros(n_zeros, y0="1", step="0.25"):
    out, y = [], mp.mpf(y0)
    prev = Lambda_real(y)
    while len(out) < n_zeros:
        y2 = y + mp.mpf(step)
        cur = Lambda_real(y2)
        if prev * cur < 0:
            out.append(mp.findroot(Lambda_real, (y, y2)))
        prev, y = cur, y2
    return out


# ============================================================ helix geometry (chart -- gauge)
DS = mp.pi / 3                                  # integer arc spacing (chart unit)

def helix_arclength(k, p, r):
    """closed form of S(k)=int_0^k sqrt(p^2+r^2+(2 pi r t)^2) dt  (matches quadrature exactly)."""
    k, p, r = mp.mpf(k), mp.mpf(p), mp.mpf(r)
    A2 = p * p + r * r
    if r == 0:
        return mp.sqrt(A2) * k
    A, B = mp.sqrt(A2), 2 * mp.pi * r
    return mp.mpf("0.5") * k * mp.sqrt(A2 + (B * k) ** 2) + A2 / (2 * B) * mp.asinh(B * k / A)

def helix_point(y, p, r):
    """3D point gamma(y) = ((r/p)e^y cos(2 pi e^y/p), (r/p)e^y sin(2 pi e^y/p), e^y)  (sec 1)."""
    z = mp.e ** mp.mpf(y)
    k = z / mp.mpf(p)
    R = mp.mpf(r) * k
    ang = 2 * mp.pi * k
    return (R * mp.cos(ang), R * mp.sin(ang), z)

def integer_count(y, p, r):
    return helix_arclength(mp.e ** mp.mpf(y) / mp.mpf(p), p, r) / DS

def comp_ratio_check(y, p, r):
    """sec 3 CORRECTED: S(e^y/p; p,r) = int_0^{e^y} sqrt(1+q_r^2+(2 pi (r/p^2) x)^2) dx, q_r=r/p.
       (the document's (2 pi q_r x) drops a factor of p.)  Returns (true_S, corrected_integral)."""
    qr = mp.mpf(r) / mp.mpf(p)
    z = mp.e ** mp.mpf(y)
    true_S = helix_arclength(z / mp.mpf(p), p, r)
    corrected = mp.quad(lambda x: mp.sqrt(1 + qr * qr + (2 * mp.pi * (mp.mpf(r) / mp.mpf(p) ** 2) * x) ** 2), [0, z])
    return true_S, corrected


# ============================================================ finite phasor -- DIAGNOSTIC ONLY
def finite_phasor_sum(y, chi, N=20000, smooth=False):
    n = np.arange(1, N + 1)
    c = np.array([chi(int(k)) for k in n], dtype=float)
    w = np.exp(-n / (N / 3.0)) if smooth else 1.0
    return float(abs(np.sum(c * w * n ** (-0.5) * np.exp(-1j * float(y) * np.log(n)))))


# ============================================================ PRODUCE zeros from GEOMETRY (no consumption)
def zeros_from_geometry(chi, n_zeros, N=100000, y_max=26.0, step=0.01):
    """PRODUCE approximate ordinates from the GEOMETRIC phasor alone -- sweep the height-readout y,
    sum the placed-integer phasors (amplitude n^{-1/2} = 1/radius, phase log n), and take the |.|-dips.
    NO zeros are consumed and NO analytic L is used.  Low precision (finite phasor converges ~N^{-1/2})."""
    n = np.arange(1, N + 1)
    c = np.array([chi(int(k)) for k in n], dtype=float)
    amp, logn = n ** (-0.5), np.log(n)
    ys = np.arange(2.0, y_max, step)
    mag = np.array([abs(np.sum(c * amp * np.exp(-1j * y * logn))) for y in ys])
    med = float(np.median(mag))
    dips = [float(ys[i]) for i in range(1, len(mag) - 1)
            if mag[i] < mag[i - 1] and mag[i] < mag[i + 1] and mag[i] < 0.4 * med]
    return dips[:n_zeros]

def refine_zero(y_guess):
    """refine a GEOMETRIC dip to full precision via the real completed Lambda.  Still consumes no
    zeros: the seed is the geometric dip; the refinement is analytic sign-change root-finding."""
    g = mp.mpf(y_guess)
    return mp.findroot(Lambda_real, (g - mp.mpf("0.15"), g + mp.mpf("0.15")))


# ============================================================ sanity test / demo
if __name__ == "__main__":
    s9 = mp.mpf("0.5") + 1j * mp.mpf("9")
    print("non-principal evaluator: HURWITZ-FREE theta.  Im(Lambda) at y=9:",
          mp.nstr(mp.im(Lambda_chi3(s9)), 3), " (real on the line)")
    print()
    zeros = chi3_zeros(3)
    print("zeros via sign-changes of the real theta-Lambda (no Hurwitz):")
    print(f"  {'j':>2} {'ordinate y_j':>44} {'|L(1/2+iy)|':>13}")
    for j, y in enumerate(zeros, 1):
        print(f"  {j:>2} {mp.nstr(y, 42):>44} {mp.nstr(abs(L_chi3(mp.mpf('0.5') + 1j * y)), 3):>13}")
    print()
    p, r = mp.mpf(1), mp.mpf("0.3")
    print("heights z_j=e^{y_j} and 3D point gamma(y_j)  [chart p,r -- gauge]:")
    for j, y in enumerate(zeros, 1):
        gx, gy, gz = helix_point(y, p, r)
        print(f"  j={j}: z={mp.nstr(gz, 14)}  gamma=({mp.nstr(gx, 6)}, {mp.nstr(gy, 6)}, {mp.nstr(gz, 8)})  N={mp.nstr(integer_count(y, p, r), 6)}")
    print()
    print("principal chi0 mod 12:  L(2, chi0) =", mp.nstr(L_principal(mp.mpf(2), 12), 12),
          " (= zeta(2)(1-1/4)(1-1/9) =", mp.nstr(mp.zeta(2) * mp.mpf(3)/4 * mp.mpf(8)/9, 12), ")")
    s3 = mp.mpf(3)                                       # convergent region -> direct sum is trustworthy
    L_eta_direct = mp.fsum(((-1) ** (n - 1)) * chi3(n) * mp.power(n, -s3) for n in range(1, 30001))
    L_eta_formula = L_eta_from_L(s3, L_chi3(s3), chi3(2))
    print("eta-accel identity (s=3):  |L_eta(direct) - (1-2^{1-s}chi(2))L| =",
          mp.nstr(abs(L_eta_direct - L_eta_formula), 3))
    ts, tc = comp_ratio_check(mp.mpf(3), mp.mpf(2), mp.mpf("0.6"))
    print("sec-3 corrected comp ratio:  true S =", mp.nstr(ts, 10), " corrected integral =", mp.nstr(tc, 10))
    print()
    y1 = zeros[0]
    print("finite phasor DIAGNOSTIC (low precision, contrast only):")
    print(f"  |C_N(y1)| N=20000 = {finite_phasor_sum(y1, chi3, 20000):.5f}   vs |L| truth = {mp.nstr(abs(L_chi3(mp.mpf('0.5')+1j*y1)), 3)}")
