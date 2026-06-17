"""
l_helix_claude.py  --  independent implementation of the high-precision L / helix pipeline.

Saved separately from l_helix_model.py so it can be validated against it.  Run directly:
    python3 l_helix_claude.py
and read the PASS/FAIL suite at the bottom.

Scope (no 3D helix point -- not needed):
  * L(s,chi) closed forms, general Dirichlet character mod q:
      principal      L(s,chi0) = zeta(s) * prod_{ell|q} (1 - ell^{-s})         [+ eta-mode]
      non-principal  L(s,chi)  = q^{-s} sum_{a=1}^q chi(a) zeta(s, a/q)         [Hurwitz; primary]
      eta accel      L_chi^(eta)(s) = sum (-1)^{n-1} chi(n) n^{-s}
                     = (1 - 2^{1-s} chi(2)) L(s,chi)   if 2 does not divide q ; = L if 2|q.
  * zeros on the REAL completed L (Hardy-Z, rotated by the root number) via sign-change bisection.
  * heights z = e^y.  closed-form conical-helix arclength.  pi/3 integer scaling + r/p calibration.
  * finite phasor sum kept ONLY as a diagnostic (raw; smoothing biases minima).

Lessons baked in:
  - the conditionally-convergent finite sum lands the zero at ~N^{-1/2} (low precision, not wrong place);
  - root-find on the REAL completed L, never on Im L / Re L (spurious points);
  - the eta-acceleration identity must be checked with a DIRECT sum -- mp.nsum mishandles the
    period-2q character series and returns a partial-sum artifact;
  - the height e^y over the pi/3 spacing forces an integer floor e^y/(pi/3); the readout "64" is y1^2
    (the old ordinate-as-radius chart), not the geometric count.
"""

import mpmath as mp
from math import gcd

mp.mp.dps = 40                                       # working precision (raise freely)

# --------------------------------------------------------------------------- characters
def prime_factors(n):
    fs, d = [], 2
    while d * d <= n:
        if n % d == 0:
            fs.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        fs.append(n)
    return fs

class DirichletChar:
    def __init__(self, q, values, name=""):
        self.q, self.values, self.name = q, list(values), name
    def __call__(self, n):
        return self.values[n % self.q]
    @property
    def is_principal(self):
        return all((self.values[a] == 1) == (gcd(a, self.q) == 1) for a in range(self.q))
    @property
    def parity(self):                                # 0 even (chi(-1)=1), 1 odd (chi(-1)=-1)
        return 0 if self(self.q - 1) == 1 else 1

def principal_char(q):
    return DirichletChar(q, [1 if gcd(a, q) == 1 else 0 for a in range(q)], f"chi0_mod{q}")

CHI3 = DirichletChar(3, [0, 1, -1], "chi3")          # odd real primitive character mod 3

# --------------------------------------------------------------------------- L evaluators
def L_value(chi, s):
    """Primary exact L(s,chi): principal -> zeta * Euler factors; else Hurwitz conductor sum."""
    s = mp.mpc(s)
    if chi.is_principal:
        out = mp.zeta(s)
        for ell in prime_factors(chi.q):
            out *= (1 - mp.power(ell, -s))
        return out
    return mp.power(chi.q, -s) * mp.fsum(chi(a) * mp.zeta(s, mp.mpf(a) / chi.q)
                                         for a in range(1, chi.q + 1))

def L_eta_principal(chi, s):
    """Independent principal-character path via the Dirichlet eta: eta/(1-2^{1-s}) * Euler factors."""
    assert chi.is_principal
    s = mp.mpc(s)
    out = mp.altzeta(s) / (1 - mp.power(2, 1 - s))   # altzeta = eta
    for ell in prime_factors(chi.q):
        out *= (1 - mp.power(ell, -s))
    return out

def eta_acceleration_factor(chi, s):
    """L_chi^(eta)(s) = factor * L(s,chi);  factor = 1 - 2^{1-s} chi(2)  (=1 when 2|q)."""
    s = mp.mpc(s)
    if chi.q % 2 == 0:
        return mp.mpc(1)
    return 1 - mp.power(2, 1 - s) * chi(2)

def L_eta_series_direct(chi, s, terms=400000):
    """L_chi^(eta)(s) by DIRECT partial summation (use where it converges fast, e.g. Re s > 1)."""
    s = mp.mpc(s)
    return mp.fsum((-1) ** (n - 1) * chi(n) * mp.power(n, -s) for n in range(1, terms))

# --------------------------------------------------------------------------- completed L / zeros
def gauss_sum(chi):
    return mp.fsum(chi(a) * mp.e ** (2j * mp.pi * a / chi.q) for a in range(1, chi.q + 1))

def root_number(chi):
    return gauss_sum(chi) / (1j ** chi.parity * mp.sqrt(chi.q))     # eps, |eps|=1

def completed_L(chi, t):
    s = mp.mpf("0.5") + 1j * mp.mpf(t)
    a = chi.parity
    return mp.power(mp.mpf(chi.q) / mp.pi, (s + a) / 2) * mp.gamma((s + a) / 2) * L_value(chi, s)

def Z(chi, t, eps):
    """Real Hardy-Z surrogate (completed L rotated by eps^{-1/2}); sign changes are the zeros."""
    return mp.re(completed_L(chi, t) / mp.sqrt(eps))

def _bisect(f, lo, hi, tol):
    flo, fhi = f(lo), f(hi)
    if (flo < 0) == (fhi < 0):
        raise ValueError("no sign change in bracket")
    for _ in range(4000):
        if hi - lo < tol:
            break
        mid = (lo + hi) / 2
        fmid = f(mid)
        if fmid == 0:
            return mid
        if (flo < 0) != (fmid < 0):
            hi, fhi = mid, fmid
        else:
            lo, flo = mid, fmid
    return (lo + hi) / 2

def chi_zeros(chi, n_zeros, t_start="1", t_max="120", step="0.2"):
    eps = root_number(chi)
    tol = mp.mpf(10) ** (-(mp.mp.dps - 5))
    t, step, t_max = mp.mpf(t_start), mp.mpf(step), mp.mpf(t_max)
    zt, zeros = Z(chi, t, eps), []
    while t < t_max and len(zeros) < n_zeros:
        t2 = t + step
        z2 = Z(chi, t2, eps)
        if (zt < 0) != (z2 < 0):
            zeros.append(_bisect(lambda u: Z(chi, u, eps), t, t2, tol))
        t, zt = t2, z2
    return zeros

# --------------------------------------------------------------------------- helix geometry (no 3D point)
DELTA = mp.pi / 3                                    # integer spacing on the curve

def helix_arclength(k, p, r):
    """S(k;p,r) = int_0^k sqrt(p^2 + r^2 + (2 pi r t)^2) dt   (closed form)."""
    k, p, r = mp.mpf(k), mp.mpf(p), mp.mpf(r)
    A2 = p * p + r * r
    if r == 0:
        return mp.sqrt(A2) * k
    A, B = mp.sqrt(A2), 2 * mp.pi * r
    return mp.mpf("0.5") * k * mp.sqrt(A2 + (B * k) ** 2) + A2 / (2 * B) * mp.asinh(B * k / A)

def geom_count(y, p, r):                             # N(y) = S(e^y/p; p,r) / Delta
    return helix_arclength(mp.e ** mp.mpf(y) / p, p, r) / DELTA

def geom_floor(y):                                   # rho=0 vertical-climb minimum
    return (mp.e ** mp.mpf(y)) / DELTA

def calibrate_ratio(y1, N_star):
    """One crossing fixes r/p only: solve N_star*Delta = S(e^{y1}; 1, rho).  N_star must exceed floor."""
    z1 = mp.e ** mp.mpf(y1)
    if mp.mpf(N_star) <= geom_floor(y1):
        raise ValueError(f"N_star={N_star} <= floor {mp.nstr(geom_floor(y1), 8)} "
                         f"(height {mp.nstr(z1, 8)} over Delta forces that many integers)")
    target = mp.mpf(N_star) * DELTA
    return _bisect(lambda rho: helix_arclength(z1, 1, rho) - target,
                   mp.mpf("1e-15"), mp.mpf("10"), mp.mpf(10) ** (-(mp.mp.dps - 5)))

# --------------------------------------------------------------------------- finite phasor DIAGNOSTIC
def finite_phasor_abs(chi, y, N=20000, smooth=False):
    import math
    y = float(y)
    S = 0j
    for n in range(1, N + 1):
        c = chi(n)
        if c == 0:
            continue
        w = math.exp(-n / (N / 3)) if smooth else 1.0
        ph = -y * math.log(n)
        S += c * w * n ** (-0.5) * complex(math.cos(ph), math.sin(ph))
    return abs(S)

# =========================================================================== self-validating suite
def _check(name, ok, detail=""):
    print(f"  [{'PASS' if ok else 'FAIL'}] {name}{('  -- ' + detail) if detail else ''}")
    return ok

if __name__ == "__main__":
    print(f"l_helix_claude self-test  [dps = {mp.mp.dps}]")
    tol = mp.mpf(10) ** (-(mp.mp.dps - 8))
    allok = True

    chi0 = principal_char(3)
    sline = mp.mpf("0.5") + 1j * mp.mpf("6.3")

    # 1. principal: zeta*Euler  ==  eta-mode
    d = abs(L_value(chi0, sline) - L_eta_principal(chi0, sline))
    allok &= _check("principal chi0: zeta*Euler == eta-mode", d < tol, f"|diff|={mp.nstr(d,3)}")

    # 2. eta-acceleration identity (DIRECT sum at s=2, where it converges absolutely)
    s2 = mp.mpf(2)
    lhs = L_eta_series_direct(CHI3, s2, 400000)
    rhs = eta_acceleration_factor(CHI3, s2) * L_value(CHI3, s2)
    allok &= _check("chi3 eta-accel: L^eta == (1-2^(1-s)chi(2))L  (s=2, direct)",
                    abs(lhs - rhs) < mp.mpf(10) ** -9, f"|diff|={mp.nstr(abs(lhs-rhs),3)}")

    # 3. completed L is real (chi3 root number +1)
    eps = root_number(CHI3)
    immax = max(abs(mp.im(completed_L(CHI3, t) / mp.sqrt(eps))) for t in (8, 12, 20))
    allok &= _check(f"chi3 completed L real (eps={mp.nstr(eps,4)})", immax < tol, f"max|Im|={mp.nstr(immax,3)}")

    # 4. zeros are TRUE zeros (robust Hardy-Z), and heights z=e^y
    zs = chi_zeros(CHI3, 5, t_max="22")
    resid = max(abs(L_value(CHI3, mp.mpf("0.5") + 1j * y)) for y in zs)
    allok &= _check("chi3 first 5 zeros: |L| ~ 0", resid < mp.mpf(10) ** -(mp.mp.dps - 12),
                    f"max|L|={mp.nstr(resid,3)}")
    print(f"        y1 = {mp.nstr(zs[0], mp.mp.dps - 4)}")
    print(f"        z1 = e^y1 = {mp.nstr(mp.e ** zs[0], 14)}")

    # 5. closed-form arclength == quadrature
    p, r, k = mp.mpf("1.3"), mp.mpf("0.7"), mp.mpf("5")
    q_ = mp.quad(lambda x: mp.sqrt(p * p + r * r + (2 * mp.pi * r * x) ** 2), [0, k])
    allok &= _check("arclength closed form == quadrature", abs(helix_arclength(k, p, r) - q_) < tol)

    # 6. count reconciliation + calibration floor guard
    floor = geom_floor(zs[0])
    y1sq = zs[0] ** 2
    print(f"        count: old-chart y1^2 = {mp.nstr(y1sq,8)}   |   new-chart floor e^y1/Delta = {mp.nstr(floor,8)}")
    guard = False
    try:
        calibrate_ratio(zs[0], 64)
    except ValueError:
        guard = True
    allok &= _check("calibration floor guard rejects sub-floor N* (64)", guard)
    Nstar = int(mp.floor(2 * floor))
    rho = calibrate_ratio(zs[0], Nstar)
    back = geom_count(zs[0], 1, rho)
    allok &= _check(f"calibration solves r/p for feasible N*={Nstar}", abs(back - Nstar) < mp.mpf("1e-6"),
                    f"r/p={mp.nstr(rho,6)}, count back={mp.nstr(back,8)}")

    # 7. finite phasor is a low-precision diagnostic, ~N^{-1/2}
    g2k, g50k = finite_phasor_abs(CHI3, zs[0], 2000), finite_phasor_abs(CHI3, zs[0], 50000)
    allok &= _check("finite phasor diagnostic shrinks ~N^{-1/2}", g50k < g2k,
                    f"N=2000 -> {g2k:.5f}, N=50000 -> {g50k:.5f}")

    print(f"\n  {'ALL CHECKS PASSED' if allok else 'SOME CHECKS FAILED'}")
