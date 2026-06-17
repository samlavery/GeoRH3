"""
High-precision L/helix validator.

This file separates three jobs that were previously mixed:

1. L(s, chi3) is evaluated by the Hurwitz closed form.
2. The conical helix arclength is evaluated by its closed form.
3. A finite phasor sum is kept only as a diagnostic; it is not the
   high-precision L-function evaluator.

Coordinate convention:

    channel ordinate:  y
    physical source height:  z = exp(y)
    conical helix:           z = p*k, R = r*k

Thus k = exp(y)/p.  If the old source radius scale is meant instead, use
it only as a diagnostic; the 3D source height in this model is z = exp(y).
"""

from __future__ import annotations

import mpmath as mp

mp.mp.dps = 80


def prime_divisors(n: int) -> list[int]:
    """Prime divisors of a positive integer."""
    out: list[int] = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        out.append(n)
    return out


def eta(s: mp.mpc) -> mp.mpc:
    """Dirichlet eta by the analytic continuation eta=(1-2^(1-s))*zeta."""
    return (1 - mp.power(2, 1 - s)) * mp.zeta(s)


def principal_L(s: mp.mpc, q: int) -> mp.mpc:
    """Principal-character L-function modulo q."""
    value = mp.zeta(s)
    for ell in prime_divisors(q):
        value *= 1 - mp.power(ell, -s)
    return value


def principal_L_via_eta(s: mp.mpc, q: int) -> mp.mpc:
    """Principal-character L-function using eta for the zeta factor."""
    value = eta(s) / (1 - mp.power(2, 1 - s))
    for ell in prime_divisors(q):
        value *= 1 - mp.power(ell, -s)
    return value


def principal_eta_coprime_filter(s: mp.mpc, q: int) -> mp.mpc:
    """Alternating coprime-filter series continued in closed form.

    This is sum_{(n,q)=1} (-1)^(n-1) n^(-s), continued analytically.
    It equals (1-2^(1-s))*L(s, chi0) when q is odd, and equals L(s, chi0)
    when q is even.
    """
    lval = principal_L(s, q)
    if q % 2 == 0:
        return lval
    return (1 - mp.power(2, 1 - s)) * lval


def L_hurwitz(s: mp.mpc, q: int, chi_values: list[complex | int | float]) -> mp.mpc:
    """Dirichlet L(s, chi) by finite Hurwitz-zeta conductor decomposition.

    chi_values is indexed by residue: chi_values[a % q].
    """
    if len(chi_values) != q:
        raise ValueError("chi_values must have length q and be indexed by residues modulo q")
    total = mp.mpc(0)
    for a in range(1, q + 1):
        total += chi_values[a % q] * mp.zeta(s, mp.mpf(a) / q)
    return mp.power(q, -s) * total


def eta_acceleration_factor(s: mp.mpc, q: int, chi2: complex | int | float) -> mp.mpc:
    """Factor relating alternating L_chi^(eta) to L(s,chi).

    If 2 divides q, then chi(2)=0 for a primitive character and the factor is 1.
    Otherwise L_chi^(eta)(s) = (1 - 2^(1-s) chi(2)) L(s, chi).
    """
    if q % 2 == 0:
        return mp.mpc(1)
    return 1 - mp.power(2, 1 - s) * chi2


def chi3(n: int) -> int:
    """Primitive real character modulo 3."""
    r = n % 3
    if r == 1:
        return 1
    if r == 2:
        return -1
    return 0


def L_chi3(s: mp.mpc) -> mp.mpc:
    """Analytic continuation of L(s, chi3) by the Hurwitz zeta closed form."""
    return L_hurwitz(s, 3, [0, 1, -1])


def completed_L_chi3_on_line(y: mp.mpf) -> mp.mpc:
    """Completed odd primitive chi3 L-function on s = 1/2 + i y.

    For chi3 the root number is +1, so this value is real on the critical
    line up to numerical noise.
    """
    s = mp.mpf("0.5") + 1j * mp.mpf(y)
    return mp.power(3 / mp.pi, (s + 1) / 2) * mp.gamma((s + 1) / 2) * L_chi3(s)


def hardy_chi3(y: mp.mpf) -> mp.mpf:
    """Real-valued completed/rotated evaluator for zeros on the line."""
    return mp.re(completed_L_chi3_on_line(y))


def refine_chi3_zero(y_guess: str | float | mp.mpf) -> mp.mpf:
    """Refine a chi3 zero near y_guess using the real completed evaluator."""
    y0 = mp.mpf(y_guess)
    return mp.findroot(hardy_chi3, (y0 - mp.mpf("0.05"), y0 + mp.mpf("0.05")))


def helix_arclength(k: mp.mpf, p: mp.mpf, r: mp.mpf) -> mp.mpf:
    """Closed-form arclength for z=p*k, R=r*k, angle=2*pi*k."""
    k = mp.mpf(k)
    p = mp.mpf(p)
    r = mp.mpf(r)
    a2 = p * p + r * r
    if r == 0:
        return mp.sqrt(a2) * k
    a = mp.sqrt(a2)
    b = 2 * mp.pi * r
    return (
        mp.mpf("0.5") * k * mp.sqrt(a2 + (b * k) ** 2)
        + a2 / (2 * b) * mp.asinh(b * k / a)
    )


def arclength_to_exp_height(y: mp.mpf, p: mp.mpf, r: mp.mpf) -> mp.mpf:
    """Arclength from source height z=0 to z=exp(y)."""
    y = mp.mpf(y)
    p = mp.mpf(p)
    return helix_arclength(mp.e**y / p, p, r)


def integer_count_from_arclength(length: mp.mpf, unit: mp.mpf = mp.pi / 3) -> mp.mpf:
    """Continuous integer-unit count S/unit."""
    return mp.mpf(length) / mp.mpf(unit)


def count_at_exp_height(y: mp.mpf, p: mp.mpf, r: mp.mpf, unit: mp.mpf = mp.pi / 3) -> mp.mpf:
    return integer_count_from_arclength(arclength_to_exp_height(y, p, r), unit)


def calibrate_alpha_for_event(
    y: mp.mpf,
    target_count: mp.mpf,
    p: mp.mpf = 1,
    unit: mp.mpf = mp.pi / 3,
    guess: mp.mpf = mp.mpf("0.01"),
) -> mp.mpf:
    """Solve for alpha=r/p so count_at_exp_height(y,p,alpha*p)=target_count.

    A solution exists only when target_count*unit >= exp(y), since every
    conical helix path has arclength at least the vertical distance exp(y).
    """
    y = mp.mpf(y)
    p = mp.mpf(p)
    target_length = mp.mpf(target_count) * mp.mpf(unit)
    min_length = mp.e**y
    if target_length < min_length:
        raise ValueError(
            "target count is below the vertical-length lower bound: "
            f"target_length={mp.nstr(target_length, 30)}, "
            f"exp(y)={mp.nstr(min_length, 30)}"
        )

    def f(alpha: mp.mpf) -> mp.mpf:
        return arclength_to_exp_height(y, p, alpha * p) - target_length

    return mp.findroot(f, guess)


def finite_phasor_sum(y: mp.mpf, n_terms: int = 20000, smooth: bool = False) -> mp.mpc:
    """Diagnostic finite phasor sum, not the L-function evaluator."""
    y = mp.mpf(y)
    total = mp.mpc(0)
    scale = mp.mpf(n_terms) / 3
    for n in range(1, n_terms + 1):
        c = chi3(n)
        if c == 0:
            continue
        w = mp.mpf(c) * mp.power(n, -mp.mpf("0.5")) * mp.e ** (-1j * y * mp.log(n))
        if smooth:
            w *= mp.e ** (-mp.mpf(n) / scale)
        total += w
    return total


def chi3_first_zero_report() -> dict[str, mp.mpf | mp.mpc]:
    y1 = refine_chi3_zero("8.04")
    lval = L_chi3(mp.mpf("0.5") + 1j * y1)
    z3 = mp.e**y1
    return {
        "y1": y1,
        "z3=exp(y1)": z3,
        "log(z3)": mp.log(z3),
        "|L|": abs(lval),
        "min_arclength_count": z3 / (mp.pi / 3),
    }


if __name__ == "__main__":
    report = chi3_first_zero_report()
    for key, value in report.items():
        print(f"{key}: {mp.nstr(value, 60)}")
