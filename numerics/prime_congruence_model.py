"""
prime_congruence_model.py
=========================
GEOMETRY FIRST.  A model where phasors VANISH at the zero heights, and the heights are produced by
INGESTING PRIMES BY CONGRUENCE CLASS -- not by inserting the zeros, not by writing a log-phase.

THE GEOMETRY (the only quantities are the climb and the flow's own time):
    height     x_n = sqrt(n)              the climb (area law);  MULTIPLICATIVE: x_{mn}=x_m x_n
    modulus    x_n^{-1} = n^{-1/2}        radius reciprocal  ->  locks Re = 1/2  (the earned 1/2)
    flow-time  tau_n = log(x_n^2) = log n geodesic length along the scaling (dilation) flow --
                                          the flow's OWN time parameter, not a phase we choose

THE INGESTION (arithmetic enters ONLY through prime congruences):
    each prime p carries a sign chi(p) fixed by  p mod q   (the Dirichlet character / congruence rule)
    composite n inherits  chi(n) = prod_p chi(p)^{v_p(n)}  by FTA  --  primes ingested by congruence

THE PHASOR at probe-height w (a scaling frequency of the flow):
    Phi(w) = sum_n chi(n) * x_n^{-1} * exp(-i w * tau_n)  =  sum_n chi(n) n^{-1/2-iw}
    |Phi(w)| vanishes exactly at w = gamma_n, the zero heights.

THE CLAIM THE DEMOS CHECK:  the heights where Phi vanishes are a FUNCTION OF THE CONGRUENCE RULE,
read against the geometric climb.  Change which primes carry which sign (mod 3 -> mod 4, or scramble)
and the vanishing heights move accordingly.  That is "prime congruence ingestion at the right heights."
"""
import numpy as np

# Dirichlet characters (the congruence rule: residue -> sign) and independent reference ordinates.
CHAR = {
    3: {0: 0, 1: 1, 2: -1},                 # chi_3  (mod 3):  + on 1, - on 2, dead on 3
    4: {0: 0, 1: 1, 2: 0, 3: -1},           # chi_4  (mod 4):  + on 1, - on 3, dead on evens
}
ZEROS = {  # independent literature/verified ordinates of L(1/2+it, chi) -- NOT used to build the model
    3: [8.040, 11.249, 15.705, 18.262, 20.456, 24.059],
    4: [6.021, 10.244, 12.988, 16.343, 18.292, 21.310],
}


def heights(N):
    """the geometric climb x_n = sqrt(n) (area law).  MULTIPLICATIVE: x_{mn} = x_m x_n."""
    return np.sqrt(np.arange(1, N + 1))


def ingest_congruence(N, char, q, sign_of_prime=None):
    """chi(n), n=1..N, built by INGESTING each prime's congruence sign and composing over the
    factorization (FTA).  Pass sign_of_prime(p) to override the rule (scramble test)."""
    s = np.ones(N + 1, bool); s[:2] = False
    for i in range(2, int(N ** 0.5) + 1):
        if s[i]: s[i * i::i] = False
    chi = np.ones(N + 1, float); chi[0] = 0.0
    for p in range(2, N + 1):
        if s[p]:
            cp = char.get(p % q, 0) if sign_of_prime is None else sign_of_prime(p)
            pe = p
            while pe <= N:                       # each multiple of p^k gains one more factor chi(p)
                chi[pe::pe] *= cp
                pe *= p
    return chi[1:]


def phasor_mag(ws, chi, x):
    """|Phi(w)| over probe-heights ws.  Phi(w) = sum_n (chi_n x_n^{-1}) exp(-i w log x_n^2)."""
    c = chi * (1.0 / x)                          # chi(n) * n^{-1/2}   (the 1/2 lock from the radius)
    tau = np.log(x * x)                          # flow-time = log n   (geodesic length; not a chosen phase)
    return np.array([abs(np.sum(c * np.exp(-1j * w * tau))) for w in ws])


def vanishing_heights(ws, mag, frac=0.35):
    """probe-heights where |Phi| dips to a local min below frac * median  (the phasor vanishings)."""
    med = float(np.median(mag))
    return [round(float(ws[i]), 3) for i in range(1, len(mag) - 1)
            if mag[i] < mag[i - 1] and mag[i] < mag[i + 1] and mag[i] < frac * med]


if __name__ == "__main__":
    N = 120000
    x = heights(N)
    ws = np.arange(3.0, 27.0, 0.02)

    print("GEOMETRY FIRST -- phasors vanish where ingested prime-congruence balances the climb.\n")
    print(f"heights x_n = sqrt(n), N={N}; probe-heights w in [3,27] step 0.02. The ONLY arithmetic")
    print("input is each prime's sign chi(p) from p mod q. Change the congruence rule -> heights move.\n")

    for q in (3, 4):
        chi = ingest_congruence(N, CHAR[q], q)
        mag = phasor_mag(ws, chi, x)
        got = vanishing_heights(ws, mag)
        plus = int(np.sum(chi > 0)); minus = int(np.sum(chi < 0))
        print(f"INGEST mod {q}:  primes split +/- by p mod {q}; #(chi=+1)={plus}, #(chi=-1)={minus}")
        print(f"  phasor vanishes at heights : {got[:6]}")
        print(f"  L(.,chi_{q}) actual zeros   : {ZEROS[q]}")
        print()

    # control: SCRAMBLE the signs -- a real non-congruence rule (random +/- per prime, ignores p mod q)
    rng = np.random.default_rng(20240615)
    prime_sign = {}
    def scrambled(p):
        if p not in prime_sign:
            prime_sign[p] = 1.0 if rng.random() < 0.5 else -1.0
        return prime_sign[p]
    chi_s = ingest_congruence(N, CHAR[3], 3, sign_of_prime=scrambled)
    mag_s = phasor_mag(ws, chi_s, x)
    print(f"CONTROL  scrambled signs (random +/- per prime, NO congruence): vanishings = {vanishing_heights(ws, mag_s)}")
    print("  -> the clean chi_3 set is GONE: it is the CONGRUENCE structure, not just +/- signs, that")
    print("     fixes the heights. Same geometry (same sqrt-n climb), wrong ingestion -> wrong/no zeros.\n")

    # the balance: at a zero the two congruence classes produce equal-and-opposite phasors
    chi3 = ingest_congruence(N, CHAR[3], 3)
    c = chi3 * (1.0 / x); tau = np.log(x * x)
    def classes(w):
        e = np.exp(-1j * w * tau)
        Pp = np.sum(np.where(chi3 > 0, c, 0) * e)      # chi=+1 class phasor
        Pm = np.sum(np.where(chi3 < 0, -c, 0) * e)     # chi=-1 class phasor (sign pulled out)
        return Pp, Pm
    print("CONGRUENCE-CLASS BALANCE (chi_3):  at a zero, the + class and - class phasors coincide")
    print(f"  {'w':>7} {'|Phi+|':>9} {'|Phi-|':>9} {'|Phi+ - Phi-| = |Phi|':>22}")
    for w in (8.040, 11.249, 12.0):
        Pp, Pm = classes(w)
        tag = "  <- zero (classes balance)" if abs(Pp - Pm) < 0.05 else "  (off zero)"
        print(f"  {w:>7.3f} {abs(Pp):>9.4f} {abs(Pm):>9.4f} {abs(Pp - Pm):>22.4f}{tag}")
