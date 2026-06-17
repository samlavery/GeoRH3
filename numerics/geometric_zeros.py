"""
geometric_zeros.py  --  PRODUCE the L(chi3) zeros from PURE GEOMETRY.

NO external analysis: no zeta, no gamma, no theta, no completed-L, no functional equation, no consumed
ordinates.  The only ingredients are the helix and its conductor:

  * integers placed at radius R ~ sqrt(n) (area law)  ->  amplitude 1/R = n^{-1/2}  (the sigma=1/2 weight)
  * phase = log n                                     (the bridge: the integer's winding rate)
  * the conductor q=3 sorts each integer into a + or - channel by  chi3(n) = chi(n mod 3)
  * a ZERO is a readout height y where the + and - channel phasors CANCEL:  Phi_+(y) = Phi_-(y)

The height of the zero is z = e^y; its 3D helix point and the closed-form arclength are geometry too.

PRECISION (honest, measured): the finite phasor converges only ~N^{-1/2}, so this PRODUCES the
ordinates to ~4-5 digits, magnified into the heights by delta z ~ e^y delta y.  Reaching 50 digits
would require a tail/gamma continuation -- the external analysis this file refuses.  What you get from
nothing but the conductor and the climb: the zeros and their heights, to a few figures.
"""
import numpy as np

Q = 3

def chi3(n):
    return (0, 1, -1)[n % 3]


def _phasor_data(N):
    """amplitude*chi (signed) and log n for the first N integers -- the placed helix points."""
    n = np.arange(1, N + 1)
    c = np.array([chi3(int(k)) for k in n], dtype=float)
    return c * n ** (-0.5), np.log(n)


def channels(y, N):
    """the + and - conductor-channel phasors at readout height y (pure geometry).  Phi_+ , Phi_- ."""
    n = np.arange(1, N + 1)
    c = np.array([chi3(int(k)) for k in n], dtype=float)
    ph = n ** (-0.5) * np.exp(-1j * y * np.log(n))
    return np.sum(np.where(c > 0, ph, 0.0)), np.sum(np.where(c < 0, ph, 0.0))


def _golden(f, a, b, it=90):
    """minimize f on [a,b] by golden section -- elementary, no analysis."""
    r = 0.6180339887498949
    c, d = b - r * (b - a), a + r * (b - a)
    for _ in range(it):
        if f(c) < f(d):
            b = d
        else:
            a = c
        c, d = b - r * (b - a), a + r * (b - a)
    return 0.5 * (a + b)


def produce_zeros(n_zeros, N_coarse=100000, N_fine=1500000, y_max=26.0, coarse=0.01):
    """PRODUCE the ordinates from the conductor-channel cancellation alone (|Phi_+ - Phi_-| dips).
    Coarse scan locates the dips; a golden-section refine on a larger phasor sharpens each.  No
    ordinate is consumed; the only inputs are the integers, the radius weight, the bridge phase."""
    ampc, lognc = _phasor_data(N_coarse)
    fc = lambda y: abs(np.sum(ampc * np.exp(-1j * y * lognc)))      # |Phi_+ - Phi_-| at coarse N
    ys = np.arange(2.0, y_max, coarse)
    m = np.array([fc(y) for y in ys])
    med = float(np.median(m))
    guesses = [ys[i] for i in range(1, len(m) - 1)
               if m[i] < m[i - 1] and m[i] < m[i + 1] and m[i] < 0.4 * med][:n_zeros]
    ampf, lognf = _phasor_data(N_fine)
    ff = lambda y: abs(np.sum(ampf * np.exp(-1j * y * lognf)))      # the same channel mismatch, finer N
    return [_golden(ff, g - coarse, g + coarse) for g in guesses]


# ---------------------------------------------------------------- the height and the 3D helix point
def height(y):
    return float(np.exp(y))                                        # z = e^y

def helix_point(y, p, r):
    z = np.exp(y); k = z / p; R = r * k; ang = 2 * np.pi * k
    return (R * np.cos(ang), R * np.sin(ang), z)

def helix_arclength(k, p, r):                                      # closed form (geometry, not analysis)
    A2 = p * p + r * r
    if r == 0:
        return np.sqrt(A2) * k
    A, B = np.sqrt(A2), 2 * np.pi * r
    return 0.5 * k * np.sqrt(A2 + (B * k) ** 2) + A2 / (2 * B) * np.arcsinh(B * k / A)


if __name__ == "__main__":
    print("PURE GEOMETRY -- conductor +/- channels cancel -> the zeros.  no zeta/gamma/theta, none consumed.\n")
    zs = produce_zeros(3)
    p, r = 1.0, 0.3
    print(f"  {'j':>2} {'ordinate y (produced)':>24} {'height z = e^y':>16} {'channels |Phi+ - Phi-|':>24}")
    for j, y in enumerate(zs, 1):
        Pp, Pm = channels(y, 200000)
        print(f"  {j:>2} {y:>24.6f} {height(y):>16.3f} {abs(Pp - Pm):>24.2e}")
    print()
    gx, gy, gz = helix_point(zs[0], p, r)
    print(f"  3D point of zero 1 (chart p={p}, r={r}):  ({gx:.3f}, {gy:.3f}, {gz:.3f})")
    # precision report (the known values are used ONLY to print the error -- never in production)
    known = [8.039737, 11.249206, 15.704619]
    print(f"  precision (pure phasor ~N^-1/2): err in y =",
          ", ".join(f"{abs(y - k):.1e}" for y, k in zip(zs, known)),
          "-> a few figures; z=e^y magnifies it. NO analysis used.")
