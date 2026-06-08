"""
helixlib_logfree.py — log-free helix source construction.

Core discipline:
  - No np.log / math.log in source construction.
  - Multiplication -> addition comes from FTA:
        Θ(n) = Σ_{p^a || n} a Θ(p)
  - Linear radial law:
        R(k) = e^mode * k
  - Integers are placed by physical arc spacing:
        arc(n) = n * U
  - Character is a weight/fibre, not the coordinate itself.
  - This library builds the source geometry and Gram objects.
  - It does not try to recover zero ordinates by a log/Mellin scan.

Use a separate analytic-shadow file if you want numerical comparison to L-zero ordinates.
"""

import math
import numpy as np


# ---------------------------------------------------------------------
# Characters
# ---------------------------------------------------------------------

class Character:
    """Finite Dirichlet character table."""

    def __init__(self, modulus, values, name, parity):
        self.q = int(modulus)
        self.values = {int(a): complex(v) for a, v in values.items()}
        self.name = str(name)
        self.parity = int(parity)

    def chi(self, n):
        n = np.atleast_1d(np.asarray(n)).astype(np.int64)
        r = np.mod(n, self.q)
        return np.array([self.values[int(x)] for x in r], dtype=complex)

    def __repr__(self):
        vals = [self.values[a] for a in range(self.q)]
        return f"<Character {self.name}: q={self.q}, parity={self.parity}, values={vals}>"

    @staticmethod
    def zeta():
        return Character(1, {0: 1.0}, "zeta trivial", parity=0)


def chi_zeta():
    return Character.zeta()


def chi3():
    return Character(3, {0: 0.0, 1: 1.0, 2: -1.0}, "chi3 mod 3", parity=1)


def chi4():
    return Character(4, {0: 0.0, 1: 1.0, 2: 0.0, 3: -1.0}, "chi4 mod 4", parity=1)


def chi8():
    return Character(
        8,
        {0: 0.0, 1: 1.0, 2: 0.0, 3: -1.0, 4: 0.0, 5: -1.0, 6: 0.0, 7: 1.0},
        "chi8 mod 8",
        parity=0,
    )


# ---------------------------------------------------------------------
# Channel geometry
# ---------------------------------------------------------------------

_HELIX_GEOMETRY = {
    "zeta trivial": (6, 3),   # U = pi/6, radial slope e^3
    "chi3 mod 3":   (3, 6),   # U = pi/3, radial slope e^6
    "chi4 mod 4":   (2, 8),   # U = pi/2, radial slope e^8
    "chi8 mod 8":   (2, 8),   # U = pi/2, radial slope e^8
}


def helix_geometry(character):
    if character.name not in _HELIX_GEOMETRY:
        raise KeyError(f"geometry for {character.name!r} not pinned")
    return _HELIX_GEOMETRY[character.name]


class Channel:
    def __init__(self, character):
        self.character = character
        helix_unit, mode = helix_geometry(character)
        self.helixUnit = int(helix_unit)
        self.mode = int(mode)
        self.name = f"{character.name} (U=pi/{helix_unit}, e^{mode})"

    @property
    def U(self):
        return math.pi / self.helixUnit

    @property
    def slope(self):
        return math.exp(self.mode)

    def loop_radius(self, k):
        return self.slope * np.asarray(k, dtype=float)

    def height(self, turns):
        return self.U * np.asarray(turns, dtype=float)

    def prime_angle(self, p):
        """
        Log-free prime generator angle.

        This is geometric/fibre data, not log(p).
        """
        p = int(p)

        if self.character.name == "zeta trivial":
            return (math.pi / self.helixUnit) * (p % (2 * self.helixUnit))

        if self.character.name == "chi3 mod 3":
            return (math.pi / 3.0) * (p % 6)

        if self.character.name in ("chi4 mod 4", "chi8 mod 8"):
            return (math.pi / 2.0) * (p % 8)

        raise KeyError(f"prime_angle not defined for {self.character.name}")

    def describe(self):
        return (
            f"{self.name}\n"
            f"    U            = pi/{self.helixUnit} = {self.U:.6f}\n"
            f"    radial slope = e^{self.mode} = {self.slope:.6f}\n"
            f"    radial law   = R(k)=e^{self.mode}*k, linear\n"
            f"    character    = {self.character!r}"
        )


def channel_A():
    return Channel(chi_zeta())


def channel_B():
    return Channel(chi3())


def channel_C():
    return Channel(chi4())


def channel_D():
    return Channel(chi8())


# ---------------------------------------------------------------------
# Arithmetic helpers
# ---------------------------------------------------------------------

def primes_upto(N):
    N = int(N)
    if N < 2:
        return np.array([], dtype=np.int64)

    sieve = np.ones(N + 1, dtype=bool)
    sieve[:2] = False

    for i in range(2, int(N**0.5) + 1):
        if sieve[i]:
            sieve[i * i :: i] = False

    return np.nonzero(sieve)[0].astype(np.int64)


def smallest_prime_factors(N):
    N = int(N)
    spf = np.zeros(N + 1, dtype=np.int64)

    for i in range(2, N + 1):
        if spf[i] == 0:
            spf[i] = i
            if i * i <= N:
                for j in range(i * i, N + 1, i):
                    if spf[j] == 0:
                        spf[j] = i

    return spf


def prime_power_triples(Q):
    """Return triples (p, a, q=p^a), q <= Q. No log weights here."""
    Q = int(Q)
    out = []

    for p in primes_upto(Q).tolist():
        q = p
        a = 1
        while q <= Q:
            out.append((p, a, q))
            q *= p
            a += 1

    return out


def prime_powers(Q):
    return np.array(sorted(q for _, _, q in prime_power_triples(Q)), dtype=np.int64)


# ---------------------------------------------------------------------
# FTA-additive source angle
# ---------------------------------------------------------------------

def fta_theta(channel, N):
    """
    Θ(n) = Σ_{p^a || n} a Θ(p), computed by SPF recurrence.

    This is the source-side multiplication -> addition law.
    """
    N = int(N)
    spf = smallest_prime_factors(N)
    theta = np.zeros(N + 1, dtype=float)

    for n in range(2, N + 1):
        p = int(spf[n])
        theta[n] = theta[n // p] + channel.prime_angle(p)

    return theta[1 : N + 1]


def verify_fta_additivity(channel, N, trials=500, seed=0):
    """
    Check Θ(ab)=Θ(a)+Θ(b) for sampled products ab <= N.

    This is the log-free source sanity check.
    """
    theta = fta_theta(channel, N)
    rng = np.random.default_rng(seed)
    errs = []

    for _ in range(trials):
        a = int(rng.integers(1, N + 1))
        bmax = N // a
        if bmax < 1:
            continue
        b = int(rng.integers(1, bmax + 1))
        lhs = theta[a * b - 1]
        rhs = theta[a - 1] + theta[b - 1]
        errs.append(abs(lhs - rhs))

    return max(errs) if errs else 0.0


# ---------------------------------------------------------------------
# Physical helix
# ---------------------------------------------------------------------

def _arc_length_table(channel, kmax, steps=300_000):
    """
    Curve:
      R(k)     = slope * k
      phi(k)   = 2*pi*k
      height   = U*k

    Speed wrt k:
      sqrt(slope^2 + (slope*2*pi*k)^2 + U^2)
    """
    k = np.linspace(0.0, float(kmax), int(steps) + 1)
    sl = channel.slope
    speed = np.sqrt(sl**2 + (sl * 2 * np.pi * k) ** 2 + channel.U**2)
    s = np.concatenate([[0.0], np.cumsum((speed[1:] + speed[:-1]) * 0.5 * np.diff(k))])
    return k, s


def helix(channel, n_max):
    """
    Build source helix.

    Integer n is placed at arc(n)=n*U on the source line.
    The line is wound by inverting the arc-length map.
    """
    n_max = int(n_max)
    n = np.arange(1, n_max + 1, dtype=float)
    arc = n * channel.U

    # asymptotic arc ≈ pi*slope*k^2
    kmax = 2.0 * np.sqrt(arc[-1] / (np.pi * channel.slope)) + 5.0
    kk, ss = _arc_length_table(channel, kmax)

    k = np.interp(arc, ss, kk)

    return dict(
        n=n,
        arc=arc,
        k=k,
        radius=channel.slope * k,
        angle=2 * np.pi * k,
        height=channel.U * k,
        fta_theta=fta_theta(channel, n_max),
        weight=channel.character.chi(n.astype(np.int64)),
    )


def helix_points(channel, n_max):
    h = helix(channel, n_max)
    x = h["radius"] * np.cos(h["angle"])
    y = h["radius"] * np.sin(h["angle"])
    return np.stack([x, y, h["height"]], axis=1), h["weight"]


# ---------------------------------------------------------------------
# Log-free source atoms / Gram
# ---------------------------------------------------------------------

def source_atoms(channel, value_cutoff, prime_powers_only=True):
    """
    Log-free source atoms.

    phase = physical helix angle + FTA factor angle.
    amp   = chi / sqrt(radius).

    No log. No theta function. No L-values. No answer key.
    """
    value_cutoff = int(value_cutoff)
    h = helix(channel, value_cutoff)

    if prime_powers_only:
        q = prime_powers(value_cutoff)
    else:
        q = np.arange(1, value_cutoff + 1, dtype=np.int64)

    idx = q - 1
    chi = channel.character.chi(q)
    keep = np.abs(chi) > 1e-12

    q = q[keep]
    idx = idx[keep]
    chi = chi[keep]

    radius = h["radius"][idx]
    physical_angle = h["angle"][idx]
    theta = h["fta_theta"][idx]

    phase = physical_angle + theta
    amp = chi / np.sqrt(np.maximum(radius, 1e-300))

    return q, amp, phase, chi


def loss_gram(channel, H, value_cutoff, prime_powers_only=True):
    """
    Log-free projection-loss Gram.

      K_mn = amp_m conj(amp_n) ∫_0^H exp(i(phase_m-phase_n)t) dt

    PSD by construction as an integrated outer product.
    """
    q, amp, phase, _ = source_atoms(channel, value_cutoff, prime_powers_only=prime_powers_only)

    if len(q) < 2:
        return np.zeros((0, 0), dtype=complex)

    dphi = phase[:, None] - phase[None, :]

    with np.errstate(divide="ignore", invalid="ignore"):
        K = np.where(
            np.abs(dphi) < 1e-12,
            H,
            (np.exp(1j * dphi * H) - 1.0) / (1j * dphi),
        )

    return (amp[:, None] * np.conj(amp)[None, :]) * K


def mode_count(channel, H, value_cutoff, threshold=1e-2, prime_powers_only=True):
    G = loss_gram(channel, H, value_cutoff, prime_powers_only=prime_powers_only)

    if G.shape[0] == 0:
        return 0

    ev = np.linalg.eigvalsh(G).real
    m = ev.max()

    return int((ev > threshold * m).sum()) if m > 0 else 0


def self_test_logfree(channel, Hs=(20, 40, 60, 80), cutoff_scale=1.0, threshold=1e-2):
    """
    Log-free growth diagnostic.

    This does not compare to zeros. It just reports source mode growth.
    """
    out = []

    for H in Hs:
        cutoff = max(10, int(cutoff_scale * H * H))
        mc = mode_count(channel, H, cutoff, threshold=threshold)
        out.append((H, cutoff, mc))

    return out


# ---------------------------------------------------------------------
# Demo
# ---------------------------------------------------------------------

if __name__ == "__main__":
    for ch in (channel_A(), channel_B(), channel_C(), channel_D()):
        print("=" * 78)
        print(ch.describe())

        h = helix(ch, 12)
        print(
            f"{'n':>2} {'arc':>9} {'k':>8} {'radius':>10} "
            f"{'angle/2pi':>10} {'height':>9} {'thetaFTA':>10} {'chi':>7}"
        )

        for i in range(12):
            print(
                f"{int(h['n'][i]):>2} {h['arc'][i]:>9.4f} {h['k'][i]:>8.4f} "
                f"{h['radius'][i]:>10.3f} {h['angle'][i]/(2*np.pi):>10.4f} "
                f"{h['height'][i]:>9.4f} {h['fta_theta'][i]:>10.4f} "
                f"{h['weight'][i].real:>+7.1f}"
            )

        print("FTA additivity max error:", verify_fta_additivity(ch, 1000))
        print("mode growth:", self_test_logfree(ch))

    print("=" * 78)
    print("Core construction is log-free.")
