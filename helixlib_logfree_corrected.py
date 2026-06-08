"""
helixlib_logfree.py — log-free helix source construction.

Core rules:
  - No log/Mellin phase in the source construction.
  - Multiplication -> addition is by FTA:
        Θ(n) = Σ_{p^a || n} a Θ(p)
  - Linear radial law:
        R(k) = e^mode * k
  - Integer spacing is physical arc spacing:
        arc(n) = n * U
  - Character is a channel/fibre weight.
  - Grams are PSD source objects; mode counts are diagnostics, not zero ordinates.

This file intentionally does NOT include:
  - reference zeros
  - Riemann-Siegel theta
  - L-values
  - np.log/math.log in the source path
"""

import math
import numpy as np


# ---------------------------------------------------------------------
# Characters
# ---------------------------------------------------------------------

class Character:
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

        This is source geometry/fibre data, not log(p).
        """
        p = int(p)

        if self.character.name == "zeta trivial":
            # 12-slot trivial winding for U=pi/6.
            return (math.pi / self.helixUnit) * (p % (2 * self.helixUnit))

        if self.character.name == "chi3 mod 3":
            # 6-slot mod-6 winding.
            return (math.pi / 3.0) * (p % 6)

        if self.character.name in ("chi4 mod 4", "chi8 mod 8"):
            # 8-slot mod-8 winding.
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
    """
    Return triples (p, a, q=p^a), q <= Q.

    No log weights here.
    """
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
# FTA-additive angle
# ---------------------------------------------------------------------

def fta_theta(channel, N):
    """
    Θ(n) = Σ_{p^a || n} a Θ(p), computed by SPF recurrence.

    This is the log-free multiplication -> addition law.
    """
    N = int(N)
    spf = smallest_prime_factors(N)
    theta = np.zeros(N + 1, dtype=float)

    for n in range(2, N + 1):
        p = int(spf[n])
        theta[n] = theta[n // p] + channel.prime_angle(p)

    return theta[1 : N + 1]


def verify_fta_additivity(channel, N, trials=500, seed=0):
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

_ARC_CACHE = {}


def _arc_length_table(channel, kmax, steps=120_000):
    """
    Curve:
      R(k)   = slope*k
      phi(k) = 2*pi*k
      z(k)   = U*k

    speed dk:
      sqrt(slope^2 + (slope*2*pi*k)^2 + U^2)
    """
    key = (channel.character.name, round(float(kmax), 8), int(steps))
    if key in _ARC_CACHE:
        return _ARC_CACHE[key]

    k = np.linspace(0.0, float(kmax), int(steps) + 1)
    sl = channel.slope
    speed = np.sqrt(sl**2 + (sl * 2 * np.pi * k) ** 2 + channel.U**2)
    s = np.concatenate([[0.0], np.cumsum((speed[1:] + speed[:-1]) * 0.5 * np.diff(k))])

    _ARC_CACHE[key] = (k, s)
    return k, s


def helix(channel, n_max):
    """
    Build the log-free physical source helix.

    Integer n is placed on source line at arc(n)=n*U.
    The line is wound by inverting arc length to loop counter k.
    """
    n_max = int(n_max)
    if n_max < 1:
        return dict(
            n=np.array([], dtype=float),
            arc=np.array([], dtype=float),
            k=np.array([], dtype=float),
            radius=np.array([], dtype=float),
            angle=np.array([], dtype=float),
            height=np.array([], dtype=float),
            fta_theta=np.array([], dtype=float),
            weight=np.array([], dtype=complex),
        )

    n = np.arange(1, n_max + 1, dtype=float)
    arc = n * channel.U

    # asymptotic arc ~ pi*slope*k^2
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
# Source atoms and PSD Gram
# ---------------------------------------------------------------------

def source_atoms(channel, value_cutoff, prime_powers_only=True, include_physical_angle=True):
    """
    Log-free source atoms.

    phase = physical_angle + FTA_theta, unless include_physical_angle=False.
    amp   = chi / sqrt(radius).

    No logs, no L-values, no zero answer key.
    """
    value_cutoff = int(value_cutoff)
    if value_cutoff < 1:
        return (
            np.array([], dtype=np.int64),
            np.array([], dtype=complex),
            np.array([], dtype=float),
            np.array([], dtype=complex),
        )

    h = helix(channel, value_cutoff)

    if prime_powers_only:
        q = prime_powers(value_cutoff)
    else:
        q = np.arange(1, value_cutoff + 1, dtype=np.int64)

    if len(q) == 0:
        return (
            np.array([], dtype=np.int64),
            np.array([], dtype=complex),
            np.array([], dtype=float),
            np.array([], dtype=complex),
        )

    idx = q - 1
    chi = channel.character.chi(q)
    keep = np.abs(chi) > 1e-12

    q = q[keep]
    idx = idx[keep]
    chi = chi[keep]

    radius = h["radius"][idx]
    theta = h["fta_theta"][idx]
    physical_angle = h["angle"][idx] if include_physical_angle else 0.0

    phase = physical_angle + theta
    amp = chi / np.sqrt(np.maximum(radius, 1e-300))

    return q, amp, phase, chi


def loss_gram(channel, H, value_cutoff, prime_powers_only=True, include_physical_angle=True):
    """
    Log-free integrated source Gram.

      G_mn = amp_m conj(amp_n) ∫_0^H exp(i(phase_m-phase_n)t) dt

    PSD by construction as an integrated outer product.
    """
    q, amp, phase, _ = source_atoms(
        channel,
        value_cutoff,
        prime_powers_only=prime_powers_only,
        include_physical_angle=include_physical_angle,
    )

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


def eigs(channel, H, value_cutoff, prime_powers_only=True, include_physical_angle=True):
    G = loss_gram(
        channel,
        H,
        value_cutoff,
        prime_powers_only=prime_powers_only,
        include_physical_angle=include_physical_angle,
    )
    if G.shape[0] == 0:
        return np.array([], dtype=float), True

    ev = np.linalg.eigvalsh(G).real
    max_ev = float(ev.max()) if len(ev) else 0.0
    min_ev = float(ev.min()) if len(ev) else 0.0
    psd_ok = min_ev >= -1e-8 * max(1.0, abs(max_ev))
    return ev, psd_ok


def raw_rank_count(ev, rel=1e-2):
    ev = np.asarray(ev, dtype=float)
    ev = ev[ev > 0]
    if len(ev) == 0:
        return 0
    m = ev.max()
    return int((ev > rel * m).sum()) if m > 0 else 0


def normalized_spectrum(ev):
    ev = np.asarray(ev, dtype=float)
    ev = ev[ev > 0]
    if len(ev) == 0:
        return np.array([], dtype=float)
    s = ev.sum()
    if s <= 0:
        return np.array([], dtype=float)
    return np.sort(ev / s)[::-1]


def elbow_count(ev_norm, min_gap=1.75, min_abs=1e-6, max_modes=200):
    """
    Heuristic middle estimator:
      sort trace-normalized eigenvalues descending;
      find first strong ratio drop λ_j / λ_{j+1};
      count modes before the drop.

    This is a diagnostic, not a theorem.
    """
    x = np.asarray(ev_norm, dtype=float)
    x = x[x > min_abs]
    if len(x) < 2:
        return len(x)

    x = x[:max_modes]
    ratios = x[:-1] / np.maximum(x[1:], 1e-300)

    j = int(np.argmax(ratios))
    if ratios[j] >= min_gap:
        return j + 1

    return int(len(x))


def bulk_outlier_count(ev_norm, floor_quantile=0.90, factor=3.0, min_abs=1e-6):
    """
    Conservative separated-outlier count.

    Smaller factor => more modes.
    Larger factor  => fewer modes.
    """
    x = np.asarray(ev_norm, dtype=float)
    x = x[x > 0]
    if len(x) == 0:
        return 0

    tail = x[max(1, len(x) // 20):]
    if len(tail) < 5:
        tail = x

    floor = float(np.quantile(tail, floor_quantile))
    cutoff = max(min_abs, factor * floor)
    return int((x > cutoff).sum())


def mode_counts(channel, H, value_cutoff, include_physical_angle=True):
    ev, psd_ok = eigs(
        channel,
        H,
        value_cutoff,
        prime_powers_only=True,
        include_physical_angle=include_physical_angle,
    )
    evn = normalized_spectrum(ev)

    return dict(
        atoms=len(ev),
        psd_ok=psd_ok,
        raw=raw_rank_count(ev, rel=1e-2),
        elbow=elbow_count(evn),
        outlier=bulk_outlier_count(evn),
        max_ev=float(ev.max()) if len(ev) else 0.0,
        min_ev=float(ev.min()) if len(ev) else 0.0,
    )


def self_test_logfree(channel, Hs=(10, 20, 30, 40), cutoff_scale=1.0, include_physical_angle=True):
    rows = []
    for H in Hs:
        cutoff = max(30, int(cutoff_scale * H * H))
        rows.append((H, cutoff, mode_counts(channel, H, cutoff, include_physical_angle)))
    return rows


# ---------------------------------------------------------------------
# Demo
# ---------------------------------------------------------------------

if __name__ == "__main__":
    for ch in (channel_A(), channel_B(), channel_C(), channel_D()):
        print("=" * 78)
        print(ch.describe())
        print("FTA additivity max error:", verify_fta_additivity(ch, 1000))

        h = helix(ch, 12)
        print(f"{'n':>2} {'arc':>9} {'k':>8} {'radius':>10} {'angle/2pi':>10} {'height':>9} {'thetaFTA':>10} {'chi':>7}")
        for i in range(12):
            print(
                f"{int(h['n'][i]):>2} {h['arc'][i]:>9.4f} {h['k'][i]:>8.4f} "
                f"{h['radius'][i]:>10.3f} {h['angle'][i]/(2*np.pi):>10.4f} "
                f"{h['height'][i]:>9.4f} {h['fta_theta'][i]:>10.4f} "
                f"{h['weight'][i].real:>+7.1f}"
            )

        print("mode diagnostics:")
        for H, cutoff, st in self_test_logfree(ch):
            print(f"  H={H:5.1f} cutoff={cutoff:6d} atoms={st['atoms']:4d} raw={st['raw']:4d} elbow={st['elbow']:4d} outlier={st['outlier']:4d} PSD={st['psd_ok']}")

    print("=" * 78)
    print("Core construction is log-free.")
