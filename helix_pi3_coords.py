"""
Source-helix model for Dirichlet L(s, chi) zeros.  Persistent reference -- everything
learned lives here, not in throwaway scripts.

PRIMES RUN THE SHOW.  The winding of integer n is the FTA-additive character built from
n's prime factorization:
        theta(n) = sum over p^a || n of  a * w(p),        w(p) = per-prime weight.
Additivity theta(m*n) = theta(m) + theta(n) is exact because it is summed over the
factorization -- no smooth shortcut.  To read the actual L-zeros the per-prime weight is
w(p) = log p, so theta(n) = log n, but it is COMPUTED from the primes.

pi/q CHART  (q = conductor of chi):
        ds = pi/q          chart unit
        A  = ds/2          midpoint half-unit  (sigma = 1/2 lives here; for q=3, A = pi/6)
        C  = ds^2          area constant,  R_n^2 = C * n  ->  R_n = (pi/q) * sqrt(n)
        sigma = (q/pi) * angle      real-coordinate readout

PI/q CHART NOTE.
        The production model now uses 3D source height z3 = exp(t), and the 1D
        readout takes logs: t = log z3.  The RESCALE helpers below are retained
        for older comparison utilities; they are not the 3D source height.

Per integer: ONE phasor, amplitude 1/R_n = (q/pi)/sqrt(n) ~ n^{-1/2} (inverse radius).
Two CONDUCTOR BANDS: split by residue of n mod q (+ band = chi=+1, - band = chi=-1).
A VANISHING is the two bands meeting (+ band == - band) after eating the enclosed integers.
"""

import math

# ----- conductor / character ------------------------------------------------
Q = 3                                   # conductor of chi3 (mod 3, odd)

def chi(n):
    """Real primitive character mod Q (chi3: residues 1 -> +1, 2 -> -1, 0 -> 0)."""
    r = n % Q
    if r == 0:
        return 0
    return 1 if r == 1 else -1

# ----- pi/q chart -----------------------------------------------------------
DS   = math.pi / Q                      # chart unit
A    = DS / 2                           # midpoint half-unit (pi/6 for q=3)
C    = DS * DS                          # area constant, R_n^2 = C n

# ----- COORDINATE RESCALE (height axis) -------------------------------------
# Same factor the real axis uses: sigma = (q/pi)*angle, so height -> t is also * (q/pi).
# (The other direction from before -- helix height runs LARGER than t, enclosing more integers.)
RESCALE = Q / math.pi                   # = q/pi ; height -> t the same way the real axis charts

def height_to_t(h):   return h * RESCALE          # helix height -> L's t  (t = (q/pi) h)
def t_to_height(t):   return t / RESCALE          # L's t -> helix height  (h = (pi/q) t)

# ----- quantum crossing ladder (amplitude thresholds) -----------------------
# Crossings (vanishings) sit at accumulated amplitude:  first at pi/2, then +pi each.
def quantum_level(k):
    """Amplitude of the k-th crossing: pi/2, 3pi/2, 5pi/2, ... = pi/2 + k*pi."""
    return math.pi / 2 + k * math.pi

def amplitude(n):
    """Harmonic phase after eating n integers: pi/6 per integer.
       1->pi/6, 2->pi/3, 3->pi/2 (FIRST CROSSING), ... ; one full cycle = 12 integers = 1 turn."""
    return n * A

def crossing_level(k):
    """Integer-count at the k-th crossing: quantum_level(k)/(pi/6) = 3 + 6k  ->  n = 3, 9, 15, ..."""
    return quantum_level(k) / A

# ----- prime-driven winding -------------------------------------------------
def w_prime(p):
    """Per-prime weight (the winding increment of prime p).  log p reads the real zeros."""
    return math.log(p)

def theta(n):
    """FTA-additive winding of n, summed over its prime factorization (primes run it)."""
    s = 0.0
    m = n
    d = 2
    while d * d <= m:
        while m % d == 0:
            s += w_prime(d)
            m //= d
        d += 1
    if m > 1:
        s += w_prime(m)
    return s                            # == log n, but built from the primes

# ----- geometry of one integer ----------------------------------------------
def radius(n):   return DS * math.sqrt(n)      # R_n = (pi/q) sqrt(n)
def amp(n):      return 1.0 / radius(n)        # phasor amplitude = inverse radius

def enclosed_count(h):
    """Integers the helix encloses at HEIGHT h: those with R_n <= radius reached.
       With R = height (pitch makes R = theta = height), n with (pi/q)sqrt(n) <= h."""
    if h <= 0:
        return 0
    return int((h / DS) ** 2)                  # = floor(q^2 h^2 / pi^2)

# ----- the two conductor bands and the vanishing ----------------------------
def conductor_bands(h, N=None, rot=None, rate_fn=None):
    """Two COUNTER-ROTATING bands via the conductor's additive characters:
         + band winds  e^{+2*pi*i*n/q},   - band winds  e^{-2*pi*i*n/q}   (rate 2*pi/q per integer).
       Each phasor also carries amp(n) = 1/R_n and the readout rotation e^{-i*t*theta(n)}
       (theta(n) from the prime factorization).  Then
            B+ - B-  =  i*sqrt(3) * L(1/2+it, chi3)   (chi3(n) = (2/sqrt3) sin(2*pi*n/3)),
       so a VANISHING is  B+ == B-  : the two counter-rotating bands meet.
       N defaults to the enclosed count at h (pure accurate counting)."""
    if N is None:
        N = enclosed_count(h)
    if rot is None:
        rot = 2 * math.pi / Q                   # default conductor additive character (builds chi3)
    if rate_fn is None:
        rate_fn = theta                         # default: prime winding log n
    t = height_to_t(h)                          # apply the coordinate rescale, once
    Sp = 0j
    Sm = 0j
    for n in range(1, N + 1):
        read = -t * rate_fn(n)                  # readout rotation
        base = amp(n) * complex(math.cos(read), math.sin(read))
        c = rot * n                             # counter-rotation factor per integer
        Sp += base * complex(math.cos(c),  math.sin(c))
        Sm += base * complex(math.cos(-c), math.sin(-c))
    return Sp, Sm


def bands_scaled(h, N=None, rot=None):
    """Bands with the SCALED integer value n*(pi/6) as the spinning rate:
       each phasor phase = -h * (n*A); counter-rotating via the conductor (+/- 2pi n/q).
       Vanishing = B+ == B-.  (No log n here -- the consumed integer's own scaled value drives it.)"""
    if N is None:
        N = enclosed_count(h)
    if rot is None:
        rot = 2 * math.pi / Q
    Sp = 0j
    Sm = 0j
    for n in range(1, N + 1):
        read = -h * (n * A)                     # scaled integer value n*pi/6 as the rate
        base = amp(n) * complex(math.cos(read), math.sin(read))
        c = rot * n
        Sp += base * complex(math.cos(c),  math.sin(c))
        Sm += base * complex(math.cos(-c), math.sin(-c))
    return Sp, Sm

def cancellation_heights(hmax=24.0, dh=0.01, thresh=0.05, N=400):
    """Scan HEIGHT; report where the scaled-rate bands cancel (the model's heights)."""
    import_gaps = []
    h = dh
    prev2 = prev1 = None
    out = []
    while h < hmax:
        Sp, Sm = bands_scaled(h, N=N)
        g = abs(Sp - Sm)
        if prev1 is not None and prev2 is not None and prev1 < prev2 and prev1 < g and prev1 < thresh:
            out.append((round(h - dh, 4), round(prev1, 4)))
        prev2, prev1 = prev1, g
        h += dh
    return out


def winding_from_primes(n, a):
    """FTA-additive winding Theta(n) = sum vp(n)*a(p), built from n's factorization.
       Geometric (log-free) if a(p) is geometric, e.g. sqrt(p), p, p^(1/3), or 1."""
    s = 0.0
    m = n
    d = 2
    while d * d <= m:
        while m % d == 0:
            s += a(d)
            m //= d
        d += 1
    if m > 1:
        s += a(m)
    return s


def search_logfree(N=600, tmax=50.0, dt=0.04):
    """Try to LAND a log-free winding: geometric per-prime weights, scan for band cancellation."""
    weights = [
        ("a(p)=sqrt(p)", lambda p: p ** 0.5),
        ("a(p)=p", lambda p: float(p)),
        ("a(p)=p^(1/3)", lambda p: p ** (1.0 / 3.0)),
        ("a(p)=1 (Omega)", lambda p: 1.0),
        ("a(p)=p/log? no -> 1/sqrt p", lambda p: 1.0 / p ** 0.5),
        ("a(p)=log p (reference)", lambda p: math.log(p)),
    ]
    for name, a in weights:
        th = [0.0] + [winding_from_primes(n, a) for n in range(1, N + 1)]
        best = 9e9
        t = dt
        while t < tmax:
            Sp = 0j
            Sm = 0j
            for n in range(1, N + 1):
                read = -t * th[n]
                base = amp(n) * complex(math.cos(read), math.sin(read))
                c = 2 * math.pi * n / Q
                Sp += base * complex(math.cos(c), math.sin(c))
                Sm += base * complex(math.cos(-c), math.sin(-c))
            g = abs(Sp - Sm)
            if g < best:
                best = g
            t += dt
        print(f"  {name:>26}: min |B+ - B-| over t in [0,{tmax:.0f}] = {best:.4f}")


def geom_cancellation_heights(a=lambda p: p ** 0.5, N=700, tmax=40.0, dt=0.02, thresh=0.12):
    """Vanishing HEIGHTS of the log-free additive geometric winding a(p) (default sqrt p)."""
    th = [0.0] + [winding_from_primes(n, a) for n in range(1, N + 1)]
    cph = [(math.cos(2 * math.pi * n / Q), math.sin(2 * math.pi * n / Q)) for n in range(0, N + 1)]

    def gap(t):
        Sp = 0j
        Sm = 0j
        for n in range(1, N + 1):
            read = -t * th[n]
            base = amp(n) * complex(math.cos(read), math.sin(read))
            cc, sc = cph[n]
            Sp += base * complex(cc, sc)
            Sm += base * complex(cc, -sc)
        return abs(Sp - Sm)

    out = []
    t = dt
    p2 = p1 = None
    while t < tmax:
        g = gap(t)
        if p1 is not None and p2 is not None and p1 < p2 and p1 < g and p1 < thresh:
            lo, hi = t - 2 * dt, t
            for _ in range(40):
                m1 = lo + (hi - lo) / 3
                m2 = hi - (hi - lo) / 3
                if gap(m1) < gap(m2):
                    hi = m2
                else:
                    lo = m1
            out.append(((lo + hi) / 2, gap((lo + hi) / 2)))
        p2, p1 = p1, g
        t += dt
    return out


def sweep_sigma(sigmas=(0.3, 0.4, 0.5, 0.6, 0.7), N=700, tmax=40.0, dt=0.04):
    """Adjust the AMPLITUDE exponent n^{-sigma} (the radius dial) and scan heights.
       sigma sets WHICH vertical line is read; crossings survive only where L has zeros."""
    ln = [0.0] + [math.log(n) for n in range(1, N + 1)]
    cph = [(math.cos(2 * math.pi * n / Q), math.sin(2 * math.pi * n / Q)) for n in range(0, N + 1)]
    for sig in sigmas:
        amps = [0.0] + [n ** (-sig) for n in range(1, N + 1)]
        best = 9e9
        t = dt
        while t < tmax:
            Sp = 0j
            Sm = 0j
            for n in range(1, N + 1):
                read = -t * ln[n]
                base = amps[n] * complex(math.cos(read), math.sin(read))
                cc, sc = cph[n]
                Sp += base * complex(cc, sc)
                Sm += base * complex(cc, -sc)
            g = abs(Sp - Sm)
            if g < best:
                best = g
            t += dt
        flag = "  <- critical line" if abs(sig - 0.5) < 1e-9 else ""
        print(f"  sigma = {sig:.2f} (amplitude n^-{sig:.2f}): min |B+ - B-| = {best:.4f}{flag}")


def worked_backwards(num=30):
    """Canonical worked-backwards model, pi/3 chart, logarithmic spiral.

      3D TARGET for ordinate t:   z = e^t      (so the 1D readout is log z = t)
      consumed integer n:         m_n = (pi/q)*n          (pi/3 scale: 1->pi/3, 2->2pi/3, ...)
      log spiral / winding:       phase_n = -(log m_n)*(log z)   (spiral angle * log height)
      amplitude:                  m_n^{-1/2}
      bands:                      counter-rotating conductor phases  +/- 2*pi*n/q
      crossing:                   B+ == B-  at  z = e^t ; the 1D log z returns the chi3 ordinate.

    Runs over the first `num` chi3 zeros and reports cancellation at each e^{ordinate} target."""
    import mpmath as mp
    mp.mp.dps = 22

    def Lval(t):
        s = mp.mpf(1) / 2 + 1j * mp.mpf(t)
        return mp.power(3, -s) * (mp.zeta(s, mp.mpf(1) / 3) - mp.zeta(s, mp.mpf(2) / 3))

    grid = [1.0 + 0.1 * k for k in range(0, 800)]
    av = [abs(Lval(x)) for x in grid]
    ords = []
    for j in range(1, len(grid) - 1):
        if len(ords) >= num:
            break
        if av[j] < av[j - 1] and av[j] < av[j + 1] and av[j] < 0.25:
            lo, hi = grid[j - 1], grid[j + 1]
            for _ in range(60):
                m1 = lo + (hi - lo) / 3
                m2 = hi - (hi - lo) / 3
                if abs(Lval(m1)) < abs(Lval(m2)):
                    hi = m2
                else:
                    lo = m1
            zr = (lo + hi) / 2
            if abs(Lval(zr)) < 1e-6:
                ords.append(float(zr))

    Nmax = int(max(ords[:num]) ** 2) + 1
    logn = [0.0] + [math.log(n) for n in range(1, Nmax + 1)]
    cph = [(math.cos(2 * math.pi * n / Q), math.sin(2 * math.pi * n / Q)) for n in range(Nmax + 1)]
    logs = math.log(DS)                                   # log of the pi/3 scale factor

    print("pi/3-chart log-spiral, worked backwards: 3D target z=e^ord, 1D readout = log z")
    print(f"{'#':>3} {'z = e^ord (3D)':>18} {'|B+ - B-|':>10} {'log z = ord':>12} {'N':>6}")
    for i, t in enumerate(ords[:num]):
        z = math.exp(t)
        lz = t                                            # log z = log(e^t) = t
        N = int(t * t)
        Sp = 0j
        Sm = 0j
        for n in range(1, N + 1):
            ph = -(logs + logn[n]) * lz                   # -(log m_n)(log z), m_n=(pi/3)n
            base = (DS * n) ** (-0.5) * complex(math.cos(ph), math.sin(ph))
            cc, sc = cph[n]
            Sp += base * complex(cc, sc)
            Sm += base * complex(cc, -sc)
        print(f"{i+1:>3} {z:>18.1f} {abs(Sp - Sm):>10.4f} {lz:>12.4f} {N:>6}")


def accuracy_test(num=30):
    """Find the model's vanishing height near each of the first `num` true chi3 zeros
       (pure enclosed counting N=t^2) and report the error."""
    import mpmath as mp
    mp.mp.dps = 22

    def Lval(t):
        s = mp.mpf(1) / 2 + 1j * mp.mpf(t)
        return mp.power(3, -s) * (mp.zeta(s, mp.mpf(1) / 3) - mp.zeta(s, mp.mpf(2) / 3))

    grid = [1.0 + 0.1 * k for k in range(0, 800)]
    av = [abs(Lval(x)) for x in grid]
    true = []
    for j in range(1, len(grid) - 1):
        if len(true) >= num:
            break
        if av[j] < av[j - 1] and av[j] < av[j + 1] and av[j] < 0.25:
            lo, hi = grid[j - 1], grid[j + 1]
            for _ in range(60):
                m1 = lo + (hi - lo) / 3
                m2 = hi - (hi - lo) / 3
                if abs(Lval(m1)) < abs(Lval(m2)):
                    hi = m2
                else:
                    lo = m1
            z = (lo + hi) / 2
            if abs(Lval(z)) < 1e-6:
                true.append(float(z))

    print(f"{'#':>3} {'true zero':>11} {'model height':>13} {'|err|':>9} {'N=t^2':>7} {'gap':>8}")
    maxerr = 0.0
    hits = 0
    for i, tz in enumerate(true[:num]):
        h0 = t_to_height(tz)
        best = (9e9, h0)
        hh = h0 - 0.4
        while hh <= h0 + 0.4:
            g = band_gap(hh)
            if g < best[0]:
                best = (g, hh)
            hh += 0.02
        a, b = best[1] - 0.02, best[1] + 0.02
        for _ in range(40):
            m1 = a + (b - a) / 3
            m2 = b - (b - a) / 3
            if band_gap(m1) < band_gap(m2):
                b = m2
            else:
                a = m1
        hpred = (a + b) / 2
        tpred = height_to_t(hpred)
        err = abs(tpred - tz)
        maxerr = max(maxerr, err)
        if err < 0.05:
            hits += 1
        print(f"{i+1:>3} {tz:>11.4f} {tpred:>13.4f} {err:>9.4f} {enclosed_count(hpred):>7} {band_gap(hpred):>8.4f}")
    print(f"\n{hits}/{num} within 0.05 ; max error {maxerr:.4f}")


def worked_example(t):
    """Source-height/readout report at channel ordinate t."""
    z3 = math.exp(t)                            # actual 3D source height
    print(f"=== SOURCE HEIGHT / LOG READOUT, channel ordinate t = {t} ===")
    print(f"3D source height z3=exp(t) = {z3:.4f};  1D readout log(z3) = {t}")
    print("finite cutoff counts are intentionally omitted; the 3D count is the arclength ledger.")


def compare_rotations(zeros=(8.0397, 11.2492, 15.7046, 18.2620, 20.4558)):
    """Try counter-rotation factor pi/6 vs pi/3 (vs conductor 2pi/3) for cancellation."""
    factors = [("pi/6", math.pi / 6), ("pi/3", math.pi / 3), ("2pi/3 (conductor)", 2 * math.pi / Q)]
    print(f"  {'chi3 zero t':>12} " + " ".join(f"{name:>18}" for name, _ in factors))
    for tz in zeros:
        h = t_to_height(tz)
        row = []
        for _, f in factors:
            Sp, Sm = conductor_bands(h, rot=f)
            row.append(abs(Sp - Sm))
        print(f"  {tz:>12.4f} " + " ".join(f"{g:>18.4f}" for g in row))

def band_gap(h, N=None):
    Sp, Sm = conductor_bands(h, N)
    return abs(Sp - Sm)                          # 0  <=>  vanishing at this height


# ----- the fiber IS a harmonic ----------------------------------------------
# On the line the fiber is a single real harmonic, fiber ~ cos(phi).  Its nodes are
# the zeros: phi = pi/2 + k*pi (first crossing pi/2, each next costs pi).  The phase
# phi is the rotation (Riemann-Siegel theta of L mod q, odd character).
try:
    import mpmath as _mp
    def theta_rotation(t):
        """Harmonic phase phi(t) = rotation theta of the fiber (L mod q, odd)."""
        return (t / 2.0) * math.log(Q / math.pi) + float(_mp.loggamma(0.75 + 0.5j * t).imag)
except Exception:
    theta_rotation = None

KNOWN_CHI3_ZEROS = [8.0397, 11.2492, 15.7046, 18.2620, 20.4558, 24.0594, 26.5779, 28.2182]

def fiber(phi):
    """The fiber as a harmonic; vanishes (node) at phi = pi/2 + k*pi."""
    return math.cos(phi)


if __name__ == "__main__":
    print(f"conductor Q={Q}  chart ds=pi/Q={DS:.5f}  midpoint A={A:.5f}  RESCALE={RESCALE}")
    print("primes run the winding: theta(n) from factorization vs log n")
    for n in (2, 3, 4, 6, 12, 30):
        print(f"  n={n:>2}: theta={theta(n):.6f}  log n={math.log(n):.6f}  (match: {abs(theta(n)-math.log(n))<1e-12})")
    print("one phasor per integer, amplitude 1/R_n ~ n^-1/2:")
    for n in (1, 2, 3, 4):
        print(f"  n={n}: R_n={radius(n):.4f}  amp={amp(n):.4f}")
    print(f"spacing pi/6 per integer: amp(1)={amplitude(1):.5f} amp(2)={amplitude(2):.5f} amp(3)={amplitude(3):.5f} (3 -> pi/2 = first crossing)")
    print("quantum crossing ladder (first at pi/2, then +pi each):")
    for k in range(4):
        print(f"  crossing {k}: amplitude={quantum_level(k):.5f}  at integer n={crossing_level(k):.0f}  (n = 3, 9, 15, ...)")
    print("\n+/- conductor bands tracked at a real chi3 zero (rescaled height):")
    for tz in (8.0397, 11.2492, 15.7046):
        h = t_to_height(tz)
        Sp, Sm = conductor_bands(h)
        print(f"  zero t={tz:.4f} -> height={h:.4f}, N={enclosed_count(h)} eaten | "
              f"+band={abs(Sp):.4f}  -band={abs(Sm):.4f}  |+ minus -|={abs(Sp-Sm):.4f}")
    if theta_rotation:
        print("\nTHE FIBER IS A HARMONIC: phase phi=theta_rotation(t); zeros should sit one node (pi) apart")
        print(f"  {'chi3 zero t':>12} {'phi=theta(t)':>13} {'fiber=cos(phi)':>15} {'Δphi from prev':>15}")
        prev = None
        for t in KNOWN_CHI3_ZEROS:
            ph = theta_rotation(t)
            d = '' if prev is None else f"{ph - prev:.4f}"
            print(f"  {t:>12.4f} {ph:>13.4f} {fiber(ph):>15.4f} {d:>15}")
            prev = ph
        print(f"  (pi = {math.pi:.4f}; if Δphi ≈ pi and fiber≈0, the zeros are the harmonic's nodes)")
