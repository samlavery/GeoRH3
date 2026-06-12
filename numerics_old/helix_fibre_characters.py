"""
helix_fibre_characters.py  --  the iy fibre-cancellation picture across the character zoo.

Generalises helix_fibre_chi3.py beyond the clean real character chi3: for ANY Dirichlet
character chi mod q,
    L(s, chi) = q^-s * sum_{a=1}^{q-1} chi(a) * zeta(s, a/q)          (the residue-class fibres)
and a zero on the line sigma=1/2 is exactly where the chi-weighted WINDING PHASORS cancel:
    S_N = sum_{n<=N} chi(n)/sqrt(n) * e^{-i*gamma*log n}  ->  0.

For REAL characters this is the +/- fibre balance; for COMPLEX characters it is a weighted
vector sum of fibres closing to zero.  Tested on chi mod 3, 4, 5 (complex, order 4), 7, 8 --
20 events each (100 total).

Numeric counterpart of RequestProject/HelixImaginaryAxis.lean (character-agnostic
lfunction_eq_helixSum / lfunction_eq_phasorSum) and HelixFibreCancellation.lean (chi3 instance).

Result: 20 events per character, max |L(1/2+i*gamma)| ~ 1e-24; the complex character mod 5
cancels exactly as cleanly as chi3; raw phasors -> 0 (~N^-1/2 generic, faster at complete
periods); controls between zeros do not balance.
"""
import mpmath as mp
mp.mp.dps = 25

def mult_order(a, q):
    o, x = 1, a % q
    while x != 1:
        x = (x * a) % q; o += 1
    return o

def prim_root(q):
    for g in range(2, q):
        if mult_order(g, q) == q - 1:
            return g

def char_prime(q, k):
    """non-principal char mod prime q:  chi(g^j) = exp(2*pi*i*k*j/(q-1))."""
    g = prim_root(q); dlog = {}; x = 1
    for j in range(q - 1):
        dlog[x] = j; x = (x * g) % q
    return lambda n: mp.mpc(0) if n % q == 0 else mp.exp(2 * mp.pi * 1j * k * dlog[n % q] / (q - 1))

def char_mod4(n):
    a = n % 4
    return mp.mpc(1) if a == 1 else (mp.mpc(-1) if a == 3 else mp.mpc(0))

def char_mod8(n):  # odd real char mod 8
    return {1: mp.mpc(1), 7: mp.mpc(1), 3: mp.mpc(-1), 5: mp.mpc(-1)}.get(n % 8, mp.mpc(0))

def make_L(q, chi):
    return lambda s: mp.power(q, -s) * mp.fsum(chi(a) * mp.zeta(s, mp.mpf(a) / q) for a in range(1, q))

cases = [
    ("mod 3  (real, order 2)",    3, char_prime(3, 1)),
    ("mod 4  (real, order 2)",    4, char_mod4),
    ("mod 5  (COMPLEX, order 4)", 5, char_prime(5, 1)),
    ("mod 7  (real, order 2)",    7, char_prime(7, 3)),
    ("mod 8  (real, order 2)",    8, char_mod8),
]

def find_zeros(L, n_want, Tmax=120.0, step=0.1):
    grid = [mp.mpf('0.5') + mp.mpf(str(step)) * k for k in range(int(Tmax / step))]
    av = [abs(L(mp.mpf('0.5') + 1j * g)) for g in grid]
    zeros = []
    for i in range(1, len(av) - 1):
        if av[i] < av[i - 1] and av[i] < av[i + 1] and av[i] < 0.4:
            try:
                g = mp.im(mp.findroot(L, mp.mpf('0.5') + 1j * grid[i]))
                if g > 0 and all(abs(g - gg) > 1e-5 for gg in zeros) \
                        and abs(L(mp.mpf('0.5') + 1j * g)) < 1e-10:
                    zeros.append(g)
            except Exception:
                pass
        if len(zeros) >= n_want:
            break
    return sorted(zeros)[:n_want]

for name, q, chi in cases:
    print("=" * 72)
    print(f"CHARACTER {name}   chi(1..{q-1}) = {[complex(chi(a)) for a in range(1, q)]}")
    L = make_L(q, chi)
    zeros = find_zeros(L, 20)
    print(f"  {len(zeros)} events;  max |L(1/2+i*gamma)| = "
          f"{float(max(abs(L(mp.mpf('0.5') + 1j * g)) for g in zeros)):.2e}")
    print(f"  gammas: {[round(float(g), 3) for g in zeros]}")
    g = zeros[0]; s = mp.mpf('0.5') + 1j * g
    row = [(N, float(abs(mp.fsum(chi(n) / mp.power(n, s) for n in range(1, N + 1)))))
           for N in (10**3, 10**4, 10**5)]
    print("  RAW phasors at first event: " + "  ".join(f"|S_{N}|={v:.2e}" for N, v in row))
    tc = (zeros[0] + zeros[1]) / 2
    print(f"  CONTROL non-event t={float(tc):.3f}: |L|={float(abs(L(mp.mpf('0.5') + 1j * tc))):.3f} (NOT ~0)")
