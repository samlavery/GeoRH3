"""
FORWARD TEST (Approach A): prime-powers -> zeros, WITHOUT inputting zeta zeros.

Build a real wave from PRIME POWERS only, with on-line damping p^{-1/2}:
    W_X(t) = - sum_{p^k <= X} (log p) * cos(t * k * log p) / p^{k/2}
This is the von Mangoldt / explicit-formula "arithmetic" oscillating part.

We then find the structure that should mark gamma_n, increase X, and measure
RMS distance of crossings to canonical gamma_n (mpmath.zetazero) -- used ONLY
for the final comparison, never fed into the construction.

KEY honest diagnostic: does the prime-power-only object develop the correct
log-T DENSITY of crossings as X grows? Compare crossing count to nzeros(T).
"""
import numpy as np
import mpmath as mp
from sympy import primerange

mp.mp.dps = 30

# ---------- canonical zeros: ONLY for final comparison ----------
NZ = 60
GAMMA = np.array([float(mp.zetazero(n).imag) for n in range(1, NZ + 1)])

# ---------- prime-power list (von Mangoldt support) ----------
def prime_powers_up_to(X):
    """Return list of (n=p^k, logp, k) for all prime powers p^k <= X, k>=1."""
    out = []
    for p in primerange(2, int(X) + 1):
        lp = np.log(p)
        pk = p
        k = 1
        while pk <= X:
            out.append((pk, lp, k))
            pk *= p
            k += 1
    return out

def build_wave(X, taper=None):
    """Return function W(t) = - sum_{p^k<=X} logp * cos(t*k*logp) / p^{k/2}.
    taper: optional callable taper(u) on u = log(n)/log(X) in [0,1] (Fejer/Gaussian).
    """
    pps = prime_powers_up_to(X)
    logX = np.log(X)
    freqs = np.array([k * lp for (pk, lp, k) in pps])      # k*log p
    amps = np.array([lp / np.sqrt(pk) for (pk, lp, k) in pps])  # logp / p^{k/2}
    if taper is not None:
        u = np.array([np.log(pk) / logX for (pk, lp, k) in pps])
        amps = amps * taper(u)
    def W(t):
        return -np.sum(amps * np.cos(t * freqs))
    return W, len(pps)

def count_sign_changes(W, t0, t1, N=200000):
    ts = np.linspace(t0, t1, N)
    vals = np.array([W(t) for t in ts])
    sc = np.where(np.sign(vals[:-1]) != np.sign(vals[1:]))[0]
    crossings = []
    for i in sc:
        # linear interp
        a, b = ts[i], ts[i + 1]
        fa, fb = vals[i], vals[i + 1]
        crossings.append(a - fa * (b - a) / (fb - fa))
    return np.array(crossings), ts, vals

def match_rms(crossings, gammas):
    """For each canonical gamma, distance to nearest crossing; RMS over gammas in range."""
    if len(crossings) == 0:
        return np.nan, 0
    used = []
    for g in gammas:
        d = np.min(np.abs(crossings - g))
        used.append(d)
    used = np.array(used)
    return np.sqrt(np.mean(used**2)), len(used)

if __name__ == "__main__":
    Tmax = 60.0
    gam_in_range = GAMMA[GAMMA < Tmax]
    print(f"# canonical gamma_n in (0,{Tmax}): {len(gam_in_range)}")
    print(f"# expected zeros up to T=60 via nzeros: {mp.nzeros(60)}")
    print()
    print(f"{'X':>8} {'#pp':>6} {'#cross':>7} {'RMS':>10}  first 6 crossings vs gamma")
    for X in [10, 30, 100, 300, 1000, 3000, 10000, 30000, 100000]:
        W, npp = build_wave(X)
        cr, ts, vals = count_sign_changes(W, 1.0, Tmax, N=120000)
        rms, ng = match_rms(cr, gam_in_range)
        first = cr[:6]
        print(f"{X:>8} {npp:>6} {len(cr):>7} {rms:>10.4f}  cross={np.round(first,3)}")
    print()
    print("canonical gamma first 6:", np.round(gam_in_range[:6], 3))
