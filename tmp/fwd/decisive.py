"""
DECISIVE FORWARD TEST: prime-powers -> zeta zeros, WITHOUT inputting gamma_n.

Memory-safe: numpy float64 for ALL wave evaluation; mpmath ONLY for reference data
at dps=15. No outer products bigger than ~5e6; loop over terms accumulating in place.

Canonical gamma_n: fetched ONCE, used ONLY for the final RMS comparison.

Tests run forward (primes -> zeros):
  S1  BARE prime-power fluctuation  W(t) = -sum_{p^k<=X} (log p) p^{-k/2} cos(t k log p)
        control; expected to FAIL on density (crossing density ~ logX, not log T).
  DENSITY DIAGNOSTIC: crossing count of S1 vs true nzeros(T); tracks maxfreq, not zeta.
  N_geo DERIVATION: can the log-T smooth count be built from PNT pi(x)~x/log x + helix
        laws (NOT arg Gamma)? Compare candidate N_geo(T) to BOTH the Riemann-vM count
        AND to theta(T)/pi (= arg Gamma readout). If N_geo == theta/pi, it's BORROWED.
  S3  forward wave with the GEOMETRIC smooth phase + prime-power fluctuation; measure
        RMS of crossings to canonical gamma_n as X grows.
"""
import sys
import math
import numpy as np
import mpmath as mp

mp.mp.dps = 15  # DEFAULT precision only

def pr(*a):
    print(*a); sys.stdout.flush()

# ---------------- reference data: fetched ONCE, plain floats ----------------
NREF = 30
GAMMA = np.array([float(mp.zetazero(n).imag) for n in range(1, NREF + 1)])  # CAP 30
pr("canonical gamma_1..10:", np.round(GAMMA[:10], 4).tolist())

# a few nzeros(T) for density check (T up to ~120)
NZEROS = {T: int(mp.nzeros(T)) for T in [30, 50, 70, 90, 110]}
pr("nzeros:", NZEROS)
pr("")

# ---------------- prime powers via numpy sieve (modest cap p^k <= 1e5) ----------------
def prime_powers(X):
    """Return float64 arrays (freq = k*log p, amp = (log p) * p^{-k/2}) for p^k <= X."""
    Xc = int(X)
    sieve = np.ones(Xc + 1, bool); sieve[:2] = False
    for i in range(2, int(Xc**0.5) + 1):
        if sieve[i]: sieve[i*i::i] = False
    primes = np.nonzero(sieve)[0]
    freqs, amps = [], []
    for p in primes.tolist():
        lp = math.log(p); pk = p; k = 1
        while pk <= Xc:
            freqs.append(k * lp)
            amps.append(lp * pk ** (-0.5))  # (log p) * (p^k)^{-1/2} = (log p) p^{-k/2}
            pk *= p; k += 1
    return np.asarray(freqs, np.float64), np.asarray(amps, np.float64)

# ---------------- memory-safe wave: loop over terms, accumulate in place ----------------
def bare_wave(t, freqs, amps):
    """W(t) = -sum amp * cos(t * freq). O(len(t)) memory."""
    W = np.zeros_like(t)
    for f, a in zip(freqs, amps):
        W += a * np.cos(f * t)
    return -W

def crossings(t, w):
    s = np.sign(w)
    idx = np.nonzero(s[:-1] * s[1:] < 0)[0]
    t0, t1 = t[idx], t[idx + 1]
    w0, w1 = w[idx], w[idx + 1]
    return t0 - w0 * (t1 - t0) / (w1 - w0)

def rms_to_gamma(cross, gammas):
    """For each gamma in range, nearest crossing; RMS."""
    if len(cross) == 0:
        return float('nan')
    d = [np.min(np.abs(cross - g)) for g in gammas]
    return math.sqrt(np.mean(np.square(d)))

# ============================================================================
# PART 1 -- S1 bare prime-power fluctuation: crossing DENSITY vs true count
# ============================================================================
pr("="*78)
pr("PART 1: BARE prime-power wave -- does crossing DENSITY match zeta's log-T count?")
pr("  W(t) = -sum_{p^k<=X} (log p) p^{-k/2} cos(t k log p)")
pr("-"*78)
t = np.arange(0.5, 110.0, 0.02)  # ~5500 pts
pr(f"{'X':>7} {'#pp':>6} {'maxfreq':>8} {'#cross(<110)':>12} {'nzeros(110)':>11} {'pred~maxf*T/2pi':>16}")
for X in [100, 1000, 10000, 100000]:
    f, a = prime_powers(X)
    W = bare_wave(t, f, a)
    cr = crossings(t, W)
    pred = f.max() * 110.0 / (2 * math.pi)
    pr(f"{X:>7} {len(f):>6} {f.max():>8.3f} {len(cr):>12} {NZEROS[110]:>11} {pred:>16.1f}")
    del W, cr
pr("  -> bare-wave crossing count GROWS with X (tracks maxfreq=logX), NOT fixed at nzeros.")
pr("  -> density is set by highest prime frequency, NOT zeta's log-T density.")
pr("")

# ============================================================================
# PART 2 -- can N_geo (smooth count) be DERIVED geometrically, or is it arg Gamma?
# ============================================================================
pr("="*78)
pr("PART 2: where does the SMOOTH count come from? Geometry/PNT or arg Gamma?")
pr("-"*78)

# True smooth count from arg Gamma (the BORROWED analytic object):
#   N(T) = theta(T)/pi + 1,  theta(T)=arg Gamma(1/4+iT/2) - (T/2) log pi
def N_argGamma(T):
    return float(mp.siegeltheta(T)) / math.pi + 1.0

# Riemann-von Mangoldt asymptotic (the "log-T density" law). This is the LEADING
# asymptotics of theta/pi; question is whether it counts as geometric.
def N_logT(T):
    x = T / (2 * math.pi)
    return x * math.log(x) - x + 7.0 / 8.0

# CANDIDATE geometric counting laws:
# (A) helix area law N ~ sqrt-type: number of integers placed up to loop k ~ k^2,
#     R ~ sqrt(n). The prompt flags this gives the WRONG density. Test it:
def N_arealaw(T):
    # if R(k)=e^mode*k and loop k holds ~k integers, cumulative ~k^2; the "scale"
    # reached at height T ... area-law predicts count ~ c*T (linear), wrong shape.
    return T / (2 * math.pi)  # bare winding count, linear in T -- no log factor

# (B) PNT-driven count: the number of prime-power frequencies below the running
#     resolution. PNT pi(x)~x/log x is arithmetic (not zeta). Does integrating the
#     prime-power density give the log-T count? The prime frequencies are k*log p in
#     [log2, logX]; their COUNT below freq f is ~ pi(e^f) ~ e^f / f (PNT). That is the
#     count of OSCILLATORS, not the count of zeros. Test if it yields log-T:
def N_pnt_oscillators(f_cut):
    # number of prime-power freqs <= f_cut ~ pi(e^{f_cut}) ~ e^{f_cut}/f_cut
    return math.exp(f_cut) / f_cut

pr("Compare candidate smooth counts to the BORROWED arg-Gamma count N(T)=theta/pi+1:")
pr(f"{'T':>6} {'N_argGamma':>11} {'N_logT(vM)':>11} {'N_winding(lin)':>14}")
for T in [20, 40, 60, 80, 100, 120]:
    pr(f"{T:>6} {N_argGamma(T):>11.4f} {N_logT(T):>11.4f} {N_arealaw(T):>14.4f}")
pr("")
pr("  -> N_logT (Riemann-vM) tracks N_argGamma closely: it IS the asymptotic of theta/pi.")
pr("  -> N_winding (linear, area/winding law) has NO log factor: WRONG density (prompt (c)).")
pr("")

# THE CRUX: is N_logT == theta/pi (i.e. arg Gamma in disguise)?
pr("CRUX: is the log-T law N_logT just arg Gamma (theta/pi) in disguise?")
pr(f"{'T':>6} {'theta/pi':>12} {'N_logT-1':>12} {'diff':>12}")
for T in [20, 40, 60, 100, 200, 500]:
    th = float(mp.siegeltheta(T)) / math.pi
    nl = N_logT(T) - 1.0
    pr(f"{T:>6} {th:>12.5f} {nl:>12.5f} {th - nl:>12.6f}")
pr("  -> N_logT is the leading + first correction of theta(T)/pi (Stirling of arg Gamma).")
pr("  -> The log-T density IS the Stirling asymptotic of arg Gamma. NOT independent geometry.")
pr("")

# ============================================================================
# PART 3 -- FORWARD WAVE: smooth phase (geometric Stirling) + prime-power fluct
#           measure RMS of crossings to canonical gamma_n as X grows.
# ============================================================================
pr("="*78)
pr("PART 3: FORWARD wave = smooth phase * (1 + prime-power fluctuation), RMS vs gamma_n")
pr("-"*78)
# Hardy Z-style: zeros of Z(t) ARE the gamma_n. Z(t)=2 sum_{n<=sqrt(t/2pi)} n^{-1/2}
#   cos(theta(t) - t log n). The smooth phase theta is the count driver; the n-sum is
#   the integer/arithmetic part. We compare TWO theta choices, BOTH using the SAME
#   arithmetic Dirichlet sum, all in numpy float64 (loop over n, accumulate in place):
#     theta_Gamma : arg Gamma  (BORROWED) -- precompute on grid via mpmath once.
#     theta_geo   : pi*(N_logT(t) - 1)  = Stirling expansion (the "geometric" count).
# The Dirichlet n cutoff sqrt(t/2pi) grows with t; X here = max integer n used.
t = np.arange(2.0, 60.0, 0.02)  # comparison window
gam_in = GAMMA[(GAMMA >= 3.0) & (GAMMA <= 58.0)]
pr(f"canonical gamma_n in [3,58]: {len(gam_in)}  -> {np.round(gam_in,3).tolist()}")

# precompute theta on the grid ONCE (mpmath, dps=15) -- this is the BORROWED phase
theta_G = np.array([float(mp.siegeltheta(tt)) for tt in t])
# geometric Stirling phase (NO mpmath / NO Gamma): pi*(N_logT - 1)
xx = t / (2 * math.pi)
theta_geo = math.pi * (xx * np.log(xx) - xx + 7.0/8.0 - 1.0)
# extend Stirling with more correction terms (still pure asymptotic, no Gamma call):
# theta(t) = (t/2)log(t/2pi) - t/2 - pi/8 + 1/(48 t) + 7/(5760 t^3) + ...
theta_stir = (t/2)*np.log(t/(2*math.pi)) - t/2 - math.pi/8 + 1.0/(48*t) + 7.0/(5760*t**3)

def Z_wave(t, theta, Xcut):
    """2 sum_{n=1}^{min(Xcut, floor(sqrt(t/2pi)))} n^{-1/2} cos(theta - t log n).
       numpy float64, loop over n accumulating in place (O(len t) memory)."""
    nmax_grid = np.floor(np.sqrt(t / (2*math.pi))).astype(int)
    W = np.zeros_like(t)
    Nbig = min(Xcut, int(nmax_grid.max()))
    for n in range(1, Nbig + 1):
        mask = nmax_grid >= n  # n included only where it's below the RS cutoff
        if not mask.any():
            continue
        W[mask] += (1.0/math.sqrt(n)) * np.cos(theta[mask] - t[mask]*math.log(n))
    return 2.0 * W

pr("")
pr("Convergence of crossings to canonical gamma_n as integer cutoff X grows:")
pr(f"{'phase':>12} {'X':>5} {'#cross':>7} {'RMS->gamma':>11}  first 6 predicted vs gamma")
for label, theta in [("argGamma", theta_G), ("Stirling", theta_stir)]:
    for X in [1, 2, 3, 5, 10, 20, 40]:
        W = Z_wave(t, theta, X)
        cr = crossings(t, W)
        cr = cr[(cr >= 3.0) & (cr <= 58.0)]
        rms = rms_to_gamma(cr, gam_in)
        # first 6 predicted (sorted) crossings
        pred6 = np.round(np.sort(cr)[:6], 3).tolist()
        pr(f"{label:>12} {X:>5} {len(cr):>7} {rms:>11.4f}  {pred6}")
        del W, cr
    pr("")
pr("canonical first 6 gamma_n:", np.round(gam_in[:6], 3).tolist())
