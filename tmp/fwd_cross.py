"""
Forward crossing test. Compare zeros (sign changes) of forward waves to canonical gamma_n.
Report ACTUAL NUMBERS.
"""
import mpmath as mp
import math
import numpy as np

mp.mp.dps = 25

# ---------------- canonical gamma_n (ONLY for comparison) ----------------
def canonical_gammas(M):
    return np.array([float(mp.im(mp.zetazero(n))) for n in range(1, M+1)])

# ---------------- prime powers up to X ----------------
def prime_powers(X):
    Xc = int(X)
    sieve = np.ones(Xc+1, bool); sieve[:2] = False
    for i in range(2, int(Xc**0.5)+1):
        if sieve[i]: sieve[i*i::i] = False
    primes = np.nonzero(sieve)[0]
    P, K, LP = [], [], []
    for p in primes.tolist():
        lp = math.log(p); pk = p; k = 1
        while pk <= Xc:
            P.append(p); K.append(k); LP.append(lp)
            pk *= p; k += 1
    return np.array(P, float), np.array(K, float), np.array(LP, float)

# ---------------- sign-change crossings of a sampled wave ----------------
def crossings(tgrid, w):
    sgn = np.sign(w)
    idx = np.nonzero(sgn[:-1] * sgn[1:] < 0)[0]
    # linear interpolation for the crossing location
    t0 = tgrid[idx]; t1 = tgrid[idx+1]
    w0 = w[idx]; w1 = w[idx+1]
    return t0 - w0 * (t1 - t0) / (w1 - w0)

def rms_match(cross, gammas):
    """For each gamma_n find nearest crossing; RMS distance over gammas in range."""
    if len(cross) == 0: return float('nan'), 0
    diffs = []
    for g in gammas:
        j = np.argmin(np.abs(cross - g))
        diffs.append(cross[j] - g)
    diffs = np.array(diffs)
    return math.sqrt(np.mean(diffs**2)), len(diffs)

# ================= S1: BARE prime-power fluctuation =================
def wave_S1(tgrid, pps):
    P, K, LP = pps
    amp = LP * P**(-K/2.0)            # (log p) p^{-k/2}
    phase = np.outer(tgrid, K*LP)     # t * k log p
    W = -2.0 * (np.cos(phase) * amp).sum(axis=1)
    return W

# ================= S2: Riemann-Siegel main sum (BORROWS Gamma) =================
def theta_gamma(t):
    """ theta(t) = arg Gamma(1/4 + it/2) - (t/2) log pi.  BORROWED (Gamma)."""
    return float(mp.siegeltheta(t))

def wave_S2(tgrid):
    W = np.zeros_like(tgrid)
    for i, t in enumerate(tgrid):
        th = theta_gamma(t)
        nmax = int(math.sqrt(t/(2*math.pi)))
        s = 0.0
        for n in range(1, nmax+1):
            s += math.cos(th - t*math.log(n)) / math.sqrt(n)
        W[i] = 2.0 * s
    return W

# ============ S3: APPROACH B -- prime-power fluct + GEOMETRIC smooth phase ============
# Geometric counting law candidates (NO arg Gamma):
#   N_geo(T) = (T/2pi) log(T/2pi) - T/2pi      <- the log-T density. Is this geometric?
# We then form a "Z-like" wave: cos(pi*N_geo(t)) modulated, OR use the phase = pi*N_smooth.
# The standard relation: theta(t)/pi + 1 = N_smooth(t), with N(T) = theta(T)/pi + 1 + S(T).
# So theta(t) = pi*(N_smooth(t) - 1). If N_geo reproduces theta/pi, we can build Z.

def N_smooth_logT(t):
    """ Riemann-von Mangoldt smooth count: (t/2pi) log(t/2pi) - t/2pi + 7/8 .
        This is the LOG-T DENSITY law. Derivable from theta asymptotics OR from geometry? """
    x = t/(2*math.pi)
    return x*math.log(x) - x + 7.0/8.0

def theta_from_Ngeo(t):
    """ theta(t) = pi*(N_smooth(t) - 1)  using the geometric/log-T smooth count. """
    return math.pi*(N_smooth_logT(t) - 1.0)

def wave_S3(tgrid, pps_for_fluct=None):
    """ Build Z-like wave with GEOMETRIC theta (from log-T count) and arithmetic Dirichlet sum.
        Z(t) = 2 sum_{n<=sqrt(t/2pi)} n^{-1/2} cos(theta_geo(t) - t log n).
        The n-sum is the integer/arithmetic part; theta_geo is from the count law (no Gamma). """
    W = np.zeros_like(tgrid)
    for i, t in enumerate(tgrid):
        th = theta_from_Ngeo(t)
        nmax = int(math.sqrt(t/(2*math.pi)))
        s = 0.0
        for n in range(1, nmax+1):
            s += math.cos(th - t*math.log(n)) / math.sqrt(n)
        W[i] = 2.0 * s
    return W

if __name__ == "__main__":
    T0, T1 = 10.0, 60.0
    dt = 0.002
    tgrid = np.arange(T0, T1, dt)
    gammas = canonical_gammas(10)
    gam_in = gammas[(gammas>=T0+0.5)&(gammas<=T1-0.5)]

    print(f"Comparison window t in [{T0},{T1}], canonical gamma_n in window: {len(gam_in)}")
    print("  ", np.round(gam_in,4).tolist())
    print()

    # S1 bare prime-power, several X
    print("=== S1: BARE prime-power fluctuation  -2 sum (log p) p^{-k/2} cos(t k log p) ===")
    for X in [50, 500, 5000, 50000]:
        pps = prime_powers(X)
        W = wave_S1(tgrid, pps)
        cr = crossings(tgrid, W)
        cr = cr[(cr>=T0+0.5)&(cr<=T1-0.5)]
        rms, n = rms_match(cr, gam_in)
        print(f"  X={X:>6}  #pp={len(pps[0]):>5}  #crossings={len(cr):>4}  RMS-to-gamma={rms:.4f}")
    print()

    # S2 RS main sum (borrows Gamma)
    print("=== S2: Riemann-Siegel main sum (theta = arg Gamma, BORROWED) ===")
    W = wave_S2(tgrid)
    cr = crossings(tgrid, W)
    cr = cr[(cr>=T0+0.5)&(cr<=T1-0.5)]
    rms, n = rms_match(cr, gam_in)
    print(f"  #crossings={len(cr)}  RMS-to-gamma={rms:.5f}")
    print(f"  crossings: {np.round(np.sort(cr),4).tolist()}")
    print()

    # S3 Approach B: geometric theta from log-T count
    print("=== S3: APPROACH B  theta_geo = pi*(N_logT - 1), Dirichlet n-sum ===")
    W = wave_S3(tgrid)
    cr = crossings(tgrid, W)
    cr = cr[(cr>=T0+0.5)&(cr<=T1-0.5)]
    rms, n = rms_match(cr, gam_in)
    print(f"  #crossings={len(cr)}  RMS-to-gamma={rms:.5f}")
    print(f"  crossings: {np.round(np.sort(cr),4).tolist()}")
    print()

    # Direct check: how close is theta_geo to true theta?
    print("=== Is theta_geo (from log-T count) == arg Gamma theta? ===")
    for t in [20.0, 40.0, 60.0, 100.0]:
        tg = theta_from_Ngeo(t); tt = float(mp.siegeltheta(t))
        print(f"  t={t:>5}  theta_geo={tg:.5f}  theta_Gamma={tt:.5f}  diff={tg-tt:.6f}")
