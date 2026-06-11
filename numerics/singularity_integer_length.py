"""
singularity_integer_length.py -- "the number of integers between singularities", vs iy.

For the first chi3 zeros gamma_n on sigma = 1/2, measure how many integers must be wound onto
the helix to produce each cancellation (singularity), purely from the partial winding sums

    L_M(1/2 + i gamma) = sum_{n<=M} chi3(n) * n^{-1/2} * e^{-i gamma log n}        (chi3 = +1,-1,0)

and relate that integer-length to iy = gamma.

FRAME (the radial-growth / area law, n ~ R^2):
  - integers sit at radius R = sqrt(n)  (the sqrt-packing of HelixImaginaryAxis: helixPt = n^{1/2+it});
  - sigma = 1/2 is only the radial-growth EXPONENT, it carries no length;
  - the length (integer count) is DERIVED from the winding (iy) by the radial growth: the
    cancellation forms once enough integers have wound, and the closure ledger says
    |L_M| * sqrt(M) -> |A(M) - L(0,chi3)| in {1/3, 2/3}, so |L_M| ~ const / sqrt(M).
  - PREDICTION: the integer-length N(gamma) ~ sqrt(q gamma / 2pi), q = 3, hence
        iy = gamma ~ (2pi/q) * N^2     <-- the imaginary part is the SQUARE of the integer-length.

EMPIRICAL integer-length (independent of the formula above):
  (A) M_peak  = argmax_M |L_M|                 -- integers wound to the winding's resonance peak
  (B) M_close = last M with |L_M|*sqrt(M) > tau -- end of the transient, onset of the closure band
Then test: does the EMPIRICAL count scale as sqrt(gamma)?  (log-log slope ~ 0.5  <=>  iy ~ count^2)
"""
import math
import mpmath as mp
mp.mp.dps = 30

q = 3
TAU = 0.9          # closure-band edge for M_close (above the 2/3 ledger ceiling, below |L_1|=1)
MMAX = 600

def chi3(n):
    r = n % 3
    return 1 if r == 1 else (-1 if r == 2 else 0)

# ---- load the high-precision zeros ------------------------------------------------
gammas = []
with open("lchi3_zeros_1000.txt") as f:
    for line in f:
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        parts = line.split()
        try:
            gammas.append(mp.mpf(parts[1]))
        except Exception:
            pass
gammas.sort()

# ---- partial-sum integer-length measures ------------------------------------------
def measures(g, Mmax=MMAX):
    L = mp.mpc(0)
    absL = []          # |L_M|
    rescaled = []      # |L_M| * sqrt(M)
    for n in range(1, Mmax + 1):
        c = chi3(n)
        if c != 0:
            L += c * mp.power(n, mp.mpf(-1) / 2) * mp.e ** (-1j * g * mp.log(n))
        a = abs(L)
        absL.append(a)
        rescaled.append(a * mp.sqrt(n))
    Mpeak = max(range(Mmax), key=lambda i: absL[i]) + 1
    Mclose = 0
    for i in range(Mmax):
        if rescaled[i] > TAU:
            Mclose = i + 1
    return Mpeak, float(absL[Mpeak - 1]), Mclose

# ---- table -------------------------------------------------------------------------
NSHOW = min(25, len(gammas))
print("=" * 100)
print(f"  chi3 singularities: integer-length of the winding vs iy   (q={q}, {len(gammas)} zeros loaded)")
print("=" * 100)
print("  n |   iy = gamma |  d(iy)  | M_peak | M_close | sqrt(3g/2pi) | gamma/M_peak^2 | gamma/Mclose^2")
print("-" * 100)
rows = []
for i in range(NSHOW):
    g = gammas[i]
    Mpeak, peakval, Mclose = measures(g)
    Nafe = float(mp.sqrt(q * g / (2 * mp.pi)))
    dg = float(gammas[i + 1] - g) if i + 1 < len(gammas) else float('nan')
    gf = float(g)
    rows.append((gf, dg, Mpeak, Mclose, Nafe))
    r1 = gf / Mpeak ** 2
    r2 = gf / Mclose ** 2 if Mclose else float('nan')
    print(f" {i+1:2d} | {gf:12.6f} | {dg:7.4f} | {Mpeak:6d} | {Mclose:7d} | {Nafe:12.3f} | {r1:14.4f} | {r2:13.4f}")

# ---- scaling fits: log(count) vs log(iy);  slope 0.5  <=>  iy ~ count^2 ------------
def loglog_slope(xs, ys):
    lx = [math.log(x) for x in xs]; ly = [math.log(y) for y in ys]
    n = len(lx); sx = sum(lx); sy = sum(ly)
    sxx = sum(a * a for a in lx); sxy = sum(a * b for a, b in zip(lx, ly))
    return (n * sxy - sx * sy) / (n * sxx - sx * sx)

gs = [r[0] for r in rows]
slope_peak = loglog_slope(gs, [r[2] for r in rows])
slope_close = loglog_slope(gs, [max(r[3], 1) for r in rows])
print("=" * 100)
print(f"  log(M_peak)  ~ {slope_peak:.3f} * log(iy)        (0.500 = sqrt radial growth  =>  iy ~ integers^2)")
print(f"  log(M_close) ~ {slope_close:.3f} * log(iy)")
print(f"  AFE length sqrt(3 gamma/2pi) has slope exactly 0.500 by construction.")

# ---- the integers BETWEEN consecutive singularities -------------------------------
print("=" * 100)
print("  integers between consecutive singularities   dN = N(g_{n+1}) - N(g_n),  N = sqrt(3 g / 2pi)")
print("-" * 100)
print("  gap  |  d(iy)=gamma_{n+1}-gamma_n |  dN (integers added)  | cumulative N")
for i in range(min(18, len(gammas) - 1)):
    Na = mp.sqrt(q * gammas[i] / (2 * mp.pi)); Nb = mp.sqrt(q * gammas[i + 1] / (2 * mp.pi))
    print(f"  {i+1:2d}->{i+2:2d} |          {float(gammas[i+1]-gammas[i]):8.4f}         |       {float(Nb-Na):8.4f}        |   {float(Nb):7.3f}")
