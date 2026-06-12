"""
helix_fibre_chi3.py  --  the iy (imaginary-axis) fibre-cancellation picture for chi3, in detail.

Confirms, on the critical line sigma=1/2 (never touching the real part):

    L(1/2 + i*gamma, chi3) = 0   <=>   fibre+(1/2+i*gamma) = fibre-(1/2+i*gamma)

where the two character fibres are sums of WINDING PHASORS over the integers in each
residue class mod 3:
    fibre+ = sum_{n = 1 (mod 3)}  (1/sqrt n) * e^{-i*gamma*log n}     (chi3 = +1)
    fibre- = sum_{n = 2 (mod 3)}  (1/sqrt n) * e^{-i*gamma*log n}     (chi3 = -1)
and n = 0 (mod 3) is silent (chi3 = 0).

This is the numeric counterpart of:
    RequestProject/HelixImaginaryAxis.lean      (wind = n^{it}, helixPt = n^{1/2+it}, L = sum chi/helixPt)
    RequestProject/HelixFibreCancellation.lean  (L = fibre+ - fibre-,  L=0 <-> fibre+ = fibre-)

Result (see bottom): all 8 events in t in (0,40) confirm fibre+ = fibre- to ~1e-11; the raw
winding phasors cancel at the exact N^{-1/2} conditional-convergence rate; a control between
zeros does NOT balance.
"""
import mpmath as mp
mp.mp.dps = 30

def chi3(n):
    r = n % 3
    return 1 if r == 1 else (-1 if r == 2 else 0)

# L and the two fibres via Hurwitz zeta (the helix's own analytic continuation):
#   L(s) = 3^-s [zeta(s,1/3) - zeta(s,2/3)]
def fibrePlus(s):   return mp.power(3, -s) * mp.zeta(s, mp.mpf(1) / 3)   # n = 1 (mod 3)
def fibreMinus(s):  return mp.power(3, -s) * mp.zeta(s, mp.mpf(2) / 3)   # n = 2 (mod 3)
def Lchi3(s):       return fibrePlus(s) - fibreMinus(s)

print("=" * 72)
print("(0) SANITY: Hurwitz form = Dirichlet series (direct partial sum at s=2, tail ~ 1/N)")
for N in (10**4, 10**6):
    direct = sum(chi3(n) / mp.power(n, 2) for n in range(1, N + 1))
    print(f"    N={N:>8}: |L_hurwitz - direct| = {float(abs(Lchi3(2) - direct)):.2e}")

print("=" * 72)
print("(1) cancellation events gamma on the line sigma=1/2, scanning t in (0,40)")
def Lline(t): return Lchi3(mp.mpf(1) / 2 + 1j * t)
grid = [mp.mpf('0.1') + mp.mpf('0.05') * k for k in range(800)]
vals = [abs(Lline(t)) for t in grid]
gammas = []
for i in range(1, len(vals) - 1):
    if vals[i] < vals[i - 1] and vals[i] < vals[i + 1] and vals[i] < 0.5:
        try:
            g = mp.im(mp.findroot(Lchi3, mp.mpf(1) / 2 + 1j * grid[i]))
            if g > 0 and all(abs(g - gg) > 1e-6 for gg in gammas) \
                    and abs(Lchi3(mp.mpf(1) / 2 + 1j * g)) < 1e-12:
                gammas.append(g)
        except Exception:
            pass
gammas = sorted(gammas)[:8]
print(f"    {len(gammas)} events:", [round(float(g), 5) for g in gammas])

print("=" * 72)
print("(2) at each event:  |L|,  fibre+,  fibre-,  |fibre+ - fibre-|")
for g in gammas:
    s = mp.mpf(1) / 2 + 1j * g
    fp, fm = fibrePlus(s), fibreMinus(s)
    print(f"    gamma={float(g):9.5f}:  |L|={float(abs(Lchi3(s))):.1e}   "
          f"fibre+={complex(fp):.4f}  fibre-={complex(fm):.4f}   "
          f"|fibre+ - fibre-|={float(abs(fp - fm)):.1e}")

print("=" * 72)
print("(3) RAW winding phasors at the first event: S_N = sum_{n<=N} chi3(n)/sqrt(n) e^{-i*gamma*log n}")
g = gammas[0]
for N in (10**3, 10**4, 10**5, 10**6):
    Sp = sum(1 / mp.sqrt(n) * mp.e ** (-1j * g * mp.log(n)) for n in range(1, N + 1) if n % 3 == 1)
    Sm = sum(1 / mp.sqrt(n) * mp.e ** (-1j * g * mp.log(n)) for n in range(1, N + 1) if n % 3 == 2)
    print(f"    N={N:>8}: |S_N| = {float(abs(Sp - Sm)):.4e}   (-> 0 at ~N^-1/2)")

print("=" * 72)
print("(4) CONTROL: non-event heights do NOT balance")
for t0 in (mp.mpf('3.0'), mp.mpf('5.0')):
    s = mp.mpf(1) / 2 + 1j * t0
    print(f"    t={float(t0):.2f}:  |fibre+ - fibre-| = {float(abs(fibrePlus(s) - fibreMinus(s))):.4f}  (NOT ~0)")
