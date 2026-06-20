"""
Corrected phasor model (per Sam: "sqrt all over the place means it's wrong").

The spin/frequency of mode n is NOT the physical winding 2*pi*k (~sqrt n).  It is the
CLIMB COORDINATE y_n of integer n on the exponential-climb carrier (kClimb = e^y/p).
With uniform arclength arc(n)=n*Delta and the genuine ClosedForm helix:
    radius = r*k (linear in k)  =>  arclength S(k) ~ pi*r*k^2  =>  k_n ~ sqrt(n)
    climb coordinate            y_n = log(height) = log(p*k_n) ~ (1/2) log n
So the ONLY sqrt is the physical turn k_n; the climb coordinate is logarithmic.
sqrt belongs only in the amplitude n^{-1/2} (the 1/2).  Phase = climb coord ~ log n.

Test: does the fiber with spin = climb coordinate resolve the zeros?
(mpmath only as yardstick for the true gamma_k.)
"""
import numpy as np, math
import mpmath as mp

mp.mp.dps = 20
PI = math.pi
DELTA = PI / 3
p = r = 1.0

# ---- ClosedForm closed-form arclength S(k) and its inverse k(S) ----
def arclength(k):
    root = math.sqrt(p**2 + r**2 + 4 * PI**2 * r**2 * k**2)
    return k / 2 * root + (p**2 + r**2) / (4 * PI * r) * math.asinh(2 * PI * r * k / math.sqrt(p**2 + r**2))

Nmax = 60000
kgrid = np.linspace(0.0, 2.0 * math.sqrt(Nmax * DELTA / (PI * r)) + 10, 400000)
Sgrid = np.array([arclength(float(k)) for k in kgrid])

n = np.arange(1, Nmax + 1, dtype=float)
S_n = n * DELTA                       # uniform arclength placement
k_n = np.interp(S_n, Sgrid, kgrid)    # invert arclength -> turn parameter (~sqrt n)
height_n = p * k_n                     # physical height = p*k (~sqrt n)
y_n = np.log(height_n)                # CLIMB COORDINATE = log(height) (~ (1/2) log n)

# ---- prove the geometry yields a LOG (not sqrt) climb coordinate ----
slope_y, int_y = np.polyfit(np.log(n[100:]), y_n[100:], 1)
slope_k, int_k = np.polyfit(np.log(n[100:]), np.log(k_n[100:]), 1)
print("=" * 80)
print("GEOMETRY CHECK — what scales like what (fit exponent b in quantity ~ n^b ... or ~ log n)")
print("=" * 80)
print(f"  physical turn k_n         ~ n^{slope_k:.4f}      (≈ 0.5  -> sqrt n : the physical sqrt)")
print(f"  climb coordinate y_n=log(height) = {slope_y:.4f}*log n + {int_y:.3f}   (slope ≈ 0.5 -> y_n ∝ log n)")
print(f"  => the carrier's natural coordinate is LOGARITHMIC; sqrt is only the physical turn.\n")

# ---- the fiber: amplitude n^{-1/2} (the ONLY sqrt), phase = climb coordinate ----
sign = (-1.0) ** (n - 1)              # eta (alternating) for convergence on the line
amp = sign * n ** (-0.5)             # amplitude n^{-1/2} : the legitimate 1/2
taper = np.exp(-(n / Nmax) ** 2)

gammas = [float(mp.im(mp.zetazero(kk))) for kk in range(1, 16)]
# y_n ≈ (1/2) log n  => spin y_n gives zeros at t = 2*gamma.  Use freq = 2*y_n ≈ log n -> zeros at gamma.
freq_climb = 2.0 * y_n               # = 2*log(height) ≈ log n  (climb coordinate, geometric)
freq_wind = 2 * PI * k_n             # the WRONG one I used before (~ sqrt n)

def fiber_abs_at(freq, points):
    A = (taper * amp).astype(complex)
    pts = np.asarray(points, float)
    out = np.empty(len(pts))
    CH = 300
    for i in range(0, len(pts), CH):
        M = np.exp(-1j * np.outer(pts[i:i+CH], freq))
        out[i:i+CH] = np.abs(M @ A)
    return out

# diagnostics: how does the geometric climb freq compare to exact log n at SMALL n?
print("  small-n check (small n dominate the n^{-1/2} sum):")
print(f"  {'n':>3} {'log n':>9} {'2·y_n (geom climb)':>20} {'diff':>9}")
for nn in [1, 2, 3, 4, 5, 8, 16, 64, 1000]:
    print(f"  {nn:>3} {math.log(nn):>9.4f} {2*y_n[nn-1]:>20.4f} {2*y_n[nn-1]-math.log(nn):>9.4f}")
print()

freq_exactlog = np.log(n)                                   # control: exact log n -> must resolve
freq_asym = 2.0 * (slope_y * np.log(n) + int_y)            # smooth asymptotic climb (no small-n wobble)

ys = np.linspace(1.0, 70.0, 8000)
print("=" * 80)
print("FIBER TEST — which spin resolves the zeros?")
print("=" * 80)
print(f"  true zeros γ_k: {[round(g,2) for g in gammas[:8]]}\n")
for name, freq in [("EXACT log n (control)", freq_exactlog),
                   ("ASYMPTOTIC climb 2·(½log n+c) (smooth, no small-n wobble)", freq_asym),
                   ("GEOMETRIC climb 2·y_n (exact, with small-n corrections)", freq_climb),
                   ("WINDING 2πk ≈ sqrt n (my earlier WRONG model)", freq_wind)]:
    allv = fiber_abs_at(freq, ys)
    base = float(np.median(allv))
    ratios = [v / base for v in fiber_abs_at(freq, gammas)]
    found = sum(1 for rr in ratios if rr < 0.30)
    deep = ys[1:-1][(allv[1:-1] < allv[:-2]) & (allv[1:-1] < allv[2:]) & (allv[1:-1] < 0.30 * base)]
    print(f"  {name}")
    print(f"     dip ratio at γ_k: {[round(rr,3) for rr in ratios[:8]]}")
    print(f"     # γ_k resolved (ratio<0.30): {found}/15")
    print(f"     its own deep minima in [1,70]: {len(deep)} at {[round(x,1) for x in deep[:14]]}")
    print()
print("=" * 80)
