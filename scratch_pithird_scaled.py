"""
Apply Sam's correction: scale EVERYTHING by pi/3 -- the integers themselves, not just spacing.
Scaled integer m = n*(pi/3).  It must appear everywhere n did: amplitude m^{-1/2} AND the spin.

Two faithful readings of how the scaled integer drives the spin:
  (a) spin = m              = n*(pi/3)          (the scaled integer IS the angle; mod 2pi -> mod 6)
  (b) spin = log(m)         = log(n*pi/3)       (climb coordinate of the scaled integer)
Show both vs the true zeros.  mpmath only as yardstick.
"""
import numpy as np, math
import mpmath as mp
mp.mp.dps = 18

PI = math.pi
U = PI / 3
n = np.arange(1, 60001, dtype=float)
m = n * U                       # the scaled integer
amp = m ** (-0.5)              # magnitude, scaled too
sign = (-1.0) ** (n - 1)      # eta alternating (zeta channel) for convergence
A = (sign * amp * np.exp(-(n / n[-1]) ** 2)).astype(complex)

gammas = [float(mp.im(mp.zetazero(k))) for k in range(1, 16)]
ys = np.linspace(1.0, 70.0, 8000)

def dips(freq, points):
    pts = np.asarray(points, float); out = np.empty(len(pts))
    for i in range(0, len(pts), 300):
        Mx = np.exp(-1j * np.outer(pts[i:i+300], freq))
        out[i:i+300] = np.abs(Mx @ A)
    return out

print("true zeros γ_k:", [round(g, 2) for g in gammas[:8]], "\n")
# (a) spin = scaled integer m = n*pi/3   (sweep a scale c on the freq so it's a fair search)
print("(a) spin = m = n*(pi/3)  [the scaled integer as the angle, mod-6]")
for c in [1.0]:
    base = float(np.median(dips(c * m, ys)))
    r = [round(v / base, 3) for v in dips(c * m, gammas)]
    allv = dips(c * m, ys)
    deep = ys[1:-1][(allv[1:-1] < allv[:-2]) & (allv[1:-1] < allv[2:]) & (allv[1:-1] < 0.30 * base)]
    print(f"    dip ratio at γ_k: {r[:8]}   resolved: {sum(1 for x in r if x<0.3)}/15")
    print(f"    its own deep minima in [1,70]: {len(deep)}  -> {'PERIODIC/none' if len(deep)<3 or len(deep)>40 else [round(x,1) for x in deep[:12]]}")

# (b) spin = log(m) = log(n*pi/3)   (climb coordinate of the scaled integer; zeros at gamma)
print("\n(b) spin = log(m) = log(n*pi/3)  [climb coordinate of the scaled integer]")
freq = np.log(m)
base = float(np.median(dips(freq, ys)))
r = [round(v / base, 4) for v in dips(freq, gammas)]
allv = dips(freq, ys)
deep = ys[1:-1][(allv[1:-1] < allv[:-2]) & (allv[1:-1] < allv[2:]) & (allv[1:-1] < 0.30 * base)]
print(f"    dip ratio at γ_k: {r[:8]}   resolved: {sum(1 for x in r if x<0.3)}/15")
print(f"    its own deep minima in [1,70]: {len(deep)} at {[round(x,1) for x in deep[:16]]}")
print(f"    NOTE: log(n*pi/3) = log n + log(pi/3); the pi/3 is a constant shift (global phase).")
