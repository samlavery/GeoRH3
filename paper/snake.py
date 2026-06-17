import math, cmath
pi = math.pi

# ===================== A REAL GEOMETRIC OBJECT =====================
# Archimedean spiral, pi/3 radial growth per loop, integers pi/6 apart on the arc.
#   R = c*theta,  radial gain per loop = c*2pi = pi/3  ->  c = 1/6
#   integer n at arc s_n = n*(pi/6):   theta_n = sqrt(2*pi*n),  R_n = c*theta_n
c = 1/6
def theta(n): return math.sqrt(2*pi*n)        # winding angle (where the integer sits)
def amp(n):   return 1.0/(c*theta(n))         # radial readout 1/R ~ n^{-1/2}

# conductor q=3: snake buckets +1 on n=1(3), -1 on n=2(3), IGNORES n=0(3)
def chi(n):
    r = n % 3
    return 1 if r == 1 else (-1 if r == 2 else 0)

# THE SNAKE: climb, eat integer n, add phasor amp(n)*e^{i theta_n} with sign chi(n).
# track the running sum S and its magnitude vs the climb height z = theta(N).
S = 0+0j
print("  climb height z       |accumulated S|   (does it return to 0?)")
checkpoints = [3,9,30,90,300,900,3000,9000,30000,90000,300000]
ci = 0
for N in range(1, 300001):
    s = chi(N)
    if s:
        S += s * amp(N) * cmath.exp(1j*theta(N))
    if ci < len(checkpoints) and N == checkpoints[ci]:
        print(f"   N={N:>7}  z={theta(N):8.3f}   |S|={abs(S):.5f}")
        ci += 1

# also: scan for the deepest approaches to the origin (candidate 'vanishings')
S = 0+0j; best=[]
for N in range(1, 300001):
    s = chi(N)
    if s: S += s*amp(N)*cmath.exp(1j*theta(N))
    best.append((abs(S), N))
best.sort()
print("\n deepest approaches to origin (|S|, N, height z):")
seen=set()
for m,N in best[:12]:
    z=round(theta(N),2)
    if z not in seen:
        seen.add(z); print(f"   |S|={m:.4f}  N={N:>7}  z={theta(N):.3f}")
print("\n first L(chi_3) zero (target) ~ 8.0398")
