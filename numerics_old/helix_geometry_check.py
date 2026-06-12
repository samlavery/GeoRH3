"""
helix_geometry_check.py -- validate the helix geometry against the chi3 zeros.

Questions (Sam): is the radial-growth constant right? the pitch? is it a helix / cylinder / cube?
the distance between integers?

What the zeros (the 1-D/2-D SHADOW) can and cannot fix (Rule Five: the projection is lossy upward):
  SHADOW-VISIBLE (testable here):
    * the radial-growth EXPONENT sigma  -> the SHAPE.  sigma=1/2 (sqrt-packing, area law) = HELIX.
        sigma=0 would be a CYLINDER (constant radius, no decay); sigma=1 a CONE/CUBE (linear radius).
    * the closure AMPLITUDE  |L_M|*M^{1/2} -> |A(M) - L(0,chi3)| in {1/3,2/3}  (the radial constant).
    * the PITCH / fold-count: the local zero density 1/dgamma ~ (1/2pi) log(q gamma/2pi) -> recovers
        q (= number of fibres = 3) and the 2pi winding period.
  NOT shadow-visible (3-D gauge, can't be read off the strip): the absolute integer spacing U, the
    absolute radial rate e^{mode}, the absolute axial pitch length. Only the exponent + amplitude +
    period survive the projection.
"""
import math, cmath

q = 3
def chi3(n):
    r = n % 3
    return 1 if r == 1 else (-1 if r == 2 else 0)

gammas = []
with open("lchi3_zeros_1000.txt") as f:
    for line in f:
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        gammas.append(float(line.split()[1]))
gammas.sort()

def Labs(g, M):
    L = 0j
    for n in range(1, M + 1):
        c = chi3(n)
        if c:
            L += c * n ** (-0.5) * cmath.exp(-1j * g * math.log(n))
    return abs(L)

# ============================================================================ (1) SHAPE
print("=" * 84)
print("(1) SHAPE = radial-growth exponent.  |L_M(1/2+i gamma)| * M^sigma at two far-apart M.")
print("    a STABLE column (same value at both M) is the true radial exponent.")
print("    sigma=0 -> CYLINDER | sigma=1/2 -> HELIX (sqrt-packing) | sigma=1 -> CONE/CUBE")
print("=" * 84)
M1, M2 = 10000, 40000   # both = 1 (mod 3): A(M)=1, |A-1/3| = 2/3
for gi in (0, 1, 4, 9):
    g = gammas[gi]
    a1, a2 = Labs(g, M1), Labs(g, M2)
    print(f"  gamma={g:8.4f}:")
    for sig in (0.0, 0.25, 0.5, 0.75, 1.0):
        v1, v2 = a1 * M1 ** sig, a2 * M2 ** sig
        tag = "  <== STABLE (the exponent)" if abs(v1 - v2) < 0.03 * max(v1, 1e-9) else ""
        print(f"      sigma={sig:4.2f}:  M={M1}: {v1:10.4f}   M={M2}: {v2:10.4f}{tag}")

# ============================================================================ (2) RADIAL CONSTANT
print("=" * 84)
print("(2) RADIAL-GROWTH CONSTANT = the closure amplitude  |L_M|*sqrt(M) -> |A(M) - L(0,chi3)|.")
print("    L(0,chi3) = 1/3 (proven cmean_chi3).  Expect the band {1/3=0.333, 2/3=0.667} by M mod 3.")
print("=" * 84)
g = gammas[0]
for M in range(3000, 3010):
    A = sum(chi3(n) for n in range(1, M + 1))
    amp = Labs(g, M) * math.sqrt(M)
    print(f"   M={M} (M%3={M%3}): A(M)={A:2d}  |A-1/3|={abs(A-1/3):.4f}   |L_M|*sqrt(M)={amp:.4f}")

# ============================================================================ (3) PITCH / FOLD COUNT
print("=" * 84)
print("(3) PITCH / FOLD COUNT from the zero density.  1/dgamma  vs  (1/2pi) log(q gamma/2pi).")
print("    matching => q=3 fibres and 2pi winding period are the recoverable 'pitch'.")
print("    (first 20 zeros only: the file is sparse after #20)")
print("=" * 84)
consec = gammas[:20]
num, den = 0.0, 0.0   # least-squares recover q: density = (1/2pi) log(q gamma/2pi)
for i in range(len(consec) - 1):
    gmid = 0.5 * (consec[i] + consec[i + 1])
    demp = 1.0 / (consec[i + 1] - consec[i])
    dth = (1 / (2 * math.pi)) * math.log(q * gmid / (2 * math.pi))
    print(f"   gamma~{gmid:7.3f}:  empirical 1/dgamma={demp:.4f}   theory(q=3)={dth:.4f}   ratio={demp/dth:.3f}")
    # recover q: 2pi*density = log(q) + log(gamma/2pi)  ->  log q = 2pi*density - log(gamma/2pi)
    num += 2 * math.pi * demp - math.log(gmid / (2 * math.pi)); den += 1
logq_fit = num / den
print(f"   --> recovered fold count q = exp(mean) = {math.exp(logq_fit):.3f}   (construction uses q=3)")

# ============================================================================ (4) INTEGER SPACING
print("=" * 84)
print("(4) DISTANCE BETWEEN INTEGERS.  In the sqrt-packing the n-th integer sits at radius sqrt(n);")
print("    the radial gap sqrt(n+1)-sqrt(n) ~ 1/(2 sqrt n) SHRINKS — integers are NOT evenly spaced")
print("    radially.  Even spacing is along the ARC (gauge U), which the zeros do NOT fix.")
print("=" * 84)
for n in (1, 4, 9, 16, 100):
    print(f"   n={n:4d}: radius sqrt(n)={math.sqrt(n):.3f}   radial gap to n+1 = {math.sqrt(n+1)-math.sqrt(n):.4f}   ~ 1/(2 sqrt n)={1/(2*math.sqrt(n)):.4f}")
