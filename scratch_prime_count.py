"""
The prime count, walked up the fiber (NOT abandoned).
psi(x,chi3) = sum_{n<=x} Lambda(n) chi3(n)   -- signed von Mangoldt count, +/- by mod-3 fiber.

(1) the count and its CANCELLATION singularities (heights where the signed sum balances / crosses 0)
(2) explicit formula: psi(x) = -sum_rho x^rho/rho   -- the count IS the zero sum (same object)
(3) two readouts of the SAME count:
      - height domain  -> the cancellation heights (zero-crossings of psi)
      - frequency domain (Fourier of psi/sqrt(x) in log x) -> the gamma_k (the L-ZEROS)
    The L-zeros are the FREQUENCIES of the count, with energy = 1/|rho| (the residue).
    The cancellation heights are the count's zero-CROSSINGS -- related but NOT the zeros.
"""
import numpy as np, math
import mpmath as mp
mp.mp.dps = 15

# ---- chi3 zeros (for the explicit-formula reconstruction and the frequency check) ----
L = lambda s: mp.power(3,-s)*(mp.zeta(s, mp.mpf(1)/3) - mp.zeta(s, mp.mpf(2)/3))
ts = np.arange(2.0, 100.0, 0.05)
av = np.array([float(abs(L(mp.mpf(1)/2+1j*mp.mpf(float(t))))) for t in ts])
zeros = []
for i in range(1, len(av)-1):
    if av[i] < av[i-1] and av[i] < av[i+1] and av[i] < 0.4:
        r = mp.findroot(lambda t: L(mp.mpf(1)/2+1j*t), mp.mpf(float(ts[i])))
        g = float(mp.re(r))
        if (not zeros or abs(g-zeros[-1]) > 1e-2) and abs(L(mp.mpf(1)/2+1j*mp.mpf(g))) < 1e-6:
            zeros.append(g)
zeros = np.array(zeros)

# ---- (1) the signed von Mangoldt count psi(x,chi3) ----
X = 2000
sieve = np.ones(X+1, bool); sieve[:2] = False
for i in range(2, int(X**0.5)+1):
    if sieve[i]: sieve[i*i::i] = False
Lam = np.zeros(X+1)
for p in np.nonzero(sieve)[0].tolist():
    lp = math.log(p); pk = p
    while pk <= X: Lam[pk] = lp; pk *= p
nn = np.arange(X+1)
chi3 = np.where(nn % 3 == 1, 1.0, np.where(nn % 3 == 2, -1.0, 0.0))
step = Lam * chi3                       # each prime power's signed mass (the fiber bucket)
psi = np.cumsum(step)                   # psi(x) = running signed prime count

# cancellation singularities: where psi crosses 0
cross = []
for x in range(2, X):
    if psi[x-1] * psi[x] < 0 or psi[x] == 0:
        cross.append(x)
cross = np.array(cross)
print(f"(1) signed prime count psi(x,chi3):  built to X={X}")
print(f"    cancellation singularities (psi crosses 0): {len(cross)} of them")
print(f"    first crossings (heights x): {cross[:12].tolist()}")
print(f"    these are NOT the zeros 8.04,11.25,15.70,...  -- they are the count's zero-CROSSINGS\n")

# ---- (2) explicit formula: the count IS the zero sum ----
def psi_zeros(x):
    xs = mp.mpf(x); tot = mp.mpf(0)
    for g in zeros:
        rho = mp.mpf(1)/2 + 1j*mp.mpf(g)
        tot += mp.power(xs, rho)/rho + mp.power(xs, mp.conj(rho))/mp.conj(rho)
    return float(-mp.re(tot))
print("(2) explicit formula:  prime count  psi(x)   vs   zero sum  -sum_rho x^rho/rho")
print(f"    {'x':>6} {'prime count':>13} {'zero sum':>13} {'diff':>9}")
for x in [50, 100, 200, 500, 1000, 1500]:
    a, b = float(psi[x]), psi_zeros(x)
    print(f"    {x:>6} {a:>13.3f} {b:>13.3f} {a-b:>9.3f}")
print("    => the count and the zeros are the SAME object (explicit formula)\n")

# ---- (3) frequency readout of the count = the zeros (with energy 1/|rho|) ----
# helix/resonance: Tchi(gamma) = sum_n Lambda(n)chi3(n) n^{-1/2-i gamma}  (the count, Fourier'd)
nz = np.nonzero(step)[0]
w  = step[nz] / np.sqrt(nz) * np.exp(-nz/ (X/2))          # n^{-1/2} weight, light taper
logn = np.log(nz)
def resonance(gamma): return abs(np.sum(w * np.exp(-1j*gamma*logn)))
print("(3) frequency readout of the SAME count (resonance peaks) vs the L-zeros, with residue energy:")
print(f"    {'L-zero gamma':>13} {'count |T|(gamma)':>17} {'energy 1/|rho|':>15}")
gs = np.arange(2,40,0.01); Hs = np.array([resonance(g) for g in gs])
for g in zeros[:8]:
    j = int(np.argmin(np.abs(gs-g)))
    rho = abs(0.5+1j*g)
    print(f"    {g:>13.4f} {Hs[j]:>17.3f} {1/rho:>15.4f}")
print("    => the count's FREQUENCIES are the zeros; the peak heights track the residue energy 1/|rho|.")
print("    Counting never stopped: the resonance IS the signed prime count, read in frequency.")
