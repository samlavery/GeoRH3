"""
The ACTUAL chi3 helix (mode 6): radius grows by e^6 each loop, smoothly.
   R(n) = e^6 * sqrt(n)            (area law k=sqrt(n); +e^6 per loop, linear/Archimedean)
   height (up)   = 2*log R(n) = 12 + log n     (log BORN here: 2*log of the radius)
   sigma-mode amplitude (out) = R(n)^{-2 sigma}
Helix value:
   W(sigma,gamma) = sum_{prime powers} Lambda(n) chi3(n) * R(n)^{-2 sigma} * e^{-i gamma * 2 log R(n)}
UP axis (gamma, at sigma=1/2)  -> the chi3 zero ordinates
OUT axis (sigma, at a zero)    -> resonance blows up as sigma -> 1/2 (the line)
No zero fed in.
"""
import numpy as np, math
import mpmath as mp
from scipy.signal import find_peaks

mode = 6.0

# ---- chi3 zeros via mpmath, ONLY to check the peaks (never fed into the helix) ----
mp.mp.dps = 12
def Lchi3(t):
    s = mp.mpf(0.5) + 1j*mp.mpf(t)
    return mp.power(3, -s) * (mp.zeta(s, mp.mpf(1)/3) - mp.zeta(s, mp.mpf(2)/3))
ts = np.arange(0.4, 25.0, 0.02)
av = np.array([float(abs(Lchi3(float(t)))) for t in ts])
mins, _ = find_peaks(-av, prominence=0.25)
chi3_zeros = [round(float(ts[i]), 3) for i in mins if av[i] < 0.25]
print("chi3 zeros (|L(1/2+it)| minima):", chi3_zeros)

# ---- sieve + von Mangoldt + chi3 ----
Ncut, Nmax = 100_000, 1_200_000
sieve = np.ones(Nmax+1, bool); sieve[:2] = False
for i in range(2, int(Nmax**0.5)+1):
    if sieve[i]: sieve[i*i::i] = False
primes = np.nonzero(sieve)[0]
Lam = np.zeros(Nmax+1)
for p in primes.tolist():
    lp = math.log(p); pk = p
    while pk <= Nmax: Lam[pk] = lp; pk *= p
n = np.nonzero(Lam)[0]
lam = Lam[n]
chi = np.where(n % 3 == 1, 1.0, np.where(n % 3 == 2, -1.0, 0.0))   # chi3
w = lam * chi
nf = n.astype(float)
R = math.exp(mode) * np.sqrt(nf)          # e^6 * sqrt(n)  -- grows by e^6 each loop
scale = 2.0 * np.log(R)                    # height = 2 log R = 12 + log n
cut = np.exp(-nf / Ncut)

def Wmag(sigma, gam):
    amp = w * R**(-2.0*sigma) * cut        # R^{-2 sigma} radial amplitude (out)
    return abs(np.sum(amp * np.exp(-1j*gam*scale)))

# ---- UP axis: produce the chi3 ordinates at sigma = 1/2 ----
gammas = np.arange(0.2, 25.0, 0.02)
absW = np.array([Wmag(0.5, g) for g in gammas])
pk, _ = find_peaks(absW, prominence=absW.max()*0.10, distance=int(0.8/0.02))
print("\nUP axis (sigma=1/2): helix peak  vs  nearest chi3 zero")
for i in pk:
    g = gammas[i]
    if not chi3_zeros: break
    z = min(chi3_zeros, key=lambda z: abs(z-g))
    flag = "" if abs(g-z) < 0.1 else "   (side-lobe)"
    print(f"   {g:7.3f}   |W|={absW[i]/absW.max():.3f}   zero {z:7.3f}   err {g-z:+.3f}{flag}")

# ---- OUT axis: at the first zero, sweep sigma; envelope e^{-12 sigma} divided out ----
if chi3_zeros:
    g1 = chi3_zeros[0]
    sig = np.arange(0.50, 0.96, 0.02)
    prof = np.array([Wmag(s, g1)*math.exp(2*mode*s) for s in sig])   # = |trunc -L'/L(sigma+i g1)|
    mx = prof.max()
    print(f"\nOUT axis: radial resonance |W(sigma, gamma_1={g1})|  (e^6 envelope removed)")
    print(f"   grows as sigma -> 1/2 (the pole sits ON the line); below 1/2 the prime series diverges")
    for s, v in zip(sig, prof):
        print(f"   sigma={s:.2f} |{'#'*int(44*v/mx)}")
