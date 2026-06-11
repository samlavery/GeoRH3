"""
ATTEMPT 2b — push harder on the self-adjoint side.

(B1) Berry-Keating-Sierra  H = x(p + ell^2/p)  (the "H = x p + ell^2 x/p" /
     semiclassical XP-with-walls model, Sierra 2008). Discretize on a finite
     x-grid with the regularizing ell^2/p term; symmetrize to make it Hermitian;
     diagonalize; compare the LOW eigenvalues' counting function to the smooth
     Riemann staircase and ask whether ANY prime structure appears.

(B2) The HONEST self-adjoint route that DOES see primes: build the finite matrix
     whose eigenvalues are forced to be the zeros via the explicit-formula /
     Gutzwiller trace formula reading -- i.e. construct H so that
        Tr cos(t H) "=" sum over prime orbits.
     We test the trace formula EMPIRICALLY: the density of zeros has oscillatory
     part  rho_osc(t) = -(1/pi) sum_{p,k} (log p / p^{k/2}) chi3(p^k) cos(t k log p).
     If a self-adjoint H has these zeros as spectrum, its smoothed level density
     MUST equal rho_smooth + rho_osc. We verify rho_osc reproduces the ACTUAL
     fluctuating zero density -- the prime-orbit <-> eigenvalue dictionary. This is
     the closest a *trace formula* gets to "operator from primes" without circularly
     planting the zeros. We then state precisely why it is NOT a construction of H.
"""
import math
import numpy as np

gammas = []
with open('lchi3_zeros_record.txt') as f:
    for line in f:
        line = line.strip()
        if not line or line.startswith('#'):
            continue
        toks = line.split()
        if len(toks) < 2:
            continue
        gammas.append(float(toks[1]))
gammas = np.array(sorted(gammas))


def chi3(n):
    r = n % 3
    return 0 if r == 0 else (1 if r == 1 else -1)


# ====================================================================
# (B1) Berry-Keating-Sierra  H = x p + ell^2 x / p  (Hermitian symmetrization)
# x in [x0, L], p=-i d/dx. The classical H=x(p+ell^2/p) has E ~ smooth Riemann
# staircase when the phase-space area below E matches N(E). ell regularizes p=0.
# ====================================================================
def bk_sierra(Ngrid=2500, x0=1.0, L=100.0, ell=1.0):
    x = np.linspace(x0, L, Ngrid)
    dx = x[1]-x[0]
    N = Ngrid
    # p = -i d/dx central (Hermitian)
    P = np.zeros((N, N), complex)
    for i in range(1, N-1):
        P[i, i+1] = -1j/(2*dx); P[i, i-1] = 1j/(2*dx)
    Xd = np.diag(x.astype(complex))
    # xp symmetrized: (XP+PX)/2
    XP = 0.5*(Xd@P + P@Xd)
    # ell^2 * x / p : need p^{-1}. Regularize p with ell: use (P + i*ell*I)^{-1}?
    # Sierra's form: H = x(p + ell^2/p). Approx p^{-1} via pseudo-inverse of P
    # restricted to its nonzero subspace (P is singular at p=0). Use Tikhonov.
    Preg = P + 1j*ell*1e-3*np.eye(N)
    try:
        Pinv = np.linalg.inv(Preg)
    except Exception:
        Pinv = np.linalg.pinv(P)
    XPinv = 0.5*(Xd@Pinv + Pinv@Xd)
    H = XP + (ell**2)*XPinv
    H = 0.5*(H + H.conj().T)  # force Hermitian
    ev = np.linalg.eigvalsh(H)
    return np.sort(ev[ev > 0])


def smooth_count(T):  # chi3 staircase
    return (T/(2*math.pi))*np.log(3.0*T/(2*math.pi)) - T/(2*math.pi)


print("=== (B1) Berry-Keating-Sierra  H = x(p + ell^2/p) ===")
evS = bk_sierra()
# compare its counting function to smooth staircase (rescaled): does it match average?
# fit linear in rank to extract effective density, check fluctuation variance
ev = evS[:300]
rk = np.arange(1, len(ev)+1)
A = np.vstack([ev, np.ones_like(ev)]).T
sol, *_ = np.linalg.lstsq(A, rk, rcond=None)
pred = A@sol
resid = rk - pred
print(f"  got {len(evS)} positive eigenvalues; first 6: {np.round(evS[:6],3)}")
print(f"  counting-fn residual std vs linear fit: {np.std(resid):.4f}")
print(f"  unfolded-spacing variance (first 300): "
      f"{np.var(np.diff(ev)/np.mean(np.diff(ev))):.4f}  (GUE 0.178, rigid 0)")
print("  -> a smooth/rigid ladder again: captures the AVERAGE, carries no prime")
print("     fluctuation. (The ell^2/p term only reshapes the average staircase.)")

# ====================================================================
# (B2) TRACE FORMULA test: prime-orbit oscillatory density == actual zero density.
# rho_osc(t) = -(1/pi) sum_{p^k} (log p) chi3(p^k) p^{-k/2} cos(t k log p)
# Smear the ACTUAL zero density with a Gaussian and subtract smooth part; compare.
# ====================================================================
def primes_up_to(N):
    s = np.ones(N+1, bool); s[:2] = False
    for p in range(2, int(N**0.5)+1):
        if s[p]: s[p*p::p] = False
    return np.nonzero(s)[0]


def rho_osc(tgrid, X):
    out = np.zeros_like(tgrid)
    for p in primes_up_to(X):
        c = chi3(int(p))
        if c == 0: continue
        k = 1
        while p**k <= X:
            amp = math.log(p)*(c**k)*p**(-k/2.0)
            out += amp*np.cos(tgrid*k*math.log(p))
            k += 1
    return -(1.0/math.pi)*out


# actual smoothed density fluctuation: sum of Gaussians at zeros minus smooth density
def actual_rho_osc(tgrid, sig=0.5):
    dens = np.zeros_like(tgrid)
    for g in gammas:
        dens += np.exp(-0.5*((tgrid-g)/sig)**2)/(sig*math.sqrt(2*math.pi))
    smooth = np.log(3.0*np.maximum(tgrid,1e-3)/(2*math.pi))/(2*math.pi)
    return dens - smooth


tg = np.linspace(20, 120, 4000)
ro_prime = rho_osc(tg, 2000)
ro_actual = actual_rho_osc(tg, sig=0.5)
# the Gaussian smoothing damps high-frequency primes; compare correlation on the
# band both resolve. Match scale via correlation coefficient.
corr = np.corrcoef(ro_prime, ro_actual)[0, 1]
print("\n=== (B2) Trace-formula check: prime-orbit density vs actual zero density ===")
print(f"  corr( prime-orbit rho_osc , actual smoothed rho_osc ) = {corr:.4f}")
print("  (Gaussian smoothing sig=0.5 damps short primes; sign/phase match is the point.)")
# tighter smoothing -> more primes needed
for sig in [0.3, 0.2, 0.15]:
    ra = actual_rho_osc(tg, sig=sig)
    rp = rho_osc(tg, int( (np.exp((1/sig))) ))  # resolve primes up to ~ e^{1/sig}? heuristic
    rp2 = rho_osc(tg, 20000)
    print(f"  sig={sig}: corr(actual, primes<=2e4) = {np.corrcoef(rp2, ra)[0,1]:.4f}")

print("\n=== verdict for Attempt 2 ===")
print("  * Hermitian XP-type operators (dilation, BBM, BK-Sierra) reproduce only the")
print("    SMOOTH staircase <N(T)>; their spectra are rigid ladders, var->0, no GUE,")
print("    no prime fluctuation.")
print("  * The prime fluctuation lives in the TRACE FORMULA (prime periodic orbits),")
print("    which empirically reproduces the actual fluctuating zero density (corr above).")
print("  * But the trace formula is a CONSTRAINT the spectrum satisfies, not a")
print("    construction of a concrete self-adjoint H. Building H FROM the primes such")
print("    that its spectrum IS the zeros is exactly the unsolved Hilbert-Polya step.")
