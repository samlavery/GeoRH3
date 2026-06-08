import numpy as np, json, sys, mpmath
mpmath.mp.dps = 15

ref = json.load(open("/Users/samuellavery/proof/three/tmp/fwd2/ref.json"))
gamma_ref = np.array(ref["gamma_ref"])

def primes_upto(N):
    s = np.ones(N + 1, dtype=bool); s[:2] = False
    for p in range(2, int(N**0.5) + 1):
        if s[p]: s[p*p::p] = False
    return np.nonzero(s)[0]

t = np.arange(0.0, 119.0, 0.02)

# ---- the SMOOTH theta phase = arg of Gamma(1/4 + it/2) - (t/2)log pi : THIS IS BORROWED FROM ZETA ----
# Evaluate theta(t) on the grid via mpmath.siegeltheta (default dps), cache as float64 array.
print("computing theta(t) via mpmath.siegeltheta (BORROWED smooth phase)...", flush=True)
theta = np.array([float(mpmath.siegeltheta(float(tt))) if tt>0.5 else 0.0 for tt in t])
print("theta done.", flush=True)

def crossings(t, W):
    s=np.sign(W); idx=np.nonzero((s[:-1]*s[1:])<0)[0]
    return np.array([t[i]-W[i]*(t[i+1]-t[i])/(W[i+1]-W[i]) for i in idx])

def updown(t,W):
    s=np.sign(W); idx=np.nonzero((s[:-1]<0)&(s[1:]>0))[0]
    return np.array([t[i]-W[i]*(t[i+1]-t[i])/(W[i+1]-W[i]) for i in idx])

# Riemann-Siegel Z-function MAIN SUM with the theta phase:
#   Z(t) ~ 2 * sum_{n<=sqrt(t/2pi)} n^{-1/2} cos(theta(t) - t log n)
# Note the cutoff is sqrt(t/2pi) -- t-dependent. Use a generous fixed cap then mask per-t.
def Zmain(t, theta, Nmax):
    Z = np.zeros_like(t)
    cutoff = np.sqrt(t/(2*np.pi))   # per-t cutoff
    for n in range(1, Nmax+1):
        mask = (n <= cutoff)
        Z += np.where(mask, 2.0*(n**-0.5)*np.cos(theta - t*np.log(n)), 0.0)
    return Z

print()
print("=== APPROACH B: SAME prime/integer sum BUT WITH borrowed theta phase (Riemann-Siegel Z) ===")
print("Z(t) = 2 sum_{n<=sqrt(t/2pi)} cos(theta(t) - t log n)/sqrt(n).  Zeros of Z = gamma_n.")
print("This BORROWS arg Gamma via theta. Testing convergence as Nmax grows.")
print(f"{'Nmax':>6} {'#cross':>7} {'true38':>7} {'ordRMS30':>9}")
for Nmax in [1, 2, 3, 5, 8]:
    Z = Zmain(t, theta, Nmax)
    cr = crossings(t, Z); cr = cr[(cr>6)&(cr<119)]
    n=min(len(cr), len(gamma_ref))
    d=cr[:n]-gamma_ref[:n] if n>0 else np.array([np.nan])
    rms=np.sqrt(np.mean(d**2)) if n>0 else np.nan
    print(f"{Nmax:>6} {len(cr):>7} {38:>7} {rms:>9.4f}")
    sys.stdout.flush()

# best one, show the actual matched zeros
Z = Zmain(t, theta, 8)
cr = crossings(t, Z); cr = cr[(cr>6)&(cr<119)]
print()
print("With theta borrowed, Nmax=8, first 10 crossings vs gamma_n:")
print("  crossings:", [round(x,3) for x in cr[:10]])
print("  gamma_n  :", [round(x,3) for x in gamma_ref[:10]])
n=min(len(cr),len(gamma_ref))
print("  ordered RMS (first %d):"%n, round(float(np.sqrt(np.mean((cr[:n]-gamma_ref[:n])**2))),4))

# ALSO: theta ALONE with NO primes (Nmax=1 means just the n=1 term: Z=2 cos(theta))
print()
print("=== theta ALONE (n=1 term only: Z=2cos(theta), NO primes at all) ===")
Z1 = 2.0*np.cos(theta)
cr1 = crossings(t, Z1); cr1 = cr1[(cr1>6)&(cr1<119)]
n=min(len(cr1),len(gamma_ref))
print("  #crossings:", len(cr1), " (true=38)")
print("  ordered RMS (first %d):"%n, round(float(np.sqrt(np.mean((cr1[:n]-gamma_ref[:n])**2))),4))
print("  -> theta phase ALONE already sets the DENSITY and approx location of zeros.")
