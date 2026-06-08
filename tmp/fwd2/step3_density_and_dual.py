"""
Step 3: the two HONEST diagnostics.

(A) DENSITY: does crossing count -> canonical N(T) (log-T density), or diverge?
    Also: control test -- is RMS "improvement" just because crossings get denser
    (so a random target has a nearer neighbor)? Compare to RMS of gamma_ref vs
    RANDOM crossing sets of the same count.

(B) COLLECTIVE dual spectrum. The explicit formula (Riemann-Weil):
       sum_n h(gamma_n) = (smooth: archimedean / log-T) - (1/2pi) sum_{p,k} Lambda...
    The cleanest collective check WITHOUT inserting Gamma:
       psi-style: compare the construction's spectral peaks.
    We instead test the DUAL directly: the canonical zeros, summed as
       D_can(u) = sum_n cos(gamma_n u),
    have sharp NEGATIVE spikes exactly at u = k log p (this IS the explicit formula:
    zeros 'know' the primes). Question for the FORWARD direction: can prime powers
    REGENERATE the zero positions? That requires inverting -- i.e. the prime sum must
    build a function whose ZEROS/crossings are gamma_n. (A) already tests that.

    Here we add the decisive control: the canonical N(T) density is
       N(T) ~ (T/2pi) log(T/2pi) - T/2pi   (log-T, theta-driven).
    Measure the construction's crossing density vs this. If construction density
    is ~constant*X-growing (prime-power high-freq noise) it is NOT log-T.
"""
import numpy as np
import json

with open("/Users/samuellavery/proof/three/tmp/fwd2/ref.json") as f:
    ref = json.load(f)
gamma_ref = np.array(ref["gamma_ref"])
nzeros_ref = {int(k): v for k, v in ref["nzeros_ref"].items()}

def primes_upto(n):
    sieve = np.ones(n + 1, dtype=bool); sieve[:2] = False
    for i in range(2, int(n**0.5)+1):
        if sieve[i]: sieve[i*i::i] = False
    return np.nonzero(sieve)[0]
primes = primes_upto(100000)

def prime_powers_upto(X):
    terms = []
    for p in primes:
        if p > X: break
        lp = np.log(p); pk = p; k = 1
        while pk <= X:
            terms.append((lp, k, pk)); pk *= p; k += 1
    return terms

t = np.arange(0.0, 120.0, 0.02)

def build_wave(X):
    W = np.zeros_like(t)
    for (lp, k, pk) in prime_powers_upto(X):
        W -= (lp/np.sqrt(pk)) * np.cos(k*lp * t)
    return W

def crossings(W):
    s = np.sign(W); idx = np.nonzero(np.diff(s) != 0)[0]
    cr = []
    for i in idx:
        w0,w1 = W[i],W[i+1]
        if w1!=w0: cr.append(t[i]-w0*(t[i+1]-t[i])/(w1-w0))
    return np.array(cr)

# theoretical theta-driven count
def N_theory(T):
    if T < 2: return 0.0
    x = T/(2*np.pi)
    return x*np.log(x) - x + 7.0/8.0

print("="*72, flush=True)
print("(A) CROSSING DENSITY vs canonical N(T) (log-T, theta-driven)", flush=True)
print("="*72, flush=True)
Ts = [20,30,40,50,60,80,100]
header = f"{'X':>7} | " + " ".join(f"N({T})" for T in Ts)
print(header, flush=True)
print(f"{'canon':>7} | " + " ".join(f"{nzeros_ref.get(T,0):5d}" for T in Ts), flush=True)
print(f"{'theory':>7} | " + " ".join(f"{N_theory(T):5.1f}" for T in Ts), flush=True)
for X in [50,200,1000,5000,20000,100000]:
    W = build_wave(X)
    cr = crossings(W)
    counts = [int(np.sum((cr>0)&(cr<T)))//2 for T in Ts]  # crossings/2 ~ oscillation count
    # actually count crossings below T (each zero -> ~ one sign change pair); report raw crossings
    raw = [int(np.sum((cr>0)&(cr<T))) for T in Ts]
    print(f"{X:>7} | " + " ".join(f"{c:5d}" for c in raw), flush=True)

print("\n--> if the row keeps GROWING past the canon/theory row, the prime-power", flush=True)
print("    wave has the WRONG (too high, X-growing) crossing density, not log-T.", flush=True)

print("\n" + "="*72, flush=True)
print("(B) CONTROL: is RMS 'improvement' real, or just denser crossings?", flush=True)
print("="*72, flush=True)
print("Compare RMS(gamma_ref -> nearest construction crossing) vs", flush=True)
print("        RMS(gamma_ref -> nearest RANDOM crossing of same count).", flush=True)
rng = np.random.default_rng(0)
for X in [50,1000,20000,100000]:
    W = build_wave(X); cr = crossings(W)
    cr = cr[(cr>5)&(cr<102)]
    # real RMS
    res = np.array([cr[np.argmin(np.abs(cr-g))]-g for g in gamma_ref])
    rms_real = np.sqrt(np.mean(res**2))
    # random control: same number of crossings, uniform in [5,102]
    rms_rand_trials = []
    for _ in range(200):
        rc = np.sort(rng.uniform(5,102,size=len(cr)))
        rr = np.array([rc[np.argmin(np.abs(rc-g))]-g for g in gamma_ref])
        rms_rand_trials.append(np.sqrt(np.mean(rr**2)))
    rms_rand = np.mean(rms_rand_trials)
    print(f"X={X:>6}  #cross={len(cr):>4}  RMS_real={rms_real:.4f}  RMS_random_samecount={rms_rand:.4f}  ratio={rms_real/rms_rand:.3f}", flush=True)

print("\n--> ratio ~1 means the construction's crossings are NO BETTER than random", flush=True)
print("    points of the same density: the RMS drop is a density artifact, not", flush=True)
print("    genuine convergence to gamma_n.", flush=True)
