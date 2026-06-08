import numpy as np, json, sys

ref = json.load(open("/Users/samuellavery/proof/three/tmp/fwd2/ref.json"))
gamma_ref = np.array(ref["gamma_ref"])
nzeros = {int(k): v for k, v in ref["nzeros"].items()}

def primes_upto(N):
    s = np.ones(N + 1, dtype=bool); s[:2] = False
    for p in range(2, int(N**0.5) + 1):
        if s[p]: s[p*p::p] = False
    return np.nonzero(s)[0]

def prime_power_terms(X):
    P = primes_upto(int(X)); terms = []
    for p in P:
        lp = np.log(p); pk = p
        while pk <= X:
            terms.append((np.log(pk), lp, float(pk))); pk *= p
    return terms

t = np.arange(0.0, 119.0, 0.02)

def build_wave(X, taper=None):
    terms = prime_power_terms(X); W = np.zeros_like(t); logX = np.log(X)
    for (logn, lam, n) in terms:
        amp = lam / np.sqrt(n)
        if taper == "fejer": w = max(0.0, 1.0 - logn/logX)
        elif taper == "gauss": w = np.exp(-0.5*(logn/logX)**2*4)
        else: w = 1.0
        W += -amp*w*np.cos(t*logn)
    return W, len(terms)

def crossings(t, W):
    s = np.sign(W); idx = np.nonzero((s[:-1]*s[1:])<0)[0]
    return np.array([t[i]-W[i]*(t[i+1]-t[i])/(W[i+1]-W[i]) for i in idx])

# TRUE density: N(T) ~ (T/2pi)log(T/2pi) - T/2pi
def Nasymp(T): return (T/(2*np.pi))*np.log(T/(2*np.pi)) - T/(2*np.pi)

print("=== TRUE zero count vs crossing count of prime-power wave ===")
print("N(T) true (mpmath nzeros):", nzeros)
print(f"N(119) asymptotic ~ {Nasymp(119):.1f}, true = {nzeros[119]}")
print()
print("Crossings counted in [6,119]; true #zeros there = 38 (gamma_1..gamma_38).")
print(f"{'X':>8} {'taper':>7} {'#cross':>7} {'true=38':>8} {'ratio':>6}")
for taper in [None, "fejer", "gauss"]:
    for X in [200, 1000, 5000, 20000, 100000]:
        W,_ = build_wave(X, taper)
        cr = crossings(t,W); cr = cr[(cr>6)&(cr<119)]
        print(f"{X:>8} {str(taper):>7} {len(cr):>7} {38:>8} {len(cr)/38:>6.2f}")
        sys.stdout.flush()
print()

# ONE-TO-ONE ordered match: does the k-th relevant feature line up with gamma_k?
# Use SIGNED-positive crossings (down->up zero crossings) as candidate zero markers, ordered.
def updown_crossings(t,W):
    s=np.sign(W); idx=np.nonzero((s[:-1]<0)&(s[1:]>0))[0]  # only upward
    return np.array([t[i]-W[i]*(t[i+1]-t[i])/(W[i+1]-W[i]) for i in idx])

print("=== ORDERED 1-to-1: k-th upward-crossing vs gamma_k (no nearest-neighbor cheat) ===")
for taper in [None, "gauss"]:
    print(f"--- taper={taper} ---")
    for X in [1000, 20000, 100000]:
        W,_=build_wave(X,taper)
        uc=updown_crossings(t,W); uc=uc[(uc>6)&(uc<119)]
        n=min(len(uc), len(gamma_ref))
        if n>0:
            d=uc[:n]-gamma_ref[:n]
            rms=np.sqrt(np.mean(d**2))
        else: rms=np.nan
        print(f"  X={X:>6} #up={len(uc):>3}  ordered-RMS(first {n})={rms:.3f}")
        if X==100000:
            print("    first 8 up-crossings:", [round(x,2) for x in uc[:8]])
            print("    first 8 gamma_n     :", [round(x,2) for x in gamma_ref[:8]])
    print()
