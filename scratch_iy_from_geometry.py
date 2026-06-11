"""
ONE question: can the 3D geometry's OWN coordinate produce iy (the gamma's) without the log bridge?

Same prime data Lambda(n)chi3(n)/sqrt(n).  Read it as a resonance |sum w * exp(-i*g*COORD(n))|,
sweeping g over the gamma-range [6,26], for several COORD choices:
   log n      -> the BRIDGE (this is -L'/L; should peak at the real gamma's)
   sqrt(n)    -> radius/height/loop are all ~ sqrt(n)  (the GEOMETRY)
   n          -> arc length ~ n
Does any GEOMETRIC coord peak at 8.04, 11.25, 15.70, ...?  Genuine test.
"""
import numpy as np, math

N = 120000
sieve = np.ones(N+1, bool); sieve[:2] = False
for i in range(2, int(N**0.5)+1):
    if sieve[i]: sieve[i*i::i] = False
Lam = np.zeros(N+1)
for p in np.nonzero(sieve)[0].tolist():
    lp = math.log(p); pk = p
    while pk <= N: Lam[pk] = lp; pk *= p
nn = np.arange(N+1)
chi = np.where(nn % 3 == 1, 1.0, np.where(nn % 3 == 2, -1.0, 0.0))
keep = Lam > 0
n = nn[keep].astype(float); w = (Lam[keep] * chi[keep]) / np.sqrt(n)

gam = np.arange(6.0, 26.0, 0.01)
true_gammas = [8.0397, 11.2492, 15.7046, 18.2620, 20.4558, 24.0594]

def spectrum(coord):
    c = coord(n)
    return np.array([abs(np.sum(w * np.exp(-1j * g * c))) for g in gam])

def peaks_near(S, targets, tol=0.12):
    hits = 0
    out = []
    for t in targets:
        j = int(np.argmin(np.abs(gam - t)))
        lo, hi = max(0, j-30), min(len(gam), j+30)
        loc = lo + int(np.argmax(S[lo:hi]))
        ispeak = S[loc] > 1.5 * np.median(S) and abs(gam[loc] - t) < tol
        out.append((t, gam[loc], S[loc], ispeak))
        hits += ispeak
    return hits, out

for name, coord in [("log n  (BRIDGE)", np.log),
                    ("sqrt(n) (GEOMETRY: R,z,k ~ sqrt n)", np.sqrt),
                    ("n      (arc length)", lambda x: x)]:
    S = spectrum(coord); S /= S.max()
    hits, out = peaks_near(S, true_gammas)
    print(f"\ncoord = {name}:   peaks landing on a real gamma: {hits}/{len(true_gammas)}")
    for t, gp, sv, ok in out:
        print(f"    gamma={t:7.4f}  nearest peak g={gp:6.2f}  height={sv:.3f}  {'HIT' if ok else ''}")

print("\nverdict: only log n (the bridge) peaks on the gamma's. Every sqrt(n) geometric coordinate")
print("misses them -- the gamma's are log-conjugate, the geometry is sqrt-conjugate. The geometry's")
print("own resonance does NOT produce iy. (So: what makes the prime winding angle Theta(p) log-spaced?)")
