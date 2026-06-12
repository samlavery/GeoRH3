"""
chi4_zeros.py -- locate the first nontrivial zeros of L(s, chi4) (Dirichlet beta)
on the critical line sigma=1/2, to high precision, and sanity-check the L-function.

chi4 = nontrivial char mod 4: +1 if n=1 mod4, -1 if n=3 mod4, 0 if even.
L(s,chi4) = beta(s) = 4^{-s}(zeta(s,1/4) - zeta(s,3/4))  via Hurwitz zeta.

Strategy (proper, not Re-sign-change):
  - fine scan |L(1/2+it)| over t in (0,60), step 0.02
  - find local minima of |L| (true zero detector, since both Re and Im must vanish)
  - mp.findroot on the COMPLEX value at each deep minimum
  - accept gamma only if |L(1/2+i gamma)| < 1e-10
"""
import mpmath as mp
mp.mp.dps = 40

def Lchi4(s):
    s = mp.mpc(s)
    return mp.power(4, -s) * (mp.zeta(s, mp.mpf(1)/4) - mp.zeta(s, mp.mpf(3)/4))

# ---- sanity checks against known special values ----
print("="*72)
print("SANITY CHECKS for L(s,chi4) = Dirichlet beta")
print("  beta(1)     =", mp.nstr(Lchi4(1), 14), "   pi/4    =", mp.nstr(mp.pi/4, 14))
print("  beta(2)     =", mp.nstr(Lchi4(2), 14), "   Catalan =", mp.nstr(mp.catalan, 14))
Lhalf = Lchi4(mp.mpf(1)/2).real
print("  L(1/2,chi4) =", mp.nstr(Lhalf, 14), "   (known ~ 0.6676914571896...)")
print("="*72)

# ---- fine scan of |L(1/2+it)| ----
def absL(t):
    return abs(Lchi4(mp.mpf(1)/2 + 1j*mp.mpf(t)))

print("\nFine scan |L(1/2+it)|, t in (0.05, 60], step 0.02  -- collecting local minima:")
step = mp.mpf('0.02')
t = mp.mpf('0.05')
tmax = mp.mpf('60')
ts, vs = [], []
while t <= tmax:
    ts.append(t); vs.append(absL(t)); t += step

# local minima (deeper than neighbors and below a threshold to be a zero candidate)
candidates = []
for i in range(1, len(vs)-1):
    if vs[i] < vs[i-1] and vs[i] < vs[i+1] and vs[i] < 0.05:
        candidates.append((float(ts[i]), float(vs[i])))
print(f"  {len(candidates)} deep local minima (|L|<0.05):")
for tc, vc in candidates:
    print(f"    t ~ {tc:8.4f}   |L| ~ {vc:.6f}")

# ---- refine each candidate with complex findroot ----
print("\nRefining each candidate with mp.findroot on the complex L(1/2+it):")
zeros = []
for tc, vc in candidates:
    try:
        root = mp.findroot(lambda x: Lchi4(mp.mpf(1)/2 + 1j*x), mp.mpf(tc))
        g = mp.re(root)
        val = abs(Lchi4(mp.mpf(1)/2 + 1j*g))
        accept = (val < mp.mpf('1e-10')) and (g > 0) and all(abs(g - z) > mp.mpf('1e-3') for z in zeros)
        tag = "ACCEPT" if accept else "reject"
        print(f"    start {tc:8.4f} -> gamma = {mp.nstr(g, 16):>22}   |L|={mp.nstr(val,4):>10}   [{tag}]")
        if accept:
            zeros.append(g)
    except Exception as e:
        print(f"    start {tc:8.4f} -> findroot FAILED: {e}")

zeros = sorted(zeros)
print("\n" + "="*72)
print(f"ACCEPTED chi4 zeros (|L|<1e-10), {len(zeros)} found up to t=60:")
for i, g in enumerate(zeros, 1):
    print(f"   gamma_{i} = {mp.nstr(g, 18)}")
print("="*72)

# write them out for the construction test
with open("chi4_zeros.txt", "w") as f:
    f.write("# nontrivial zeros of L(s,chi4)=Dirichlet beta on sigma=1/2\n")
    f.write("# index  gamma\n")
    for i, g in enumerate(zeros, 1):
        f.write(f"{i}  {mp.nstr(g, 25)}\n")
print("wrote chi4_zeros.txt")
