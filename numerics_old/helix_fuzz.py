"""
helix_fuzz.py -- fresh 3D-helix fuzzing harness.

Integers 1..M evenly on a line (arc a_n = n), wound UP (z) and OUT (R) around a helix.  A phasor rides
each integer; wind by amount w; S(w)=sum_n chi3(n)*weight_n*exp(-i w rot_n).  SWEEP w; a cancellation
dip (|S| collapses) that lands on a chi3 zero gamma_n = the phasors aligning to cancel there.

Metric: ratio = mean|S| at first 10 zeros / median|S|.  ratio<<1 => dips sit ON the zeros.

Fuzz dimensions: winding geometry R(n),z(n); rotation profile rot_n (what the phasor winds against);
amplitude weight_n; rotation-speed calibration.  Rounds below probe each.
"""
import numpy as np

ZER = []
with open("lchi3_zeros_1000.txt") as f:
    for ln in f:
        ln = ln.strip()
        if ln and not ln.startswith("#"):
            ZER.append(float(ln.split()[1]))
ZER = np.array(sorted(ZER))

M = 40000
n = np.arange(1, M + 1).astype(float)
sign = np.where(n.astype(int) % 3 == 1, 1.0, np.where(n.astype(int) % 3 == 2, -1.0, 0.0))
wgrid = np.arange(0.3, 35.0, 0.01)

def sweep(rot, weight):
    c = sign * weight
    rot = np.asarray(rot, float)
    return np.array([abs(np.sum(c * np.exp(-1j * w * rot))) for w in wgrid])

def ratio(rot, weight, k=10):
    cur = sweep(rot, weight)
    return float(np.interp(ZER[:k], wgrid, cur).mean() / np.median(cur))

w_half = n ** (-0.5)
print(f"M={M}, sweep w in [0.3,35]@0.01, ratio = mean|S|@first10 zeros / median|S|  (<<1 = cancels ON zeros)\n")

# ROUND 1: rotation profile, weight n^{-1/2}
print("ROUND 1  weight n^{-1/2}; rotation profile:")
for name, rot in [("log n", np.log(n)), ("sqrt n", np.sqrt(n)), ("n", n.copy()),
                  ("(n^0.3-1)/0.3", (n**0.3 - 1)/0.3)]:
    print(f"   rot = {name:16s}  ratio = {ratio(rot, w_half):.4f}")

# ROUND 2: does the GEOMETRY make the winding angle theta = sum(arc/R) = cumsum(1/R) ~ log n?
# wind angle for a flat spiral, even arc spacing: dtheta = ds/R = 1/R  ->  theta_n = cumsum(1/R).
print("\nROUND 2  phasor rides the GEOMETRIC WINDING theta=cumsum(1/R); weight n^{-1/2}; vary R(n):")
for name, R in [("R=sqrt(n)", np.sqrt(n)), ("R=n", n.copy()), ("R=n^0.75", n**0.75),
                ("R=n/log n", n/np.log(n+1)), ("R=const", np.ones_like(n))]:
    theta = np.cumsum(1.0 / R)
    # report how theta scales (fit theta ~ c*log n ?) and the cancellation ratio
    fit = np.polyfit(np.log(n[100:]), theta[100:], 1)  # theta vs log n slope
    print(f"   {name:12s}  theta ~ {fit[0]:.3f}*log n + {fit[1]:.2f}   ratio = {ratio(theta, w_half):.4f}")

# ROUND 3: the FULL geometric phasor -- cone supplies BOTH weight(=1/R) and winding(theta=cumsum 1/R).
print("\nROUND 3  cone supplies its OWN weight 1/R AND winding theta=cumsum(1/R); vary R(n):")
for name, R in [("R=sqrt(n)", np.sqrt(n)), ("R=n", n.copy()), ("R=n^0.75", n**0.75)]:
    theta = np.cumsum(1.0 / R)
    print(f"   {name:12s}  weight 1/R, phase theta   ratio = {ratio(theta, 1.0/R):.4f}")

# ROUND 4: split -- weight from radius (out), phase from height (up).  Which (R,z) gives BOTH?
print("\nROUND 4  weight = 1/R (out), phase = z (up); which (R,z) cancels?")
for name, R, z in [("R=sqrt n, z=log n", np.sqrt(n), np.log(n)),
                   ("R=sqrt n, z=sqrt n", np.sqrt(n), np.sqrt(n)),
                   ("R=sqrt n, z=cumsum(1/R)", np.sqrt(n), np.cumsum(1/np.sqrt(n)))]:
    print(f"   {name:26s}  ratio = {ratio(z, 1.0/R):.4f}")

# ============ ROUND 5: precision -- exact log n vs the discrete geometric winding ============
print("\nROUND 5  precision of the rotation (weight n^{-1/2}):")
Hn = np.cumsum(1.0 / n)                       # harmonic = discrete winding for R=n
for name, rot in [("exact log n", np.log(n)),
                  ("harmonic H_n (discrete winding)", Hn),
                  ("H_n - gamma (de-shifted)", Hn - 0.5772156649),
                  ("log n + 0.5/n (add disc. corr.)", np.log(n) + 0.5/n),
                  ("log n + 0.05*sin(n)", np.log(n) + 0.05*np.sin(n))]:
    print(f"   rot = {name:34s}  ratio = {ratio(rot, w_half):.4f}")

# ============ ROUND 6: FTA -- completely-additive phase f(n)=sum_p v_p(n)*a_p ============
# build via smallest-prime-factor sieve; f is additive over multiplication. a_p=log p => f=log n.
Mx = M
spf = np.zeros(Mx + 1, dtype=np.int64)
for i in range(2, Mx + 1):
    if spf[i] == 0:
        spf[i::i] = np.where(spf[i::i] == 0, i, spf[i::i])
def additive(ap):
    """f(n)=sum over prime factors (with multiplicity) of ap(prime)."""
    f = np.zeros(Mx + 1)
    for m in range(2, Mx + 1):
        p = spf[m]
        f[m] = f[m // p] + ap(p)
    return f[1:Mx + 1]

print("\nROUND 6  FTA: phase = completely-additive f(n)=sum_p v_p(n)*a_p; vary a_p (weight n^{-1/2}):")
rng = np.random.default_rng(0)
prime_vals = {p: rng.normal() for p in range(2, Mx + 1) if spf[p] == p}
for name, ap in [("a_p = log p     (=> f=log n, the L bridge)", lambda p: np.log(p)),
                 ("a_p = log p *1.3 (rescaled)            ", lambda p: 1.3*np.log(p)),
                 ("a_p = sqrt p    (additive, wrong vals) ", lambda p: np.sqrt(p)),
                 ("a_p = random N(0,1) per prime          ", lambda p: prime_vals[p])]:
    f = additive(ap)
    print(f"   {name:42s}  ratio = {ratio(f, w_half):.4f}")
print("   => cancellation needs additive-over-FTA AND a_p = log p (the multiplicative->L bridge).")

# ============ ROUND 7: the alignment snapshot -- partial-sum walk at a zero vs off it ============
print("\nROUND 7  alignment: partial-sum walk |sum_{n<=K}| at gamma_1 (zero) vs midpoint (non-zero):")
g0 = ZER[0]; gmid = 0.5*(ZER[0]+ZER[1])
for tag, w in [("AT zero gamma_1=%.3f"%g0, g0), ("OFF zero %.3f"%gmid, gmid)]:
    term = sign * w_half * np.exp(-1j * w * np.log(n))
    walk = np.abs(np.cumsum(term))
    print(f"   {tag:26s}: |partial sum| at K=10^3,10^4,4·10^4 = "
          f"{walk[999]:.4f}, {walk[9999]:.4f}, {walk[-1]:.4f}")
print("   => AT a zero the walk returns toward 0 (phasors realign to cancel); off a zero it settles at |L|>0.")

# ============ ROUND 8: is the sqrt(n) weight (the cone radius = "out") necessary? ============
# weight = n^{-sigma}; rotation = log n.  sum = L(chi3, sigma+i*gamma); cancels only where a zero sits.
print("\nROUND 8  weight = n^{-sigma} (cone radius R=n^sigma), rotation log n; vary sigma:")
for s in [0.30, 0.40, 0.45, 0.50, 0.55, 0.60, 0.70]:
    print(f"   sigma = {s:.2f}  (R = n^{s})   ratio = {ratio(np.log(n), n**(-s)):.4f}")
print("   => the dips sit on the chi3 zeros ONLY at sigma=1/2: the cone radius MUST be sqrt(n).")
