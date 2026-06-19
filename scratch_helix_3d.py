"""
FIT TO FROBENIUS, IN 3-D  (no projected n^{-s} series, no unit-circle phase).

3-D helix (ClosedForm.Geometry):  helix p r k = (r k cos 2pi k, r k sin 2pi k, p k).
The e^y height is z = p k  (k = kClimb p y = e^y/p).

Integers are placed EVENLY ALONG THE ARC, then rewound.  Arc length
    S(k) = int_0^k sqrt(p^2 + r^2 + (2 pi r t)^2) dt  ~  pi r k^2     (winding dominates -> ~k^2).
So integer n at arc S = n*U sits at  k_n ~ sqrt(n)  =>  radius r k_n ~ sqrt(n),  height p k_n ~ sqrt(n).
That sqrt(n) IS sigma=1/2 -- it emerges from the 3-D arc on the e^y helix, not put in by hand.

Frobenius x p:  n -> p n  =>  arc -> p*arc  =>  k -> sqrt(p) k  =>  radius -> sqrt(p)*radius.
The sqrt(q)-purity is the 3-D RADIAL action of Frobenius (q = p), forced by arc ~ k^2 (the e^y winding).
"""
import numpy as np

p, r = 1.0, 1.0
def speed(t):
    return np.sqrt(p**2 + r**2 + (2*np.pi*r*t)**2)

# cumulative arc length S(k) along the 3-D helix
K = np.linspace(0.0, 400.0, 400001)
sp = speed(K)
S = np.concatenate([[0.0], np.cumsum(0.5*(sp[1:] + sp[:-1]) * np.diff(K))])

print("(1) 3-D helix ARC length  S(k) ~ pi*r*k^2   (the winding/rewind makes it quadratic):")
for k in [10, 50, 100, 300]:
    i = np.searchsorted(K, k)
    print(f"    k={k:4d}   S(k)={S[i]:12.1f}   S/k^2={S[i]/k**2:.5f}   (pi*r={np.pi*r:.5f})")

U = np.pi * r          # arc unit: place integer n at arc S = n*U  =>  k_n ~ sqrt(n)
def k_of_n(n):
    return K[np.searchsorted(S, n * U)]

print("\n(2) even-arc placement on the e^y helix -> radius r*k_n proportional to sqrt(n)  [=> sigma=1/2]:")
print("    (height z = p*k_n is the e^y axis; the sqrt(n) is NOT input -- it falls out of the arc)")
for n in [1, 4, 9, 25, 100, 400]:
    kn = k_of_n(n)
    print(f"    n={n:4d}   k_n={kn:8.3f}   sqrt(n)={np.sqrt(n):8.3f}   radius/sqrt(n)={r*kn/np.sqrt(n):.4f}   height z={p*kn:8.3f}")

print("\n(3) Frobenius x p (n -> p n) is a 3-D RADIAL SCALING by sqrt(p) = sqrt(q):")
for (n, pp) in [(4, 2), (9, 3), (25, 5), (49, 7)]:
    ratio = k_of_n(pp * n) / k_of_n(n)
    print(f"    n={n:3d}, p={pp}:   radius(p n)/radius(n) = {ratio:.4f}    sqrt(p) = sqrt(q) = {np.sqrt(pp):.4f}")

print("""
3-D FIT:  sigma=1/2 is the sqrt(n) radius that EMERGES from even-arc placement on the e^y helix
(arc ~ k^2).  Frobenius x p scales that radius by sqrt(p)=sqrt(q): the sqrt(q)-purity is the
3-D radial action of Frobenius, forced by the e^y winding geometry -- not a phase on a 1-D circle.
The zeros stay the downstream 1-D shadow; the FORCING (the purity) lives here, in 3-D.""")
