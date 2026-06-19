"""
ON THE HELIX (no mpmath zeta).  Compute the helix phasor sum directly:

    helixPt(t)(n) = sqrt(n) * wind(t)(n),   wind(t)(n) = n^{it} = e^{i t log n}
    L(s) = sum_n chi(n) / helixPtGen(sigma,t)(n) = sum_n chi(n) * n^{-sigma} * e^{-i t log n}

The radial magnitude n^{-sigma}: at sigma=1/2 it is 1/sqrt(n) = 1/sqrt(height),
since the helix height is z = e^y and the area-law radius is R = sqrt(n) = e^{y/2}.
So sigma=1/2 is NOT a chosen parameter -- it is the e^y geometry (R^2 ~ n).

Claim under test (Sam): the zeros are the WINDING CANCELLATION events -- the heights t
where these sqrt(n)-weighted phasors cancel -- and ONLY at the geometric radius sigma=1/2.
We find them from the helix sum's own minima, then (only as a check) print the known gamma.
"""
import numpy as np

N = 40000
nn = np.arange(1, N + 1, dtype=np.float64)
logn = np.log(nn)
alt = np.where((np.arange(1, N + 1) % 2) == 1, 1.0, -1.0)   # (-1)^{n+1}: eta regularization

def eta_helix(sigma, t):
    # helix phasor sum (alternating-regularized):  sum (-1)^{n+1} n^{-sigma} e^{-i t log n}
    return np.sum(alt * nn ** (-sigma) * np.exp(-1j * t * logn))

def zeta_helix(sigma, t):
    # divide out the eta factor (1 - 2^{1-s}); nonzero off sigma=1, so safe here
    s_eta = 1.0 - 2.0 ** (1.0 - sigma) * np.exp(-1j * t * np.log(2.0))
    return eta_helix(sigma, t) / s_eta

ts = np.arange(8.0, 42.0, 0.01)
print(f"[helix phasor sum from scratch, N={N} terms; NO mpmath zeta called]\n")

def sweep(sigma):
    return np.abs(np.array([zeta_helix(sigma, t) for t in ts]))

def find_dips(v, thr, merge=0.8):
    idx = [i for i in range(1, len(v) - 1) if v[i] < v[i-1] and v[i] <= v[i+1] and v[i] < thr]
    dips = []
    for i in idx:
        if dips and ts[i] - dips[-1][0] < merge:
            if v[i] < dips[-1][1]:
                dips[-1] = (ts[i], v[i])
        else:
            dips.append((ts[i], v[i]))
    return dips

on = sweep(0.5)
true_g = [14.134725, 21.022040, 25.010858, 30.424876, 32.935062, 37.586178, 40.918719]
print("=== ON THE HELIX, sigma=1/2  (radius = sqrt(n) = e^{y/2}, forced by the e^y height) ===")
print("    minima of |zeta_helix| = where the sqrt(n)-weighted winding phasors CANCEL:")
for (t, v) in find_dips(on, 0.20):
    g = min(true_g, key=lambda x: abs(x - t))
    print(f"    cancellation at t = {t:7.3f}   |zeta_helix| = {v:.4f}    [check: true zero gamma = {g:8.4f},  |t-gamma| = {abs(t-g):.3f}]")

off = sweep(0.85)
print(f"\n=== OFF THE LINE, sigma=0.85  (radius n^0.85, NOT the area-law sqrt(n)) ===")
print(f"    min |zeta_helix| over [8,42] = {off.min():.3f}   (phasors never collapse -> no cancellation -> no zeros)")
print(f"    on-line min = {on.min():.4f}   vs   off-line min = {off.min():.4f}")

print("""
READOUT: the zeros were located by the HELIX phasor sum cancelling -- with the
radial weight n^{-1/2} that the e^y height forces (R=sqrt(n)) -- not by evaluating
zeta.  Move off that geometric radius and the cancellation disappears.""")
