"""
Adjust the AMPLITUDE (the radial field of each placed prime) and see which one puts the
singularities (where the signed mod-6 sum -> 0) in the right range.

Each integer n sits at radius R(n)=e^6*k(n) (arc-length placement). Its field amplitude ~ R^{-2*sigma}
(sigma=1/2 is the inverse-radius field 1/R = n^{-1/2}, EARNED from the radius, not injected).
Read along the radial scale c(n)=2*log R(n) ( = log n + const ).  Sweep reading frequency t.
Forward mod-6 signed sum  S(sigma,t) = sum_n chi6(n) R^{-2sigma} e^{-i t * 2logR}.
A singularity = |S| -> 0.  Which sigma makes them appear, and at what t?
"""
import numpy as np
from scipy.signal import find_peaks

e6 = np.exp(6.0); U = np.pi/3; A = e6/(4*np.pi)
N, Ncut = 2_000_000, 200_000

# radius R(n) by arc-length inversion s(Phi)=n*U
Phi_grid = np.linspace(0.0, 320.0, 4_000_000)
s_grid = A*(Phi_grid*np.sqrt(Phi_grid**2+1)+np.arcsinh(Phi_grid))
n = np.arange(2, N+1)
Phi = np.interp(n*U, s_grid, Phi_grid)
R = e6*Phi/(2*np.pi)                  # radius of integer n
c = 2*np.log(R)                       # radial-scale readout ( = log n + const )

chi6 = np.where(n % 6 == 1, 1.0, np.where(n % 6 == 5, -1.0, 0.0))
cut  = np.exp(-n/Ncut)
keep = chi6 != 0
c, chi6, cut, Rk = c[keep], chi6[keep], cut[keep], R[keep]

chi3_zeros = [8.04, 11.24, 15.70, 18.26, 20.46, 24.06, 26.58, 28.22]

def forward(sigma):
    w = chi6 * Rk**(-2*sigma) * cut          # amplitude R^{-2 sigma}
    du = 0.0008; u0 = c.min(); M = int((c.max()-u0)/du)+2
    s = np.zeros(M); np.add.at(s, ((c-u0)/du).astype(np.int64), w)
    P = 1 << 21
    S = np.fft.fft(s, P)
    t = 2*np.pi*np.arange(P)/(P*du)
    sel = (t > 0.5) & (t <= 31)
    return t[sel], np.abs(S[sel])

for sigma in (0.0, 0.5, 1.0):
    t, absS = forward(sigma)
    absS /= absS.max()
    dips, _ = find_peaks(-absS, prominence=0.05, distance=int(0.8/(t[1]-t[0])))
    dips = [i for i in dips if absS[i] < 0.35]
    hit = sum(1 for z in chi3_zeros if dips and min(abs(t[i]-z) for i in dips) < 0.3)
    label = "1/R inverse-radius field (=n^-1/2)" if sigma==0.5 else ("unit amplitude" if sigma==0 else "1/R^2")
    print(f"\n=== amplitude R^(-2*{sigma}) : {label} ===")
    print(f"   |S| minima (sum->0) landing on a chi3 zero: {hit}/{len(chi3_zeros)}")
    for z in chi3_zeros:
        if dips:
            i = min(dips, key=lambda i: abs(t[i]-z))
            d = t[i]-z
            print(f"   zero {z:6.2f}   nearest dip t={t[i]:6.2f} (|S|/max={absS[i]:.3f}, d={d:+.2f})"
                  f"{'  HIT' if abs(d)<0.3 else ''}")
        else:
            print(f"   zero {z:6.2f}   (no dips found)")
