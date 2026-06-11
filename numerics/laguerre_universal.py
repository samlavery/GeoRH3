"""
laguerre_universal.py -- the Laguerre node-detector for EVERY primitive Dirichlet L.
Universal recipe: Z_chi(t) = eps^{-1/2} * Lambda(1/2+it, chi)  is REAL for any primitive chi
(FE: Lambda(s,chi) = eps * Lambda(1-s, conj chi) + Schwarz reflection => constant phase eps^{1/2}).
Then the SAME detector: L(t) = Z'^2 - Z Z'' >= 0 (true zeros = touching nodes), and an off-line
fusion of two real roots into (t-m)^2 + delta^2 must drive L < 0.  No evenness used (complex chi ok).
"""
import numpy as np, mpmath as mp
mp.mp.dps = 30

CH = {
 'mod 4 quad (real, odd)':    (4, 1, {1:1, 3:-1}),
 'mod 5 quad (real, even)':   (5, 0, {1:1, 4:1, 2:-1, 3:-1}),
 'mod 5 quartic (COMPLEX)':   (5, 1, {1:1, 2:1j, 4:-1, 3:-1j}),
}
def Lval(q, tab, s):
    return q**(-s)*sum(mp.mpc(c)*mp.zeta(s, mp.mpf(a)/q) for a, c in tab.items())
def Lam(q, a, tab, s):
    return (mp.mpf(q)/mp.pi)**((s+a)/2) * mp.gamma((s+a)/2) * Lval(q, tab, s)

for name, (q, a, tab) in CH.items():
    tabc = {k: complex(v).conjugate() for k, v in tab.items()}
    # root number from the FE at a test point; |eps| must be 1
    s0 = mp.mpc('0.3', '1.7')
    eps = Lam(q, a, tab, s0)/Lam(q, a, tabc, 1-s0)
    phase = mp.e**(-1j*mp.arg(eps)/2)
    Z = lambda t: mp.re(phase*Lam(q, a, tab, mp.mpf(1)/2 + 1j*t))
    Zim = lambda t: mp.im(phase*Lam(q, a, tab, mp.mpf(1)/2 + 1j*t))
    imchk = max(float(abs(Zim(mp.mpf(x)))) for x in ['1.3','4.7','9.2'])
    # first zeros of Z by sign change + bisection (real function!)
    ts = np.arange(0.5, 22.0, 0.05); vals = [float(Z(mp.mpf(t))) for t in ts]; zs = []
    for i in range(len(ts)-1):
        if vals[i]*vals[i+1] < 0:
            zs.append(float(mp.findroot(Z, mp.mpf((ts[i]+ts[i+1])/2))))
    zs = sorted(zs)
    # exact-zero check: |L(1/2 + i gamma)|
    exact = max(float(abs(Lval(q, tab, mp.mpf(1)/2+1j*mp.mpf(g)))) for g in zs[:4])
    # Laguerre on the true Z: min over window
    lag = lambda F, t: mp.diff(F, t)**2 - F(t)*mp.diff(F, t, 2)
    grid = np.arange(zs[0]-1.0, zs[3]+1.0, 0.1)
    minL = min(float(lag(Z, mp.mpf(t))) for t in grid)
    # A/B: remove zeros 1,2 (real roots in t), reinsert on-line vs off-line
    g1m, g2m = mp.mpf(repr(zs[0])), mp.mpf(repr(zs[1])); m = (g1m+g2m)/2
    base = lambda t: Z(t)/((t-g1m)*(t-g2m))
    Fon  = lambda t: base(t)*((t-m+mp.mpf('0.4'))*(t-m-mp.mpf('0.4')))
    dl = mp.mpf('0.1')
    Foff = lambda t: base(t)*((t-m)**2 + dl**2)
    w = np.arange(float(m)-1.2, float(m)+1.2, 0.05)
    minLon  = min(float(lag(Fon,  mp.mpf(t))) for t in w)
    minLoff = min(float(lag(Foff, mp.mpf(t))) for t in w)
    print(f"{name:26s}: eps={complex(eps):.4f} |eps|={float(abs(eps)):.6f}  max|Im Z|={imchk:.1e}")
    print(f"{'':26s}  zeros {[round(z,4) for z in zs[:4]]}  max|L(1/2+ig)|={exact:.1e}  (exact)")
    print(f"{'':26s}  min Laguerre: true Z {minL:+.2e} | on-line {minLon:+.2e} | OFF-line d=0.1 {minLoff:+.2e}"
          f"   {'DETECTED' if minLoff<0 and minL>=-1e-12 and minLon>=-1e-12 else 'PROBLEM'}\n")
print("=> one recipe (constant root-number phase) gives a REAL standing wave for every primitive chi --")
print("   real or complex -- and the SAME Laguerre detector passes/detects identically.")
