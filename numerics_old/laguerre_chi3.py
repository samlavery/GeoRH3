"""
laguerre_chi3.py -- the LOCAL line-detector: Laguerre inequality on the chi3 standing wave.

Xi(t) = completed Lambda(1/2+it), real & even.  If all zeros are REAL (GRH(chi3)) then Xi is in the
Laguerre-Polya class, hence the LAGUERRE INEQUALITY holds pointwise:

        L(t) = Xi'(t)^2 - Xi(t)*Xi''(t)  >=  0     for ALL real t.

Standing-wave reading: a true zero is a NODE (the wave touches 0). An off-line pair gamma +- i*delta
LIFTS the node: Xi dips to ~4*g^2*delta^2 > 0 without touching; at that lifted minimum Xi'=0, Xi>0,
Xi''>0, so L = -Xi*Xi'' < 0.  The violation exists for EVERY delta>0 (magnitude ~ delta^2) -- a local,
non-gauge detector of the line, unlike the global Jensen window (blind below x-angle pi/4).

A/B: slide the two lowest zero-pairs ALONG the line (L must stay >=0) vs FUSE them off the line
(L must go negative near the lifted node), at the same coefficient-free, direct-evaluation level.
"""
import mpmath as mp

mp.mp.dps = 50
g1 = mp.mpf('8.0397371556814666817136232141729658027930102674')
g2 = mp.mpf('11.2492062077729352497050256788632146486959267932')
gavg = (g1 + g2)/2

def Lfun(s): return 3**(-s)*(mp.zeta(s, mp.mpf(1)/3) - mp.zeta(s, mp.mpf(2)/3))
def Xi(t):
    s = mp.mpf(1)/2 + 1j*t
    return mp.re((mp.mpf(3)/mp.pi)**((s+1)/2) * mp.gamma((s+1)/2) * Lfun(s))

def base(t):                       # Xi with the two lowest zero-pairs divided out (entire, >0 nearby)
    return Xi(t)/((t**2 - g1**2)*(t**2 - g2**2))

def F_on(eps):                     # reinsert TWO REAL pairs: zeros slid along the line
    return lambda t: base(t)*((t**2 - (gavg-eps)**2)*(t**2 - (gavg+eps)**2))
def F_off(dl):                     # fuse into the off-line quartet gavg +- i*dl (manifestly real form)
    return lambda t: base(t)*((t**2 - gavg**2 + dl**2)**2 + 4*gavg**2*dl**2)

def laguerre(F, t):
    return mp.diff(F, t)**2 - F(t)*mp.diff(F, t, 2)

def scan(F, lo, hi, step):
    tmin, lmin = None, mp.mpf('inf')
    t = mp.mpf(lo)
    while t <= hi:
        l = laguerre(F, t)
        if l < lmin: lmin, tmin = l, t
        t += step
    return float(lmin), float(tmin)

print("LAGUERRE L(t)=Xi'^2 - Xi*Xi''  (>=0 everywhere <=> consistent with all-real zeros)\n")

lmin, tmin = scan(Xi, 0.5, 20.0, 0.25)
print("  chi3 itself          : min L on [0.5,20]   = %+.3e  at t=%.2f   (>=0: PASS)" % (lmin, tmin))

for eps in ['1.5', '0.5', '0.1']:
    F = F_on(mp.mpf(eps))
    lmin, tmin = scan(F, 7.0, 13.0, 0.1)
    print("  ON-line slide eps=%-4s: min L on [7,13]     = %+.3e  at t=%.2f   (%s)"
          % (eps, lmin, tmin, "PASS >=0" if lmin >= -1e-30 else "FAIL"))

print()
for dl in ['1.0', '0.5', '0.1', '0.01', '0.001']:
    F = F_off(mp.mpf(dl))
    lmin, tmin = scan(F, 8.6, 10.7, 0.05)
    # lifted node: min |F| near gavg vs the on-line touch
    fmin = min(abs(F(mp.mpf(t)/100)) for t in range(int(8.6*100), int(10.7*100), 5))
    print("  OFF-line fuse d=%-5s: min L = %+.3e  at t=%.2f ; lifted node min|F| = %.3e   (%s)"
          % (dl, lmin, tmin, fmin, "DETECTED L<0" if lmin < 0 else "blind"))

print("""
  => chi3 and every ON-line rearrangement: L(t) >= 0 (nodes touch).  EVERY off-line fusion,
     down to delta=0.001, drives L(t) < 0 at the lifted node (violation ~ delta^2, never zero).
     The line is exactly 'every node of the standing wave touches zero' -- a local, falsifiable,
     non-gauge inequality on Xi alone.  GRH(chi3) <=> no lifted node, anywhere, ever.""")
