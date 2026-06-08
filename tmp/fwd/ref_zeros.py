import mpmath as mp
import numpy as np
import json, os

mp.mp.dps = 15

OUT = "/Users/samuellavery/proof/three/tmp/fwd/ref_zeros.json"

# ---------- Channel A reference: Riemann zeta nontrivial zeros ----------
# L(chi0 mod 3, s) = zeta(s)*(1 - 3^-s); nontrivial zeros identical to zeta's.
NA = 25
zetaA = [float(mp.im(mp.zetazero(n))) for n in range(1, NA+1)]

# ---------- Channel B reference: L(chi3 mod 3) zeros ----------
# chi3: +1 if n=1 mod3, -1 if n=2 mod3, 0 if n=0 mod3. Odd real primitive char mod 3.
# L(chi3,s) = 3^-s ( zeta(s,1/3) - zeta(s,2/3) ) via Hurwitz zeta.
def Lchi3(s):
    s = mp.mpf(s) if not isinstance(s, mp.mpc) else s
    return mp.power(3, -s) * (mp.zeta(s, mp.mpf(1)/3) - mp.zeta(s, mp.mpf(2)/3))

# Odd character: completed L includes Gamma((s+1)/2). To find zeros on critical line
# we look at the real-valued function on s=1/2+it. For an odd primitive real char with
# root number 1, the completed Lambda(1/2+it) is real. Use a Hardy-Z-like real function:
#   Z_chi(t) = (rotation) * L(chi3, 1/2+it)  made real via the functional-equation phase.
# Simplest robust approach: track L on the line and use the completed function's real part.
# For odd char mod q=3: Lambda(s) = (q/pi)^((s+1)/2) Gamma((s+1)/2) L(s).
def Lambda_chi3(t):
    s = mp.mpc(0.5, t)
    q = mp.mpf(3)
    gam = mp.gamma((s+1)/2)
    pref = mp.power(q/mp.pi, (s+1)/2)
    val = pref * gam * Lchi3(s)
    return val  # should be real (up to tiny imaginary) on the line

# Build a real function whose sign changes mark zeros: take the real rotation.
# Determine phase at t small and divide it out as a real Hardy function.
def Z_chi3(t):
    v = Lambda_chi3(t)
    return v  # complex; we'll use a consistently-rotated real part

# Find sign changes of the real part of a phase-corrected Lambda.
# Lambda(1/2+it) for this self-dual char is real-valued; numeric residue tiny.
# Sanity check realness:
import sys
test_ts = [0.5, 2.0, 8.0]
real_check = [(t, complex(Lambda_chi3(t))) for t in test_ts]

# Real Hardy function:
def hardy(t):
    return float(mp.re(Lambda_chi3(t)))

# scan for sign changes
ts = np.arange(0.01, 45.0, 0.02)
vals = np.array([hardy(t) for t in ts])
zerosB = []
for i in range(len(ts)-1):
    if vals[i] == 0:
        continue
    if vals[i]*vals[i+1] < 0:
        a, b = ts[i], ts[i+1]
        try:
            r = mp.findroot(hardy, (a+b)/2)
            zerosB.append(float(r))
        except Exception:
            pass
# dedup
zerosB_clean = []
for z in sorted(zerosB):
    if not zerosB_clean or abs(z - zerosB_clean[-1]) > 1e-3:
        zerosB_clean.append(z)
zerosB_clean = zerosB_clean[:15]

out = {
    "channelA_zeta_zeros": zetaA,
    "channelB_Lchi3_zeros": zerosB_clean,
    "realness_check": [(t, abs(c.imag)) for t,c in real_check],
}
with open(OUT, "w") as f:
    json.dump(out, f, indent=2)

print("Channel A (zeta) first 10:", [round(x,4) for x in zetaA[:10]])
print("Channel B (Lchi3) first 15:", [round(x,4) for x in zerosB_clean])
print("Realness check (t, |imag(Lambda)|):", [(t, round(im,2e-16 if False else 12)) for t,im in [(t, abs(c.imag)) for t,c in real_check]])
