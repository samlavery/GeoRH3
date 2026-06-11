"""
spectral_staircase.py -- the zeros as a SPECTRUM: each zero = a threshold where a new harmonic is
realized. The counting is a STEP FUNCTION N(T) (the spectral staircase); its smooth part is the Weyl
term theta(T)/pi (the 'volume'). The harmonic is the standing wave Z(T)=e^{i theta}L(1/2+iT) -- REAL,
with a NODE at each zero; theta advances by exactly pi per node (one new half-harmonic per step).
"""
import numpy as np, mpmath as mp
mp.mp.dps = 25
q = 3
def L(s): return 3**(-s)*(mp.zeta(s, mp.mpf(1)/3) - mp.zeta(s, mp.mpf(2)/3))
# theta(T): odd primitive char mod 3 (a=1).  theta = (T/2)log(q/pi) + Im logGamma(3/4 + iT/2)
def theta(T): return float((mp.mpf(T)/2)*mp.log(mp.mpf(q)/mp.pi) + mp.im(mp.loggamma(mp.mpf(3)/4 + 1j*mp.mpf(T)/2)))
# Z(T) = e^{i theta} L(1/2+iT) -- the real standing wave (Hardy Z analog)
def Z(T): return complex(mp.e**(1j*theta(T)) * L(mp.mpf(1)/2 + 1j*mp.mpf(T)))

# first chi3 zeros
zs=[]
for ln in open("lchi3_zeros_1000.txt"):
    ln=ln.strip()
    if ln and not ln.startswith("#"): zs.append(float(ln.split()[1]))
zs=np.array(sorted(zs))[:12]

print("(A) the standing wave Z(T) is REAL, and each zero is a NODE (sign change):")
print(f"   {'T':>8} {'Z(T) (real?)':>22} {'theta(T)/pi':>12}")
for T in [5.0, zs[0], 9.5, zs[1], 13.0, zs[2]]:
    z=Z(T); print(f"   {T:8.3f}   {z.real:+10.4f}{('  (Im=%.1e)'%z.imag):>12}   {theta(T)/np.pi:8.3f}")
print("   => Im(Z)~0 (real standing wave); Z flips sign exactly across each zero (a node).")

print("\n(B) the SPECTRAL STAIRCASE: N(T) (step, +1 per zero) vs the smooth Weyl term theta(T)/pi + 1:")
print(f"   {'zero gamma_n':>12} {'n (step)':>9} {'theta/pi+1 (Weyl)':>18} {'S=N-Weyl (fluct)':>17} {'d(theta)/pi':>11}")
prev=None
for n,g in enumerate(zs, start=1):
    weyl=theta(g)/np.pi + 1
    dth = (theta(g)-theta(prev))/np.pi if prev is not None else float('nan')
    print(f"   {g:12.4f} {n:9d} {weyl:18.3f} {n-weyl:17.3f} {dth:11.3f}")
    prev=g
print("   => the smooth Weyl term tracks the integer step count; d(theta)/pi ~ 1 between consecutive")
print("      zeros: theta advances by ONE pi per zero = ONE new half-harmonic realized at each threshold.")
print("      N(T) - Weyl = S(T), the small fluctuation -- the only non-trivial part (the 'harmonics'\n      arrive a bit early/late, but exactly ONE per step).")
