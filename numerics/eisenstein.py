"""
eisenstein.py -- ground the 6th-root-of-unity / hexagonal structure of chi3.
chi3 is the character of Q(sqrt-3) = the Eisenstein integers Z[omega], omega=e^{2pi i/3} (a 6th root).
Hexagonal lattice, units = six 6th-roots, norm N(a,b)=a^2-ab+b^2.  Key: zeta_{Q(sqrt-3)} = zeta * L(chi3).
We verify this WITHOUT log/sqrt -- pure lattice/quadratic-form structure.
"""
import numpy as np, mpmath as mp
mp.mp.dps = 25
def chi3(n): return [0,1,-1][n%3]

# (1) chi3(p) IS the Eisenstein splitting of the prime p:
print("(1) chi3(p) = Eisenstein splitting:  p=1 mod3 SPLITS (chi=+1), p=2 mod3 INERT (chi=-1)")
for p in [2,3,5,7,11,13,17,19,23,29,31]:
    kind = "ramified" if p%3==0 else ("split " if p%3==1 else "inert ")
    print(f"    p={p:3d}: p mod3={p%3}, chi3(p)={chi3(p):+d}  -> {kind}")

# (2) the hexagonal Epstein zeta = zeta * L(chi3)  (the chi3 zeros live in the lattice's zeta)
def Lchi3(s): return 3**(-s)*(mp.zeta(s, mp.mpf(1)/3) - mp.zeta(s, mp.mpf(2)/3))
def hex_epstein(s, B=400):
    # (1/6) sum_{(a,b)!=0} (a^2-ab+b^2)^{-s}  -- pure quadratic norm form, no log/sqrt in the SUM
    tot = mp.mpf(0)
    for a in range(-B, B+1):
        for b in range(-B, B+1):
            m = a*a - a*b + b*b
            if m != 0: tot += mp.mpf(m)**(-s)
    return tot/6
s = mp.mpf(2)
lhs = hex_epstein(s, 300); rhs = mp.zeta(s)*Lchi3(s)
print(f"\n(2) at s=2:  (1/6)*sum_hex (a^2-ab+b^2)^-2 = {mp.nstr(lhs,12)}")
print(f"             zeta(2)*L(chi3,2)              = {mp.nstr(rhs,12)}   (match => hex lattice zeta = zeta*L_chi3)")

# (3) the 'volume of (Eisenstein) integers' -- hexagonal lattice point count vs norm
print("\n(3) hexagonal lattice point count  N(X)=#{(a,b)!=0: a^2-ab+b^2<=X}  ~ (2pi/sqrt3) X :")
for X in [100, 1000, 10000]:
    cnt = sum(1 for a in range(-150,151) for b in range(-150,151)
              if 0 < a*a-a*b+b*b <= X)
    print(f"    X={X:6d}: count={cnt:7d}   (2pi/sqrt3)*X={2*np.pi/np.sqrt(3)*X:9.1f}   ratio={cnt/(2*np.pi/np.sqrt(3)*X):.4f}")
print("    => the 'volume of integers' here is a HEXAGONAL lattice count (quadratic norm), not log/sqrt.")

# (4) the 6th roots of unity: the units, and chi3 over one period via 6th-root phasors
print("\n(4) the six 6th-roots e^{i k pi/3}, k=0..5, are the UNITS of Z[omega] (sum to 0):")
roots = [mp.e**(1j*mp.pi*k/3) for k in range(6)]
print(f"    sum of 6th roots = {mp.nstr(sum(roots),6)}   (balanced)")
