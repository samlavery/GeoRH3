"""
fiber_midpoint.py -- at a zero, do the fibre components' phasors ALIGN, pointing at a central midpoint?
Fibre a's regularized resultant (its full phasor walk, continued) is the Hurwitz piece
   R_a(s) = q^{-s} zeta(s, a/q).
chi3:  L = R_1 - R_2.  At a zero: R_1 = R_2 -- the two fibres MEET at one point V (alignment!),
and V must be the FAMILY MIDPOINT: V = (1/2)[R_1+R_2] = (q^s-1)/2 * zeta(s) / q^s * ... = (3^s-1)zeta(s)/2.
The midpoint is the principal-character (zeta) component -- the centre of the mod-3 family.
"""
import mpmath as mp
mp.mp.dps = 25
Z3 = ['8.0397371556814666817','11.2492062077729352497','15.7046191767216255652',
      '18.2619974956931275689','20.4557708077424928534']
print("chi3 (q=3): fibre resultants R_a = 3^{-s} zeta(s,a/3) at s = 1/2 + i*gamma")
print(f"  {'gamma':>9} {'|R1-R2|':>10} {'align angle':>11} {'|R1 - midpoint|':>15} {'arg V':>8} {'|V|':>7}")
for g in Z3:
    s = mp.mpf(1)/2 + 1j*mp.mpf(g)
    R1 = 3**(-s)*mp.zeta(s, mp.mpf(1)/3); R2 = 3**(-s)*mp.zeta(s, mp.mpf(2)/3)
    V  = (3**s - 1)*mp.zeta(s)/(2*3**s)          # predicted midpoint = principal/zeta component /3^s
    ang = abs(mp.arg(R1/R2))
    print(f"  {float(mp.mpf(g)):9.4f} {float(abs(R1-R2)):10.1e} {float(ang):11.1e} "
          f"{float(abs(R1-V)):15.1e} {float(mp.arg(V)):8.3f} {float(abs(V)):7.4f}")
print("  off-zero control (t=9.5): ", end="")
s = mp.mpf(1)/2 + 1j*mp.mpf('9.5')
R1 = 3**(-s)*mp.zeta(s, mp.mpf(1)/3); R2 = 3**(-s)*mp.zeta(s, mp.mpf(2)/3)
print(f"|R1-R2| = {float(abs(R1-R2)):.3f},  align angle = {float(abs(mp.arg(R1/R2))):.3f} rad  (NOT aligned)")

print("\nmod 4: at the first chi4 zero, fibres 1 and 3 must meet at (1-2^{-s})zeta(s)/2:")
s = mp.mpf(1)/2 + 1j*mp.mpf('6.0209489046975965')
R1 = 4**(-s)*mp.zeta(s, mp.mpf(1)/4); R3 = 4**(-s)*mp.zeta(s, mp.mpf(3)/4)
V  = (1 - 2**(-s))*mp.zeta(s)/2
print(f"  |R1-R3| = {float(abs(R1-R3)):.1e}   |R1-V| = {float(abs(R1-V)):.1e}   (align: {float(abs(mp.arg(R1/R3))):.1e} rad)")

print("\nmod 5 quad: fibre GROUPS {1,4} and {2,3} must meet at (1-5^{-s})zeta(s)/2:")
s = mp.mpf(1)/2 + 1j*mp.mpf('6.6484531451')
Rp = 5**(-s)*(mp.zeta(s,mp.mpf(1)/5)+mp.zeta(s,mp.mpf(4)/5))
Rm = 5**(-s)*(mp.zeta(s,mp.mpf(2)/5)+mp.zeta(s,mp.mpf(3)/5))
V  = (1 - 5**(-s))*mp.zeta(s)/2
print(f"  |R+ - R-| = {float(abs(Rp-Rm)):.1e}   |R+ - V| = {float(abs(Rp-V)):.1e}   (align: {float(abs(mp.arg(Rp/Rm))):.1e} rad)")
