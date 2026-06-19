"""
pi/3 helix Frobenius fit -- using the ACTUAL placement rule (RequestProject/HelixGaugeIdentity.lean).

  piThirdA  = pi/6            (radial growth A)
  piThirdDs = pi/3            (arc spacing ds)
  piThirdGauge C = 2*A*ds = (pi/3)^2     (area gauge)
  piThirdRadiusSq n = C*n     ->   R_n = (pi/3)*sqrt(n)        [area-packing placement]

  gauge-trace residue at a zero rho:  -n * C^{-rho},  magnitude  n * C^{-Re rho}   (helixTraceCont_residue_tendsto)
  baseline (area-packing radius sqrt(n), sigma=1/2):  n * C^{-1/2}
  FORCING (online_of_gauge_eq_baseline):  |C^{-rho}| = C^{-1/2}  <=>  Re rho = 1/2.

  C = (pi/3)^2 is the helix's 'q'; C^{-rho} is the gauge/Frobenius weight; |C^{-rho}| = C^{-1/2}
  is the sqrt(q)-pure baseline.  Frobenius x p scales the radius R_n by sqrt(p) exactly.
"""
import numpy as np

A  = np.pi/6
ds = np.pi/3
C  = 2*A*ds
print(f"pi/3 gauge:  A=pi/6={A:.6f}   ds=pi/3={ds:.6f}   C=2*A*ds={C:.6f}   (pi/3)^2={(np.pi/3)**2:.6f}")

def R(n):  # placement radius  R_n = (pi/3) sqrt(n),  R_n^2 = C*n
    return (np.pi/3)*np.sqrt(n)

print("\n(1) placement R_n = (pi/3) sqrt(n)   (area-packing  R_n^2 = C*n):")
for n in [1,2,3,5,7,16]:
    print(f"    n={n:2d}:  R_n={R(n):.5f}   R_n^2={R(n)**2:.5f}   C*n={C*n:.5f}")

print("\n(2) Frobenius x p:  R_(pn)/R_n = sqrt(p) = sqrt(q)   (EXACT radial scaling on the pi/3 placement):")
for (n,p) in [(1,2),(1,3),(2,5),(3,7)]:
    print(f"    n={n}, p={p}:  R(pn)/R(n)={R(p*n)/R(n):.6f}   sqrt(p)={np.sqrt(p):.6f}")

print("\n(3) gauge forcing:  |C^{-rho}| = C^{-Re rho}  vs baseline C^{-1/2}   (online_of_gauge_eq_baseline):")
baseline = C**(-0.5)
print(f"    baseline C^(-1/2) = {baseline:.6f}   (= 3/pi = {3/np.pi:.6f})")
for sigma in [0.5, 0.85, 0.3]:
    mag = C**(-sigma)
    flag = "== baseline  ->  Re rho = 1/2 (ON LINE)" if abs(mag-baseline) < 1e-12 else "!= baseline  ->  off line"
    print(f"    Re rho={sigma:<4}:  |C^(-rho)| = C^(-{sigma}) = {mag:.6f}   {flag}")

print("\n(4) actual zeros rho = 1/2 + i*gamma: the gauge/Frobenius weight C^{-rho} sits on the sqrt(q) baseline:")
for g in [14.134725, 21.022040, 25.010858]:
    rho = 0.5 + 1j*g
    eig = C**(-rho)
    print(f"    rho=1/2+{g}i:  C^(-rho)={eig.real:+.5f}{eig.imag:+.5f}i   |C^(-rho)|={abs(eig):.6f}   baseline={baseline:.6f}")

print(f"""
FIT (pi/3, the real rule):
  - integers placed by AREA: R_n = (pi/3) sqrt(n)  =>  the sigma=1/2 baseline is the sqrt(n) radius.
  - Frobenius x p is an EXACT radial dilation by sqrt(p)=sqrt(q) on that placement.
  - the area gauge C=(pi/3)^2 is the helix's q; the gauge weight C^{{-rho}} is sqrt(q)-pure
    ( |C^{{-rho}}| = C^{{-1/2}} )  iff  Re rho = 1/2  -- the EARNED forcing online_of_gauge_eq_baseline.
  - OPEN WELD (named plainly, Rule Ten): GaugeBaselineIdentity  || C^{{-rho}}*(-n) || = n*C^{{-1/2}},
    the norm identity equivalent to Re rho=1/2 -- that the residue atom IS the on-baseline source atom.
""")
