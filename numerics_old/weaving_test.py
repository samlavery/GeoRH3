import mpmath
mpmath.mp.dps=28
# Davenport-Heilbronn: period-5 coefficients, FE-symmetric, NON-multiplicative (no Euler product)
xi = (mpmath.sqrt(10-2*mpmath.sqrt(5))-2)/(mpmath.sqrt(5)-1)
a = [0, mpmath.mpf(1), xi, -xi, mpmath.mpf(-1), mpmath.mpf(0)]   # a(1..5)
def DH(s): return mpmath.power(5,-s)*sum(a[r]*mpmath.zeta(s, mpmath.mpf(r)/5) for r in range(1,6))
# genuine Euler-product L(chi5): MULTIPLICATIVE, per-fiber unit-circle winding
chi5={1:1,2:1j,3:-1j,4:-1}
def L5(s): return mpmath.power(5,-s)*sum(chi5.get(r,0)*mpmath.zeta(s,mpmath.mpf(r)/5) for r in range(1,6))
print(f"xi = {float(xi):.6f}   (DH coefficients are NOT multiplicative: a(2)a(3)={float(a[2]*a[3]):.4f} != a(6)=a(1)={float(a[1])})")
print("\n=== BROKEN weaving (DH, no per-fiber factorization): hunt off-line zero near 0.8085+85.699i ===")
best=None
for re in [0.79,0.805,0.81,0.815,0.83]:
    for im in [85.6,85.69,85.70,85.75]:
        v=abs(complex(DH(mpmath.mpc(re,im))))
        if best is None or v<best[2]: best=(re,im,v)
print(f"  coarse min |DH| at Re={best[0]} Im={best[1]} : |DH|={best[2]:.4f}")
z=mpmath.findroot(DH, mpmath.mpc(best[0],best[1]))
print(f"  ZERO: s = {mpmath.nstr(z,14)}")
print(f"  Re s = {float(mpmath.re(z)):.8f}   Re s − 1/2 = {float(mpmath.re(z)-0.5):+.8f}   |DH(z)|={float(abs(DH(z))):.1e}")
print(f"  ==> {'OFF THE CRITICAL LINE' if abs(float(mpmath.re(z))-0.5)>1e-5 else 'on line'}")
print("\n=== GENUINE per-fiber-unitary weaving (L(chi5), Euler product): a zero, on the line ===")
z5=mpmath.findroot(L5, mpmath.mpc(0.5,6.18))
print(f"  ZERO: s = {mpmath.nstr(z5,14)}   Re s = {float(mpmath.re(z5)):.8f}   {'ON LINE' if abs(float(mpmath.re(z5))-0.5)<1e-6 else 'off'}")
print("\n=== same continuous background (both q=5 gamma/FE): Re(−f'/f(1/2+it)) vs (1/2)log(5t/2π) ===")
def nLLp(f,s): return -complex(mpmath.diff(lambda x: mpmath.log(f(x)), s))
for t in [18,22]:
    pred=float(mpmath.log(5*t/(2*mpmath.pi))/2)
    print(f"  t={t}:  DH:{nLLp(DH,complex(0.5,t)).real:+.3f}   L(chi5):{nLLp(L5,complex(0.5,t)).real:+.3f}   pred:{pred:+.3f}")
