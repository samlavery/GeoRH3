import mpmath
mpmath.mp.dps=24
xi=(mpmath.sqrt(10-2*mpmath.sqrt(5))-2)/(mpmath.sqrt(5)-1)
a=[0,mpmath.mpf(1),xi,-xi,mpmath.mpf(-1),mpmath.mpf(0)]
def DH(s): return mpmath.power(5,-s)*sum(a[r]*mpmath.zeta(s,mpmath.mpf(r)/5) for r in range(1,6))
chi5={1:1,2:1j,3:-1j,4:-1}
def L5(s): return mpmath.power(5,-s)*sum(chi5.get(r,0)*mpmath.zeta(s,mpmath.mpf(r)/5) for r in range(1,6))
def Tabs(f,z): return abs(complex(mpmath.diff(lambda x: mpmath.log(f(x)), 0.5+1j*z)))  # |T(z)|=|f'/f(1/2+iz)|
print("=== GENUINE Euler weaving L(chi5): singular support ON R  (IsSelfAdjointReceiver holds) ===")
print("  scan |T_L5(6.18358 + i y)| across the real axis — resonance should sit at y=0:")
for y in [-0.30,-0.15,-0.06,-0.02,0.0,0.02,0.06,0.15,0.30]:
    print(f"    Im z={y:+.2f}: |T_L5| = {Tabs(L5,complex(6.18358,y)):8.1f}"+("   <-- ON R" if y==0 else ""))
print("\n=== BROKEN weaving DH: a resonance OFF R at Im z = -0.3085  (IsSelfAdjointReceiver FAILS) ===")
print("  scan |T_DH(85.69935 + i y)| — resonance should sit OFF the real axis at y=-0.3085:")
for y in [-0.45,-0.35,-0.31,-0.3085,-0.30,-0.25,-0.12,0.0,0.15]:
    mark="   <-- OFF R (off-line zero)" if abs(y+0.3085)<0.01 else ""
    print(f"    Im z={y:+.4f}: |T_DH| = {Tabs(DH,complex(85.69935,y)):8.1f}{mark}")
print("\n=== control: is L(chi5) regular at that same OFF-R height (no off-line resonance)? ===")
for y in [-0.3085,-0.15,0.0]:
    print(f"    Im z={y:+.4f}: |T_L5(85.69935+iy)| = {Tabs(L5,complex(85.69935,y)):8.1f}")
