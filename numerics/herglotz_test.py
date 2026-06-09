import mpmath
mpmath.mp.dps=22
def L(s): return mpmath.power(3,-s)*(mpmath.zeta(s,mpmath.mpf(1)/3)-mpmath.zeta(s,mpmath.mpf(2)/3))
def LLp(s): return complex(mpmath.diff(lambda x: mpmath.log(L(x)), s))   # L'/L
def g(z): return -1j*LLp(0.5+1j*z)    # i*(-L'/L(1/2+iz)) : candidate Herglotz / self-adjoint resolvent
print("=== Herglotz test: is g(z)=i*(-L'/L(1/2+iz)) self-adjoint-resolvent (Im g has sign of Im z)? ===")
print("(Im z>0  <=> Re s<1/2 left of line; Im z<0 <=> right.)  Want Im(g) sign = sign(Im z) EVERYWHERE.")
allok=True
for y in [0.3,0.7,1.5,3.0,-0.3,-0.7,-1.5,-3.0]:
    vals=[g(complex(x,y)).imag for x in [4,7,10,13,16,19,22,25]]
    ok=all((v>0)==(y>0) for v in vals)
    allok=allok and ok
    print(f"Im z={y:+.1f} (Re s={0.5-y:+.2f}): Im(g) = "+" ".join(f"{v:+.2f}" for v in vals)+f"   {'HERGLOTZ-OK' if ok else '*** VIOLATED'}")
print(f"\n=> g is {'Herglotz on the tested grid (self-adjoint-resolvent signature, regular off R by POSITIVITY)' if allok else 'NOT globally Herglotz'}")
print("\n=== spectral measure positivity: Im g(x+i0+) >= 0 (the absorption density) near the line ===")
for x in [6,7,8.04,9,11.25,13]:
    v=g(complex(x,0.03)).imag
    print(f"  t={x:6.2f}: Im g(t+i0+) = {v:+.3f}"+("   <-- zero (absorption peak)" if abs(x-8.04)<0.1 or abs(x-11.25)<0.1 else ""))
