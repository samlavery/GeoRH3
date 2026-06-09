import mpmath, numpy as np
mpmath.mp.dps=25
def L(s): return mpmath.power(3,-s)*(mpmath.zeta(s,mpmath.mpf(1)/3)-mpmath.zeta(s,mpmath.mpf(2)/3))
def nLLp(s): return -mpmath.diff(lambda x: mpmath.log(L(x)), s)   # -L'/L
zeros=[8.0397,11.2492,15.7046,18.2620,20.4558]
print("=== Test A: |-L'/L(sigma+i*gamma_n)| at the zeros, sigma -> 1/2+  (predict ~ 1/(sigma-1/2)) ===")
print("sigma   " + "   ".join(f"g={g:.1f}" for g in zeros) + "    1/(sig-.5)")
for sig in [1.5,1.0,0.7,0.6,0.55,0.52,0.51]:
    vals=[abs(complex(nLLp(mpmath.mpc(sig,g)))) for g in zeros]
    print(f"{sig:.2f}  " + "  ".join(f"{v:7.1f}" for v in vals) + f"    {1/(sig-0.5):6.0f}")
print("\n=== Test B: |-L'/L(0.52+it)| lineshape (sharp resonances at gamma_n on smooth bg) ===")
for t in np.arange(7.0,12.4,0.2):
    v=abs(complex(nLLp(mpmath.mpc(0.52,t))))
    print(f"t={t:5.2f} |{'#'*int(min(v,55)):<55} {v:5.1f}" + ("  <-- zero" if any(abs(t-g)<0.12 for g in zeros) else ""))
print("\n=== Test C: between zeros, is -L'/L(1/2+it) on the boundary 'real' (no-drift)? Re vs Im ===")
for t in [9.5,13.0,17.0,19.3,22.0]:
    w=complex(nLLp(mpmath.mpc(0.5,t)))
    print(f"t={t:5.1f}  -L'/L(1/2+it) = {w.real:+.4f} {w.imag:+.4f}i   |Im/Re|={abs(w.imag)/(abs(w.real)+1e-12):.2e}")
