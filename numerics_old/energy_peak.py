import mpmath
mpmath.mp.dps=24
def L(s): return mpmath.power(3,-s)*(mpmath.zeta(s,mpmath.mpf(1)/3)-mpmath.zeta(s,mpmath.mpf(2)/3))
def nLLp(s): return complex(-mpmath.diff(lambda x: mpmath.log(L(x)), s))   # -L'/L
def chi3(n): return [0,1,-1][n%3]
print("=== SMOOTH scale: geometric energy bound  vs  harmonic/spectral peak (chi3) ===")
print(" the geometric counting Σχ(n)n^(-1/2-iγ) has ~ √(3t/2π) effective fibers (the AFE/area-law")
print(" cutoff where the two sides cancel). Its energy bound = log(#fibers). Compare to Re(-L'/L):")
print(f"{'t':>4} {'#fibers √(3t/2π)':>16} {'energy=log(fibers)':>18} {'spectral peak Re(-L/L)':>22}")
for t in [12,16,22,30,50,80]:
    X = mpmath.sqrt(3*t/(2*mpmath.pi))
    energy = mpmath.log(X)                       # geometric energy bound
    peak   = nLLp(complex(0.5,t)).real           # harmonic/spectral peak (density)
    print(f"{t:4d} {float(X):16.3f} {float(energy):18.4f} {float(peak):22.4f}")
print("  => energy bound = log(#fibers) = (1/2)log(3t/2π) = the spectral peak.  EQUAL.")
print("\n=== PER-SINGULARITY scale: the cancellation's energy = the resonance residue = multiplicity ===")
print(" at a zero the counting vanishes (order = how it cancels); -L'/L has a pole there.")
print(" residue of -L'/L at ρ = -(order). Compute (s-ρ)·(-L'/L) → -order at γ₁,γ₂:")
for g in [mpmath.mpf("8.0397371556814667"), mpmath.mpf("11.2492062077729352")]:
    rho=complex(0.5,float(g))
    for eps in [1e-4,1e-6]:
        res = eps*nLLp(complex(rho.real+eps, rho.imag))
        print(f"  γ={float(g):.4f}  ε={eps:.0e}:  (s-ρ)(-L'/L)={res.real:+.4f}{res.imag:+.4f}i  → -order")
print("  => |residue| = 1 = order = multiplicity:  the singularity's energy = the spectral peak's residue.")
