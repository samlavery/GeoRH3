"""
blocky_primefeedback.py
=======================
The fluctuation S(T) is, by the explicit formula, the PRIME side. So the only honest way a
self-consistent blocky helix can capture the per-block jitter is if its feedback rule carries
PRIME information (not just the smooth log mean). We test the two real candidates:

  (A) PHASE-VELOCITY pitch:  the instantaneous winding rate of the resultant is
        d/dt arg L(1/2+it) = -Im (L'/L)(1/2+it)  =  (smooth density) + (prime fluctuation).
      Set the block pitch from THIS (a causal, structure-internal quantity) and integrate:
        N(t) = (1/pi) integral_0^t [-Im L'/L] dt'  -> boundary k where N(t_k)=k-1/2 (Riemann-von Mangoldt
      with the S(T) term INCLUDED). Does declaring boundaries at N(t)=k+1/2 hit the gamma_k exactly?
      This is the self-consistent rule with the fluctuation built into the winding density.

  (B) PRIME-PHASOR resultant: build the 3D phasor solid from PRIMES p (with chi3(p) weights and
      phase t log p), wind it, and ask whether ITS collapse/feature predicts the next zero.
"""
import numpy as np
import mpmath as mp
from blocky_helix_build import compute_exact_zeros, chi3

mp.mp.dps = 25
Q = 3
GAMMA = compute_exact_zeros(65)
gap = np.diff(GAMMA)

def L(s):  return mp.power(3,-s)*(mp.zeta(s,mp.mpf(1)/3)-mp.zeta(s,mp.mpf(2)/3))
def Lp(s): return mp.diff(L, s)

print("="*78)
print("(A) PHASE-VELOCITY pitch  =>  N(t) counting with the S(T) fluctuation INCLUDED")
print("="*78)
# winding density rho(t) = (1/pi) * d/dt arg L(1/2+it) = -(1/pi) Im (L'/L)(1/2+it)
def rho(t):
    s = mp.mpf(1)/2 + 1j*mp.mpf(str(t))
    return float(-mp.im(Lp(s)/L(s))/mp.pi)

# Integrate N(t) on a fine grid; boundaries where N(t) hits half-integers = predicted zeros.
tlo, thi = 0.5, GAMMA[24]+0.5
ts = np.arange(tlo, thi, 0.02)
rhov = np.array([rho(t) for t in ts])
Ncum = np.concatenate([[0], np.cumsum(0.5*(rhov[1:]+rhov[:-1])*np.diff(ts))])
# predicted zero heights: N(t) crosses k+0.5 (the standard counting normalization)
# offset: N(gamma_1) should be ~0.5. find level set crossings.
def crossings(level):
    out=[]
    for i in range(len(ts)-1):
        if (Ncum[i]-level)*(Ncum[i+1]-level) < 0:
            t = ts[i] + (level-Ncum[i])/(Ncum[i+1]-Ncum[i])*(ts[i+1]-ts[i])
            out.append(t)
    return out
# determine offset by matching count at gamma_1
N1 = np.interp(GAMMA[0], ts, Ncum)
print(f"  N(gamma_1) = {N1:.4f}  (sets the half-integer offset)")
off = N1 - 0.5  # so that level k-0.5+off matches
print(f"  {'k':>3} {'exact gamma':>12} {'pred from N(t)=k-1/2':>22} {'err':>9}")
errs=[]
for k in range(1, 16):
    cr = crossings(k-0.5+off)
    pred = cr[0] if cr else float('nan')
    e = pred-GAMMA[k-1]
    errs.append(e)
    print(f"  {k:3d} {GAMMA[k-1]:12.4f} {pred:22.4f} {e:+9.4f}")
errs=np.array(errs)
print(f"\n  phase-velocity counting: mean|err|={np.nanmean(np.abs(errs)):.4f} "
      f"std={np.nanstd(errs):.4f}  vs gap-jitter {np.std(gap):.3f}")
print("  NOTE: this uses L'/L which CONTAINS the zeros -- it is the exact counting function.")
print("  It WILL match (that's Riemann-von Mangoldt). The honest question is whether the")
print("  fluctuation part can come from a PRIME sum WITHOUT already knowing L'/L (part B).")

print("\n" + "="*78)
print("(B) PRIME-PHASOR resultant  -- the von Mangoldt / explicit-formula side")
print("="*78)
# explicit formula: the fluctuation of the counting function is
#   S(T) = -(1/pi) sum_{p,m} chi(p)^m/(m p^{m/2}) sin(T m log p)/... (Riemann-Mangoldt oscillatory)
# Build the prime-phasor SUM P(t) = sum over prime powers chi(p^m) Lambda(p^m) p^{-m/2} e^{i t m log p}.
# Its IMAGINARY part integrated gives the oscillatory S(T). Test: does adding the prime correction
# to the SMOOTH counting reproduce the exact zeros (capturing the fluctuation)?
def vonmangoldt_terms(Pmax=2000):
    terms=[]
    sieve=np.ones(Pmax+1,bool); sieve[:2]=False
    for i in range(2,int(Pmax**.5)+1):
        if sieve[i]: sieve[i*i::i]=False
    primes=np.nonzero(sieve)[0]
    for p in primes:
        m=1; pm=p
        while pm<=Pmax:
            terms.append((p,m,pm))
            m+=1; pm=p**m
    return terms
terms = vonmangoldt_terms(5000)
def Sprime(t, terms):
    # oscillatory part: -(1/pi) sum chi(p)^m /(m p^{m/2}) sin(t m log p)
    s=0.0
    for (p,m,pm) in terms:
        c = chi3(int(p))**m
        if c==0: continue
        s += c/(m*pm**0.5)*np.sin(t*m*np.log(p))
    return -s/np.pi
# smooth main term: theta-like, N_smooth(t) = (t/pi) log(q t /(2 pi e)) /? use (t/2pi) log(qt/2pi)-t/2pi
def Nsmooth(t):
    return (t/(2*np.pi))*np.log(Q*t/(2*np.pi)) - t/(2*np.pi)   # +const
# predicted counting = Nsmooth + Sprime ; zeros where it hits half-integers
Nsp = np.array([Nsmooth(t)+Sprime(t,terms) for t in ts])
off2 = np.interp(GAMMA[0],ts,Nsp) - 0.5
print(f"  {'k':>3} {'exact gamma':>12} {'pred (smooth+prime)':>22} {'err':>9}")
def cross2(level):
    out=[]
    for i in range(len(ts)-1):
        if (Nsp[i]-level)*(Nsp[i+1]-level)<0:
            out.append(ts[i]+(level-Nsp[i])/(Nsp[i+1]-Nsp[i])*(ts[i+1]-ts[i]))
    return out
errs2=[]
for k in range(1,16):
    cr=cross2(k-0.5+off2); pred=cr[0] if cr else float('nan')
    e=pred-GAMMA[k-1]; errs2.append(e)
    print(f"  {k:3d} {GAMMA[k-1]:12.4f} {pred:22.4f} {e:+9.4f}")
errs2=np.array(errs2)
print(f"\n  smooth-only would give std~{np.std(gap):.3f}; smooth+PRIME gives "
      f"std={np.nanstd(errs2):.4f} mean|err|={np.nanmean(np.abs(errs2)):.4f}")
# compare: smooth ONLY
Nsm = np.array([Nsmooth(t) for t in ts]); off3=np.interp(GAMMA[0],ts,Nsm)-0.5
def cross3(level):
    out=[]
    for i in range(len(ts)-1):
        if (Nsm[i]-level)*(Nsm[i+1]-level)<0:
            out.append(ts[i]+(level-Nsm[i])/(Nsm[i+1]-Nsm[i])*(ts[i+1]-ts[i]))
    return out
errs3=[]
for k in range(1,16):
    cr=cross3(k-0.5+off3); errs3.append((cr[0] if cr else np.nan)-GAMMA[k-1])
errs3=np.array(errs3)
print(f"  smooth-ONLY (no prime): std={np.nanstd(errs3):.4f} mean|err|={np.nanmean(np.abs(errs3)):.4f}")
print(f"  => prime correction reduces error from {np.nanstd(errs3):.3f} to {np.nanstd(errs2):.3f}? "
      f"({'YES, captures fluctuation' if np.nanstd(errs2)<0.6*np.nanstd(errs3) else 'partial/no'})")
