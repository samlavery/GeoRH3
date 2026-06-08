"""
Step 4: THE CRUX. Where does the smooth (log-T density / theta) part come from?

We test three constructions on the SAME footing (crossings vs gamma_n + density):

  (1) BARE prime powers  Z1(t) = cos(theta_fake) ... NO -- just the prime sum's role.
      The honest object whose zeros ARE gamma_n is the Riemann-Siegel Z function:
          Z(t) = 2 sum_{n<=sqrt(t/2pi)} cos(theta(t) - t log n)/sqrt(n)
      Its zeros are exactly gamma_n. It has TWO ingredients:
          - the prime/integer sum  sum cos(t log n)/sqrt(n)   (geometry/Euler side)
          - the smooth phase theta(t) = arg Gamma(1/4 + it/2) - (t/2) log pi   (BORROWED)

  (2) PRIME-ONLY proxy: replace theta(t) by a GEOMETRIC candidate for the smooth phase
      that the helix/projection might supply WITHOUT Gamma:
        - sqrt(n) area law  -> phase ~ c*sqrt(t)   (prior bake-off: WRONG density)
        - winding/pitch linear -> phase ~ c*t       (constant density, also wrong)
      and see if ANY log-free geometric phase reproduces N(T)~ (T/2pi)log(T/2pi).

  (3) Show that ONLY theta(t) (= arg Gamma, the borrowed piece) gives the right density,
      by plugging theta into the SAME integer sum and checking zeros -> gamma_n.

This isolates exactly what the smooth part is and whether geometry can supply it.
"""
import numpy as np
import mpmath
import json

mpmath.mp.dps = 15
with open("/Users/samuellavery/proof/three/tmp/fwd2/ref.json") as f:
    ref = json.load(f)
gamma_ref = np.array(ref["gamma_ref"])
nzeros_ref = {int(k): v for k, v in ref["nzeros_ref"].items()}

t = np.arange(0.0, 120.0, 0.02)

def crossings(W):
    s = np.sign(W); idx = np.nonzero(np.diff(s)!=0)[0]
    cr=[]
    for i in idx:
        w0,w1=W[i],W[i+1]
        if w1!=w0: cr.append(t[i]-w0*(t[i+1]-t[i])/(w1-w0))
    return np.array(cr)

def rms(cr, g):
    cr2 = cr[(cr>5)&(cr<102)]
    if len(cr2)==0: return float('nan')
    res = np.array([cr2[np.argmin(np.abs(cr2-x))]-x for x in g])
    return np.sqrt(np.mean(res**2))

def density_row(cr, Ts):
    return [int(np.sum((cr>0)&(cr<T))) for T in Ts]

Ts=[20,40,60,80,100]

# ---- theta(t) via mpmath siegeltheta, sampled on grid ONCE (default dps) ----
# This is the BORROWED arg-Gamma piece. We use it only to demonstrate the crux.
theta = np.array([float(mpmath.siegeltheta(float(x))) if x>1 else 0.0 for x in t])

# integer sum with a given phase: Z(t) = 2 sum_{n<=Nmax(t)} cos(phase - t log n)/sqrt(n)
def Z_with_phase(phase, Ncap):
    """Hardy-Z-like wave with main-sum length Ncap(t)=floor(sqrt(t/2pi)) and given smooth phase."""
    W = np.zeros_like(t)
    Nmax = np.floor(np.sqrt(np.maximum(t,0)/(2*np.pi))).astype(int)
    bigN = int(Nmax.max())
    # term n contributes where Nmax>=n
    for n in range(1, max(bigN,1)+1):
        mask = Nmax >= n
        ln = np.log(n)
        W[mask] += 2.0*np.cos(phase[mask] - t[mask]*ln)/np.sqrt(n)
    return W

print("="*72, flush=True)
print("(1) BORROWED-Gamma: Riemann-Siegel Z with theta = arg Gamma (the working case)", flush=True)
print("="*72, flush=True)
Z_true = Z_with_phase(theta, None)
cr = crossings(Z_true)
print(f"  density {Ts}: {density_row(cr,Ts)}   canon: {[nzeros_ref.get(T,0) for T in Ts]}", flush=True)
print(f"  RMS vs gamma_n: {rms(cr,gamma_ref):.5f}   <-- this is the WORKING (Gamma-borrowed) baseline", flush=True)

print("\n" + "="*72, flush=True)
print("(2) GEOMETRIC phase candidates (NO Gamma) -- can geometry supply the smooth part?", flush=True)
print("="*72, flush=True)
# candidate A: sqrt-area-law phase ~ c*t^{3/2}? The phase whose derivative gives the density.
# density n(t) = theta'(t)/pi ~ (1/2pi) log(t/2pi). So theta ~ (t/2)log(t/2pi)-t/2.
# A pure-geometry phase WITHOUT log can't produce a log derivative. Demonstrate:
for name, phase in [
    ("linear  c*t      (winding/pitch, const density)", 0.5*t),
    ("sqrt    c*t^1.5  (area-law sqrt(n))",            (2.0/3.0)*np.sqrt(2*np.pi)*np.power(np.maximum(t,0),1.5)/(2*np.pi)),
    ("quadratic c*t^2",                                 0.01*t**2),
]:
    Z = Z_with_phase(phase, None)
    cr = crossings(Z)
    print(f"  {name:42s} density{Ts}={density_row(cr,Ts)}  RMS={rms(cr,gamma_ref):.4f}", flush=True)
print(f"  {'canonical':42s} density{Ts}={[nzeros_ref.get(T,0) for T in Ts]}", flush=True)

print("\n" + "="*72, flush=True)
print("(3) CRUX VERDICT: theta = (t/2)log(t/2pi) - t/2  -- the LOG phase (= arg Gamma asymptotics)", flush=True)
print("="*72, flush=True)
# This IS the log-T smooth part. It is arg Gamma's asymptotic. Contains log(t).
theta_log = np.where(t>2, 0.5*t*np.log(np.maximum(t,1e-9)/(2*np.pi)) - 0.5*t + np.pi/8.0, 0.0)
Z = Z_with_phase(theta_log, None)
cr = crossings(Z)
print(f"  log-phase density {Ts}: {density_row(cr,Ts)}   canon: {[nzeros_ref.get(T,0) for T in Ts]}", flush=True)
print(f"  log-phase RMS vs gamma_n: {rms(cr,gamma_ref):.5f}", flush=True)
print("\n  --> ONLY a phase containing log(t) (= theta = arg Gamma) gives the right density.", flush=True)
print("      No log-free geometric phase (linear/sqrt/quadratic) reproduces N(T)~(T/2pi)log(T/2pi).", flush=True)
print("      The smooth part is INTRINSICALLY log -- and in this repo log is forbidden in the 3D", flush=True)
print("      helix geometry (CLAUDE.md RULE EIGHT). So the smooth part is BORROWED, not geometric.", flush=True)
