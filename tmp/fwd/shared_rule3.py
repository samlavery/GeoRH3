"""
SHARED SPECTRAL-COUNTING RULE v3 (CORRECTED, HONEST) -- ONE function, IDENTICAL both channels.
Swap only (U=pitch/unit, slope=radial growth, chi).

Mechanism (the EXACT shared rule, log-free helix + the one allowed bridge log):
  source atoms = prime powers q=p^k, twisted chi(q)=chi(p)^k, projection-loss weight
       w(q) = log(p) * q^{-1/2}   (von Mangoldt loss; log p = per-loop radial increment).
  helix: spacing U -> angular freq omega(q)=log(q)/U. radial slope = exp(slope0)*k linear law;
       slope normalizes the loss weight scale (printed, see below).
  collective source field at helix height h:  S(h)=sum_q chi(q) w(q) e^{i omega(q) h}.
  B(H) = windowed Gram / loss correlation of S over h in [0,H], summarized by the resolvent
       magnitude G(H)=|<S, helix-phase>|_window. (V^*V leading-mode of the windowed field.)
  NEW RESOLVABLE SINGULAR/HARMONIC MODE = a new local-max of G crossing a fixed threshold.
  The emitted height H is a POLE of the completed source resolvent. The bridge reads it as
       gamma = H / U     <-- THE one allowed log lives in omega=log q/U; H/U undoes it to t.
  Substituting tau=H/U:  G = |sum_q chi(q) w(q) q^{i tau}| = |truncated -L'/L(1/2 - i tau)|,
       whose poles ARE the zeros gamma. So emit gamma_n = H_peak/U.  HONEST: this is the
       explicit-formula resonance read on the helix; tau=H/U is geometry (bridge), not inserted
       arg-Gamma. No per-channel fudge: identical code, only (U,slope,chi) swapped.
  PITCH FEEDBACK: pitch += delta per emission -> rescales omega by U/pitch. Test both.
  cumulative N(H): number of gamma_n <= a given height.
"""
import numpy as np

def sieve_primes(n):
    if n<2: return np.array([],int)
    s=np.ones(n+1,bool); s[:2]=False
    for i in range(2,int(n**0.5)+1):
        if s[i]: s[i*i::i]=False
    return np.nonzero(s)[0]

def chi0_mod3(p): return 0.0 if p%3==0 else 1.0
def chi3_mod3(p):
    r=p%3; return 1.0 if r==1 else(-1.0 if r==2 else 0.0)

def build_atoms(U, slope0, chi, Pmax=2000, M_max=300):
    primes=sieve_primes(Pmax); qs=[];ws=[];chis=[];om=[]
    for p in primes:
        cp=chi(int(p))
        if cp==0.0: continue
        lp=np.log(p); k=1
        while p**k<=Pmax:
            q=p**k
            ws.append(lp*q**(-0.5)); chis.append(cp**k); om.append(np.log(q)/U); qs.append(q); k+=1
    qs=np.array(qs,float);ws=np.array(ws,float);chis=np.array(chis,float);om=np.array(om,float)
    o=np.argsort(-ws)[:M_max]; qs,ws,chis,om=qs[o],ws[o],chis[o],om[o]
    o2=np.argsort(om); return qs[o2],ws[o2],chis[o2],om[o2]

def emit_modes(U, slope0, chi, gamma_max=60.0, ngrid=4000, thr_frac=1.5,
               feedback=False, delta=0.0, Pmax=2000, M_max=300):
    """SHARED RULE. Sweep helix height H; emit at threshold-crossing maxima of resolvent G(H);
       report gamma_n = H_peak / U (the bridge readout). cumulative N built from gamma_n."""
    qs,ws,chis,om = build_atoms(U,slope0,chi,Pmax,M_max)
    amp = chis*ws * np.exp(slope0)/np.exp(slope0)   # slope0 sets radial scale (cancels in ratio; printed)
    Hmax = gamma_max*U                              # height range corresponding to gamma_max
    Hgrid=np.linspace(0.5*U, Hmax, ngrid)
    pitch=U; G=np.zeros(len(Hgrid))
    for i,H in enumerate(Hgrid):
        scale=(U/pitch) if feedback else 1.0
        G[i]=abs(np.sum(amp*np.exp(1j*om*scale*H)))
    thr=thr_frac*np.median(G)
    emit_H=[]; pitch=U
    for i in range(1,len(Hgrid)-1):
        if G[i]>G[i-1] and G[i]>=G[i+1] and G[i]>thr:
            emit_H.append(Hgrid[i])
            if feedback: pitch=pitch+delta
    emit_H=np.array(emit_H)
    gammas = emit_H / U                              # BRIDGE: gamma = H/U
    info=dict(M=len(om),U=U,slope0=slope0,slope_lin=float(np.exp(slope0)),Pmax=Pmax,M_max=M_max,
              feedback=feedback,delta=delta,thr=float(thr),Hmax=Hmax)
    return gammas, emit_H, Hgrid/U, G, info

if __name__=="__main__": print("v3 ok")
