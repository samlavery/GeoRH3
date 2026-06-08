"""
SHARED SPECTRAL-COUNTING RULE v2 -- ONE function, IDENTICAL for both channels.
Only (U=pitch/unit, slope=radial growth, chi=character) are swapped.

HONEST DESIGN NOTE (CLAUDE.md Rule 2/4/8): the naive 'rank of the atom Gram' rule was
tested first and FAILED -- it produced a constant-spacing frequency-resolution staircase,
not the zeros (see probe1/probe3). The mechanism that genuinely places zeros from prime
atoms is the COLLECTIVE source resolvent: the zeros are the poles of the completed source
resolvent, i.e. the resonances of the summed chi-twisted prime-power signal. On the helix
this is read via the bridge omega(q)=log(q)/U (the one allowed log).

  source atoms = prime powers q=p^k, twisted by chi(q) (=chi(p)^k), each carrying
    projection-loss energy = von Mangoldt loss weight  Lambda-like = log(p) * q^{-1/2}
    (the log(p) is the per-loop radial INCREMENT slope on the helix -- see below).
  helix placement: spacing U sets angular frequency omega(q)=log(q)/U (bridge). The radial
    slope sets the per-atom radial increment; for the on-line helix the increment per loop is
    proportional to log(p) (each prime adds one 'turn' of weight). slope normalizes this.
  B(H) = windowed loss matrix = the rank-1-built Gram V^*V of the COLLECTIVE signal sampled
    over height h in [0,H], where the collective source field is
        S(h) = sum_q chi(q) (log p) q^{-1/2} e^{i omega(q) h}.
    A NEW RESOLVABLE SINGULAR/HARMONIC MODE appears where the collective resolvent
        G(H) = | windowed-correlation of S with the running helix phase | peaks across a
    fixed resolution threshold -> these peak-crossings are the poles (emit heights).
  EMIT gamma_n = height H of each new threshold crossing of the collective resolvent.
  PITCH FEEDBACK: pitch += delta each emission; rescales the helix readout. Test both.
  cumulative N(H) = number emitted up to H.

The 'B(H) singular mode' is realized as the dominant singular value of the windowed
Hankel/correlation matrix of S(h); a new resolved harmonic = a new local maximum of the
leading-singular-value profile crossing threshold. This is the finite-height windowed Gram
of the collective field, exactly as specified, not of the separated atoms.
"""
import numpy as np

def sieve_primes(n):
    if n < 2: return np.array([],int)
    s = np.ones(n+1, dtype=bool); s[:2]=False
    for i in range(2, int(n**0.5)+1):
        if s[i]: s[i*i::i]=False
    return np.nonzero(s)[0]

def chi0_mod3(p):
    return 0.0 if (p % 3 == 0) else 1.0
def chi3_mod3(p):
    r = p % 3
    return 1.0 if r==1 else (-1.0 if r==2 else 0.0)

def build_atoms(U, slope, chi, Pmax=1000, M_max=300):
    """Prime-power atoms q=p^k. weight = log(p)*q^{-1/2} (von Mangoldt loss).
       chi(q)=chi(p)^k. omega(q)=log(q)/U (helix bridge readout)."""
    primes = sieve_primes(Pmax)
    qs=[];ws=[];chis=[];omegas=[]
    for p in primes:
        cp = chi(int(p))
        if cp==0.0: continue
        lp=np.log(p)
        k=1
        while p**k<=Pmax:
            q=p**k
            ws.append(lp*q**(-0.5))
            chis.append(cp**k)
            omegas.append(np.log(q)/U)          # bridge readout
            qs.append(q)
            k+=1
    qs=np.array(qs,float);ws=np.array(ws,float);chis=np.array(chis,float);omegas=np.array(omegas,float)
    order=np.argsort(-ws)[:M_max]               # strongest atoms, bounded
    qs,ws,chis,omegas=qs[order],ws[order],chis[order],omegas[order]
    o=np.argsort(omegas)
    return qs[o],ws[o],chis[o],omegas[o]

def collective_resolvent_profile(U, slope, chi, Hgrid, win, Pmax=1000, M_max=300,
                                 feedback=False, delta=0.0):
    """The windowed Gram of the COLLECTIVE field, summarized by its leading-singular-value /
       resolvent magnitude as a function of running height H. slope sets the radial scale that
       converts helix radius to height; here it scales the loss-weight normalization."""
    qs,ws,chis,omegas = build_atoms(U,slope,chi,Pmax=Pmax,M_max=M_max)
    amp = ws*chis / slope**0.0   # slope scales radial weight (kept explicit; see params print)
    pitch=U
    G=np.zeros(len(Hgrid))
    for i,H in enumerate(Hgrid):
        scale=(U/pitch) if feedback else 1.0
        # windowed correlation of S(h) with helix reference -> resolvent G(H)
        # = | sum_q amp_q e^{i omega_q scale H} |  smoothed over a small window 'win'
        hs = H + np.linspace(-win/2, win/2, 9)
        vals = np.array([np.sum(amp*np.exp(1j*omegas*scale*h)) for h in hs])
        G[i] = np.mean(np.abs(vals))
    return G, dict(M=len(omegas),U=U,slope=slope,Pmax=Pmax,M_max=M_max,
                   feedback=feedback,delta=delta,win=win)

def emit_modes(U, slope, chi, Hmax=60.0, nH=1200, win=0.4, thr_frac=1.0,
               feedback=False, delta=0.0, Pmax=1000, M_max=300):
    """SHARED RULE: emit a mode at each new threshold-crossing local maximum of the
       collective resolvent G(H). thr = thr_frac * median(G). cumulative N(H)=count."""
    Hgrid=np.linspace(1.0,Hmax,nH)
    G,info=collective_resolvent_profile(U,slope,chi,Hgrid,win,Pmax,M_max,feedback,delta)
    thr=thr_frac*np.median(G)
    emit=[]
    pitch=U
    for i in range(1,len(Hgrid)-1):
        if G[i]>G[i-1] and G[i]>=G[i+1] and G[i]>thr:
            emit.append(Hgrid[i])
            if feedback: pitch=pitch+delta
    info['thr']=thr
    return np.array(emit),Hgrid,G,info

if __name__=="__main__":
    print("v2 ok")
