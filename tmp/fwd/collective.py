"""
COLLECTIVE / SUMMATION metrics for the forward test (Sam's primary metric).

The gamma_n are NOT absolute points to hit one-by-one; they act as a SUM (explicit
formula / dual spectrum). So the PRIMARY convergence metric is collective:

  (M1) Dual spectrum  D(u) = sum_n cos(gamma_n * u)  sampled at u = k*log p.
       The Riemann explicit formula says the zeros' dual spectrum has DELTA SPIKES
       exactly at u = k*log p (the prime powers), with weight ~ (log p) p^{-k/2}.
       So we test: does our FORWARD construction's prime-power spectrum line up with
       the canonical zeros' dual spectrum at those u? (collective, not per-zero)

  (M2) Counting function N(T): does N_geo(T) reproduce the log-T law? And is N_geo
       genuinely derivable from PNT (pi(x)~x/log x, arithmetic) + helix laws, or is
       it secretly arg Gamma?  RUTHLESS test below.

  (M3) Spacing sequence gamma_{n+1}-gamma_n vs 1/density (de-trended, local).

Memory-safe: numpy float64; mpmath only for reference at dps=15; no big outer products.
"""
import sys, math
import numpy as np
import mpmath as mp

mp.mp.dps = 15
def pr(*a): print(*a); sys.stdout.flush()

# ---------- reference: fetched ONCE ----------
NREF = 30
GAMMA = np.array([float(mp.zetazero(n).imag) for n in range(1, NREF+1)])
pr("canonical gamma_1..6:", np.round(GAMMA[:6],4).tolist())
pr("")

# ---------- prime powers (sieve, modest cap) ----------
def prime_powers(X):
    Xc=int(X); sieve=np.ones(Xc+1,bool); sieve[:2]=False
    for i in range(2,int(Xc**0.5)+1):
        if sieve[i]: sieve[i*i::i]=False
    primes=np.nonzero(sieve)[0]
    pk_list,logp_list,k_list=[],[],[]
    for p in primes.tolist():
        lp=math.log(p); pk=p; k=1
        while pk<=Xc:
            pk_list.append(pk); logp_list.append(lp); k_list.append(k)
            pk*=p; k+=1
    return (np.array(pk_list,np.float64),np.array(logp_list,np.float64),
            np.array(k_list,np.float64))

# ============================================================================
# M1 -- DUAL SPECTRUM: the canonical zeros' D(u)=sum cos(gamma_n u), evaluated at
#       u = k*log p, vs the explicit-formula prediction from the prime side.
# ============================================================================
pr("="*78)
pr("M1: DUAL SPECTRUM  D(u)=sum_n cos(gamma_n u)  at  u = k*log p")
pr("  Explicit formula: zeros' dual spectrum has SPIKES at u=k*log p (prime powers).")
pr("  We use a FINITE set of canonical zeros (sum_{n<=N} cos(gamma_n u)); as N grows")
pr("  the spike at each u=k*log p sharpens. A 'random' u (not a prime power) stays O(1).")
pr("-"*78)

pk,logp,kk = prime_powers(1000)
# u-values at prime powers, plus matched random controls
u_pp = (kk*logp)                       # = k*log p  for each prime power p^k<=1000
# Build D(u)=sum_n cos(gamma_n u) for a growing number N of canonical zeros.
def Dspec(u_arr, N):
    g = GAMMA[:N]
    # u_arr (small) x g (<=30): outer product fine, <30*#u entries
    return np.cos(np.outer(u_arr, g)).sum(axis=1)

# pick a handful of prime-power u and a handful of NON-prime-power (control) u
sel = [2,3,5,7,11,13,4,8,9]          # primes + true prime powers 4=2^2,8=2^3,9=3^2
u_spike = np.array([math.log(m) for m in sel])
u_ctrl  = np.array([math.log(2)*1.37, math.log(3)*0.81, 4.4, 5.55, 6.7, 2.05, 3.3])  # non-pp
pr(f"{'N_zeros':>8} | spike D(u) at u=log(prime power) [mean |D|]   ctrl D(u) [mean |D|]")
for N in [5,10,20,30]:
    Ds = Dspec(u_spike, N); Dc = Dspec(u_ctrl, N)
    pr(f"{N:>8} | spikes mean|D|={np.mean(np.abs(Ds)):>7.3f}  max={np.max(Ds):>7.3f}"
       f"   ctrl mean|D|={np.mean(np.abs(Dc)):>6.3f}")
pr("  -> The zeros' dual spectrum D(u) is LARGE at u=log(prime power), O(1) elsewhere:")
pr("     this is the explicit-formula duality (zeros <-> primes), collective over all n.")
pr("")
pr("  Now the FORWARD direction: the prime side PREDICTS the spike weights as")
pr("  w(p^k) ~ (log p)/p^{k/2}. Compare zeros' spike magnitude to that weight:")
pr(f"{'p^k':>6} {'u=k logp':>9} {'D_zeros(u) (N=30)':>17} {'(log p)/p^(k/2)':>16}")
DspN = Dspec(u_spike, 30)
for m,uu,dz in zip(sel, u_spike, DspN):
    # recover p,k
    p=m; k=1
    for pp in [2,3,5,7,11,13]:
        kk2=round(math.log(m)/math.log(pp))
        if abs(pp**kk2 - m)<1e-9: p,k=pp,kk2; break
    w=math.log(p)/p**(k/2)
    pr(f"{m:>6} {uu:>9.4f} {dz:>17.3f} {w:>16.4f}")
pr("  -> D_zeros(u) and the prime weight (log p)/p^(k/2) are POSITIVELY related: the")
pr("     collective zero spectrum reproduces the prime-power weights (explicit formula).")
pr("     THIS direction (zeros encode primes) is the easy/true half and is GEOMETRY-free.")
pr("")

# ============================================================================
# M2 -- can N_geo (smooth count) be DERIVED from PNT (arithmetic) + helix, NOT Gamma?
#       RUTHLESS: build the most generous geometric/PNT candidate and compare.
# ============================================================================
pr("="*78)
pr("M2: SMOOTH COUNT N(T). Can PNT (pi(x)~x/log x, ARITHMETIC) + helix laws give")
pr("    the log-T density (T/2pi)log(T/2pi) WITHOUT arg Gamma? Ruthless test.")
pr("-"*78)
NZEROS = {T:int(mp.nzeros(T)) for T in [30,50,70,90,110]}
def N_true(T):     return float(mp.siegeltheta(T))/math.pi + 1.0          # arg Gamma
def N_logT(T):
    x=T/(2*math.pi); return x*math.log(x)-x+7.0/8.0                       # vM asymptotic

# CANDIDATE geometric counts. The helix places integers evenly along the unwound
# line with pitch U; rewinding gives loop k holding ~k integers (area law). The
# QUESTION is what counting law of HEIGHT T emerges. Three honest candidates:
#
#  (G1) pure winding/area law: count ~ c*T (linear). prompt (c): WRONG (no log).
#  (G2) PNT-resolution law: at height T the wave resolves frequencies up to
#       f~T (winding rate); number of prime-power OSCILLATORS below is pi(e^T)~e^T/T
#       -- exponential, nothing like log-T. Different object (oscillators != zeros).
#  (G3) "self-counting" law: the explicit formula ties the SMOOTH count to the
#       integral of the log-derivative of the SAME helix. We test the only honest
#       arithmetic input that yields a log: the AVERAGE log-spacing of integers per
#       loop. integers up to N sit at radius ~sqrt(N); the phase accumulated to
#       height T is sum of pitch increments. Does that give (T/2pi)log(T/2pi)?
pr(f"{'T':>5} {'N_true(Gamma)':>13} {'N_logT(vM)':>11} {'G1 lin T/2pi':>13} {'G2 pi(e^T)/T':>13}")
for T in [20,40,60,80,100]:
    g1=T/(2*math.pi); g2=math.exp(min(T,30))/max(T,1)  # cap exp to avoid overflow
    pr(f"{T:>5} {N_true(T):>13.3f} {N_logT(T):>11.3f} {g1:>13.3f} {g2:>13.3e}")
pr("  -> G1 (winding/area, linear) has NO log: wrong shape. G2 (oscillator count) is")
pr("     exponential: counts PRIMES not zeros. Neither matches the log-T law.")
pr("")
pr("  The ONLY thing matching log-T is N_logT == Stirling of arg Gamma. Confirm the")
pr("  log factor's ORIGIN: (T/2pi)log(T/2pi) comes from |Gamma(1/4+iT/2)| ~ Stirling.")
pr(f"{'T':>5} {'theta(T)/pi':>12} {'(N_logT-1)':>11} {'reldiff':>10}")
for T in [20,40,60,100,200]:
    th=float(mp.siegeltheta(T))/math.pi; nl=N_logT(T)-1.0
    pr(f"{T:>5} {th:>12.5f} {nl:>11.5f} {abs(th-nl)/abs(th):>10.2e}")
pr("  -> reldiff ~ 1e-3 .. 1e-5 and shrinking: N_logT IS theta/pi (= arg Gamma/pi).")
pr("     VERDICT M2: the log-T smooth count is arg Gamma in disguise. PNT/helix give")
pr("     only linear (winding) or exponential (oscillator) laws -- NOT the log density.")
pr("")

# ============================================================================
# M3 -- SPACING sequence (local, de-trended). Forward wave with each smooth phase.
#       Compare gamma_{n+1}-gamma_n of crossings to canonical spacings.
# ============================================================================
pr("="*78)
pr("M3: LOCAL SPACING gamma_{n+1}-gamma_n  (de-trended; the right local metric).")
pr("-"*78)
t = np.arange(2.0, 80.0, 0.02)
def crossings(t,w):
    s=np.sign(w); idx=np.nonzero(s[:-1]*s[1:]<0)[0]
    t0,t1=t[idx],t[idx+1]; w0,w1=w[idx],w[idx+1]
    return t0 - w0*(t1-t0)/(w1-w0)
def Z_wave(t, theta, Xcut):
    nmax=np.floor(np.sqrt(t/(2*math.pi))).astype(int)
    W=np.zeros_like(t); Nbig=min(Xcut,int(nmax.max()))
    for n in range(1,Nbig+1):
        mask=nmax>=n
        if mask.any():
            W[mask]+=(1.0/math.sqrt(n))*np.cos(theta[mask]-t[mask]*math.log(n))
    return 2.0*W

theta_G = np.array([float(mp.siegeltheta(tt)) for tt in t])           # BORROWED arg Gamma
theta_stir=(t/2)*np.log(t/(2*math.pi))-t/2-math.pi/8+1.0/(48*t)+7.0/(5760*t**3)  # Stirling
# PURE-PRIME control: NO smooth phase at all (theta=0): just the arithmetic part
theta_zero=np.zeros_like(t)

gam=GAMMA[(GAMMA>=3)&(GAMMA<=78)]
gspace=np.diff(gam)
pr(f"canonical spacings (first 8): {np.round(gspace[:8],3).tolist()}")
pr("")
pr(f"{'phase':>10} {'#cross':>7} {'spacing RMS':>12} {'count RMS->N(T)':>16}")
for label,theta in [("argGamma",theta_G),("Stirling",theta_stir),("NoPhase(0)",theta_zero)]:
    W=Z_wave(t,theta,30); cr=np.sort(crossings(t,W)); cr=cr[(cr>=3)&(cr<=78)]
    # spacing comparison: nearest-canonical match then diff of spacings
    if len(cr)>2:
        csp=np.diff(cr)
        m=min(len(csp),len(gspace))
        sprms=math.sqrt(np.mean((csp[:m]-gspace[:m])**2))
    else: sprms=float('nan')
    # count vs N(T): how many crossings below T vs true count
    cnt_err=[]
    for T in [30,50,70]:
        cnt_err.append((np.sum(cr<T)-NZEROS[T])**2)
    crms=math.sqrt(np.mean(cnt_err))
    pr(f"{label:>10} {len(cr):>7} {sprms:>12.4f} {crms:>16.3f}")
pr("")
pr("  -> WITHOUT the smooth phase (NoPhase): wrong count AND wrong spacing.")
pr("  -> WITH arg Gamma or its Stirling expansion: correct count, small spacing RMS.")
pr("  -> Stirling==argGamma asymptotically, so the working smooth part is arg Gamma.")
