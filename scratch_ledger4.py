"""
Ledger 4 test (energy / atom matching), chi3 — earned, no zero_embed:
 (A) residue of -L'/L at each zero = the spectral atom weight = multiplicity (should be 1, from the trace kernel).
 (B) explicit formula: prime trace  psi(x,chi3)=sum Lambda(n)chi3(n)  ==  zero atoms  -sum_rho x^rho/rho.
     If they reconstruct each other, the prime energy and the zero/loss atoms are the same ledger.
"""
import numpy as np, math
import mpmath as mp
mp.mp.dps = 20

def L(s):   return mp.power(3,-s)*(mp.zeta(s,mp.mpf(1)/3)-mp.zeta(s,mp.mpf(2)/3))
def negLp_L(s):  return -mp.diff(L,s)/L(s)        # -L'/L

# --- find chi3 zeros up to T ---
T = 60.0
ts = np.arange(0.5, T, 0.05)
av = np.array([float(abs(L(mp.mpf(1)/2+1j*mp.mpf(float(t))))) for t in ts])
gammas=[]
for i in range(1,len(av)-1):
    if av[i]<av[i-1] and av[i]<av[i+1] and av[i]<0.4:
        r = mp.findroot(lambda t: L(mp.mpf(1)/2+1j*t), mp.mpf(float(ts[i])))
        g = float(mp.re(r))
        if (not gammas or abs(g-gammas[-1])>1e-3) and abs(L(mp.mpf(1)/2+1j*mp.mpf(g)))<1e-8:
            gammas.append(g)
gammas=np.array(sorted(g for g in gammas if g>0))
print(f"chi3 zeros found up to {T}: {len(gammas)}")

# --- (A) residue of -L'/L at each zero (atom weight) ---
print("\n(A) residue of -L'/L at rho = 1/2 + i*gamma   (= spectral atom weight = multiplicity)")
for g in gammas[:8]:
    rho = mp.mpf(1)/2 + 1j*mp.mpf(g)
    eps = mp.mpf('1e-7')
    res = eps*negLp_L(rho+eps)              # residue ~ eps * (-L'/L)(rho+eps)
    print(f"   gamma={g:8.4f}   residue = {mp.nstr(res,6)}   |residue| = {float(abs(res)):.4f}")

# --- (B) explicit formula: prime trace vs zero atoms ---
Nmax=200000
sieve=np.ones(Nmax+1,bool); sieve[:2]=False
for i in range(2,int(Nmax**0.5)+1):
    if sieve[i]: sieve[i*i::i]=False
Lam=np.zeros(Nmax+1)
for p in np.nonzero(sieve)[0].tolist():
    lp=math.log(p); pk=p
    while pk<=Nmax: Lam[pk]=lp; pk*=p
nn=np.arange(0,Nmax+1)
chi3=np.where(nn%3==1,1.0,np.where(nn%3==2,-1.0,0.0))
contrib=Lam*chi3                                   # Lambda(n) chi3(n)

def psi_prime(x):                                  # prime trace  sum_{n<=x} Lambda chi3
    return float(np.sum(contrib[:int(x)+1]))

def psi_zeros(x):                                  # zero atoms  -sum_rho x^rho/rho  (rho=1/2+/-i gamma)
    xs=mp.mpf(x); tot=mp.mpf(0)
    for g in gammas:
        rho=mp.mpf(1)/2+1j*mp.mpf(g)
        tot+= mp.power(xs,rho)/rho + mp.power(xs,mp.conj(rho))/mp.conj(rho)
    return float(-mp.re(tot))

print("\n(B) explicit formula  psi(x,chi3)  vs  -sum_rho x^rho/rho   (prime trace vs zero atoms)")
print(f"{'x':>6} {'prime trace':>14} {'zero atoms':>14} {'diff':>10}")
for x in [10,20,30,47,50,73,100,150]:
    a=psi_prime(x); b=psi_zeros(x)
    print(f"{x:>6} {a:14.4f} {b:14.4f} {a-b:10.4f}")
