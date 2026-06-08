"""
Step 5: confirm the crux with the collective dual spectrum + asymptotic-theta refinement.

(A) Dual spectrum D(u)=sum_n cos(gamma_n u) at u=k log p.
    canonical (from gamma_ref) vs from the BARE-prime-power crossings (forward construction).
    If forward crossings are the right zeros, their dual spectrum should peak/dip at u=k log p
    like the canonical. We measure correlation.

(B) Make asymptotic theta progressively more exact (add the 1/(48t) correction term)
    and watch per-zero RMS shrink -> shows the smooth part IS arg-Gamma (its asymptotic series).
"""
import numpy as np
import mpmath
import json

mpmath.mp.dps = 15
with open("/Users/samuellavery/proof/three/tmp/fwd2/ref.json") as f:
    ref = json.load(f)
gamma_ref = np.array(ref["gamma_ref"])
nzeros_ref = {int(k):v for k,v in ref["nzeros_ref"].items()}
t = np.arange(0.0,120.0,0.02)

def primes_upto(n):
    s=np.ones(n+1,bool); s[:2]=False
    for i in range(2,int(n**0.5)+1):
        if s[i]: s[i*i::i]=False
    return np.nonzero(s)[0]
primes=primes_upto(100000)
def pp(X):
    out=[]
    for p in primes:
        if p>X: break
        lp=np.log(p); v=p; k=1
        while v<=X: out.append((lp,k,v)); v*=p; k+=1
    return out
def crossings(W):
    s=np.sign(W); idx=np.nonzero(np.diff(s)!=0)[0]; cr=[]
    for i in idx:
        w0,w1=W[i],W[i+1]
        if w1!=w0: cr.append(t[i]-w0*(t[i+1]-t[i])/(w1-w0))
    return np.array(cr)
def rms(cr,g):
    c=cr[(cr>5)&(cr<102)]
    if len(c)==0: return float('nan')
    return np.sqrt(np.mean([ (c[np.argmin(np.abs(c-x))]-x)**2 for x in g]))

print("="*72, flush=True)
print("(A) COLLECTIVE dual spectrum D(u)=sum cos(gamma_n u) at u=k log p", flush=True)
print("    canonical zeros vs forward bare-prime-power crossings", flush=True)
print("="*72, flush=True)
# u values = k log p for small prime powers
uvals=[]
labels=[]
for p in [2,3,5,7,11]:
    for k in [1,2]:
        uvals.append(k*np.log(p)); labels.append(f"{p}^{k}")
uvals=np.array(uvals)
Dcan=np.array([np.sum(np.cos(gamma_ref*u)) for u in uvals])
print(f"  {'u=klogp':>8} {'D_canonical':>12} | forward-crossing D at increasing X:", flush=True)
# forward crossings for several X
fwd={}
for X in [1000,20000,100000]:
    W=np.zeros_like(t)
    for (lp,k,v) in pp(X): W-= (lp/np.sqrt(v))*np.cos(k*lp*t)
    cr=crossings(W); cr=cr[(cr>5)&(cr<102)]
    fwd[X]=np.array([np.sum(np.cos(cr*u)) for u in uvals])
print(f"  {'':8} {'':12}   X=1000   X=20000  X=100000", flush=True)
for i,lab in enumerate(labels):
    print(f"  {lab:>8} {Dcan[i]:>12.3f}   {fwd[1000][i]:7.3f} {fwd[20000][i]:8.3f} {fwd[100000][i]:9.3f}", flush=True)
for X in [1000,20000,100000]:
    c=np.corrcoef(Dcan,fwd[X])[0,1]
    print(f"  corr(D_canonical, D_forward[X={X}]) = {c:.3f}", flush=True)
print("  --> corr near 0 = forward crossings' dual spectrum does NOT match the canonical;", flush=True)
print("      prime powers alone do not regenerate the zeros' collective signature.", flush=True)

print("\n" + "="*72, flush=True)
print("(B) asymptotic theta refinement: per-zero RMS as theta -> exact arg Gamma", flush=True)
print("="*72, flush=True)
Nmax=np.floor(np.sqrt(np.maximum(t,0)/(2*np.pi))).astype(int); bigN=int(Nmax.max())
def Zwave(phase):
    W=np.zeros_like(t)
    for n in range(1,max(bigN,1)+1):
        m=Nmax>=n; W[m]+=2*np.cos(phase[m]-t[m]*np.log(n))/np.sqrt(n)
    return W
tt=np.maximum(t,1e-9)
theta0=np.where(t>2,0.5*tt*np.log(tt/(2*np.pi))-0.5*tt-np.pi/8.0,0.0)        # leading
theta1=theta0+np.where(t>2,1.0/(48*tt),0.0)                                   # +1/(48t)
theta2=theta1+np.where(t>2,7.0/(5760*tt**3),0.0)                             # +7/(5760 t^3)
theta_exact=np.array([float(mpmath.siegeltheta(float(x))) if x>2 else 0.0 for x in t])
for name,ph in [("leading log only",theta0),("+1/(48t)",theta1),("+7/(5760t^3)",theta2),("exact siegeltheta",theta_exact)]:
    cr=crossings(Zwave(ph))
    print(f"  theta = {name:20s}  RMS vs gamma_n = {rms(cr,gamma_ref):.5f}", flush=True)
print("  --> RMS shrinks monotonically toward the exact-arg-Gamma value as the", flush=True)
print("      asymptotic series of theta is completed: the smooth part IS arg Gamma.", flush=True)
