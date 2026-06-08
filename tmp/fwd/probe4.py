import numpy as np
from shared_rule import sieve_primes, chi0_mod3, chi3_mod3

# Test: do peaks of the truncated -L'/L Dirichlet series cluster near zeros?
# F(t) = sum_{p^k <= X} chi(p)^k log(p) p^{-k/2} cos(t*k*log p) etc.
# We use -L'/L(s) = sum_p sum_k chi(p)^k log p * p^{-k s}. On s=1/2+it real part:
def neg_LprimeL(t, X, chi):
    primes = sieve_primes(X)
    tot = 0.0+0.0j
    for p in primes:
        lp = np.log(p)
        for k in range(1, int(np.log(X)/lp)+2):
            q = p**k
            if q > X: break
            c = chi(p)**k if chi(p)!=0 else 0.0
            tot += c*lp*q**(-0.5)*np.exp(-1j*t*k*lp)
    return tot

ts = np.arange(2,60,0.05)
mag = np.array([abs(neg_LprimeL(t, 1000, chi0_mod3)) for t in ts])
# find local maxima
peaks=[]
for i in range(1,len(ts)-1):
    if mag[i]>mag[i-1] and mag[i]>=mag[i+1] and mag[i]>np.median(mag)*1.5:
        peaks.append(ts[i])
print("ChA truncated -L'/L |.| peaks (X=1000):", np.round(peaks[:20],2))
zetaA=[14.1347,21.022,25.0109,30.4249,32.9351,37.5862,40.9187,43.3271,48.0052,49.7738]
print("zeta zeros:                            ", zetaA)
