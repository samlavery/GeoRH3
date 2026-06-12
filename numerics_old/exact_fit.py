"""
exact_fit.py -- fit the winding-count to the chi3 zeros WITH the offset (count origin != first zero).
No conclusions; just the residual.  Model: n = N_smooth(gamma_n) + C, where N_smooth is the winding
phase of the completed L (the gamma/conductor factor), C the offset.  Residual = what is left unfit.
"""
import mpmath as mp
mp.mp.dps = 30
q = 3
gammas = []
with open("lchi3_zeros_1000.txt") as f:
    for line in f:
        line = line.strip()
        if line and not line.startswith("#"):
            gammas.append(mp.mpf(line.split()[1]))
gammas.sort()
consec = gammas[:20]                          # consecutive block

def Nsmooth(T):
    s = mp.mpf(1)/2 + 1j*T
    z = (s/2)*mp.log(q/mp.pi) + mp.loggamma((s+1)/2)   # odd-character winding phase
    return mp.im(z)/mp.pi

Ns = [Nsmooth(g) for g in consec]
offs = [mp.mpf(i+1) - Ns[i] for i in range(len(consec))]
C = sum(offs)/len(offs)
resid = [float((i+1) - Ns[i] - C) for i in range(len(consec))]
print(f"fitted offset C = {float(C):.5f}   (the count starts {float(C):.3f} before the first zero)")
print(" n |  gamma   | N_smooth |  n - N_smooth |  residual (unfit)")
for i, g in enumerate(consec):
    print(f"{i+1:2d} | {float(g):8.4f} | {float(Ns[i]):8.4f} | {float((i+1)-Ns[i]):11.5f} | {resid[i]:+.5f}")
rs = mp.matrix(resid)
import math
mean = sum(resid)/len(resid)
std = math.sqrt(sum((r-mean)**2 for r in resid)/len(resid))
print(f"\n  residual: max|.| = {max(abs(r) for r in resid):.4f}   rms = {std:.4f}   (0 = exact fit)")
