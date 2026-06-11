"""
chi4_convergence.py -- confirm the two chi4 results SHARPEN as M grows like M^{-1/2}:
  (1) cancellation defect at each zero  -> 0
  (2) z_meas = (1/6)*partial            -> (1/6)*L(1/2,chi4)
and that the OFF-zero defect stays O(1) (so cancellation is real, not a small-M wash).
"""
import numpy as np
import mpmath as mp
mp.mp.dps = 30

gammas = []
with open("chi4_zeros.txt") as f:
    for line in f:
        line = line.strip()
        if line and not line.startswith("#"):
            gammas.append(float(line.split()[1]))
gammas.sort(); G = gammas[:6]

def Lchi4(s):
    s = mp.mpc(s)
    return mp.power(4, -s) * (mp.zeta(s, mp.mpf(1)/4) - mp.zeta(s, mp.mpf(3)/4))
Lhalf = float(Lchi4(mp.mpf(1)/2).real)
slope = (np.pi/3)/(2*np.pi)  # 1/6

print(f"L(1/2,chi4) = {Lhalf:.10f}   slope=1/6   z_pred = {slope*Lhalf:.10f}\n")
print(f"{'M':>9} | {'M^-1/2':>9} | {'mean |defect| @ 6 zeros':>23} | {'min off-zero defect':>19} | {'|z_meas - z_pred|':>17}")
print("-"*95)
for M in (100000, 400000, 1000000, 4000000):
    n = np.arange(1, M+1)
    r = n % 4
    sign = np.zeros(M); sign[r==1]=1.0; sign[r==3]=-1.0
    logn = np.log(n); amp = n.astype(float)**(-0.5)
    def collapse(g): return abs(np.sum(sign*amp*np.exp(-1j*g*logn)))
    at = np.mean([collapse(g) for g in G])
    offs = [collapse(0.5*(G[i]+G[i+1])) for i in range(len(G)-1)]
    central = np.sum(sign*amp)
    zd = abs(slope*central - slope*Lhalf)
    print(f"{M:>9} | {M**-0.5:9.2e} | {at:23.6e} | {min(offs):19.4f} | {zd:17.3e}")
print("\nExpect: defect-at-zeros ~ M^-1/2 -> 0 ; off-zero stays O(1) ; |z_meas-z_pred| ~ M^-1/2 -> 0.")
print("If so, chi4 obeys the SAME construction as chi3 -> character-agnostic.")
