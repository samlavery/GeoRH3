"""
chi4_construction.py -- test the phasor-drag / projection-loss construction for chi4,
to confirm it is CHARACTER-AGNOSTIC (same as established for chi3).

Established for chi3 (do_it_right.py, phasor_drag.py, spiral_helix.py, pitch_battery.py):
  amplitude  = n^{-1/2}              (1/sqrt R, R~n linear spiral, sigma=1/2)
  drag spin  = log n  (= log R)      (winding earned from radial growth)
  phasor_n   = chi(n) * n^{-1/2} * e^{-i gamma log n}
  CANCELLATION:  |sum phasor_n| -> 0  at each L(chi) zero gamma   (~ M^{-1/2})
  Z-IDENTITY:    z = (pitch/2pi) * L(1/2,chi),  pitch = pi/3  =>  slope = 1/6
                 z_meas = (1/6) * sum chi(n) n^{-1/2}  ->  (1/6) * L(1/2,chi)

We now run the SAME construction for chi4 (Dirichlet beta).
"""
import numpy as np
import mpmath as mp
mp.mp.dps = 30

# ---- chi4 zeros (from chi4_zeros.py) ----
gammas = []
with open("chi4_zeros.txt") as f:
    for line in f:
        line = line.strip()
        if line and not line.startswith("#"):
            gammas.append(float(line.split()[1]))
gammas.sort()
gammas = gammas[:6]  # first six

# ---- L(1/2,chi4) exact (Hurwitz) ----
def Lchi4(s):
    s = mp.mpc(s)
    return mp.power(4, -s) * (mp.zeta(s, mp.mpf(1)/4) - mp.zeta(s, mp.mpf(3)/4))
Lhalf = float(Lchi4(mp.mpf(1)/2).real)

pitch = np.pi/3
slope = pitch/(2*np.pi)   # = 1/6

print("="*78)
print("chi4 = Dirichlet beta.   L(1/2,chi4) =", f"{Lhalf:.10f}")
print(f"pitch = pi/3,  slope = pitch/2pi = {slope:.10f}  (= 1/6 = {1/6:.10f})")
print(f"predicted z = (pitch/2pi)*L(1/2,chi4) = {slope*Lhalf:.10f}")
print("first six chi4 zeros:", [round(g,5) for g in gammas])
print("="*78)

# ---- build the integers / chi4 fibre ----
M = 400000
n = np.arange(1, M+1)
r = n % 4
sign = np.zeros(M)
sign[r == 1] = 1.0
sign[r == 3] = -1.0          # chi4(n): +1 (n=1 mod4), -1 (n=3 mod4), 0 (even)
logn = np.log(n)
amp = n.astype(float) ** (-0.5)   # n^{-1/2}, the wave amplitude (1/sqrt R, R~n)

# ---- TASK 2a: cancellation at each zero, and at a between-zeros control ----
print("\n[A] CANCELLATION  |sum chi4(n) n^{-1/2} e^{-i gamma log n}|   (M = %d)" % M)
print("    (should be small ~ M^{-1/2} = %.2e at each zero; LARGE off the zeros)" % (M**-0.5))
print("    " + "-"*64)
def collapse(g):
    return abs(np.sum(sign * amp * np.exp(-1j * g * logn)))
for g in gammas:
    print(f"    AT  gamma = {g:9.5f}:  defect = {collapse(g):.6f}")
print("    " + "-"*64)
for i in range(len(gammas)-1):
    mid = 0.5*(gammas[i]+gammas[i+1])
    print(f"    OFF (between g{i+1},g{i+2}) t={mid:9.5f}:  defect = {collapse(mid):.6f}")

# ---- TASK 2b: the z-identity ----
central = np.sum(sign * amp)          # = sum chi4(n) n^{-1/2} = partial sum of L(1/2,chi4)
z_meas  = slope * central
z_pred  = slope * Lhalf
print("\n[B] Z-IDENTITY   z = (pitch/2pi) * L(1/2,chi4)")
print("    " + "-"*64)
print(f"    sum chi4(n) n^-1/2  (M={M})  = {central:.8f}")
print(f"    L(1/2,chi4)  (exact, mpmath) = {Lhalf:.8f}")
print(f"    |partial - L|               = {abs(central-Lhalf):.3e}   (conv ~ M^-1/2 = {M**-0.5:.2e})")
print(f"    z_meas = (1/6)*partial       = {z_meas:.8f}")
print(f"    z_pred = (1/6)*L(1/2,chi4)    = {z_pred:.8f}")
print(f"    |z_meas - z_pred|            = {abs(z_meas-z_pred):.3e}")

# ---- convergence of the partial sum toward L(1/2) at several M ----
print("\n[C] convergence of sum chi4(n) n^-1/2 -> L(1/2,chi4) (Dirichlet-series, conditional):")
for MM in (50000, 100000, 200000, 400000):
    nn = np.arange(1, MM+1); rr = nn % 4
    sg = np.zeros(MM); sg[rr==1]=1.0; sg[rr==3]=-1.0
    part = np.sum(sg * nn.astype(float)**(-0.5))
    print(f"    M={MM:7d}: partial = {part:.8f}   |partial-L| = {abs(part-Lhalf):.3e}")

print("\n" + "="*78)
print("VERDICT: cancellation at chi4 zeros + z=(pitch/2pi)L(1/2,chi4) ?")
print("="*78)
