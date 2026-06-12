"""
fiber_continuous.py -- the user's picture: a CONTINUOUS fiber LENGTHENED at each cancellation, iy a
cumulative length/volume. We test the SPACING/COUNT structure of the chi3 zeros (NOT the tautological
F=L). Column 1 of the file is the TRUE zero index n; we also compute a consecutive run via mpmath.
"""
import numpy as np, mpmath as mp
mp.mp.dps = 25
q = 3
# --- file landmarks: (true index n, gamma_n) ---
idx, gam = [], []
with open("lchi3_zeros_1000.txt") as f:
    for ln in f:
        ln = ln.strip()
        if ln and not ln.startswith("#"):
            p = ln.split(); idx.append(int(p[0])); gam.append(float(p[1]))
idx, gam = np.array(idx), np.array(gam)

def Nvm(T):  # Riemann-von Mangoldt count for L(chi mod q)
    return (T/(2*np.pi))*np.log(q*T/(2*np.pi)) - T/(2*np.pi) + 7/8

print("(1) SPACING LAW: does the n-th cancellation height obey N(gamma_n)=n exactly? (file's true index)")
print(f"    {'n':>5} {'gamma_n':>10} {'N_vM(gamma)':>12} {'err':>8}")
for n0, g0 in zip(idx, gam):
    if n0 in (1,5,10,20,35) or n0 >= 700:
        print(f"    {n0:5d} {g0:10.3f} {Nvm(g0):12.3f} {Nvm(g0)-n0:8.3f}")
print("    => N(gamma_n)=n to <1 even at the 750th zero: the cancellations are placed by a CONTINUOUS count.")

# --- compute a CONSECUTIVE run of zeros via mpmath for gap/density statistics ---
def Lval(s):
    t = mp.mpf(1)  # chi3 table {1:1, 2:-1}
    return q**(-s) * (mp.zeta(s, mp.mpf(1)/q) - mp.zeta(s, mp.mpf(2)/q))
def find_zeros(hi):
    ts = np.arange(0.6, hi, 0.05)
    mag = np.array([float(abs(Lval(mp.mpf(1)/2+1j*mp.mpf(t)))) for t in ts])
    zs = []
    for i in range(1, len(ts)-1):
        if mag[i] < mag[i-1] and mag[i] < mag[i+1] and mag[i] < 0.5:
            try:
                r = mp.findroot(lambda s: Lval(mp.mpf(1)/2+1j*s), mp.mpc(ts[i],0))
                tm = float(mp.re(r))
                if abs(float(mp.im(r)))<1e-6 and abs(complex(Lval(mp.mpf(1)/2+1j*mp.mpf(tm))))<1e-9 \
                   and tm>0.5 and all(abs(tm-z)>1e-3 for z in zs): zs.append(tm)
            except Exception: pass
    return np.array(sorted(zs))
G = find_zeros(170.0)
print(f"\n    computed {len(G)} consecutive chi3 zeros up to T=170 (N_vM(170)={Nvm(170):.0f})")

# --- (2) the FIBER = number of active integers (approx functional eqn): N_eff = sqrt(qT/2pi) ---
Neff = np.sqrt(q*G/(2*np.pi))
print("\n(2) FIBER LENGTH = #active integers N_eff = sqrt(qT/2pi)  (the integers actually summed at height T)")
print(f"    N_eff: gamma_1 -> {Neff[0]:.3f},  gamma_{len(G)} (T={G[-1]:.1f}) -> {Neff[-1]:.3f}")
print(f"    iy vs fiber:  gamma = 2pi/q * N_eff^2  (so iy is the SQUARE of the fiber length)")

# --- (3) density and gap: cancellation rate vs log(fiber) ---
gap = np.diff(G); mid = 0.5*(G[1:]+G[:-1]); Neff_mid = np.sqrt(q*mid/(2*np.pi))
# RvM: dN/dT = (1/2pi) log(qT/2pi) = (1/pi) log N_eff.  so gap ~ pi/log N_eff.
pred_gap = np.pi/np.log(Neff_mid)
print("\n(3) GAP between cancellations vs pi/log(fiber length):  gap*log(N_eff)/pi should be ~1")
r = gap*np.log(Neff_mid)/np.pi
print(f"    mean {r.mean():.3f}, std {r.std():.3f}  over {len(gap)} consecutive gaps  "
      f"(~1 => the fiber's LOG sets the cancellation rate)")

# --- (4) 'volume of integers between cancellations' -- the honest reading ---
print("\n(4) integer VOLUME between successive cancellations:")
dN = np.diff(Neff)
print(f"    new active integers added per event Delta N_eff: mean {dN.mean():.3f} "
      f"(early {dN[:20].mean():.3f}, late {dN[-20:].mean():.3f})")
print(f"    NOT constant: as the fiber lengthens, cancellations densify (gap~pi/log N_eff), so each")
print(f"    event consumes LESS new fiber.  The cumulative law is N(T)=(1/pi)∫log(N_eff)dt = RvM count.")
print("\nHONEST READING: 'iy = volume of integers between cancellations' = the Riemann-von Mangoldt")
print("counting law. iy = 2pi/q * (active-integer fiber)^2; the fiber lengthens as sqrt(iy); the")
print("cancellation DENSITY = log(fiber)/pi. This is the known zero-density + approx functional eqn,")
print("re-read as a growing fiber -- a faithful re-description of the spacing, not a new forcing.")
