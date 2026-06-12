"""
pitch_battery.py -- discriminate: is the PITCH axis a passive projection-loss dimension,
or an active second winding?  Four experiments on the spiral-helix construction.

Geometry (established): integers on a spiral helix, linear radial growth R = n (the spiral),
azimuthal spacing pi/3 (6 integers per loop), pitch = axial rise per loop.  Each phasor is
dragged: spin = gamma*log R (= gamma*log n up to const), amplitude 1/sqrt(R) = n^{-1/2}.
The xy-shadow of the 3D resultant -> 0 at a chi3 zero (that IS the zero); the kept z-component
is the projection loss down the pitch axis.

L(1/2,chi3) ~ 0.480868 ; claimed identity z = (pitch/2pi)*L(1/2,chi3).

Run:  python3 pitch_battery.py
"""
import numpy as np

# ---- load zeros ----
gammas = []
with open("lchi3_zeros_1000.txt") as f:
    for line in f:
        line = line.strip()
        if line and not line.startswith("#"):
            gammas.append(float(line.split()[1]))
gammas.sort()
gammas = np.array(gammas)

def build(N):
    n = np.arange(1, N + 1)
    sign = np.where(n % 3 == 1, 1.0, np.where(n % 3 == 2, -1.0, 0.0))
    R = n.astype(float)                 # linear spiral
    w = 1.0 / np.sqrt(R)                # amplitude n^{-1/2}
    Phi = np.log(R)                     # drag winding = log R
    azim = (np.pi / 3) * n              # azimuth of integer n
    return n, sign, R, w, Phi, azim

# reference L(1/2,chi3)
try:
    import mpmath as mp
    mp.mp.dps = 30
    Lhalf = float(mp.power(3, mp.mpf('-0.5')) *
                  (mp.zeta(mp.mpf('0.5'), mp.mpf(1)/3) - mp.zeta(mp.mpf('0.5'), mp.mpf(2)/3)))
except Exception:
    Lhalf = 0.4808683  # fallback literal

print("="*78)
print("L(1/2, chi3) =", Lhalf)
print("="*78)

# ============================================================================
# EXPERIMENT 1 -- PITCH SWEEP
#   vary pitch in {0, pi/6, pi/3, 2pi/3, pi}; slope = pitch/2pi.
#   Does the pitch MOVE the gamma where |xy|->0 (=> genuine 2-torus winding),
#   or only rescale the kept z by slope (=> pitch = passive lost axis)?
# ============================================================================
print("\nEXPERIMENT 1 -- PITCH SWEEP  (N=200000)")
N = 200000
n, sign, R, w, Phi, azim = build(N)
print(f"{'pitch':>10} {'slope':>9} | {'|xy| @ g1':>11} {'|xy| @ g2':>11} {'|xy| @ g3':>11} | {'z (kept)':>11} {'z/slope':>11}")
print("-"*84)
g1, g2, g3 = gammas[0], gammas[1], gammas[2]
base_xy = {}
for pitch in [0.0, np.pi/6, np.pi/3, 2*np.pi/3, np.pi]:
    slope = pitch/(2*np.pi)
    row = []
    for g in (g1, g2, g3):
        Sx = np.sum(sign*w*np.cos(g*Phi)); Sy = np.sum(sign*w*np.sin(g*Phi))
        row.append(np.hypot(Sx, Sy))
    # z = slope * sum(sign*w)  (the un-wound central value carried up the pitch axis)
    z = slope * np.sum(sign*w)
    zps = (z/slope) if slope != 0 else float('nan')
    print(f"{pitch:10.5f} {slope:9.5f} | {row[0]:11.6f} {row[1]:11.6f} {row[2]:11.6f} | {z:11.6f} {zps:11.6f}")
print("VERDICT-1: if |xy| columns are IDENTICAL across pitch rows -> pitch does NOT move the")
print("           zeros (passive). z/slope should be ~constant = un-wound central sum.")

# ============================================================================
# EXPERIMENT 2 -- Z-IDENTITY ACROSS ALL ZEROS
#   verify z = (pitch/2pi)*L(1/2,chi3) is gamma-independent across ALL zeros,
#   at large N.  z here does NOT depend on gamma at all (it is slope*sum(sign*w));
#   the real test is: does slope*sum(sign*w) -> slope*L(1/2,chi3) as N->inf?
#   AND is the *3D* resultant z-component the same at every actual zero?
# ============================================================================
print("\nEXPERIMENT 2 -- Z-IDENTITY ACROSS ALL ZEROS")
for N in (400000, 1000000):
    n, sign, R, w, Phi, azim = build(N)
    pitch = np.pi/3; slope = pitch/(2*np.pi)
    central = np.sum(sign*w)                 # partial sum of L(1/2,chi3) = sum chi3(n) n^{-1/2}
    z_pred = slope*Lhalf
    z_meas = slope*central
    # per-zero 3D z-component (it is gamma-independent by construction: slope*sum(sign*w))
    devs = []
    for g in gammas:
        zc = slope*np.sum(sign*w)            # same for every g
        devs.append(abs(zc - z_pred))
    print(f"  N={N:8d}: sum chi3 n^-1/2 = {central:.8f}  L(1/2)={Lhalf:.8f}  "
          f"diff={abs(central-Lhalf):.2e}")
    print(f"            z_meas={z_meas:.8f}  z_pred(slope*L)={z_pred:.8f}  "
          f"max dev over all {len(gammas)} zeros={max(devs):.2e}")
print("VERDICT-2: z is gamma-independent BY CONSTRUCTION (slope*central). The content is whether")
print("           central -> L(1/2,chi3); convergence is ~1/sqrt(N) (conditionally convergent).")

# ============================================================================
# EXPERIMENT 3 -- SECOND-WINDING TEST
#   give each phasor an AXIAL rotation tied to its height: e^{-i*delta*height_n},
#   height_n = (pitch/2pi)*azim_n = slope*(pi/3)*n.  Multiply onto e^{-i*gamma*Phi}.
#   Does cancellation at the zeros need a SPECIAL delta, or is delta free?
#   special delta => active second winding; only delta=0 cancels => passive axis.
# ============================================================================
print("\nEXPERIMENT 3 -- SECOND-WINDING TEST  (N=200000, pitch=pi/3)")
N = 200000
n, sign, R, w, Phi, azim = build(N)
pitch = np.pi/3; slope = pitch/(2*np.pi)
height = slope*azim                          # axial height of integer n
print(f"{'delta':>10} | mean |xy-defect| over first 6 zeros (small = still cancels)")
print("-"*60)
for delta in [0.0, 1e-4, 1e-3, 1e-2, 0.1, 0.5, 1.0, slope, 1.0/6.0, 2*np.pi]:
    defs = []
    for g in gammas[:6]:
        ph = np.exp(-1j*g*Phi) * np.exp(-1j*delta*height)
        defs.append(abs(np.sum(sign*w*ph)))
    print(f"{delta:10.5f} | {np.mean(defs):.6f}")
print("VERDICT-3: if ONLY delta=0 cancels (defect rises monotonically with |delta|) -> the axial")
print("           rotation is NOT a free second winding; the pitch axis carries no independent phase")
print("           the cancellation needs -> PASSIVE. If some delta!=0 *also* drives |xy|->0 -> ACTIVE.")

# fine scan near 0 to see if there's a second cancellation valley away from delta=0
print("  fine delta scan (looking for a second valley):")
ds = np.linspace(0, 2.0, 41)
vals = []
for delta in ds:
    defs = [abs(np.sum(sign*w*np.exp(-1j*g*Phi)*np.exp(-1j*delta*height))) for g in gammas[:6]]
    vals.append(np.mean(defs))
vals = np.array(vals)
# report minima
order = np.argsort(vals)[:5]
print("   five smallest-defect deltas:", [f"d={ds[i]:.3f}:{vals[i]:.4f}" for i in sorted(order)])

# ============================================================================
# EXPERIMENT 4 -- OFFSET / SPACING
#   (a) does the azimuthal spacing value affect the xy cancellation at all?
#   (b) is there a winding/count offset -- does the natural origin sit before g1?
# ============================================================================
print("\nEXPERIMENT 4 -- OFFSET / SPACING  (N=200000)")
N = 200000
n, sign, R, w, Phi, azim = build(N)
print(" (a) vary azimuthal spacing; measure |xy| at g1 (spacing should be IRRELEVANT to xy,")
print("     since xy depends only on the drag winding gamma*log R, not on azimuth):")
g = gammas[0]
for sp in [np.pi/6, np.pi/3, np.pi/2, np.pi, 2*np.pi/7]:
    # azimuth changes but the dragged-phasor sum uses Phi=log R, independent of azimuth
    Sx = np.sum(sign*w*np.cos(g*Phi)); Sy = np.sum(sign*w*np.sin(g*Phi))
    print(f"     spacing={sp:.5f}: |xy @ g1| = {np.hypot(Sx,Sy):.6f}  (azimuth-independent)")
print(" (b) winding-count offset: place phasor at gamma*(log R + c) -> multiplies sum by e^{-i*gamma*c}")
print("     (a global phase; |xy| unchanged). Test a few offsets c:")
for c in [0.0, 1.0, 6-np.log(6), 10.0]:
    Sx = np.sum(sign*w*np.cos(g*(np.log(R)+c))); Sy = np.sum(sign*w*np.sin(g*(np.log(R)+c)))
    print(f"     offset c={c:8.4f}: |xy @ g1| = {np.hypot(Sx,Sy):.6f}")
print(" (c) is the construction's natural winding origin BEFORE the first zero? Report the")
print("     phase accumulated to the first integer vs the first zero gamma:")
print(f"     first integer drag log R_1 = {np.log(R[0]):.5f}; first zero gamma_1 = {gammas[0]:.5f}")
print("VERDICT-4: spacing & offset are pure gauge for the xy-cancellation (global phase only).")
print("="*78)
