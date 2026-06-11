"""
helix_from_line.py -- build the helix Sam's way:
   make a line -> put the integers on it SOME SPACE APART -> create fibres -> dither into winding & pitch.

The integers are EVENLY spaced (the log was the analytic bridge, not the geometry -- Rule Eight).
The winding advances the angle by a fixed step per integer (start: pi/3); the pitch grows the radius.
We watch the chi3 fibres cancel turn-by-turn (the geometric sum_chi3 = 0), what the sqrt-radius leaves,
and how the cancellation degrades when we dither the winding step off pi/3.
"""
import numpy as np

STEP = np.pi / 6           # integer distance pi/6 (12 integers per turn)
M = 6000
n = np.arange(1, M + 1)
res = n % 3
sign = np.where(res == 1, 1.0, np.where(res == 2, -1.0, 0.0))   # +fibre, -fibre, silent

print(f"(1-2) integers 1..{M} EVENLY spaced; winding step = pi/3 = {STEP:.5f} rad/integer")
print(f"      full turn = 2pi/step = {2*np.pi/STEP:.3f} integers")
print(f"      fibres:  + (1 mod 3) = {n[res==1][:6].tolist()}...   - (2 mod 3) = {n[res==2][:6].tolist()}...")

# angle of integer n at winding step s:
def theta(s):
    return s * n

# ---------- (3) DITHER THE WINDING: per-turn fibre cancellation vs the step ----------
print("\n(3) DITHER WINDING -- one-turn fibre sum  |sum_{one turn} sign * e^{i theta}|  (radius 1):")
for lbl, s in [("pi/3 -10%", STEP*0.90), ("pi/3 -2%", STEP*0.98), ("pi/3", STEP),
               ("pi/3 +2%", STEP*1.02), ("pi/3 +10%", STEP*1.10)]:
    K = int(round(2 * np.pi / s))                       # integers per turn
    th = theta(s)
    one_turn = abs(np.sum(sign[:K] * np.exp(1j * th[:K])))
    print(f"      step {lbl:9s} (turn = {K} integers):  |turn sum| = {one_turn:.5f}")

# exact at pi/3:  6 integers/turn, +,-,0,+,-,0 at 60,120,180,240,300,360 deg -> they cancel
th3 = theta(STEP)
print("\n     at pi/3, the 6 phasors of one turn (sign, angle deg, e^{i theta}):")
for k in range(6):
    print(f"        n={n[k]} sign={sign[k]:+.0f}  angle={np.degrees(th3[k])%360:6.1f}deg  "
          f"phasor={np.exp(1j*th3[k]):+.3f}")
print(f"        turn sum = {np.sum(sign[:6]*np.exp(1j*th3[:6])):.3e}   (exact geometric cancellation)")

# ---------- (4) DITHER THE PITCH: radius n^p; the sqrt residual the turn leaves ----------
print("\n(4) DITHER PITCH -- radius n^p; per-turn residual that the radial growth leaves (mid-helix turn):")
turn0 = 500                                              # integers 3000..3005
idx = slice(turn0 * 6, turn0 * 6 + 6)
for p in (0.0, 0.25, 0.5, 0.75, 1.0):
    r = n[idx].astype(float) ** p
    resid = abs(np.sum(sign[idx] * r * np.exp(1j * th3[idx])))
    print(f"      pitch p={p:.2f} (radius n^{p}):  |turn residual near n=3000| = {resid:.5f}")

# cumulative winding sum with the sqrt-packing weight 1/radius = n^{-1/2}
S = np.abs(np.cumsum(sign * n.astype(float) ** (-0.5) * np.exp(1j * th3)))
print(f"\n  cumulative |sum_{{n<=M}} chi3 * n^(-1/2) * e^(i (pi/3) n)|:  M=600 -> {S[599]:.4f}   M={M} -> {S[-1]:.4f}")
print("  (this is the LINEAR-winding geometric object; the log-winding bridge is what maps it to L.)")
