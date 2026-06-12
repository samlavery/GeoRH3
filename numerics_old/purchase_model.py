"""
purchase_model.py -- THE BARE-BONES PURCHASE MODEL vs REALITY.

Model (kernel-complete, HelixProduction Part 20): ladder t_n = unique height where the
accumulation E crosses n*pi. E = the traversal phase theta_chi(t):
  zeta : E(t) = siegeltheta(t)            (mpmath)
  chi3 : E(t) = (t/2)*log(3/pi) + Im logGamma(3/4 + i t/2)   (odd char, conductor 3)
Calibrate the ray offset (the epsilon constant) on the FIRST zero, then PREDICT the rest.
Compare: predicted ladder vs actual zeros -- offsets, and the staircase count.
"""
import mpmath as mp
mp.mp.dps = 25

def theta_zeta(t): return mp.siegeltheta(t)
def theta_chi3(t): return (t/2)*mp.log(3/mp.pi) + mp.im(mp.loggamma(mp.mpf(3)/4 + 0.5j*t))

def ladder(theta, t1, n_count, offset):
    """solve theta(t) = (n + offset)*pi for n = 0..n_count-1 starting near t1"""
    ts, t_guess = [], t1
    for n in range(n_count):
        target = (n + offset)*mp.pi
        f = lambda t: theta(t) - target
        t_sol = mp.findroot(f, t_guess)
        ts.append(float(t_sol)); t_guess = float(t_sol) + 2.0
    return ts

print("="*72)
print("ZETA: model ladder (theta crossings) vs actual zeros")
zeros_z = [float(mp.im(mp.zetazero(n))) for n in range(1, 31)]
off_z = float(theta_zeta(zeros_z[0])/mp.pi)   # calibrate on zero #1
print(f"  calibrated offset from zero 1: theta(g1)/pi = {off_z:.6f}")
lad_z = ladder(theta_zeta, zeros_z[0], 30, off_z)
ds = [lad_z[n] - zeros_z[n] for n in range(30)]
for n in [0,1,2,3,4,9,19,29]:
    print(f"  n={n+1:3d}  model={lad_z[n]:10.4f}  actual={zeros_z[n]:10.4f}  offset={ds[n]:+8.4f}")
print(f"  mean|offset|={sum(abs(d) for d in ds)/len(ds):.4f}  max|offset|={max(abs(d) for d in ds):.4f}")
gaps = [zeros_z[n+1]-zeros_z[n] for n in range(29)]
print(f"  mean zero gap={sum(gaps)/len(gaps):.4f}  -> offsets are {sum(abs(d) for d in ds)/len(ds)/(sum(gaps)/len(gaps))*100:.1f}% of a gap")
# staircase: does count match exactly per window?
miss = sum(1 for n in range(29) if not (lad_z[n] < zeros_z[n+1] and zeros_z[n] < lad_z[n+1] if n+1 < 30 else True))
print(f"  interlacing violations (model rung outside neighbor zeros): {miss}/29")

print("="*72)
print("CHI3: model ladder vs actual zeros (verified file)")
zeros_3 = []
with open('/Users/samuellavery/proof/three/numerics/lchi3_zeros_1000.txt') as f:
    for ln in f:
        ln = ln.strip()
        if ln and not ln.startswith('#'):
            p = ln.split()
            if int(p[0]) <= 30: zeros_3.append(float(p[1]))
off_3 = float(theta_chi3(zeros_3[0])/mp.pi)
print(f"  calibrated offset from zero 1: theta3(g1)/pi = {off_3:.6f}")
lad_3 = ladder(theta_chi3, zeros_3[0], len(zeros_3), off_3)
d3 = [lad_3[n] - zeros_3[n] for n in range(len(zeros_3))]
for n in [0,1,2,3,4,9,19,len(zeros_3)-1]:
    print(f"  n={n+1:3d}  model={lad_3[n]:10.4f}  actual={zeros_3[n]:10.4f}  offset={d3[n]:+8.4f}")
print(f"  mean|offset|={sum(abs(d) for d in d3)/len(d3):.4f}  max|offset|={max(abs(d) for d in d3):.4f}")
g3 = [zeros_3[n+1]-zeros_3[n] for n in range(len(zeros_3)-1)]
print(f"  mean zero gap={sum(g3)/len(g3):.4f}  -> offsets are {sum(abs(d) for d in d3)/len(d3)/(sum(g3)/len(g3))*100:.1f}% of a gap")
print("="*72)
print("VERDICT: staircase count exact iff every |offset| < local gap; heights wander by S(t).")
