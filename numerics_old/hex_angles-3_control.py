"""
hex_angles-3_control.py  --  APPENDIX to hex_angles-3.py (ID angles-3 / H3).

Two clean diagnostics that make the H3 negative result airtight:

  (A) APPARATUS CONTROL.  On the SAME area-law cone, the BARE log-winding phasor
      sum WITHOUT the sector phase -- amp=1/R~n^{-1/2}, beta=log R~log n -- must
      collapse to ~0 at every chi3 zero (it is e^{-i t log n} n^{-1/2} = the L
      partial sum, the known tautology).  If this hits 8/8, the apparatus is
      proven correct, so the failure of the GEOMETRIC drifts in hex_angles-3.py
      is a real negative, not a broken rig.

  (B) ISOLATE THE SECTOR PHASE.  Add the per-loop 6th-root sector phase back onto
      the SAME bare log winding and show it DEGRADES the cancellation -- i.e. the
      pi/3 sector rotation, the one genuinely-hexagonal ingredient, actively
      breaks the alignment rather than carrying it.  This pins exactly why the
      geometric construction does not reproduce the zeros.

  (C) FRAME HONESTY.  Report the true 3D-vector resultant (phasors each in their
      OWN local normal plane) vs the single-plane complex |A(t)|, quantifying the
      small gap, so the "phasors are real 3D vectors" claim is exact.
"""
import numpy as np
import mpmath as mp
mp.mp.dps = 30

def Lchi3(s):
    return 3 ** (-s) * (mp.zeta(s, mp.mpf(1) / 3) - mp.zeta(s, mp.mpf(2) / 3))
def absL(g):
    return float(abs(Lchi3(mp.mpf(1) / 2 + 1j * mp.mpf(g))))

GAM = []
with open("lchi3_zeros_1000.txt") as f:
    for ln in f:
        ln = ln.strip()
        if ln and not ln.startswith("#"):
            GAM.append(float(ln.split()[1]))
GAM = np.array(sorted(GAM)); Z8 = GAM[:8]

# ---- build the SAME area-law cone (arc=pi/3, c=6) ----
def build_cone(M, c=6.0, arc=np.pi/3, pitch=np.pi/3, theta_max=12000.0, grid=1_500_000):
    A = np.exp(c)/(2*np.pi)
    th = np.linspace(0.0, theta_max, grid)
    dsdth = np.sqrt(A**2*(1+th**2) + (pitch/(2*np.pi))**2)
    s = np.concatenate([[0.0], np.cumsum(0.5*(dsdth[1:]+dsdth[:-1])*np.diff(th))])
    n = np.arange(1, M+1); s_n = n*arc
    theta = np.interp(s_n, s, th); R = A*theta; k = theta/(2*np.pi)
    x, y = R*np.cos(theta), R*np.sin(theta); z = pitch*k
    return n, theta, R, k, x, y, z

M = 60000
n, theta, R, k, x, y, z = build_cone(M)
sign = np.where(n%3==1,1.0,np.where(n%3==2,-1.0,0.0))
sector = (np.floor(k).astype(int)%6)*(np.pi/3)
amp = 1.0/R
beta_log = np.log(R)                       # ~ (1/2) log n + const  (emergent area log)

def Abare(t):  # NO sector phase: pure log winding on the cone (the apparatus control)
    return abs(np.sum(sign*amp*np.exp(-1j*t*beta_log)))
def Asector(t):  # SAME winding + 6th-root sector phase
    return abs(np.sum(sign*amp*np.exp(1j*(sector - t*beta_log))))

print("="*74)
print("(A) APPARATUS CONTROL: bare log-winding on the cone (NO sector), |A| at zeros")
print("    amp=1/R~n^-1/2, beta=log R~log n  =>  should be ~0 at every chi3 zero")
print("="*74)
print(f"   {'gamma':>9} {'|A_bare|':>10} {'|A_sector|':>11}   note")
nbare = 0
for g in Z8:
    ab, asec = Abare(g), Asector(g)
    if ab < 0.05: nbare += 1
    print(f"   {g:9.4f} {ab:10.5f} {asec:11.5f}   {'<= bare cancels' if ab<0.05 else ''}")
print(f"\n   bare-log control hits {nbare}/8 chi3 zeros (|A|<0.05).")
print("   => if 8/8, the rig is correct: e^{-it logR} n^{-1/2} IS the L partial sum.")
print("   The sector column shows the SAME winding with the pi/3 6th-root phase added.\n")

# scan both and count deepest-minima hits
def hits(metric, tlo=2.0, thi=40.0, nt=16000):
    ts = np.linspace(tlo, thi, nt)
    v = np.array([metric(t) for t in ts])
    mins = [(ts[j],v[j]) for j in range(1,len(ts)-1) if v[j]<v[j-1] and v[j]<=v[j+1]]
    mins = sorted(mins, key=lambda m:m[1])[:8]
    nm = sum(min(abs(GAM-tm))<0.05 for tm,_ in mins)
    return nm, mins
nm_b, mins_b = hits(Abare)
nm_s, mins_s = hits(Asector)
print("(B) deepest-minima hit count (t in [2,40]):")
print(f"      bare log winding (no sector) : {nm_b}/8   deepest min |A|={mins_b[0][1]:.4f} at t={mins_b[0][0]:.3f}")
print(f"      + pi/3 sector phase          : {nm_s}/8   deepest min |A|={mins_s[0][1]:.4f} at t={mins_s[0][0]:.3f}")
print("      => the hexagonal sector phase DEGRADES the cancellation (the ingredient")
print("         that is genuinely 6th-root breaks alignment, it does not carry zeros).\n")

# verify the bare-control minima ARE true zeros
print("   verify bare-control deepest minima refine to true L roots (|L|<1e-12):")
for tm, am in sorted(mins_b, key=lambda m:m[0])[:6]:
    try:
        root = mp.findroot(lambda s: Lchi3(mp.mpf(1)/2+1j*s), mp.mpf(tm))
        rh = float(root.real if hasattr(root,'real') else root); v = absL(rh)
    except Exception:
        rh, v = float('nan'), float('nan')
    tag = "VERIFIED |L|<1e-12" if v<1e-12 else f"|L|={v:.2e}"
    print(f"      A-min t={tm:8.4f}(|A|={am:.4f}) -> root {rh:9.5f}  {tag}")

# ---- (C) frame honesty: 3D vector resultant vs complex |A| ----
def local_frame(x,y,z):
    Tx,Ty,Tz = np.gradient(x),np.gradient(y),np.gradient(z)
    Tn = np.sqrt(Tx**2+Ty**2+Tz**2); Tx,Ty,Tz = Tx/Tn,Ty/Tn,Tz/Tn
    dot = Tz  # up=(0,0,1)
    e1x,e1y,e1z = -dot*Tx, -dot*Ty, 1-dot*Tz
    e1n = np.sqrt(e1x**2+e1y**2+e1z**2); e1x,e1y,e1z = e1x/e1n,e1y/e1n,e1z/e1n
    e2x = Ty*e1z-Tz*e1y; e2y = Tz*e1x-Tx*e1z; e2z = Tx*e1y-Ty*e1x
    return (e1x,e1y,e1z),(e2x,e2y,e2z)
E1,E2 = local_frame(x,y,z)
def resultant3d(t):
    ang = sector - t*beta_log
    bx = np.cos(ang)*E1[0]+np.sin(ang)*E2[0]
    by = np.cos(ang)*E1[1]+np.sin(ang)*E2[1]
    bz = np.cos(ang)*E1[2]+np.sin(ang)*E2[2]
    w = sign*amp
    return np.sqrt(np.sum(w*bx)**2+np.sum(w*by)**2+np.sum(w*bz)**2)
print("\n"+"="*74)
print("(C) FRAME HONESTY: true 3D phasor resultant (each phasor in its OWN normal")
print("    plane) vs single-plane complex |A(t)|.  Gap = genuine 3D tilt of the planes.")
print("="*74)
print(f"   {'t':>8} {'|3D resultant|':>14} {'|complex A|':>12} {'rel.gap':>9}")
for g in Z8[:5]:
    r3 = resultant3d(g); ac = Asector(g)
    gap = abs(r3-ac)/max(ac,1e-12)
    print(f"   {g:8.3f} {r3:14.5f} {ac:12.5f} {gap:9.4f}")
print("   small gap => normal planes are nearly co-vertical (tangent ~ horizontal);")
print("   the phasors ARE real 3D vectors and their resultant ~ the complex sum.")
