"""
pressure_chi3.py -- WHAT presses the nodes down: the Laguerre form as CURVATURE/PRESSURE.

(1) EXACT ALGEBRA:   L(t) = Xi'(t)^2 - Xi(t)Xi''(t) = -Xi(t)^2 * (log|Xi|)''(t).
    Laguerre >= 0  <=>  log|Xi| CONCAVE between nodes. "Pressing down" = downward curvature.

(2) ZERO SIDE (Hadamard, genus 0: Xi(t) = Xi(0) prod (1 - t^2/g_n^2)):
    -(log|Xi|)''(t) = sum_n 2(g_n^2+t^2)/(g_n^2-t^2)^2.   EVERY term > 0 for ALL t:
    a real zero can ONLY press down, everywhere.  An off-line pair is the only object whose
    term goes negative (pushes up) -- the lifted node.

(3) PRIME SIDE (Euler product):  for sigma > 1 EXACTLY (absolute convergence):
    -(d^2/dt^2) log|Lambda(sigma+it)| = A_sigma(t) + sum_n Lambda(n) chi3(n) log(n) n^{-sigma} cos(t log n),
    A_sigma(t) = Re psi'((sigma+it+1)/2)/4.   The prime cosine field IS the curvature.
    Pushing sigma -> 1/2 (where the pressure would hold the nodes down) is exactly the
    continuation/EF weld -- tracked numerically below, not overclaimed.
"""
import numpy as np
import mpmath as mp

mp.mp.dps = 30
q = 3

def Lfun(s): return 3**(-s)*(mp.zeta(s, mp.mpf(1)/3) - mp.zeta(s, mp.mpf(2)/3))
def Lam_c(s):  # completed Lambda(s), entire, zeros = nontrivial zeros only
    return (mp.mpf(3)/mp.pi)**((s+1)/2) * mp.gamma((s+1)/2) * Lfun(s)
def Xi(t): return mp.re(Lam_c(mp.mpf(1)/2 + 1j*t))

# ---------- zeros: verified consecutive file zeros (1..20) + scan up to 200 ----------
fileG = []
with open("lchi3_zeros_1000.txt") as f:
    for ln in f:
        ln = ln.strip()
        if ln and not ln.startswith("#"):
            p = ln.split()
            if int(p[0]) <= 20: fileG.append(float(p[1]))
def scan_zeros(lo, hi):
    f = lambda s: Lfun(mp.mpf(1)/2 + 1j*s)
    ts = np.arange(lo, hi, 0.05)
    mag = np.array([float(abs(f(mp.mpf(t)))) for t in ts]); zs = []
    for i in range(1, len(ts)-1):
        if mag[i] < mag[i-1] and mag[i] < mag[i+1] and mag[i] < 0.6:
            try:
                r = mp.findroot(f, mp.mpc(ts[i], 0)); tm = float(mp.re(r))
                if abs(float(mp.im(r))) < 1e-6 and abs(complex(f(mp.mpf(tm)))) < 1e-9 \
                   and tm > lo and all(abs(tm-z) > 1e-3 for z in zs): zs.append(tm)
            except Exception: pass
    return zs
G = sorted(set(round(z, 8) for z in fileG + scan_zeros(54.0, 200.0)))
G = np.array([z for z in G])
print(f"zeros: {len(fileG)} verified (file, consecutive idx 1-20) + scan to 200 -> {len(G)} total.\n")

# ---------- (1) Laguerre = curvature: exact ----------
print("(1) Laguerre = curvature:  L(t) vs -Xi(t)^2*(log|Xi|)''(t)")
for t0 in ['5.0', '9.6', '13.3']:
    t = mp.mpf(t0)
    L = mp.diff(Xi, t)**2 - Xi(t)*mp.diff(Xi, t, 2)
    C = -Xi(t)**2 * mp.diff(lambda u: mp.log(abs(Xi(u))), t, 2)
    print(f"    t={t0}:  L = {mp.nstr(L,8):>14}   -Xi^2(log|Xi|)'' = {mp.nstr(C,8):>14}   rel.diff {float(abs(L-C)/abs(L)):.1e}")

# ---------- (2) zero side: every real zero presses down ----------
def D_zero(t):
    tt = float(t)
    s = float(np.sum(2*(G**2 + tt**2)/(G**2 - tt**2)**2))
    # numeric tail with RvM density beyond the last zero
    Tc = float(G[-1]) + 1.0
    gs = np.arange(Tc, 5000.0, 1.0)
    dens = np.log(q*gs/(2*np.pi))/np.pi
    s += float(np.sum(2*(gs**2 + tt**2)/(gs**2 - tt**2)**2 * dens))
    return s
print("\n(2) zero side: -(log|Xi|)'' (direct) vs Hadamard pressure sum over the zeros (+RvM tail)")
for t0 in ['5.0', '9.6', '13.3']:
    t = mp.mpf(t0)
    direct = float(-mp.diff(lambda u: mp.log(abs(Xi(u))), t, 2))
    dz = D_zero(t)
    print(f"    t={t0}:  direct = {direct:9.5f}   zero-pressure sum = {dz:9.5f}   rel.diff {abs(direct-dz)/abs(direct):.1e}")
print("    per-term sign: 2(g^2+t^2)/(g^2-t^2)^2 > 0 ALWAYS -- a real zero can only PRESS DOWN, everywhere.")
g0, dl = 9.6444716817, 0.5
fpair = lambda t: (t**2 - g0**2 + dl**2)**2 + 4*g0**2*dl**2
conv = float(-mp.diff(lambda u: mp.log(fpair(u)), mp.mpf(g0), 2))
print(f"    off-line pair (delta={dl}) at its ghost t={g0:.2f}: -(log f_pair)'' = {conv:+.4f} < 0 -- pushes UP.")
print("    => the ONLY object that creates convexity (a lifted node, L<0) is an off-line pair.")

# ---------- (3) prime side: exact for sigma>1; tracked toward the line ----------
N = 300000
spf = np.zeros(N+1, dtype=np.int64)
for i in range(2, N+1):
    if spf[i] == 0: spf[i::i] = np.where(spf[i::i] == 0, i, spf[i::i])
Lam = np.zeros(N+1)
for m in range(2, N+1):
    p = spf[m]; mm = m
    while mm % p == 0: mm //= p
    if mm == 1: Lam[m] = np.log(p)
nn = np.arange(1, N+1)
chi = np.where(nn % 3 == 1, 1.0, np.where(nn % 3 == 2, -1.0, 0.0))
logn = np.log(nn)
base_amp = Lam[1:]*chi*logn

def prime_pressure(sig, t):
    return float(np.sum(base_amp*nn**(-float(sig))*np.cos(float(t)*logn)))
def A_arch(sig, t):                                     # Re psi'((s+1)/2)/4, psi' = zeta(2,.)
    return float(mp.re(mp.zeta(2, (mp.mpf(str(sig)) + 1j*t + 1)/2))/4)
def direct_curv(sig, t):                                # -(d^2/dt^2) log|Lambda(sigma+it)|
    return float(-mp.diff(lambda u: mp.log(abs(Lam_c(mp.mpf(str(sig)) + 1j*u))), mp.mpf(str(t)), 2))

print("\n(3) prime side  -(log|Lambda|)''_tt = arch + SUM Lambda(n)chi(n)log(n) n^-sigma cos(t log n)")
print("    EXACT at sigma=1.2 (absolute convergence):")
for t0 in [5.0, 9.6, 13.3]:
    lhs = direct_curv(1.2, t0)
    rhs = A_arch(1.2, t0) + prime_pressure(1.2, t0)
    print(f"      t={t0:5.1f}:  direct = {lhs:+9.6f}   arch+primes = {rhs:+9.6f}   rel.diff {abs(lhs-rhs)/max(abs(lhs),1e-12):.1e}")
print("    tracked toward the line (truncated N=3e5; conditional -- the continuation weld):")
for sig in [0.8, 0.65]:
    row = []
    for t0 in [5.0, 9.6, 13.3]:
        lhs = direct_curv(sig, t0)
        rhs = A_arch(sig, t0) + prime_pressure(sig, t0)
        row.append((t0, lhs, rhs))
    txt = "  ".join(f"t={a:4.1f}: {b:+8.4f} vs {c:+8.4f}" for a, b, c in row)
    print(f"      sigma={sig}:  {txt}")
print("""
=> the three readings of the SAME object:
   L(t) >= 0  <=>  log|Xi| concave  <=>  total pressure >= 0:
   zero side  -- every real zero presses down everywhere (term-positivity, exact);
   prime side -- the von-Mangoldt cosine field Lambda(n)chi(n)log(n)n^{-sigma}cos(t log n) + arch
                 IS the curvature, EXACT for sigma>1, tracking as sigma -> 1/2.
   "The Euler product presses the nodes down": the primes are the curvature of log|Xi|; an off-line
   zero is a point where the prime pressure would have to go negative (the lifted node).  Carrying
   the exact sigma>1 identity onto the line is the continuation/EF weld -- the open thing, stated
   plainly, the same weld the repo isolates everywhere else.""")
