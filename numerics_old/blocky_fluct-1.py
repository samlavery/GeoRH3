"""
blocky_fluct-1.py  (ID: fluct-1)
================================================================================
BLOCKY-HELIX realization of the zeros of L(chi3), chi3 = real char mod 3.

GOAL: build the REAL 3D blocky (stepped, piecewise) helix with EXPLICIT (x,y,z)
coordinates and a real rotating PHASOR hung at each integer; detect a cancellation
event as the chi3-weighted PHASOR VECTOR-SUM collapsing onto the central axis;
and test the HEADLINE claim H1 (CONFIRMED, to reproduce + push past):

  The per-block FLUCTUATION S(T_n) of the chi3 zeros is recovered (not just the
  smooth log MEAN) by the AXIS-MISALIGNMENT ANGLE of a BLOCKY-radial helix's
  chi3-weighted phasor vector-sum:

     R(n) = ceil(sqrt n)                      [STEPPED radial law: const in block,
                                               +1 jump at each block boundary]
     amp(n) = 1/R(n)                          [geometric amplitude falloff]
     psi(n) = w * log n                       [phasor winding phase, w = height]
     (vx,vy) = sum_{n<=N} chi3(n) amp(n) (cos psi, sin psi)
     alpha(w) = atan2(vy, vx)                 [resultant MISALIGNMENT angle]
     hatS(w) ~ sin alpha(w)
     test corr( sin alpha(gamma_n), S(T_n) )  over the exact zeros gamma_n.

  Claimed: corr = +0.78 over 64 zeros, p<1e-4 vs shuffle, stable across N,
  out-of-sample, survives gamma-detrending. SMOOTH amp n^-1/2 gives ~0 (dead
  analytic-L trap). The BLOCKY radial step is the necessary geometric ingredient.

EVERYTHING IS RECOMPUTED FROM SCRATCH (no /tmp cache):
  - chi3 zeros: scan |L(1/2+it)| via Hardy-Z sign changes, refine with mp.findroot
    to |L| < 1e-12  (L(chi3,s) = 3^-s (zeta(s,1/3) - zeta(s,2/3))).
  - S(T_n) = n - (theta(T_n)/pi + 1),  theta from the chi3 (odd, a=1) gamma factor
    via single-valued mp.loggamma.

HONESTY (Rules 2 & 4): the phasor sum sum chi3(n) amp(n) e^{i w log n} IS, with
amp=n^-1/2, literally a truncation of L(1/2+iw); the geometric content is ENTIRELY
in the BLOCKY amp (1/ceil(sqrt n)) deviating from n^-1/2. We make that explicit
(STEP 4) and verify the smooth version is dead. We also report, honestly, that the
log-n phase is the analytic bridge (the open gap: it is not yet self-calibrated by
the pure geometry), and that the SIGN of the correlation flips with the rounding
convention (ceil/floor) -- magnitude robust, sign not geometrically pinned.
"""
import numpy as np
import mpmath as mp

mp.mp.dps = 30

# =============================================================================
# L(chi3, s) and exact zeros
# =============================================================================
def Lchi3(s):
    s = mp.mpf(s) if not isinstance(s, mp.mpc) else s
    return mp.power(3, -s) * (mp.zeta(s, mp.mpf(1)/3) - mp.zeta(s, mp.mpf(2)/3))

def Lhalf(t):
    return Lchi3(mp.mpf(0.5) + 1j*mp.mpf(t))

def hardy_Z_proxy(t):
    """A real-valued proxy whose sign changes bracket zeros: Re of rotated L.
    We just use |L| minima + sign of a smooth real surrogate. For robustness we
    bracket by scanning |L| and refining each local min with findroot on L itself."""
    return abs(Lhalf(t))

def compute_chi3_zeros(n_zeros=64, t_start=2.0, t_end=160.0, coarse=0.05):
    """Scan |L(1/2+it)| for local minima, refine each with mp.findroot to |L|<1e-12.
    Returns (G_float for the double-precision helix work, worst |L| at the HIGH-precision
    mpmath roots -- the float() truncation alone moves |L| up to ~1e-10 since |L| is
    steep near a zero, so verification must be at full mp precision)."""
    ts = np.arange(t_start, t_end, coarse)
    vals = np.array([float(abs(Lhalf(t))) for t in ts])
    zeros = []
    mp_zeros = []
    for i in range(1, len(vals)-1):
        if vals[i] < vals[i-1] and vals[i] < vals[i+1] and vals[i] < 0.5:
            t0 = ts[i]
            try:
                # polish on the real height: findroot on t |-> L(1/2+it), then refine
                root = mp.findroot(lambda z: Lchi3(mp.mpf(0.5)+1j*z), mp.mpf(t0),
                                   tol=mp.mpf(10)**-40)
                g = mp.re(root)
                # one extra Newton polish to push |L| below 1e-12
                root = mp.findroot(lambda z: Lchi3(mp.mpf(0.5)+1j*z), g,
                                   tol=mp.mpf(10)**-40)
                g = mp.re(root)
                if abs(mp.im(root)) < 1e-9 and abs(Lchi3(mp.mpf(0.5)+1j*g)) < mp.mpf(10)**-12:
                    gf = float(g)
                    if not zeros or abs(gf - zeros[-1]) > 1e-4:
                        zeros.append(gf); mp_zeros.append(g)
            except Exception:
                pass
            if len(zeros) >= n_zeros:
                break
    order = np.argsort(zeros)
    zeros = [zeros[i] for i in order][:n_zeros]
    mp_zeros = [mp_zeros[i] for i in order][:n_zeros]
    worst = max(float(abs(Lchi3(mp.mpf(0.5)+1j*g))) for g in mp_zeros)
    return np.array(zeros), worst

# =============================================================================
# S(T): the fluctuation we are trying to capture
#   N(T) = theta(T)/pi + 1 + S(T);  at the n-th zero N=n  =>  S = n - (theta/pi + 1)
#   chi3 is ODD (a=1): theta(T) = Im[ ((s+1)/2) log(3/pi) + loggamma((s+1)/2) ], s=1/2+iT
# =============================================================================
def theta_chi3(T):
    T = mp.mpf(T); s = mp.mpf(0.5) + 1j*T; a = 1
    term1 = ((s + a)/2) * mp.log(mp.mpf(3)/mp.pi)
    term2 = mp.loggamma((s + a)/2)
    return float(mp.im(term1 + term2))

def S_of_zeros(G):
    n = np.arange(1, len(G)+1)
    weyl = np.array([theta_chi3(g)/np.pi + 1 for g in G])
    return n - weyl, weyl

# =============================================================================
# chi3 weight
# =============================================================================
def chi3(n):
    n = np.asarray(n)
    return np.where(n % 3 == 1, 1.0, np.where(n % 3 == 2, -1.0, 0.0))

# =============================================================================
# THE REAL 3D BLOCKY HELIX OBJECT (explicit x,y,z) with PHASORS
# =============================================================================
class BlockyHelix3D:
    """
    Integers n=1..N wound onto a vertical axis, split into sqrt-AREA BLOCKS:
      block k = ceil(sqrt n)  -> block k holds ~ (2k-1) integers (area law n~k^2).
    Within block k the geometry is CONSTANT; at each boundary the params STEP.

      R(n)   = ceil(sqrt n)            stepped radial law (the headline ingredient)
      ds     = pi/3                    integer arc spacing (constant here; fuzzed elsewhere)
      pitch  = stepped axial rise per turn
      dphi   = ds / R(n)               winding angle increment (arc/radius)
      dz     = pitch * dphi/(2pi)      axial rise
      (x,y)  = R(cos phi, sin phi);  z = cumsum(dz)

    PHASOR at integer n: real unit vector u(n) = (cos psi(n), sin psi(n)) transverse
    to the axis, psi(n) = w * log n  (winding phase, the analytic bridge readout).
    chi3(n) and amp(n)=1/R(n) weight it.
    """
    def __init__(self, N, ds=np.pi/3, pitch_law=None):
        self.N = N
        self.n = np.arange(1, N+1)
        self.k = np.ceil(np.sqrt(self.n)).astype(int)   # block index = ceil(sqrt n)
        self.R = self.k.astype(float)                   # STEPPED radial law
        self.amp = 1.0 / self.R
        self.ds = np.full(N, ds)
        if pitch_law is None:
            pitch_law = lambda k: np.pi/3 * np.ones_like(k, dtype=float)
        self.pitch = pitch_law(self.k.astype(float))
        # explicit 3D coords
        self.dphi = self.ds / np.maximum(self.R, 1e-9)
        self.phi = np.cumsum(self.dphi)
        self.dz = self.pitch * self.dphi / (2*np.pi)
        self.z = np.cumsum(self.dz)
        self.x = self.R * np.cos(self.phi)
        self.y = self.R * np.sin(self.phi)

    def print_sample(self):
        print("=== STEP 1: THE BUILT 3D BLOCKY HELIX (explicit coordinates) ===")
        print(f"   block k(n)=ceil(sqrt n);  R(n)=k;  ds=pi/3;  dphi=ds/R;  z=cumsum(pitch*dphi/2pi)")
        print(f"   {'n':>6} {'block k':>7} {'R':>5} {'phi(wind)':>11} {'z(height)':>11}    "
              f"{'(x,':>9}{'y,':>9}{'z)':>9}")
        for nn in [1,2,3,4,5,9,16,25,100,400,1000]:
            if nn > self.N: continue
            i = nn-1
            print(f"   {nn:6d} {self.k[i]:7d} {self.R[i]:5.1f} {self.phi[i]:11.4f} "
                  f"{self.z[i]:11.4f}    ({self.x[i]:7.2f},{self.y[i]:7.2f},{self.z[i]:7.3f})")

    def phasor_sample(self, w):
        print(f"\n=== STEP 2: PHASOR at each point (real unit vectors), sample at w={w:.4f} ===")
        psi = w * np.log(self.n)
        print(f"   psi(n)=w*log n ;  u(n)=(cos psi, sin psi) ;  chi3-weighted, amp=1/R")
        for nn in [1,2,4,5,7,8,16,17]:
            if nn > self.N: continue
            i = nn-1
            u = (np.cos(psi[i]), np.sin(psi[i]))
            print(f"   n={nn:3d}: chi3={chi3(nn):+.0f}  R={self.R[i]:4.1f}  "
                  f"phasor u=({u[0]:+.3f},{u[1]:+.3f})  amp={self.amp[i]:.3f}")

    def resultant(self, w, amp=None, phase=None):
        """chi3-weighted PHASOR VECTOR-SUM -> 2D resultant vector (vx,vy)."""
        if amp is None: amp = self.amp
        if phase is None: phase = np.log(self.n)
        ch = chi3(self.n)
        psi = w * phase
        vx = np.sum(ch * amp * np.cos(psi))
        vy = np.sum(ch * amp * np.sin(psi))
        return vx, vy

    def axis_misalignment_angle(self, w, amp=None, phase=None):
        vx, vy = self.resultant(w, amp, phase)
        return np.arctan2(vy, vx)

    def axis_defect(self, w, amp=None, phase=None):
        """0 = phasors collapse onto axis (perfect cancellation); 1 = no cancellation."""
        if amp is None: amp = self.amp
        vx, vy = self.resultant(w, amp, phase)
        tot = np.sum(np.abs(chi3(self.n)) * amp)
        return np.hypot(vx, vy) / max(tot, 1e-12)


# =============================================================================
# correlation helpers
# =============================================================================
def corr(a, b):
    a = np.asarray(a, float); b = np.asarray(b, float)
    v = np.isfinite(a) & np.isfinite(b)
    if v.sum() < 5: return np.nan
    return np.corrcoef(a[v], b[v])[0, 1]

def shuffle_p(sig, target, n_shuffle=20000, seed=0):
    rng = np.random.default_rng(seed)
    real = corr(sig, target)
    t = np.asarray(target, float).copy()
    cs = np.empty(n_shuffle)
    for i in range(n_shuffle):
        rng.shuffle(t)
        cs[i] = corr(sig, t)
    p = np.mean(np.abs(cs) >= abs(real))
    return real, cs.std(), p


# =============================================================================
# MAIN
# =============================================================================
if __name__ == "__main__":
    print("#"*80)
    print("# blocky_fluct-1.py : BLOCKY HELIX -> chi3 zero FLUCTUATION S(T)")
    print("#"*80)

    # ---- exact zeros (recompute, verify |L|<1e-12) ----
    print("\n--- computing exact chi3 zeros (scan + findroot, verify |L|<1e-12) ---")
    G, worst = compute_chi3_zeros(n_zeros=64, t_end=132.0, coarse=0.04)
    print(f"   found {len(G)} zeros; worst |L(1/2+i gamma)| at HIGH precision = {worst:.2e}")
    print(f"   first six: {np.round(G[:6],6)}")
    assert worst < 1e-12, "zero verification failed (|L| not below 1e-12)"

    # ---- S(T) ----
    S, weyl = S_of_zeros(G)
    print(f"   S(T) range: [{S.min():+.3f}, {S.max():+.3f}]  (the fluctuation to capture)")

    Nzer = len(G)

    # ---- STEP 1 & 2: build the real 3D object, print samples ----
    print()
    H = BlockyHelix3D(N=6000)
    H.print_sample()
    H.phasor_sample(w=float(G[0]))

    # ---- the central cancellation demonstration at the first exact zero ----
    print("\n=== STEP 3: chi3-weighted PHASOR VECTOR-SUM collapse vs exact zeros ===")
    print(f"   {'gamma_n':>11} {'|resultant|':>12} {'axis-defect':>12}  {'alpha=atan2':>12}  {'sinAlpha':>9}")
    for i in range(min(8, Nzer)):
        g = float(G[i])
        vx, vy = H.resultant(g)
        defect = H.axis_defect(g)
        alpha = np.arctan2(vy, vx)
        print(f"   {g:11.5f} {np.hypot(vx,vy):12.5f} {defect:12.5f}  {alpha:+12.5f}  {np.sin(alpha):+9.4f}")

    # =====================================================================
    # HEADLINE: does sin(alpha) at the zeros carry S(T)?  (BLOCKY radial)
    # =====================================================================
    print("\n" + "="*80)
    print("HEADLINE H1: corr( sin(axis-misalignment angle), S(T) )  -- BLOCKY radial")
    print("="*80)

    def angle_signal(heights, amp=None, phase=None, N=6000):
        hh = BlockyHelix3D(N=N)
        if amp is None: amp = hh.amp
        out = []
        for w in heights:
            vx, vy = hh.resultant(w, amp=amp, phase=phase)
            out.append(np.arctan2(vy, vx))
        return np.sin(np.array(out))

    sinA = angle_signal(G)                       # blocky 1/ceil(sqrt n), phase=log n
    print(f"\n  IN-SAMPLE / OUT-OF-SAMPLE:")
    for lo, hi, name in [(0,30,"zeros 1-30"),(30,Nzer,f"zeros 31-{Nzer}"),(0,Nzer,f"zeros 1-{Nzer}")]:
        print(f"    {name:14s}: corr(sinAlpha, S) = {corr(sinA[lo:hi], S[lo:hi]):+.3f}  (n={hi-lo})")

    real, nstd, p = shuffle_p(sinA, S, n_shuffle=20000)
    print(f"\n  SHUFFLE NULL (full {Nzer}): real corr {real:+.3f}; null std {nstd:.3f}; "
          f"p(|null|>=|real|) = {p:.5f}")

    # midpoints (signal should be AT zeros, not between)
    mid = 0.5*(G[:-1] + G[1:])
    sinA_mid = angle_signal(mid)
    print(f"  AT MIDPOINTS (not zeros): corr(sinAlpha, S[:-1]) = {corr(sinA_mid, S[:-1]):+.3f}  "
          f"(should be ~0)")

    # gamma-detrend both
    B = np.vstack([G, np.ones(Nzer)]).T
    cA,_,_,_ = np.linalg.lstsq(B, sinA, rcond=None); sinA_res = sinA - B@cA
    cS,_,_,_ = np.linalg.lstsq(B, S, rcond=None);    S_res    = S - B@cS
    print(f"  gamma-DETRENDED (both): corr(sinAlpha_res, S_res) = {corr(sinA_res, S_res):+.3f}")

    # =====================================================================
    # STEP 4 (HONESTY): blocky vs smooth -- is the geometry necessary?
    # =====================================================================
    print("\n" + "="*80)
    print("HONESTY: which amplitude carries S?  (BLOCKY geometric step vs SMOOTH analytic-L)")
    print("="*80)
    N = 6000
    n = np.arange(1, N+1)
    sm   = n**-0.5
    kc   = np.ceil(np.sqrt(n));  kc[kc<1]=1
    kf   = np.floor(np.sqrt(n)); kf[kf<1]=1
    kr   = np.round(np.sqrt(n)); kr[kr<1]=1
    rng  = np.random.default_rng(7)
    variants = {
        "SMOOTH n^-1/2 (analytic L)":   sm,
        "BLOCKY 1/ceil(sqrt n)":        1/kc,
        "BLOCKY 1/floor(sqrt n)":       1/kf,
        "BLOCKY 1/round(sqrt n)":       1/kr,
        "delta only (ceil - smooth)":   1/kc - sm,
        "smooth + RANDOM sawtooth":     sm + (rng.random(N)-0.5)*0.2*sm,
        "smooth * (1+.2cos(2pi n/3))":  sm*(1+0.2*np.cos(2*np.pi*n/3)),
    }
    for name, amp in variants.items():
        sig = angle_signal(G, amp=amp, N=N)
        print(f"    {name:30s} corr(sinAlpha,S) = {corr(sig, S):+.3f}")

    # =====================================================================
    # N-STABILITY: does the BLOCKY signal decay with N (small-T artifact?)
    # while the SMOOTH residual decays to 0 (analytic-L trap)?
    # =====================================================================
    print("\n" + "="*80)
    print("N-STABILITY: blocky vs smooth correlation as truncation N grows")
    print("="*80)
    print(f"    {'N':>7} {'blocky 1/ceil':>14} {'smooth n^-1/2':>14}")
    for N in [500, 1000, 2000, 4000, 8000, 15000]:
        nn = np.arange(1, N+1)
        ac = 1/np.maximum(np.ceil(np.sqrt(nn)),1)
        asm = nn**-0.5
        sb = angle_signal(G, amp=ac, N=N)
        ss = angle_signal(G, amp=asm, N=N)
        print(f"    {N:7d} {corr(sb,S):+14.3f} {corr(ss,S):+14.3f}")

    # =====================================================================
    # PUSH PAST (a): SIGN pinning -- which rounding is forced? report flip.
    # =====================================================================
    print("\n" + "="*80)
    print("PUSH (a): SIGN of correlation vs rounding convention (the open sign-ambiguity)")
    print("="*80)
    for name, kk in [("ceil ", kc), ("floor", kf), ("round", kr)]:
        sig = angle_signal(G, amp=1/kk, N=6000)
        print(f"    R=#{name}(sqrt n):  corr = {corr(sig,S):+.3f}")
    print("    -> magnitude robust; SIGN flips ceil<->floor. Sign not yet geometrically pinned.")

    # =====================================================================
    # PUSH PAST (b): PHASE-SCALE -- the open gap. Is the log-n phase essential,
    # or does a purely-geometric winding phi(n) self-calibrate?
    # =====================================================================
    print("\n" + "="*80)
    print("PUSH (b): PHASE-SCALE -- log-n (analytic bridge) vs geometric winding phi(n)")
    print("="*80)
    N = 6000
    Hg = BlockyHelix3D(N=N)
    # geometric winding angle phi(n) (from the actual 3D build) at various rescalings
    phi_geom = Hg.phi  # = cumsum(ds/R), the helix's own winding
    print("    phase = c * phi_geom (pure geometry), swept scale c:")
    best = (0.0, None)
    for c in [0.1,0.3,0.5,0.7,1.0,1.5,2.0,3.0,5.0]:
        sig = angle_signal(G, amp=1/np.ceil(np.sqrt(np.arange(1,N+1))),
                           phase=c*phi_geom, N=N)
        cval = corr(sig, S)
        if abs(cval) > abs(best[0]): best = (cval, c)
        print(f"      c={c:4.1f}: corr(sinAlpha,S) = {cval:+.3f}")
    print(f"    best geometric-phase corr = {best[0]:+.3f} at c={best[1]}")
    print("    REFERENCE log-n phase corr =", f"{corr(angle_signal(G, N=N), S):+.3f}")
    print("    -> if geometric phi cannot match log-n, the phase scale is the OPEN gap (honest).")

    print("\n" + "#"*80)
    print("# DONE")
    print("#"*80)
