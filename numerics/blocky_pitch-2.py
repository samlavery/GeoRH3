"""
blocky_pitch-2.py  --  ID: pitch-2
==================================
PHASOR-ARGUMENT PITCH-STEP HELIX.

CLAIM under test: the correct per-block pitch p_k (axial rise per turn within block k)
is NOT a smooth function of height but is the LOCAL WINDING RATE OF THE RUNNING
CHI3-PHASOR RESULTANT:

        p_k = d(arg W)/dT   averaged across block k,

where W(T) = e^{i theta(T)} S(T) is the rotated (real) standing wave of the chi3
phasor vector-sum S(T). The self-referential pitch is supposed to reproduce the
IRREGULAR spacing (the S(T) fluctuation) because arg(W) advances by EXACTLY pi across
each block (one node per zero) while the RATE of that advance fluctuates block-to-block.

Falsifiable prediction (the real test, STEP 4):
  Integrate the BLOCK-LOCAL rate r(T)=d(arg W)/dT forward from one zero; the next
  boundary solves  integral_{gamma_k}^{gamma_{k+1}} r(T) dT = pi.  If integrating the
  *block-constant* local rate predicts the NEXT zero to high accuracy (RMS << mean gap
  ~1.6), it captures the per-block FLUCTUATION.  If it only reproduces the smooth log
  mean, RMS ~ 1.6 and the fluctuation is NOT captured.

HARD RULE honored: we build the REAL 3D blocky solid with explicit (x,y,z) AND a real
rotating phasor vector at every integer point, PRINT a coordinate sample BEFORE
measuring, and the collapse is the chi3-weighted PHASOR VECTOR-SUM landing on the
central axis -- never an abstract scalar.

HONESTY GUARD baked in:
  - The phasor resultant S(T) = sum chi3(n) n^{-1/2} exp(-iT log n) exp(-(n/N)^2) IS a
    truncated, Gaussian-damped Dirichlet sum.  As N->inf this converges to L(1/2+iT),
    so if we then "find where S collapses" we have SECRETLY re-derived analytic L.  To
    avoid fooling ourselves the FALSIFICATION step does NOT root-find L (or S).  It uses
    ONLY the block-local winding RATE r(T) measured from the phasor cloud INSIDE the
    current block, integrated forward, with NO peek at the next zero.  That is the
    genuine self-referential stepping.  We additionally run a CONTROL where r(T) is
    replaced by the smooth log-density and by the listed constant steps (pi/3, pi/2,
    log2, log3, sqrt2) -- which MUST fail (RMS~1.6) if the phasor rate is doing real work.
"""

import numpy as np
import mpmath as mp

mp.mp.dps = 30
Q = 3


# ----------------------------------------------------------------- chi3 + L + zeros
def chi3(n):
    r = n % 3
    return 0 if r == 0 else (1 if r == 1 else -1)


def Lchi3(s):
    s = mp.mpc(s)
    return mp.mpf(3) ** (-s) * (mp.zeta(s, mp.mpf(1) / 3) - mp.zeta(s, mp.mpf(2) / 3))


def Lt(t):
    return Lchi3(mp.mpf(1) / 2 + mp.mpc(0, 1) * mp.mpf(str(t)))


def load_exact_zeros(path="/Users/samuellavery/proof/three/numerics/chi3_zeros_exact.txt"):
    g = []
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            g.append(float(line))
    g = np.array(sorted(g))
    # verify |L| < 1e-11 at each
    bad = 0
    for t in g[:8]:
        if float(abs(Lt(t))) > 1e-10:
            bad += 1
    print(f"[zeros] loaded {len(g)} exact chi3 zeros; |L|<1e-10 spot-checked on first 8 "
          f"({'all pass' if bad == 0 else f'{bad} FAIL'})")
    return g


# ========================================================================= STEP 1
# Build the REAL 3D blocky helix with explicit (x,y,z) and a phasor per integer point.
#
# Geometry (the established area-law cone, per Hyp 1 / prompt FORMULA):
#   integer n sits at radius   R_n = sqrt(n)          (area law: ~k integers in loop k)
#   amplitude (phasor length)  a_n = 1/R_n = n^{-1/2} (the critical-line n^{-1/2})
#   "drag"  phase per height   phi_n(T) = -T * log R_n = -(T/2) log n
#   chi3 sign                  chi3(n) in {+1,0,-1}
#   axial coordinate z         set by the STEPPED pitch p_k (built in STEP 3)
#
# The phasor at integer n, observed at height T, is the rotating unit vector
#       u_n(T) = exp(i * phi_n(T))   (a real 2-vector (cos,sin) that spins as T grows).
# The chi3-weighted phasor VECTOR-SUM (the resultant) is
#       S(T) = sum_n chi3(n) a_n u_n(T) exp(-(n/N)^2)
# A cancellation event = S(T) collapses onto the central axis (|S| -> 0).
def build_blocky_helix_points(N, pitch_per_block, block_bounds_z=None):
    """Explicit 3D coordinates of the N integer points on the blocky cone-helix.

    radius   R_n = sqrt(n)          (area-law cone)
    winding  theta_n: each integer advances the winding angle by ~1/R_n of a turn-unit
             so loop k (R~k) holds ~k integers -> cumulative ~k^2 = area law.  We use the
             canonical theta_n = 2*pi * (cumulative count within growing loops); concretely
             theta advances by d theta = 1/R_n per integer (so circumference 2 pi R holds
             ~2 pi R integers).  This is the rewinding, NOT a log placement.
    z_n      : STEPPED pitch.  z accumulates p_{block} per unit winding angle.  pitch steps
             at each block boundary -> the helix VISIBLY changes pitch each block (blocky).
    Returns explicit arrays x,y,z,R,theta,block and the complex phasor base (chi3*amp).
    """
    n = np.arange(1, N + 1)
    R = np.sqrt(n.astype(float))
    # winding angle: d theta = 1/R per integer (area-law rewinding)
    dtheta = 1.0 / R
    theta = np.cumsum(dtheta)
    # block index of each integer: which pitch-block its axial position falls in.
    # We tie blocks to winding-angle bands of width = one "half turn of the resultant".
    # For STEP 1 display we simply band by equal theta chunks; the physically meaningful
    # blocks (between zeros) are imposed in STEP 3/4 via pitch_per_block indexed by height.
    nblk = len(pitch_per_block)
    # map each integer to a block by splitting the total winding into nblk equal arcs
    th_max = theta[-1]
    block = np.minimum((theta / th_max * nblk).astype(int), nblk - 1)
    # accumulate z with the STEPPED pitch p_block per unit winding angle
    p_of_n = np.array([pitch_per_block[b] for b in block])
    z = np.cumsum(p_of_n * dtheta)
    x = R * np.cos(theta)
    y = R * np.sin(theta)
    # phasor base = chi3 sign * amplitude (the spinning part exp(-i T/2 log n) is added at read time)
    sgn = np.array([chi3(int(k)) for k in n], dtype=float)
    amp = R ** -1.0  # = n^{-1/2}
    return dict(n=n, R=R, theta=theta, block=block, x=x, y=y, z=z,
                chi=sgn, amp=amp)


def resultant_phasor_sum(obj, T, N=None):
    """The chi3-weighted PHASOR VECTOR-SUM at height T (real 2-vector, returned complex).
    S(T) = sum chi3(n) n^{-1/2} exp(-i (T/2) log R_n^2)... = sum chi3(n) n^{-1/2} exp(-i T log n).
    Note log R_n = (1/2) log n, and the drag is exp(-i T log n) (the n^{it} of the L-sum).
    Gaussian damping exp(-(n/N)^2) tames the truncation.  This IS a Dirichlet partial sum
    (-> L as N->inf); see honesty guard -- it is used ONLY to read winding RATE, never to
    root-find the zero in the falsification step."""
    if N is None:
        N = len(obj["n"])
    n = obj["n"][:N].astype(float)
    chi = obj["chi"][:N]
    amp = obj["amp"][:N]
    damp = np.exp(-((n / N) ** 2))
    phase = np.exp(-1j * T * np.log(n))
    return np.sum(chi * amp * damp * phase)


def axis_alignment(obj, T, N=None):
    """ALIGN-TO-AXIS test at height T: do the chi3-signed phasors (as 2D vectors in the
    transverse plane) point at / away from the central axis when S collapses?  The phasor
    direction is angle(chi*amp*exp(-iT log n)); 'aligned to axis' would be all phasors
    parallel/antiparallel (resultant on a line through origin = collapses to axis).
    We report the resultant-direction concentration: |sum of UNIT phasors| / count
    (1 => perfectly aligned, 0 => isotropic)."""
    if N is None:
        N = len(obj["n"])
    n = obj["n"][:N].astype(float)
    chi = obj["chi"][:N]
    mask = chi != 0
    ph = chi[mask] * np.exp(-1j * T * np.log(n[mask]))
    ph = ph / np.abs(ph)
    return abs(np.sum(ph)) / mask.sum()


# ========================================================================= STEP 2/3
# The rotated standing wave W(T) = e^{i theta(T)} S(T) chosen real, and its winding rate.
def rotated_standing_wave(obj, Ts, N=None):
    """Return S(T) over a grid and the rotation that makes the wave real.
    W(T) = e^{-i arg S(T0_anchor)} ... we instead use the canonical Hardy-type rotation:
    multiply S by the unit phase that flattens its argument's smooth part.  Operationally,
    arg W advances by ~pi between consecutive zeros (resultant passes through origin).
    We just track arg S unwrapped; the 'rotation' is a global constant and does not change
    the RATE d(arg S)/dT, which is what we integrate."""
    S = np.array([resultant_phasor_sum(obj, float(T), N=N) for T in Ts])
    return S


def arg_rate(Ts, S):
    """instantaneous winding rate r(T) = d(arg S)/dT, from unwrapped phase of the resultant."""
    arg = np.unwrap(np.angle(S))
    r = np.gradient(arg, Ts)
    return arg, r


# ========================================================================= helpers
def smooth_pitch(gamma):
    """control: smooth log-density pitch p^smooth = (1/2) log(q*gamma/2pi)."""
    return 0.5 * np.log(Q * gamma / (2 * np.pi))


# ======================================================================== MAIN
def main():
    np.set_printoptions(suppress=True, linewidth=120)
    print("=" * 80)
    print("blocky_pitch-2  :  PHASOR-ARGUMENT PITCH-STEP HELIX")
    print("=" * 80)

    GAMMA = load_exact_zeros()
    gap = np.diff(GAMMA)
    mean_gap = float(np.mean(gap))
    print(f"[zeros] mean gap = {mean_gap:.4f}  (this is the 'RMS~1.6' fail threshold)")

    # ---- required per-block pitch p_k = pi/gap_k (the thing a helix must reproduce) ----
    p_required = np.pi / gap  # axial rise per turn within block k
    p_ctrl = smooth_pitch(GAMMA[:-1])  # smooth log-density control

    # ================================================================= STEP 1
    print("\n" + "=" * 80)
    print("STEP 1  --  BUILD THE REAL 3D BLOCKY HELIX (explicit x,y,z) + phasors")
    print("=" * 80)
    N = 4000
    # build with the REQUIRED stepped pitch p_k so the helix is genuinely blocky.
    obj = build_blocky_helix_points(N, pitch_per_block=p_required)
    print(f"built {N} integer points on the area-law cone (R_n=sqrt(n)), "
          f"{len(p_required)} pitch-blocks stepped to p_k=pi/gap_k.")
    print("\nSAMPLE of explicit 3D coordinates (n, block, R, theta, x, y, z) + phasor base:")
    print(f"  {'n':>5} {'blk':>4} {'R':>8} {'theta':>9} {'x':>9} {'y':>9} {'z':>9} "
          f"{'chi':>4} {'amp':>8}")
    for i in list(range(0, 12)) + [40, 100, 400, 1000, 3999]:
        print(f"  {obj['n'][i]:5d} {obj['block'][i]:4d} {obj['R'][i]:8.3f} "
              f"{obj['theta'][i]:9.3f} {obj['x'][i]:9.3f} {obj['y'][i]:9.3f} "
              f"{obj['z'][i]:9.3f} {int(obj['chi'][i]):4d} {obj['amp'][i]:8.4f}")

    # show the pitch VISIBLY stepping (blocky): mean dz/dtheta within first few blocks
    print("\n  PITCH STEPS PER BLOCK (z accumulates p_k per unit winding -> blocky helix):")
    print(f"  {'k':>3} {'gamma_k':>9} {'gap_k':>7} {'p_k=pi/gap':>11} {'p_smooth':>9} "
          f"{'ratio':>7}")
    for k in range(12):
        print(f"  {k:3d} {GAMMA[k]:9.4f} {gap[k]:7.4f} {p_required[k]:11.4f} "
              f"{p_ctrl[k]:9.4f} {p_required[k] / p_ctrl[k]:7.3f}")

    # ================================================================= STEP 2
    print("\n" + "=" * 80)
    print("STEP 2  --  PHASOR VECTOR-SUM S(T): collapse to central axis at zeros?")
    print("=" * 80)
    print("  Evaluate |S(T)| = |chi3-weighted phasor resultant| at exact zeros vs midpoints.")
    print(f"  {'k':>3} {'gamma_k':>9} {'|S(gamma)|':>11} {'|S(mid)|':>10} "
          f"{'align@gamma':>11} {'|L(gamma)|':>11}")
    collapse_ratio = []
    for k in range(10):
        g = GAMMA[k]
        mid = 0.5 * (GAMMA[k] + GAMMA[k + 1])
        Sg = resultant_phasor_sum(obj, g)
        Sm = resultant_phasor_sum(obj, mid)
        al = axis_alignment(obj, g)
        Lg = float(abs(Lt(g)))
        collapse_ratio.append(abs(Sg) / abs(Sm))
        print(f"  {k:3d} {g:9.4f} {abs(Sg):11.5f} {abs(Sm):10.5f} {al:11.4f} {Lg:11.2e}")
    cr = np.array(collapse_ratio)
    print(f"\n  mean |S(zero)|/|S(midpoint)| = {cr.mean():.3f}  "
          f"(<1 => phasor resultant DOES collapse toward the axis at zeros)")

    # ================================================================= STEP 3
    print("\n" + "=" * 80)
    print("STEP 3  --  WINDING of arg S(T): does it advance ~pi per block?")
    print("=" * 80)
    # dense grid across first ~18 blocks; measure d(arg S)/dT and the per-block advance.
    Thi = GAMMA[18] + 0.5
    Tgrid = np.arange(7.0, Thi, 0.01)
    S = rotated_standing_wave(obj, Tgrid)
    arg, rate = arg_rate(Tgrid, S)

    def arg_at(T):
        return np.interp(T, Tgrid, arg)

    def rate_at(T):
        return np.interp(T, Tgrid, rate)

    print(f"  {'k':>3} {'gamma_k':>9} {'gap':>7} {'d(argS)/pi over block':>22} "
          f"{'mean rate':>10} {'pi/gap':>8}")
    dwind = []
    rate_per_block = []
    for k in range(18):
        a0, a1 = arg_at(GAMMA[k]), arg_at(GAMMA[k + 1])
        w = (a1 - a0) / np.pi
        # mean rate across the block (block-constant rate estimate)
        Tk = np.linspace(GAMMA[k], GAMMA[k + 1], 40)
        rk = np.mean(rate_at(Tk))
        dwind.append(w)
        rate_per_block.append(rk)
        print(f"  {k:3d} {GAMMA[k]:9.4f} {gap[k]:7.4f} {w:22.4f} {rk:10.4f} "
              f"{np.pi / gap[k]:8.4f}")
    dwind = np.array(dwind)
    rate_per_block = np.array(rate_per_block)
    print(f"\n  mean winding/pi per block = {dwind.mean():.4f}  std = {dwind.std():.4f}")
    print(f"  (claim: ~1 advance per block, i.e. arg S advances ~pi between zeros)")

    # variance split: how much of p_required variance does smooth law miss?
    var_req = np.var(p_required[:18])
    resid_smooth = p_required[:18] - p_ctrl[:18]
    var_resid = np.var(resid_smooth)
    print(f"\n  VARIANCE SPLIT (first 18 blocks):")
    print(f"    var(p_required)            = {var_req:.5f}")
    print(f"    var(p_required - p_smooth) = {var_resid:.5f}  "
          f"({100 * var_resid / var_req:.0f}% of p_required variance is fluctuation "
          f"the smooth law misses)")

    # ================================================================= STEP 4 (FALSIFY)
    print("\n" + "=" * 80)
    print("STEP 4  --  FALSIFICATION: step gamma_k -> gamma_{k+1} by integrating the")
    print("            BLOCK-LOCAL phasor winding rate to advance arg S by pi.")
    print("            NO direct L/S root-find of the next zero.  Pure self-referential step.")
    print("=" * 80)
    # Predict next boundary: from gamma_k, using the LOCAL rate r(T) measured in a window
    # INSIDE the current block (T just above gamma_k, before we could 'see' gamma_{k+1}),
    # find T* with integral_{gamma_k}^{T*} r(T) dT = pi.  Block-constant rate variant uses
    # the average rate over a short causal window [gamma_k, gamma_k + w].
    fine_T = np.arange(7.0, GAMMA[40] + 1.0, 0.005)
    fineS = rotated_standing_wave(obj, fine_T)
    _, fine_rate = arg_rate(fine_T, fineS)

    def frate(T):
        return np.interp(T, fine_T, fine_rate)

    def predict_next_local_rate(gk, window=0.5):
        """advance arg S by pi using the LOCAL rate measured just after gk (causal)."""
        # block-constant rate from a causal window strictly inside the just-entered block
        Tw = np.linspace(gk + 0.02, gk + window, 25)
        r0 = np.mean(frate(Tw))
        if r0 == 0:
            return gk + mean_gap
        return gk - np.pi / r0  # rate is negative (arg decreasing); advance |pi|

    def predict_next_integrated(gk):
        """advance arg S by pi by integrating the ACTUAL instantaneous rate forward from
        gk until cumulative |delta arg| reaches pi.  This is the integral-of-local-rate rule
        from the FORMULA.  It still uses ONLY S's winding (the phasor cloud), never an L root."""
        Ts = np.arange(gk + 0.005, gk + 4.0, 0.005)
        r = frate(Ts)
        cum = np.concatenate([[0], np.cumsum(0.5 * (r[1:] + r[:-1]) * np.diff(Ts))])
        target = -np.pi  # arg decreases; one half-turn
        idx = np.argmax(cum <= target)
        if idx == 0 and cum[-1] > target:
            return gk + mean_gap  # never reached -> fallback
        return float(np.interp(target, cum[::-1], Ts[::-1]))

    print("\n  (4a) BLOCK-CONSTANT local rate  (causal window inside current block):")
    print(f"  {'k':>3} {'gamma_k':>9} {'pred next':>10} {'exact next':>11} "
          f"{'err':>8}")
    err_local = []
    for k in range(35):
        pred = predict_next_local_rate(GAMMA[k])
        exact = GAMMA[k + 1]
        err_local.append(pred - exact)
        if k < 14:
            print(f"  {k:3d} {GAMMA[k]:9.4f} {pred:10.4f} {exact:11.4f} {pred - exact:8.4f}")
    err_local = np.array(err_local)
    rms_local = float(np.sqrt(np.mean(err_local ** 2)))

    print("\n  (4b) INTEGRATED instantaneous rate (advance arg S by pi, forward integral):")
    print(f"  {'k':>3} {'gamma_k':>9} {'pred next':>10} {'exact next':>11} {'err':>8}")
    err_int = []
    for k in range(35):
        pred = predict_next_integrated(GAMMA[k])
        exact = GAMMA[k + 1]
        err_int.append(pred - exact)
        if k < 14:
            print(f"  {k:3d} {GAMMA[k]:9.4f} {pred:10.4f} {exact:11.4f} {pred - exact:8.4f}")
    err_int = np.array(err_int)
    rms_int = float(np.sqrt(np.mean(err_int ** 2)))

    # ----- CONTROLS: constant arithmetic steps + smooth log-density. These MUST fail. -----
    print("\n  (4c) CONTROLS -- constant/smooth pitch steps (MUST fail, RMS~mean_gap):")
    const_steps = {
        "pi/6": np.pi / 6, "pi/3": np.pi / 3, "pi/2": np.pi / 2, "pi": np.pi,
        "log2": np.log(2), "log3": np.log(3), "sqrt2": np.sqrt(2), "sqrt3": np.sqrt(3),
        "e": np.e,
    }
    print(f"  {'rule':>10} {'RMS boundary err':>18}")
    ctrl_rms = {}
    for name, c in const_steps.items():
        # a constant-step rule predicts gamma_{k+1} = gamma_k + (pi / p)  where p is the
        # constant pitch (since arg advances pi over gap, gap = pi/p).  Constant p => constant gap.
        pred = GAMMA[:35] + (np.pi / c)
        e = pred - GAMMA[1:36]
        ctrl_rms[name] = float(np.sqrt(np.mean(e ** 2)))
        print(f"  {name:>10} {ctrl_rms[name]:18.4f}")
    # smooth log-density step: gap_pred = pi / p_smooth(gamma_k)
    pred_smooth = GAMMA[:35] + np.pi / smooth_pitch(GAMMA[:35])
    e_sm = pred_smooth - GAMMA[1:36]
    rms_smooth = float(np.sqrt(np.mean(e_sm ** 2)))
    print(f"  {'log-smooth':>10} {rms_smooth:18.4f}")

    # ================================================================= STEP 5
    print("\n" + "=" * 80)
    print("STEP 5  --  SWEEP rate-window and truncation N: is the miss truncation noise")
    print("            or a GENUINE mismatch?  (4a block-constant local-rate RMS vs window/N)")
    print("=" * 80)
    print(f"  {'N':>6} {'window':>7} {'RMS(4a)':>9}   (compare smooth control "
          f"{rms_smooth:.4f}, mean gap {mean_gap:.4f})")
    sweep_best = np.inf
    for Nsw in (2000, 4000, 8000):
        objsw = build_blocky_helix_points(Nsw, pitch_per_block=p_required)
        Tsw = np.arange(7.0, GAMMA[40] + 1.0, 0.005)
        Ssw = np.array([resultant_phasor_sum(objsw, float(T), N=Nsw) for T in Tsw])
        _, rsw = arg_rate(Tsw, Ssw)

        def frsw(T, _r=rsw, _t=Tsw):
            return np.interp(T, _t, _r)

        for window in (0.3, 0.5, 0.8):
            errs = []
            for k in range(35):
                gk = GAMMA[k]
                Tw = np.linspace(gk + 0.02, gk + window, 25)
                r0 = np.mean(frsw(Tw))
                pred = gk - np.pi / r0 if r0 != 0 else gk + mean_gap
                errs.append(pred - GAMMA[k + 1])
            rms = float(np.sqrt(np.mean(np.array(errs) ** 2)))
            sweep_best = min(sweep_best, rms)
            print(f"  {Nsw:6d} {window:7.2f} {rms:9.4f}")
    print(f"\n  best RMS over the whole N x window sweep = {sweep_best:.4f}")
    print(f"  (if this stays >~ smooth control {rms_smooth:.4f} across all N, the miss is")
    print(f"   GENUINE -- not truncation; the phasor rate cannot be tuned to beat the mean.)")

    # ================================================================= VERDICT
    print("\n" + "=" * 80)
    print("VERDICT")
    print("=" * 80)
    print(f"  mean gap (fail threshold)                  = {mean_gap:.4f}")
    print(f"  RMS (4a block-constant local phasor rate)  = {rms_local:.4f}")
    print(f"  RMS (4b integrated instantaneous rate)     = {rms_int:.4f}")
    print(f"  RMS (smooth log-density control)           = {rms_smooth:.4f}")
    print(f"  best constant-step control                 = "
          f"{min(ctrl_rms.values()):.4f}  ({min(ctrl_rms, key=ctrl_rms.get)})")
    best_phasor = min(rms_local, rms_int)
    captures = best_phasor < 0.5 * mean_gap and best_phasor < 0.6 * rms_smooth
    print()
    if captures:
        print(f"  ==> PHASOR-RATE stepping RMS {best_phasor:.4f} << mean gap {mean_gap:.4f}")
        print(f"      and beats smooth control {rms_smooth:.4f}: CAPTURES FLUCTUATION.")
    else:
        print(f"  ==> PHASOR-RATE stepping RMS {best_phasor:.4f} is NOT << mean gap "
              f"{mean_gap:.4f}")
        print(f"      and does NOT decisively beat the smooth control {rms_smooth:.4f}.")
        print(f"      => reproduces (at best) the MEAN spacing, NOT the per-block fluctuation.")
        print(f"      The 'p_k = local arg-S winding rate' identity is TRUE only because")
        print(f"      arg S advances ~pi per zero BY CONSTRUCTION of S (S->L, zeros = S=0);")
        print(f"      reading the rate causally WITHOUT seeing the next zero recovers only")
        print(f"      the smooth density.  The fluctuation S(T) is NOT predicted forward.")

    return dict(mean_gap=mean_gap, rms_local=rms_local, rms_int=rms_int,
                rms_smooth=rms_smooth, ctrl_rms=ctrl_rms, captures=captures,
                var_req=float(var_req), var_resid=float(var_resid),
                dwind_mean=float(dwind.mean()), dwind_std=float(dwind.std()),
                collapse_ratio=float(cr.mean()), sweep_best=float(sweep_best))


if __name__ == "__main__":
    R = main()
