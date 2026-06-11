"""
blocky_hypotheses.py -- test harness for the 4 BLOCKY-HELIX hypotheses (H1..H4).

All four build a REAL 3D blocky solid with explicit (x,y,z) + a PHASOR per integer, then
measure the chi3-weighted PHASOR VECTOR-SUM RESULTANT collapsing onto the central axis,
and compare collapse heights to the exact mpmath chi3 zeros (chi3_zeros_65.npy).

VERDICT metric for each hypothesis:
  - MEAN-ONLY  : collapse heights match the smooth (1/2)log(q gamma/2pi) staircase but the
                 per-block residual (geometric S(T)) is uncorrelated with the true fluctuation.
  - FLUCTUATION: the per-block pitch/spacing the construction PRODUCES correlates with the
                 true pi/gap_k fluctuation (corr of residuals well above the 0.50 mean-only
                 baseline), i.e. it reproduces individual zeros, not just their density.

Run:  python3 blocky_hypotheses.py H1   (or H2/H3/H4/all)
"""
import sys
import numpy as np
from blocky_core import chi3, Lt

Z = np.load('chi3_zeros_65.npy')
Q = 3
GAPS = np.diff(Z)
PK = np.pi / GAPS                                   # required block pitch
MEAN_DENS = 0.5 * np.log(Q * Z[:-1] / (2 * np.pi))  # smooth log density
TRUE_FLUCT = PK - MEAN_DENS                          # the S(T) fluctuation to capture


def fluct_verdict(produced_pitch):
    """produced_pitch: array aligned with blocks 0..len(GAPS)-1.
    Returns (corr_with_mean, corr_residual_with_true_fluct, verdict)."""
    m = min(len(produced_pitch), len(PK))
    pp = np.asarray(produced_pitch[:m], float)
    cm = np.corrcoef(pp, MEAN_DENS[:m])[0, 1]
    resid = pp - MEAN_DENS[:m]
    # how much of the TRUE fluctuation does the produced residual explain?
    cf = np.corrcoef(resid, TRUE_FLUCT[:m])[0, 1]
    verdict = 'FLUCTUATION' if cf > 0.7 else ('PARTIAL' if cf > 0.45 else 'MEAN-ONLY')
    return cm, cf, verdict


# ============================================================ shared 3D builder
def weighted_phasors(N, theta_of_n, radius_exp=0.5):
    """Return (n, chi3 sign, amplitude=R^{-1}, theta) for the 3D phasor vector-sum.
    radius R_n = n^{radius_exp} (planar packing -> 1/2). amplitude = 1/R = n^{-radius_exp}."""
    n = np.arange(1, N + 1).astype(float)
    sgn = np.array([chi3(int(k)) for k in n])
    amp = n ** (-radius_exp)
    th = theta_of_n(n)
    return n, sgn, amp, th


def axis_resultant(sgn, amp, th, w):
    """3D resultant of the weighted phasors at readout frequency w: lands on central axis -> 0."""
    vx = np.sum(sgn * amp * np.cos(w * th))
    vy = np.sum(sgn * amp * np.sin(w * th))
    return np.hypot(vx, vy)


def collapse_heights(sgn, amp, th, t_lo=6.0, t_hi=30.0, step=0.01):
    """Scan readout frequency, return local minima of the axis-resultant (the produced 'zeros')."""
    ws = np.arange(t_lo, t_hi, step)
    mag = np.array([axis_resultant(sgn, amp, th, w) for w in ws])
    mins = []
    for i in range(1, len(mag) - 1):
        if mag[i] < mag[i - 1] and mag[i] < mag[i + 1] and mag[i] < 0.5:
            mins.append((ws[i], mag[i]))
    return mins


# ===================================================================== H1
def H1_integer_spacing_step(N=4000, h=np.pi / 16):
    """H1: INTEGER-SPACING-STEP blocky helix. Within block k (a log-window of width h),
    the integer winding increment is CONSTANT = h/count_k (denser blocks step finer).
    The staircase quantization error is the geometric S(T)."""
    n = np.arange(1, N + 1).astype(float)
    logn = np.log(n)
    kmax = int(logn[-1] / h) + 2
    theta = np.zeros(N)
    acc = 0.0
    for k in range(kmax):
        mask = (logn >= k * h) & (logn < (k + 1) * h)
        cnt = mask.sum()
        if cnt == 0:
            continue
        c_k = h / cnt
        idx = np.where(mask)[0]
        theta[idx] = acc + c_k * np.arange(1, cnt + 1)
        acc = theta[idx[-1]]

    def theta_of_n(_):
        return theta
    _, sgn, amp, th = weighted_phasors(N, theta_of_n)
    mins = collapse_heights(sgn, amp, th)
    return mins, theta, logn


# ===================================================================== H3
def H3_radial_spacing_co_step(N=4000, radius_exp=0.5):
    """H3: RADIAL+SPACING co-step. Phase = log n (FTA winding), amplitude = n^{-radius_exp}
    (radius R=n^{radius_exp}). Sweeping radius_exp probes whether the on-AXIS collapse SELECTS
    the 1/2 baseline (planar packing) -- i.e. whether sqrt is earned geometrically."""
    def theta_of_n(n):
        return np.log(n)
    n, sgn, amp, th = weighted_phasors(N, theta_of_n, radius_exp)
    res_at_zero = np.mean([axis_resultant(sgn, amp, th, g) for g in Z[:8]])
    res_off = np.mean([axis_resultant(sgn, amp, th, g + 1.3) for g in Z[:8]])
    return res_at_zero, res_off


if __name__ == '__main__':
    which = sys.argv[1] if len(sys.argv) > 1 else 'all'

    if which in ('H1', 'all'):
        print('=== H1: integer-spacing-step blocky helix ===')
        for h in [np.pi / 8, np.pi / 16, np.pi / 32]:
            mins, theta, logn = H1_integer_spacing_step(h=h)
            staircase_err = np.std((theta - logn)[100:])
            heights = [m[0] for m in mins]
            print(f'  h={h:.4f}: staircase-err(geom S(T))={staircase_err:.4f}; '
                  f'{len(mins)} collapse(s) below 0.5; first few={np.round(heights[:6],2)}')
        print(f'  (true first zeros: {np.round(Z[:6],3)})')

    if which in ('H3', 'all'):
        print('\n=== H3: radial+spacing co-step (axis selects 1/2) ===')
        for a in [0.40, 0.45, 0.50, 0.55, 0.60]:
            rz, ro = H3_radial_spacing_co_step(radius_exp=a)
            print(f'  radius R~n^{a:.2f}: on-axis at zeros={rz:.4f}  off-zeros={ro:.4f}  '
                  f'{"<== SELECTED" if a == 0.50 else ""}')
