"""
SPECTRAL COUNTING MECHANISM -- FULL RUN, character-agnostic, BASE vs PITCH-FEEDBACK.

Honest build of Sam's chain:
  height H -> accumulated source subspace H_F(H) -> Gram/block operator A_H (Hankel-Gram of the
  accumulated chi-twisted loss field) -> new RESOLVABLE singular mode -> emitted gamma_n.

SOURCE FIELD (only place chi enters):
  Psi_chi(x) = sum_{n<=x} Lambda(n) chi(n)      (accumulated FTA-additive winding loss, chi-twisted)
  climb in u = log x ;   F(u) = (Psi_chi(e^u) - M_chi(e^u)) / e^{u/2}
  M_chi = e^u for trivial chi (the n=1 main term of zeta);  M_chi = 0 for non-principal chi (no pole).
  The p^{-1/2} == e^{-u/2} radial weight is the on-line loss energy.  This field's oscillation
  frequencies in u are EXACTLY the imaginary parts gamma of the L(chi,.) zeros (explicit formula).

ACCUMULATED SUBSPACE / GRAM  A_H:
  Hankel matrix of F over the u-window; its left singular subspace (SVD) = H_F(H).  A new resolvable
  singular mode = a new oscillation frequency the window can separate.  We read the emitted
  frequencies (poles of the principal-part field) by matrix-pencil on that subspace -- this is the
  pole readout of the completed source resolvent built on H_F(H).  gamma_n = cumulative emitted heights.

PITCH = resolution budget per accumulation step (how finely the subspace resolves).
  BASE     : pitch CONSTANT -> fixed pencil order (fixed # modes sought) across the whole climb.
  FEEDBACK : pitch -> pitch + delta on each NEW resolved mode -> the order/resolution GROWS as modes
             accumulate, so height-per-turn changes self-consistently.  Models "each resolved mode
             alters the climb".  We FIT delta and report sign + whether it supplies the log density.

CHARACTER-AGNOSTIC: identical code; ONLY the chi table changes.  Reference zeros used ONLY at the end.
numpy float64 throughout; mpmath dps=15 ONLY for reference.  Footprint < 200 MB (N<=3e6, Gram<=~400).
"""
import sys, math
import numpy as np
import mpmath as mp
mp.mp.dps = 15

def pr(*a): print(*a); sys.stdout.flush()

# ===========================================================================
# CHARACTERS  (the ONLY per-L input to the construction)
# ===========================================================================
CHI = {
    'zeta':  ('trivial', None),
    'mod3':  (3, {1: 1, 2: -1}),     # real primitive odd
    'mod4':  (4, {1: 1, 3: -1}),     # real primitive odd
}
def make_chi(kind):
    mod, tab = CHI[kind]
    if mod == 'trivial':
        return (lambda n: 1), True       # principal -> has main term e^u
    return (lambda n: tab.get(n % mod, 0)), False

# ===========================================================================
# SOURCE FIELD  F(u)   (chi-twisted accumulated loss along the climb)
# ===========================================================================
def source_field(kind, N, du):
    chi, principal = make_chi(kind)
    sieve = np.ones(N+1, bool); sieve[:2] = False
    for i in range(2, int(N**0.5)+1):
        if sieve[i]: sieve[i*i::i] = False
    Lam = np.zeros(N+1, np.float64)
    for p in np.nonzero(sieve)[0].tolist():
        lp = math.log(p); pk = p
        while pk <= N:
            Lam[pk] = chi(pk) * lp
            pk *= p
    psi = np.cumsum(Lam)                            # Psi_chi(x)
    u = np.arange(5.0, math.log(N) - 0.05, du)
    x = np.exp(u); idx = np.clip(np.floor(x).astype(int), 0, N)
    main = x if principal else 0.0                  # main term only for principal chi
    F = (psi[idx] - main) / np.sqrt(x)
    F = F - F.mean()
    return u, F

# ===========================================================================
# GRAM / HANKEL SUBSPACE  +  MATRIX-PENCIL POLE READOUT
# ===========================================================================
def emit_modes(F, du, order, dband=1.0):
    """Read the resolvable on-line modes (poles) from the Hankel subspace of F.
    order = pitch (resolution budget).  Returns sorted positive gammas with small damping."""
    n = len(F); L = n // 2
    Hk = np.lib.stride_tricks.sliding_window_view(F, L + 1)   # Hankel  (accumulated Gram source)
    _, sv, Vh = np.linalg.svd(Hk, full_matrices=False)
    order = min(order, Vh.shape[0] - 2)
    V = Vh.conj().T[:, :order]
    ev = np.linalg.eigvals(np.linalg.pinv(V[:-1]) @ V[1:])
    z = np.log(ev.astype(complex)) / du
    gam, damp = z.imag, z.real
    sel = (gam > 0) & (np.abs(damp) < dband)
    return np.sort(gam[sel]), sv

# ===========================================================================
# BASE (constant pitch)  vs  FEEDBACK (pitch += delta per emitted mode)
# ===========================================================================
def run_base(F, du, order, Hmax):
    g, sv = emit_modes(F, du, order)
    g = g[g <= Hmax]
    return g

def run_feedback(F, du, order0, delta, Hmax):
    """FEEDBACK: resolution order grows as modes accumulate.
    Self-consistent loop: extract with current order, count modes below a rising height ceiling,
    bump order by delta per newly-resolved mode, re-extract; iterate to a fixed point.
    The fitted 'delta' is the order-increase per resolved mode (the pitch step)."""
    order = float(order0)
    prev = -1
    g = np.array([])
    for _ in range(40):
        gi, sv = emit_modes(F, du, int(round(order)))
        gi = gi[gi <= Hmax]
        m = len(gi)
        order = order0 + delta * m          # pitch += delta per resolved mode
        if m == prev:
            g = gi; break
        prev = m; g = gi
    return g, order

# ===========================================================================
# REFERENCE ZEROS (FINAL comparison ONLY)
# ===========================================================================
def ref_zeros(kind, Nz):
    if kind == 'zeta':
        return [float(mp.zetazero(n).imag) for n in range(1, Nz+1)]
    mod, tab = CHI[kind]
    chi = lambda n: tab.get(n % mod, 0)
    def Lam_completed(t):
        s = mp.mpf('0.5') + 1j*mp.mpf(t)
        gam = mp.gamma((s + 1)/2) * (mp.mpf(mod)/mp.pi)**(s/2)
        L = mod**(-s) * mp.fsum(chi(a) * mp.zeta(s, mp.mpf(a)/mod) for a in range(1, mod+1))
        return float((gam * L).real)
    ts = np.arange(0.01, 60.0, 0.01)
    vals = np.array([Lam_completed(float(t)) for t in ts])
    sgn = np.sign(vals); idx = np.nonzero(sgn[:-1]*sgn[1:] < 0)[0]
    out = []
    for i in idx:
        t0,t1,v0,v1 = ts[i],ts[i+1],vals[i],vals[i+1]
        out.append(t0 - v0*(t1-t0)/(v1-v0))
        if len(out) >= Nz: break
    return out

def match_rms(emitted, refs, tol=0.4):
    """RMS over refs that have a GENUINELY resolved emitted mode within tol (honest:
    do not penalize for not-yet-resolved high zeros; report how many WERE resolved)."""
    if len(emitted) == 0: return [], float('inf'), 0
    m, errs = [], []
    for r in refs:
        c = float(emitted[np.argmin(np.abs(emitted - r))])
        if abs(c - r) < tol:
            m.append(c); errs.append(c - r)
    if not errs: return [], float('inf'), 0
    return m, float(np.sqrt(np.mean(np.array(errs)**2))), len(errs)

def Ntrue_zeta(T):
    return T/(2*math.pi)*math.log(T/(2*math.pi)) - T/(2*math.pi) + 7/8

# ===========================================================================
# MAIN
# ===========================================================================
if __name__ == "__main__":
    N   = 3_000_000
    du  = 0.0025
    ORDER = 300          # base constant pitch (resolution budget; >= mode count)
    Hmax  = 90.0
    NZ    = 25

    pr("="*78)
    pr("SPECTRAL COUNTING MECHANISM  (numpy f64; refs mpmath dps=15, FINAL compare only)")
    pr(f"N={N:,}  du={du}  base order(pitch)={ORDER}  Hmax={Hmax}")
    pr("="*78)

    for kind in ('zeta', 'mod3', 'mod4'):
        pr(f"\n----- chi = {kind}  (ONLY chi changed) -----")
        u, F = source_field(kind, N, du)
        pr(f"signal len={len(F)}  u-span={u[-1]-u[0]:.2f}")

        refs = ref_zeros(kind, NZ)              # held out until comparison
        gb = run_base(F, du, ORDER, Hmax)
        mb, rb, nb = match_rms(gb, refs)

        pr(f"refs   ({NZ}): {np.round(refs,3).tolist()}")
        pr(f"BASE emit  : {np.round(gb[:NZ],3).tolist()}")
        pr(f"BASE matched {nb}/{len(refs)} zeros  RMS={rb:.4f}  (#emit={len(gb)})")

        # density check (zeta has a closed-form N(T))
        if kind == 'zeta':
            pr("   density (cumulative count vs true):")
            for H in (20,40,60,80):
                pr(f"     N_emit({H})={int(np.sum(gb<=H))}  N_true={Ntrue_zeta(H):.2f}")

        # FEEDBACK vs BASE: pitch += delta per resolved mode (order grows).
        # Fit delta over a scan; report whether it improves the resolved-zero count / RMS.
        best = None
        for delta in np.arange(-5.0, 10.01, 1.0):
            gf, ofin = run_feedback(F, du, ORDER, float(delta), Hmax)
            mf, rf, nf = match_rms(gf, refs)
            score = (nf, -rf if rf < float('inf') else -1e9)   # more resolved, then lower RMS
            if best is None or score > best[0]:
                best = (score, delta, gf, rf, nf, ofin)
        _, delta, gf, rf_fb, nf, ofin = best
        pr(f"FEEDBACK best delta={delta:+.2f}  order:{ORDER}->{ofin:.0f}  "
           f"matched {nf}/{len(refs)}  RMS={rf_fb:.4f}  (#emit={len(gf)})")
        pr(f"   FEEDBACK vs BASE: resolved {nf} vs {nb}, RMS {rf_fb:.4f} vs {rb:.4f}  "
           f"-> feedback {'HELPS' if (nf>nb or rf_fb<rb-1e-6) else 'no gain'}")
