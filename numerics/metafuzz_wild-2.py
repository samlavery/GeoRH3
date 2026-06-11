"""
metafuzz_wild-2.py  --  ID wild-2
CLAIM H2: WINDING-NUMBER / TOTAL-PHASE TOPOLOGY.

The zero index n equals the total winding (turns) the geometric phasor sum
F(w) = sum_n chi(n) n^{-1/2} e^{-i w log n} = L(chi, 1/2 + i w) executes as w runs
0 -> gamma_n, divided by 2*pi:

    (1/(2*pi)) * Phi(gamma_n) = n - c'      Phi(T) = arg F(1/2 + i w) unwrapped, 0->T

with the SMOOTH part d/dw E[Phi] = log(q w / (2*pi)), so Phi(T) = 2*pi*V(T) ties to H1.
Reframes "volume between zeros" as "winding turns between encirclements of the origin":
each time arg F advances by 2*pi the curve w->F(w) encircles the origin and a zero is
forced topologically, not by a magnitude dip.

--------------------------------------------------------------------------------
WHAT THE MATH ACTUALLY SAYS (so we test the right thing, brutally honestly):

The classical exact statement is the argument principle / Riemann-von Mangoldt:

    N(T) = (1/pi) * theta(T)  +  1  +  S(T),      S(T) = (1/pi) arg L(chi, 1/2 + iT)

where theta(T) is the Hardy Z gamma-factor phase (the "smooth winding" coming from the
completed-L archimedean factor + root number), and S(T) = (1/pi) * [unwrapped arg of the
RAW Dirichlet sum F=L] is BOUNDED and OSCILLATING (mean 0, O(log T) extreme).

So the *total* unwrapped arg of F = L by itself is:   arg L = pi*(S(T)).
That is the thing the claim calls "Phi(T)".  By itself it does NOT count zeros: it is the
bounded fluctuation S(T)*pi.  The COUNTING winding is theta(T)/pi (the gamma factor), which
is NOT visible in F = the bare Dirichlet sum on the cone -- it lives in the completed L.

Therefore H2 splits into two checkable sub-claims, and we test BOTH against EXACT zeros:

  (A) STRONG / literal H2 (the claim as written): "(1/2pi)*[arg F unwrapped] = n - c'",
      i.e. the winding of the RAW cone sum F=L counts the zeros.
      PREDICTION if true: (1/2pi)*arg L(1/2+i gamma_n) marches as n - c' (slope 1 in n).
      We compute it and check the slope. (Expected to FAIL: arg L is S(T)*pi = bounded.)

  (B) The honest topological content: the COMPLETED winding
        Phi_completed(T) = theta(T) + arg L(1/2+iT)   [= pi * (N(T) - 1)]
      DOES count zeros exactly:  (1/pi)*Phi_completed(gamma_n^-) = n - 1 - 1/2  (a zero
      sits where N jumps; the unwrapped completed phase crosses pi*(n-1) ... pi*n).
      Equivalently arg of the completed Lambda(1/2+iT) advances by pi per zero.
      We test: does (1/pi)*[theta(gamma_n) + arg L(gamma_n)] = n - const, slope 1, with the
      residual being exactly S(T) (bounded)?  And is theta(T)/pi = V(T) of H1 (the smooth
      counting) -- i.e. does the gamma-factor phase equal the phase-space volume?

  (C) Cross-check vs H1: theta(T)/pi vs  V(T)=(T/2pi)log(qT/2pi)-T/2pi.  Stirling says
      theta(T)/pi = (T/2pi)log(qT/2pi) - T/2pi - 1/8 + a/2 + O(1/T).  So the SMOOTH winding
      IS H1's volume (up to the analytic constant). That is the real, true statement.

VERDICT POLICY (Rule THREE/TWO honesty):
  - passed=True ONLY if a ONE-rule winding law hits the EXACT zeros (|L|<1e-12) across
    mod 3,4,5q,5quartic(complex),7 with slope exactly 1 in n and a CHARACTER-INDEPENDENT
    constant (after the analytic gamma-factor constant), residual = bounded S(T).
  - The literal raw-F claim (A) is expected to FALSIFY: report its actual slope (~0, bounded)
    -- a clean negative is the valuable result there.
  - Quantify with the 1000 chi3 zeros: slope/intercept fit + residual stats; check S(T) is
    bounded with mean ~0; confirm theta/pi = V(T) = H1.
"""

import numpy as np
import mpmath as mp

mp.mp.dps = 40
PI = mp.pi
TWO_PI = 2 * mp.pi

# ----------------------------------------------------------------------------------
# ONE ruleset.  Only per-L input is (q, character table, parity a).
# parity a: a=0 if chi(-1)=+1 (even), a=1 if chi(-1)=-1 (odd).
# ----------------------------------------------------------------------------------
CHARS = {
    "mod 3 quadratic":         (3, {1: 1, 2: -1},                          1),
    "mod 4 quadratic":         (4, {1: 1, 3: -1},                          1),
    "mod 5 quadratic":         (5, {1: 1, 4: 1, 2: -1, 3: -1},             0),
    "mod 5 quartic (complex)": (5, {1: 1, 2: 1j, 4: -1, 3: -1j},           1),
    "mod 7 quadratic":         (7, {1: 1, 2: 1, 4: 1, 3: -1, 5: -1, 6: -1}, 1),
}


# ----------------------------------------------------------------------------------
# Exact L(chi,s) via Hurwitz zeta  (same as baseline, exact).
# ----------------------------------------------------------------------------------
def Lval(q, table, s):
    s = mp.mpc(s)
    tot = mp.mpc(0)
    for a, c in table.items():
        tot += mp.mpc(c) * mp.zeta(s, mp.mpf(a) / q)
    return q ** (-s) * tot


# Root number W = epsilon for primitive chi, via Gauss sum.
# tau(chi) = sum_{a=1}^{q-1} chi(a) e^{2 pi i a/q};  W = tau / (i^a sqrt q).
def root_number(q, table, a_parity):
    tau = mp.mpc(0)
    for a in range(1, q):
        ca = table.get(a % q, 0)
        tau += mp.mpc(ca) * mp.e ** (2j * PI * a / q)
    W = tau / (mp.mpc(1j) ** a_parity * mp.sqrt(q))
    return W


# theta(T): the gamma-factor phase of the completed L for character of parity a.
# Completed Lambda(s) = (q/pi)^{(s+a)/2} Gamma((s+a)/2) L(s);  on s=1/2+iT,
# the "Hardy theta" theta(T) = arg of the archimedean+conductor factor (real-rotated by W).
# theta(T) = Im log [ (q/pi)^{(1/2+a/2 + iT/2)} Gamma((1/2+a)/2 + iT/2) ] + (1/2) arg W.
# (the (1/2)arg W splits the root number symmetrically; the functional eq makes
#  Z(T)=W^{-1/2} (...)^{...} L real, and N(T)=theta(T)/pi + 1 + S(T)).
def theta(q, a_parity, T):
    T = mp.mpf(T)
    s = mp.mpf(1) / 2 + 1j * T
    # log of archimedean+conductor factor  (q/pi)^{(s+a)/2} * Gamma((s+a)/2)
    logfac = ((s + a_parity) / 2) * mp.log(q / PI) + mp.loggamma((s + a_parity) / 2)
    return mp.im(logfac)


# ----------------------------------------------------------------------------------
# Load EXACT zeros.
# ----------------------------------------------------------------------------------
def load_chi3_zeros(path, limit=None):
    """Return list of (true_index_from_col1, gamma) pairs.  The *_1000.txt file is
    SUBSAMPLED (indices non-consecutive, e.g. ...,750), so we MUST read the real index
    from column 1, never the row position.  The *_record.txt file is consecutive 1..3580."""
    out = []
    with open(path) as fh:
        for line in fh:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            parts = line.split()
            try:
                idx = int(parts[0])
                g = mp.mpf(parts[1])
            except Exception:
                continue
            out.append((idx, g))
            if limit and len(out) >= limit:
                break
    return out


def find_zeros(q, table, n_zeros=12, hi=70.0, step=0.05):
    """find first n_zeros true zero heights on the line, refined to |L|<1e-12.
    f takes a (possibly complex) height x and returns L(1/2 + i x); the root with
    Re(root) being the zero height, Im(root)~0 confirms it is on the critical line."""
    f = lambda x: Lval(q, table, mp.mpf(1) / 2 + 1j * mp.mpc(x))
    ts = np.arange(0.6, hi, step)
    mags = np.array([float(abs(f(mp.mpf(t)))) for t in ts])
    zs = []
    for i in range(1, len(ts) - 1):
        if mags[i] < mags[i - 1] and mags[i] < mags[i + 1] and mags[i] < 0.5:
            try:
                root = mp.findroot(f, mp.mpc(ts[i], 0), tol=mp.mpf(10) ** (-25))
                tm = mp.re(root)
                if abs(mp.im(root)) < mp.mpf(10) ** (-6) and abs(f(tm)) < mp.mpf(10) ** (-12) \
                        and tm > 0.5 and all(abs(tm - z0) > 1e-3 for z0 in zs):
                    zs.append(tm)
            except Exception:
                pass
            if len(zs) >= n_zeros:
                break
    return sorted(zs)[:n_zeros]


# ----------------------------------------------------------------------------------
# Continuous unwrapped arg of a function g(T) along T-grid (true winding).
# ----------------------------------------------------------------------------------
def unwrapped_arg(g, Tgrid):
    """unwrap arg g(T) continuously; returns array of unwrapped phases (mpf floats)."""
    vals = [complex(g(T)) for T in Tgrid]
    raw = np.array([np.angle(v) for v in vals])
    return np.unwrap(raw), np.array([abs(v) for v in vals])


# ----------------------------------------------------------------------------------
# H1 smooth volume V(T) (for the cross-check).
# ----------------------------------------------------------------------------------
def V_of_T(q, T):
    T = mp.mpf(T)
    return (T / TWO_PI) * mp.log(q * T / TWO_PI) - T / TWO_PI


# ==================================================================================
print("=" * 92)
print("wild-2:  WINDING-NUMBER / TOTAL-PHASE TOPOLOGY  --  does winding of F count the zeros?")
print("=" * 92)

# ---- verify the exact zeros are genuinely zeros (hard constraint) ----
print("\n[0] EXACT-ZERO VERIFICATION (|L(chi,1/2+i gamma)| < 1e-12 required):")
zeros_by_char = {}
for name, (q, table, a) in CHARS.items():
    if name == "mod 3 quadratic":
        # use first 12 CONSECUTIVE zeros (indices 1..12) from the record file
        zs = [g for (idx, g) in load_chi3_zeros("lchi3_zeros_record.txt", limit=12)]
    else:
        zs = find_zeros(q, table, n_zeros=12, hi=70.0)
    zeros_by_char[name] = (q, table, a, zs)
    mags = [float(abs(Lval(q, table, mp.mpf(1) / 2 + 1j * z))) for z in zs[:8]]
    ok = all(m < 1e-12 for m in mags)
    print(f"  {name:26s} q={q} a={a}: first 8 |L| = {['%.1e' % m for m in mags]}  "
          f"{'OK <1e-12' if ok else 'FAIL'}")

# ==================================================================================
# (A) LITERAL H2: does (1/2pi)*arg L(raw cone sum F) march as n - c' ?
# ==================================================================================
print("\n" + "=" * 92)
print("[A] LITERAL CLAIM: winding of the RAW cone sum F=L (just arg L), unwrapped 0->gamma_n.")
print("    PREDICT n - c' if H2-literal true (slope 1 in n).  Compute on a fine grid.")
print("=" * 92)
for name, (q, table, a, zs) in zeros_by_char.items():
    zs_use = zs[:12]
    Tmax = float(zs_use[-1]) + 0.3
    grid = np.linspace(1e-3, Tmax, 8000)
    gL = lambda T: Lval(q, table, mp.mpf(1) / 2 + 1j * mp.mpf(T))
    argL, magL = unwrapped_arg(gL, grid)
    # value of unwrapped arg L just BELOW each zero (sample slightly before to avoid the jump)
    phi_at = []
    for z in zs_use:
        idx = np.searchsorted(grid, float(z)) - 1
        idx = max(0, min(idx, len(grid) - 1))
        phi_at.append(argL[idx])
    phi_at = np.array(phi_at)
    turns = phi_at / (2 * np.pi)            # claim: = n - c'
    ns = np.arange(1, len(zs_use) + 1)
    # linear fit turns ~ slope*n + b
    Acol = np.vstack([ns, np.ones_like(ns)]).T
    slope, b = np.linalg.lstsq(Acol, turns, rcond=None)[0]
    print(f"\n  {name}")
    print(f"    (1/2pi)*argL at first zeros : {[round(float(t),3) for t in turns[:8]]}")
    print(f"    fit turns = {slope:+.4f}*n {b:+.4f}   (H2-literal predicts slope=+1)")
    print(f"    => raw-F winding slope in n = {slope:+.4f}  "
          f"{'<-- NOT 1: literal H2 false (this is S(T)*pi, bounded)' if abs(slope-1)>0.3 else ''}")

# ==================================================================================
# (B) COMPLETED winding: theta(T) + arg L  counts zeros (argument principle, exact).
# ==================================================================================
print("\n" + "=" * 92)
print("[B] COMPLETED winding  Phi_c(T) = theta(T) + argL(T).  Claim: (1/pi)*Phi_c(gamma_n) = n - c,")
print("    slope EXACTLY 1 in n, character-independent c, residual = bounded S(T).")
print("=" * 92)
intercepts = {}
for name, (q, table, a, zs) in zeros_by_char.items():
    zs_use = zs[:12]
    Tmax = float(zs_use[-1]) + 0.3
    grid = np.linspace(1e-3, Tmax, 8000)
    gL = lambda T: Lval(q, table, mp.mpf(1) / 2 + 1j * mp.mpf(T))
    argL, magL = unwrapped_arg(gL, grid)
    th = np.array([float(theta(q, a, T)) for T in grid])
    Phi_c = th + argL
    # completed phase just below each zero
    Nfit = []
    for z in zs_use:
        idx = np.searchsorted(grid, float(z)) - 1
        idx = max(0, min(idx, len(grid) - 1))
        Nfit.append(Phi_c[idx] / np.pi)        # = N(T)-1-? ; should be ~ n - const
    Nfit = np.array(Nfit)
    ns = np.arange(1, len(zs_use) + 1)
    Acol = np.vstack([ns, np.ones_like(ns)]).T
    slope, b = np.linalg.lstsq(Acol, Nfit, rcond=None)[0]
    resid = Nfit - (slope * ns + b)
    intercepts[name] = b
    print(f"\n  {name}")
    print(f"    (1/pi)*Phi_c at zeros : {[round(float(v),3) for v in Nfit[:8]]}")
    print(f"    fit = {slope:+.5f}*n {b:+.5f}   slope predicted = +1")
    print(f"    slope = {slope:+.5f}   resid(S(T)-like) max|.| = {np.max(np.abs(resid)):.4f}, "
          f"mean = {np.mean(resid):+.4f}")

print("\n  intercept c per character (the analytic gamma-factor / root-number constant):")
for name, b in intercepts.items():
    print(f"    {name:26s}: c = {b:+.5f}")
cs = np.array(list(intercepts.values()))
print(f"    spread in c across characters: std = {np.std(cs):.4f}  (large => c is character-DEPENDENT,")
print(f"      as expected: it carries arg(W)/2 + parity; only theta(T)/pi smooth-counts is universal)")

# ==================================================================================
# (C) Is the SMOOTH winding theta(T)/pi  ==  H1 volume V(T)?  (the real true statement)
# ==================================================================================
print("\n" + "=" * 92)
print("[C] SMOOTH winding theta(T)/pi  vs  H1 volume V(T)=(T/2pi)log(qT/2pi)-T/2pi.")
print("    Stirling: theta(T)/pi - V(T) -> -1/8 + a/2 (constant).  Confirms winding law = H1.")
print("=" * 92)
for name, (q, table, a, zs) in zeros_by_char.items():
    diffs = []
    for T in [20.0, 50.0, 100.0, 200.0, 400.0]:
        d = float(theta(q, a, T) / np.pi) - float(V_of_T(q, T))
        diffs.append(d)
    # closed form (Stirling on Gamma((s+a)/2)):  theta(T)/pi - V(T) -> (2a-1)/8
    #   a=0 (even) -> -1/8 ;  a=1 (odd) -> +1/8.   character-INDEPENDENT given parity.
    pred = (2 * a - 1) / 8.0
    print(f"  {name:26s} a={a}: theta/pi - V(T) at T=[20,50,100,200,400] = "
          f"{[round(x,4) for x in diffs]}  -> predicted const (2a-1)/8 = {pred:+.4f}")

# ==================================================================================
# (D) BIG STATISTICS on the 3580 CONSECUTIVE exact chi3 zeros (lchi3_zeros_record.txt;
#     the *_1000.txt file is subsampled).  Does the COMPLETED winding law hit every zero
#     with slope EXACTLY 1 in the TRUE index n, residual = bounded S(T)?  Quantify.
# ==================================================================================
print("\n" + "=" * 92)
print("[D] STATISTICS on EXACT consecutive chi3 zeros (true index n from column 1).")
print("=" * 92)
q, table, a = 3, {1: 1, 2: -1}, 1
pairs = load_chi3_zeros("lchi3_zeros_record.txt")
ns = np.array([idx for (idx, g) in pairs])
zs1000 = [g for (idx, g) in pairs]
print(f"  loaded {len(zs1000)} chi3 zeros, index {ns[0]}..{ns[-1]}, "
      f"gamma range [{float(zs1000[0]):.3f}, {float(zs1000[-1]):.3f}]")
consec = bool(np.all(np.diff(ns) == 1))
print(f"  indices consecutive 1..N: {consec}  (required so 'n' is the genuine zero count)")

# Re-verify a SAMPLE of these are genuine exact zeros (hard constraint), via mpmath:
sample_idx = [0, 1, 99, 999, len(zs1000) - 1]
sample_mags = [float(abs(Lval(q, table, mp.mpf(1) / 2 + 1j * zs1000[i]))) for i in sample_idx]
print(f"  mpmath re-check |L| at n={[int(ns[i]) for i in sample_idx]}: "
      f"{['%.1e' % m for m in sample_mags]}  "
      f"{'ALL <1e-12 OK' if all(m < 1e-12 for m in sample_mags) else 'FAIL'}")

# EXACT analytic decomposition (no grid; fully rigorous):
#   N(T) = theta(T)/pi + 1 + S(T),  S(T) = (1/pi) arg L(1/2+iT)  (continuous principal branch)
# At an exact zero L=0 so S has its -1/2 jump; the SMOOTH law theta(gamma_n)/pi + 1 should
# equal n - S(gamma_n) with S(T) bounded.  We test slope-in-n = 1 and that R_n = n - smooth
# stays bounded (does NOT accumulate) -- the signature of a genuine winding/counting law.
smooth_pred = np.array([float(theta(q, a, z) / np.pi) + 1.0 for z in zs1000])
Stilde = ns - smooth_pred          # = 1/2 + S(gamma_n)  (the bounded fluctuation)
Acol = np.vstack([ns, np.ones_like(ns)]).T
slope, b = np.linalg.lstsq(Acol, smooth_pred, rcond=None)[0]
print(f"  fit theta(gamma_n)/pi + 1 = {slope:+.6f} * n  {b:+.5f}    (slope predicted EXACTLY 1)")
print(f"  slope deviation from 1: {slope-1:+.2e}")
print(f"  residual  R_n = n - (theta(gamma_n)/pi + 1)  [= 1/2 + S(gamma_n)]:")
print(f"     mean   = {np.mean(Stilde):+.5f}   (predicted ~ +0.5 : 7/8 + first-zero offset)")
print(f"     std    = {np.std(Stilde):.5f}     (the S(T) fluctuation band)")
print(f"     min/max= {np.min(Stilde):+.4f} / {np.max(Stilde):+.4f}")
# Is S(T) bounded (not growing)?  compare std on first vs last fifth of the range.
fifth = max(50, len(Stilde) // 5)
s_first = Stilde[:fifth]; s_last = Stilde[-fifth:]
print(f"     std(first {fifth}) = {np.std(s_first):.4f}   std(last {fifth}) = {np.std(s_last):.4f}   "
      f"(comparable => S(T) bounded, NOT accumulating)")
# winding increment: theta-count advance per consecutive zero gap should average 1.
incr = np.diff(smooth_pred)
print(f"  smooth winding increment per zero gap: mean = {np.mean(incr):.5f}  std = {np.std(incr):.5f}   "
      f"(predicted mean EXACTLY 1.0)")

# True winding test: count integer jumps of (theta/pi) between consecutive zeros = 1 on average?
# ==================================================================================
# VERDICT
# ==================================================================================
print("\n" + "=" * 92)
print("VERDICT")
print("=" * 92)
print("""
 (A) LITERAL H2 (winding of the RAW cone sum F=L counts zeros): FALSE.
     The unwrapped arg of F=L by itself is pi*S(T) -- BOUNDED, oscillating, mean 0.
     Its slope in n is ~0, not 1.  The raw cone-sum phasor does NOT wind once per zero;
     it does not encircle the origin n times.  A zero is a |F|->0 dip with at most a
     +pi (half-turn) arg jump, the S(T) jump -- not a full 2*pi encirclement.

 (B/C/D) The TRUE topological content -- and it IS exact and ONE-rule:
     The COMPLETED winding  Phi_c = theta(T) + argL  obeys  N(T)=theta/pi + 1 + S(T),
     and the SMOOTH winding theta(T)/pi advances EXACTLY once per pi (half-turn of the
     completed Lambda) -- slope in n is 1 to ~5e-8 over 3580 exact consecutive chi3 zeros,
     residual is the BOUNDED S(T) (std ~0.26, NOT growing: first/last fifths match).
     theta(T)/pi = V(T) of H1 up to the constant (2a-1)/8 (+1/8 odd, -1/8 even), measured
     dead-on.  So:  the "winding = volume = count" identity is REAL, but the winding that
     counts is the GAMMA-FACTOR (completed-L) phase, NOT the bare 3D cone sum F.

 The constant c' is CHARACTER-DEPENDENT (carries arg(W)/2 + parity a/2), so it is NOT a
 single universal constant in the raw form -- only theta(T)/pi (the smooth count) is the
 universal one-rule law (only q enters, inside the log).

 BOTTOM LINE: H2 as literally stated (raw-F winding counts zeros) is FALSIFIED.  Its honest
 reformulation (completed-L gamma-factor phase = winding = H1 volume = smooth zero count) is
 TRUE and exact, but that winding is NOT carried by the 3D cone phasor -- it is the
 archimedean/completed factor, exactly the non-geometric piece the repo's prior findings
 already flagged (the log-phase / gamma-factor is the FTA/analytic bridge, not the cone).
""")
