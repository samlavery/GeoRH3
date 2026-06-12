"""
radial_step_blocky_test.py

THE REAL TEST.  Build A (smooth per-integer log height) hits every zero -- it IS
the analytic L made geometric.  Now QUANTIZE it: make the geometry BLOCKY/stepped
and ask whether stepping still tracks individual zeros (FLUCTUATION) or only the
mean spacing.

Three blocky builds, each a real 3D solid with phasors:

  (B1) STEP-HEIGHT (radial+pitch step per block, height piecewise-CONSTANT in block):
       height z_n = z_block(k) constant within block k; blocks = log-bins of n.
       This destroys the within-block phase -> expect MEAN only.

  (B2) STAIRCASE-LOG: height z_n = log(n) but ROUNDED to a per-block step (the
       height takes a discrete value per block, the staircase of log).  Sweep the
       step size; measure how coarse the staircase can be before the zeros blur.

  (B3) FEEDBACK BLOCKY: the block's own pitch p_k = pi/gap_k sets where the next
       boundary falls; check the fixed-point boundaries against the zeros.  Radius
       steps geometrically; within a block height advances LINEARLY in local index
       (so per-integer phase survives) but the SLOPE steps per block.  This is the
       genuinely blocky helix that can still carry per-integer phase.

We measure for each: do |resultant(w)| minima land on the gamma_k (FLUCTUATION) or
only reproduce the average spacing (MEAN)?  Off-zero discrimination included.
"""
import numpy as np
import mpmath as mp
mp.mp.dps = 25

def chi3(n):
    r = n % 3
    return 1.0 if r == 1 else (-1.0 if r == 2 else 0.0)

def load_zeros(path="lchi3_zeros_1000.txt", k=20):
    g = []
    with open(path) as f:
        for ln in f:
            ln = ln.strip()
            if ln and not ln.startswith("#"):
                g.append(float(ln.split()[1]))
    return np.array(sorted(g))[:k]
GAMMA = load_zeros(k=20)

def resultant(phase, amp, sign, w):
    a = w * phase
    return np.hypot(np.sum(sign*amp*np.cos(a)), np.sum(sign*amp*np.sin(a)))

def find_minima(ws, vals, thresh):
    out = []
    for i in range(1, len(ws)-1):
        if vals[i] < vals[i-1] and vals[i] < vals[i+1] and vals[i] < thresh:
            out.append((ws[i], vals[i]))
    return out

def score_against_zeros(mins, tol=0.02):
    """How many gamma_k are matched by a minimum within tol; mean |dw|."""
    matched = 0; ds = []
    for g in GAMMA[:12]:
        if mins:
            ww = np.array([m[0] for m in mins])
            j = np.argmin(np.abs(ww - g))
            d = abs(ww[j]-g)
            if d < tol:
                matched += 1; ds.append(d)
    return matched, (np.mean(ds) if ds else float('nan'))

N = 40000
n = np.arange(1, N+1).astype(float)
sign = np.array([chi3(int(k)) for k in n])
R_area = np.sqrt(n)
amp = 1.0 / R_area               # n^{-1/2}, earned from area law
logn = np.log(n)
ws = np.linspace(6.0, 35.0, 7000)

print("="*78)
print("BLOCKY RADIAL-STEP TESTS: does stepping keep the FLUCTUATION or only MEAN?")
print("="*78)

# ---- B1: piecewise-CONSTANT height per block (one block per unit of log n) ----
def build_B1(block_width):
    """height constant within a block of log-width block_width; radius steps too."""
    blk = np.floor(logn / block_width)              # block index
    z = blk * block_width                            # height: bottom of the block (constant in block)
    return z
print("\n--- B1: height piecewise-CONSTANT per block (kills within-block phase) ---")
for bw in [0.05, 0.1, 0.25, 0.5]:
    z = build_B1(bw)
    vals = np.array([resultant(z, amp, sign, w) for w in ws])
    mins = find_minima(ws, vals, 0.02)
    matched, md = score_against_zeros(mins)
    print(f"  block_width(log)={bw:4.2f}: matched {matched}/12 zeros, mean|dw|={md:.4f}, #minima={len(mins)}")

# ---- B2: STAIRCASE log -- height = round(log n / step)*step (discrete log) ----
def build_B2(step):
    return np.round(logn / step) * step
print("\n--- B2: STAIRCASE log height = round(log n/step)*step (discrete log) ---")
for step in [0.001, 0.005, 0.01, 0.02, 0.05, 0.1]:
    z = build_B2(step)
    vals = np.array([resultant(z, amp, sign, w) for w in ws])
    mins = find_minima(ws, vals, 0.05)
    matched, md = score_against_zeros(mins)
    print(f"  step={step:5.3f}: matched {matched}/12 zeros (tol0.02), mean|dw|={md:.4f}, #minima={len(mins)}")

# ---- B3: FEEDBACK blocky -- radius steps geometric, height slope steps per block,
#          per-integer phase survives (linear in local index) ------------------
def build_B3(rho, slope_law):
    """Loops: loop k has radius rho^k, holds ~rho^k integers. Within a loop the
    height advances LINEARLY in local fraction with slope set by slope_law(k).
    This keeps per-integer phase but makes the slope step per block."""
    xs_z = np.zeros(N)
    n_i = 0
    running_z = 0.0
    k = 0
    while n_i < N:
        m_k = max(1, int(round(rho**k)))
        slope = slope_law(k)
        for j in range(m_k):
            if n_i >= N: break
            frac = j / m_k
            xs_z[n_i] = running_z + slope * frac
            n_i += 1
        running_z += slope
        k += 1
    return xs_z
print("\n--- B3: FEEDBACK blocky (radius geometric, height slope steps per block) ---")
# slope per block chosen so cumulative height ~ log(n): slope_k ~ const (since
# loop k holds rho^k integers and we want +const height per loop = +const per
# multiplicative factor rho in n = log step).
for rho, slope0 in [(np.e**0.5, 1.0), (np.e**0.25, 1.0), (1.5, 1.0), (2.0, 1.0)]:
    z = build_B3(rho, lambda k: slope0)
    # rescale so that z ~ log n (fit)
    m = n >= 50
    c = np.polyfit(logn[m], z[m], 1)
    zr = (z - c[1]) / c[0]
    res = np.std(zr[m]-logn[m])/np.std(logn[m])
    vals = np.array([resultant(zr, amp, sign, w) for w in ws])
    mins = find_minima(ws, vals, 0.05)
    matched, md = score_against_zeros(mins)
    print(f"  rho={rho:.4f}: z~log n residual {res:.4f}; matched {matched}/12 (tol0.02), mean|dw|={md:.4f}")

print("\n--- CONTROL: smooth z=log(n) exactly (Build A) ---")
vals = np.array([resultant(logn, amp, sign, w) for w in ws])
mins = find_minima(ws, vals, 0.05)
matched, md = score_against_zeros(mins)
print(f"  matched {matched}/12 (tol0.02), mean|dw|={md:.4f}, #minima={len(mins)}")
