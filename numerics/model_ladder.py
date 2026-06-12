"""
model_ladder.py -- THE ZERO-PARAMETER PURCHASE-MODEL TEST.

Model (kernel: HelixProduction Part 20, hilbertPolyaChainComplete steps 7-9):
rungs = unique crossings of the accumulation through successive quanta.
Accumulation (traversal phase): theta_chi(t) = Im logGamma((1/2+it+a)/2) + (t/2) log(q/pi).
Ray offset: arg(eps_chi)/2 -- from the ROOT NUMBER (theory), not fitted.
Rung n: the n-th solution of  theta_chi(t) + arg(eps)/2 = (k + 1/2)*pi  (k in Z),
taken in the monotone regime t > 2*pi/q, indexed in order. Paired with zeros in order.
ZERO free parameters: parity, conductor, root number only.
"""
import mpmath as mp, re, os
mp.mp.dps = 25
ZD = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'zeros')

SPECS = [
    ("L1_zeta_q1.txt",     1, 0, mp.mpc(1, 0)),   # eps placeholder; parsed from file when present
    ("L2_chi3_q3.txt",     3, 1, None),
    ("L3_chi4_q4.txt",     4, 1, None),
    ("L4_chi5quad_q5.txt", 5, 0, None),
    ("L5_chi5c4_q5.txt",   5, 1, None),
    ("L6_chi7quad_q7.txt", 7, 1, None),
]

def load(fname):
    zeros, eps = [], None
    with open(os.path.join(ZD, fname)) as f:
        for ln in f:
            if ln.startswith('#'):
                if 'root number eps' in ln:
                    tail = ln.rsplit('= ', 1)[-1].strip()
                    m = re.match(r'\(([-0-9.e]+)\s*([+-])\s*([0-9.e]+)j\)', tail)
                    if m:
                        re_, sgn, im_ = m.groups()
                        eps = mp.mpc(mp.mpf(re_), mp.mpf(im_) * (1 if sgn == '+' else -1))
            else:
                p = ln.split()
                if len(p) == 2: zeros.append(mp.mpf(p[1]))
    return zeros, eps

def theta(q, a, t):
    return mp.im(mp.loggamma((mp.mpf(1)/2 + 1j*t + a)/2)) + (t/2)*mp.log(mp.mpf(q)/mp.pi)

def ladder(q, a, eps, count):
    """zero-parameter rungs: ordered half-integer crossings of (theta + arg(eps)/2)/pi
    in the monotone regime t > 2*pi/q."""
    # Z = eps^(-1/2)*omega*L  =>  smooth rungs at theta - arg(eps)/2 = (k+1/2)*pi  (derived sign)
    off = -mp.arg(eps)/2
    F = lambda t: (theta(q, a, t) + off)/mp.pi
    t0 = 2*mp.pi/q + 1e-9          # theta' = (1/2)log(qt/2pi) > 0 beyond here
    rungs, t = [], t0
    fprev, step = F(t0), mp.mpf('0.05')
    # first half-integer level strictly above F(t0)
    lvl = mp.floor(fprev - mp.mpf(1)/2) + mp.mpf(3)/2
    while len(rungs) < count:
        t2 = t + step
        f2 = F(t2)
        while f2 >= lvl and len(rungs) < count:
            r = mp.findroot(lambda u: F(u) - lvl, (t + t2)/2)
            rungs.append(mp.mpf(r)); lvl += 1
        t, fprev = t2, f2
    return rungs

print("="*78)
print("ZERO-PARAMETER PURCHASE MODEL vs 600 CERTIFIED ZEROS  (nothing fitted)")
print("="*78)
overall = []
for fname, q, a, eps0 in SPECS:
    zeros, eps = load(fname)
    if eps is None: eps = eps0 if eps0 is not None else mp.mpc(1, 0)
    rungs = ladder(q, a, eps, len(zeros))
    ds = [float(rungs[i] - zeros[i]) for i in range(len(zeros))]
    gaps = [float(zeros[i+1] - zeros[i]) for i in range(len(zeros)-1)]
    mg = sum(gaps)/len(gaps)
    interlace_viol = 0
    for i in range(len(zeros)):
        lo = float(zeros[i-1]) if i > 0 else 0.0
        hi = float(zeros[i+1]) if i < len(zeros)-1 else float('inf')
        if not (lo < float(rungs[i]) < hi): interlace_viol += 1
    mean_off = sum(abs(d) for d in ds)/len(ds)
    max_off  = max(abs(d) for d in ds)
    name = fname.split('.')[0]
    print(f"\n{name}  (q={q}, a={a}, arg(eps)/pi={float(mp.arg(eps)/mp.pi):+.4f})")
    print(f"  rung1={float(rungs[0]):9.4f} vs zero1={float(zeros[0]):9.4f}   "
          f"rung100={float(rungs[-1]):9.4f} vs zero100={float(zeros[-1]):9.4f}")
    print(f"  mean|off|={mean_off:6.4f}  max|off|={max_off:6.4f}  mean gap={mg:5.3f}"
          f"  -> {mean_off/mg*100:4.1f}% of a gap   interlacing violations: {interlace_viol}/100")
    overall.append((name, mean_off/mg*100, max_off/mg*100, interlace_viol))
print("\n" + "="*78)
print(f"{'function':22s} {'mean%gap':>9s} {'max%gap':>9s} {'violations':>11s}")
for n, m, x, v in overall:
    print(f"{n:22s} {m:9.1f} {x:9.1f} {v:11d}")
print("="*78)
