"""
Diagnose the n=2 weak spot. The truncated nontrivial-zero sum omits:
  - the log term  -(b_chi + log? ) constant (smooth, killed by DIFFERENCE),
  - the trivial-zero sum: for ODD chi, trivial zeros at s=-1,-3,-5,...
    contributing  sum_{m>=0} x^{-(2m+1)}/(2m+1) = (1/2) log((1+1/x)/(1-1/x)) = atanh(1/x).
The trivial part T(x) = - sum_{m>=0} x^{-(2m+1)}/(2m+1) = -atanh(1/x).
At small x this is NON-negligible and varies fast => its DIFFERENCE across the
window is what we're missing at n=2. Add it back and re-check n=2,4,5.

Also: the truncation at gamma_max=3502 limits real-space resolution to
dx ~ pi*x/gamma_max. For n=2: dx ~ 0.0028 -> fine; the n=2 error is the trivial
sum + the log-derivative tail, NOT lack of zeros. Confirm.
"""
import math

gammas = []
with open('lchi3_zeros_record.txt') as f:
    for line in f:
        line = line.strip()
        if not line or line.startswith('#'):
            continue
        toks = line.split()
        if len(toks) < 2:
            continue
        gammas.append(float(toks[1]))
gammas.sort()


def chi3(n):
    r = n % 3
    return 0 if r == 0 else (1 if r == 1 else -1)


def vm(n):
    if n < 2:
        return 0.0, None
    m, p = n, 2
    while p * p <= m:
        if m % p == 0:
            while m % p == 0:
                m //= p
            return (math.log(p), p) if m == 1 else (0.0, None)
        p += 1
    return math.log(n), n


def psi_nt(x):
    """nontrivial-zero part only."""
    lx = math.log(x); acc = 0.0
    for g in gammas:
        c = math.cos(g * lx); s = math.sin(g * lx)
        acc += (c * 0.5 + s * g) / (0.25 + g * g)
    return -2.0 * math.sqrt(x) * acc


def trivial_part(x):
    # ODD chi: trivial zeros at -1,-3,-5,...  -sum x^{rho}/rho over these = -atanh(1/x)
    return -math.atanh(1.0 / x) if x > 1 else 0.0


def D(n, h=0.5, corr=False):
    a = psi_nt(n + h) - psi_nt(n - h)
    if corr:
        a += trivial_part(n + h) - trivial_part(n - h)
    return a


print(" n  true   D(no corr)   D(+trivial)   chi3")
for n in [2, 4, 5, 7, 8, 11, 13]:
    lam, p = vm(n)
    tj = chi3(n) * lam if lam > 0 else 0.0
    print("%2d  %+7.4f   %+8.4f    %+8.4f    %+d" %
          (n, tj, D(n, corr=False), D(n, corr=True), chi3(n)))

print("\nn=2 detail: true=-0.6931")
print("  D no corr   = %+.4f" % D(2, corr=False))
print("  trivial diff= %+.4f" % (trivial_part(2.5) - trivial_part(1.5)))
print("  D +trivial  = %+.4f  <- should land near -0.6931" % D(2, corr=True))
