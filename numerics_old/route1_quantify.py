"""
ROUTE 1 quantification. The raw window-difference D(n)=psi(n+h)-psi(n-h) already
recovers Lambda_chi(n). Quantify accuracy, optimal window h, and the chi3
'flat at multiples of 3' signature. Also a clean SIGN+presence classifier.
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


def true_jump(n):
    lam, p = vm(n)
    return chi3(n) * lam if lam > 0 else 0.0


def psi(x, smooth=0.0):
    if x <= 0:
        return 0.0
    lx = math.log(x)
    acc = 0.0
    for g in gammas:
        if smooth > 0.0:
            w = math.exp(-0.5 * (g * smooth) ** 2)
            if w < 1e-13:
                break
        else:
            w = 1.0
        c = math.cos(g * lx); s = math.sin(g * lx)
        acc += ((c * 0.5 + s * g) / (0.25 + g * g)) * w
    return -2.0 * math.sqrt(x) * acc


# Optimal window: the explicit-formula partial sum equals the SMOOTHED step
# (Cesaro/midpoint). At a true jump, psi(n+)-psi(n-) -> the jump. Choose h so the
# window (n-h, n+h) contains ONLY n among prime powers. h=0.5 is safe for n>=2.
def D(n, h=0.5, smooth=0.0):
    return psi(n + h, smooth) - psi(n - h, smooth)


print("=== Accuracy of raw window-difference (h=0.5, no smoothing) ===")
print(" n   chi3  true_jump   recon_D    abs_err   rel_err   class")
errs = []
for n in range(2, 50):
    tj = true_jump(n)
    d = D(n)
    ae = abs(d - tj)
    re = ae / abs(tj) if abs(tj) > 1e-9 else float('nan')
    lam, p = vm(n)
    if lam > 0 and chi3(n) != 0:
        errs.append(re)
        cls = 'PP-coprime'
    elif lam > 0 and chi3(n) == 0:
        cls = 'PP-mult3(flat)'
    else:
        cls = 'composite'
    print("%2d   %+d   %+8.4f   %+8.4f   %7.4f   %s   %s" %
          (n, chi3(n), tj, d, ae,
           ("%6.1f%%" % (re * 100)) if re == re else "   -  ", cls))

import statistics
print("\nMean rel-err on coprime prime powers (2..49): %.2f%%" %
      (100 * statistics.mean(errs)))
print("Median rel-err: %.2f%%" % (100 * statistics.median(errs)))

# --- SIGN classifier: does sign(D) == chi3(p) at every prime power, and |D| small at mult-3? ---
print("\n=== SIGN test: does sign(recon_D) match chi3 at prime powers? ===")
correct = 0; tested = 0
for n in range(4, 60):  # start at 4 (n=2,3 are the hardest low-res cases)
    lam, p = vm(n)
    if lam > 0 and chi3(n) != 0:
        d = D(n)
        tested += 1
        ok = (d > 0) == (chi3(n) > 0)
        correct += ok
        if not ok:
            print("  MISMATCH n=%d chi3=%+d D=%+.3f" % (n, chi3(n), d))
print("  sign matches: %d / %d prime-power positions (n=4..59)" % (correct, tested))

# --- FLATNESS at multiples of 3 ---
print("\n=== FLATNESS: |D| at multiples-of-3 prime powers vs nearby coprime PPs ===")
for n in [3, 9, 27]:
    d = D(n)
    print("  n=%2d (3^k):  |D|=%.4f   (true jump = 0)" % (n, abs(d)))
# compare scale: typical coprime PP |D|
ppd = [abs(D(n)) for n in range(4, 30) if vm(n)[0] > 0 and chi3(n) != 0]
print("  median |D| at coprime prime powers (n=4..29): %.4f" % statistics.median(ppd))
print("  => multiples-of-3 are ~%.0fx smaller (flat signature CONFIRMED if >>1)" %
      (statistics.median(ppd) / max(abs(D(3)), abs(D(9)), abs(D(27)))))

# --- background at composite coprime n (should also be ~0) ---
print("\n=== background |D| at non-prime-power coprime n (should be ~0) ===")
bg = [abs(D(n)) for n in range(4, 30) if vm(n)[0] == 0 and chi3(n) != 0]
print("  median |D| composite coprime: %.4f, max: %.4f" %
      (statistics.median(bg), max(bg)))
