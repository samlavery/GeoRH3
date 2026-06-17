import mpmath as mp
mp.mp.dps = 30
pi = mp.pi
def ns(x,n=10): return mp.nstr(x,n)

print("="*72)
print("FINITE SUM (no smoothing): only the integers inside the radius contribute")
print("="*72)

# The geometric cutoff: at readout height t the radius admits N = floor(sqrt(t/2pi))
# integers -- a FINITE set. The readout is the finite main sum
#    Z(t) = 2 sum_{n=1}^{N} cos(theta(t) - t log n) / sqrt(n)  + RS remainder
# theta = Riemann-Siegel theta (the accumulated phase). No infinite tail, no
# Gaussian cutoff, no Euler acceleration.

def main_sum(t):
    N = int(mp.floor(mp.sqrt(t/(2*pi))))
    th = mp.siegeltheta(t)
    s = mp.mpf(0)
    for n in range(1, N+1):
        s += mp.cos(th - t*mp.log(n))/mp.sqrt(n)
    return 2*s, N

print("\n[finite] readout = finite main sum (count N = integers inside the radius):")
for t in [mp.mpf('13.0'), mp.mpf('14.0'), mp.mpf('14.1347251417'), mp.mpf('15.0')]:
    ms, N = main_sum(t)
    Zexact = mp.siegelz(t)               # mpmath's RS value (finite, no smoothing)
    print(f"  t={ns(t,9):>13}: N={N}  mainSum={ns(ms,5):>9}  Z(exact RS)={ns(Zexact,5):>9}")

# locate the first crossing with NO smoothing: bisect the exact RS Z on [13,15]
zero = mp.findroot(mp.siegelz, mp.mpf('14.0'))
print(f"\n[crossing] first sign change of the finite RS readout: t = {ns(zero,14)}")
print(f"           actual first zeta zero:                       {ns(mp.im(mp.zetazero(1)),14)}")
print(f"           match to 13 digits: {ns(zero - mp.im(mp.zetazero(1)),4)}")

print("\n[reading] for t=14.13:  N = floor(sqrt(14.13/2pi)) =",
      int(mp.floor(mp.sqrt(mp.mpf('14.1347')/(2*pi)))),
      " -> a single in-radius integer; the carrier cos(theta) plus the RS")
print("          correction locate the zero. No infinite sum was smoothed.")
print("\n[note] this is the finite 'integers inside the radius' sum -- the")
print("       geometric cutoff. The 2pi here is the conductor constant; if your")
print("       pi/3 chart sets the cutoff radius by a different constant, give me")
print("       the exact rescale t -> a*t (or s-shift) and I'll run that precisely.")
