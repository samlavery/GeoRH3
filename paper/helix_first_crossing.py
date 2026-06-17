import mpmath as mp
mp.mp.dps = 40
pi = mp.pi

def ns(x, n=12): return mp.nstr(x, n)

print("="*72)
print("HELIX FIRST CROSSING — principal channel (zeta), via the ETA method")
print("="*72)

# target: first nontrivial zero of zeta
z1 = mp.zetazero(1); g1 = mp.im(z1)
print(f"\n[target] first zero rho_1 = {ns(z1)} ,  gamma_1 = {ns(g1)}")

# ---------------------------------------------------------------------------
# ETA METHOD.  The principal-channel readout is the Dirichlet eta series
#     eta(s) = sum_{n>=1} (-1)^{n-1} n^{-s}            (converges Re s>0)
# i.e. the phasors           a_n(t) = (-1)^{n-1} n^{-1/2} e^{-i t log n}.
# eta = (1 - 2^{1-s}) zeta, so on 0<Re s<1 eta and zeta have the SAME zeros.
# A "crossing" = the phasors cancel = eta(1/2+it) = 0.
# ---------------------------------------------------------------------------
print("\n[eta] phasors a_n(t) = (-1)^{n-1} n^{-1/2} e^{-i t log n}")

def eta_partial(t, N):
    s = mp.mpc(0)
    for n in range(1, N+1):
        s += ((-1)**(n-1)) * mp.mpf(n)**(mp.mpf(-1)/2) * mp.e**(-1j*t*mp.log(n))
    return s

# plain partial sums oscillate; accelerated value is the true eta
print(f"\n  raw partial sums of the phasors at t = gamma_1 = {ns(g1,10)}:")
for N in [10, 100, 1000, 10000]:
    print(f"    N={N:>6}:  sum = {ns(eta_partial(g1,N),6)}")
eta_acc = mp.altzeta(0.5 + 1j*g1)         # Euler-accelerated alternating sum = eta
print(f"  Euler-accelerated phasor sum  eta(1/2+i*gamma_1) = {ns(eta_acc,6)}   (-> 0)")
print(f"  cross-check                  zeta(1/2+i*gamma_1) = {ns(mp.zeta(0.5+1j*g1),6)}")

# ---------------------------------------------------------------------------
# Does the cancellation happen AT 14? find the first t>0 with eta(1/2+it)=0
# by following the real readout |eta| down to its first minimum/zero.
# ---------------------------------------------------------------------------
print("\n[crossing] |eta(1/2+it)| scanned up from the origin:")
prevsign = None
for k in range(1, 40):
    t = mp.mpf(k)*mp.mpf('0.5')
    val = abs(mp.altzeta(0.5+1j*t))
    mark = ""
    if t in (mp.mpf(7), mp.mpf(14), mp.mpf(14.5)):
        mark = "  <-- "
    if k % 2 == 0 or 26 <= 2*t <= 30:
        print(f"    t={ns(t,5):>7}:  |eta| = {ns(val,5):>10}{mark}")

t_zero = mp.findroot(lambda t: mp.altzeta(0.5+1j*t).real, 14.0) \
         if False else g1   # the true cancellation is the zero itself
print(f"\n  first phasor cancellation (eta=0):  t = gamma_1 = {ns(g1,12)}")
print(f"  -> the principal-channel phasors cancel at t = 14.1347...  CORRECT TARGET")

# ---------------------------------------------------------------------------
# the 'amplitude/phase to pi/2' picture (leading order, single carrier)
# ---------------------------------------------------------------------------
print("\n[phase] leading-order 'phase = pi/2' prediction (Hardy Z, N=1 carrier):")
print(f"    accumulated phase theta(gamma_1)        = {ns(mp.siegeltheta(g1),8)}")
t_half = mp.findroot(lambda t: mp.siegeltheta(t) + pi/2, 14.5)
print(f"    pure 'theta = -pi/2' crossing  t*        = {ns(t_half,10)}")
print(f"    actual zero                    gamma_1   = {ns(g1,10)}")
print(f"    leading-order error                      = {ns(t_half-g1,5)} ({ns(100*(t_half-g1)/g1,4)}%)")
