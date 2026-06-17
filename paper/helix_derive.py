import mpmath as mp
mp.mp.dps = 25
pi = mp.pi
def ns(x,k=8): return mp.nstr(x,k)

# EXACT SPEC, pure geometry:
#   * integers placed pi/6 apart on a line:        arc s_n = n*(pi/6)
#   * CONSTANT radial growth pi/3 per loop:        Archimedean R = c*theta,
#         radial gain per loop = c*2pi = pi/3  =>  c = 1/6
#   * constant pitch (climb z linear in theta).
#
# wind: arc length of R=c*theta is ~ (c/2)theta^2, invert at s_n:
#         theta_n = sqrt(2 s_n / c) = sqrt(2 n (pi/6) / (1/6)) = sqrt(2 pi n)
#         R_n     = c*theta_n = (1/6)sqrt(2 pi n)            ~ sqrt(n)   (area law)
# read off the geometry:
#         amplitude  A_n = 1/R_n        ~ n^{-1/2}     (radial: the "out")
#         frequency  w_n = theta_n = sqrt(2 pi n)      (winding angle the climb scales)
#
# standing wave at climb height z:  sum_n (-1)^{n-1} A_n cos(z * w_n)
# DERIVED crossing = first z>0 it vanishes.  (scale-free: compare ratios z_k/z_1.)

c = mp.mpf(1)/6
def w(n): return mp.sqrt(2*pi*n)          # winding angle  ~ sqrt(n)
def A(n): return 1/(c*w(n))               # 1/radius       ~ n^{-1/2}

def wave(z, N=5000):
    s = mp.mpf(0)
    for n in range(1, N+1):
        s += (-1)**(n-1) * A(n) * mp.cos(z*w(n)) * mp.e**(-(mp.mpf(n)/N)**2)
    return s

def crossings(count, hi=30, step=mp.mpf('0.02')):
    out, z, prev = [], step, wave(step)
    while z < hi and len(out) < count:
        z += step; cur = wave(z)
        if (prev<0)!=(cur<0): out.append(mp.findroot(wave, z))
        prev = cur
    return out

g = crossings(4)
print("DERIVED crossings z_k (pi/3 const radial):", [ns(x) for x in g])
if g:
    print("ratios z_k/z_1                           :", [ns(x/g[0]) for x in g])
zt = [mp.im(mp.zetazero(k)) for k in range(1,5)]
print("zeta zeros                               :", [ns(x) for x in zt])
print("zeta ratios z_k/z_1                      :", [ns(x/zt[0]) for x in zt])
