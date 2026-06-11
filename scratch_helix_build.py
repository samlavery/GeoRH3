"""
Build the helix EXACTLY as specified:
  - a line with all integers spaced U = pi/3 apart  (arc-length position of integer n = n*pi/3)
  - wind it: Archimedean spiral, radius grows by e^6 per loop   R(k) = e^6 * k
  - pitch: height grows by pi/3 per loop                        z(k) = (pi/3) * k
  - care about primes by residue mod 6
Find loop number k(n) by ARC LENGTH (the line doesn't stretch when wound), then the 3D point.
"""
import numpy as np

e6 = np.exp(6.0)
U  = np.pi/3                      # arc spacing per integer  AND  pitch per loop
# spiral R(phi) = (e^6/2pi) * phi,  phi = angle in radians (phi = 2*pi*k).
# arc length of that spiral up to angle Phi:  s(Phi) = (e^6/4pi)[ Phi*sqrt(Phi^2+1) + asinh(Phi) ]
A = e6/(4*np.pi)
def s_of_Phi(Phi):
    return A*(Phi*np.sqrt(Phi**2 + 1) + np.arcsinh(Phi))

N = 120_000
# invert s(Phi) = n*U  ->  Phi(n)   (fine grid + interpolation; s is monotone)
Phi_grid = np.linspace(0.0, 2*np.pi*11, 3_000_000)
s_grid   = s_of_Phi(Phi_grid)
n = np.arange(1, N+1)
Phi = np.interp(n*U, s_grid, Phi_grid)

k     = Phi/(2*np.pi)            # loop number
R     = e6*k                     # radius  (out)  = e^6 per loop
theta = Phi                      # winding angle
z     = U*k                      # height  (up)   = pi/3 per loop
x, y  = R*np.cos(theta), R*np.sin(theta)

# primes + residue mod 6
sieve = np.ones(N+1, bool); sieve[:2] = False
for i in range(2, int(N**0.5)+1):
    if sieve[i]: sieve[i*i::i] = False
isp = sieve[1:N+1]
pv  = n[isp]
m6  = pv % 6

print("==================  HELIX WORKED OUT  ==================")
print(f"arc spacing U = pi/3 = {U:.5f}    radial growth e^6 = {e6:.3f} per loop    pitch = pi/3 = {U:.5f} per loop")
print(f"integers placed: 1..{N};  loops completed: k(N) = {k[-1]:.3f}")
print(f"radius:height aspect = e^6/(pi/3) = {e6/U:.1f} : 1   -> a nearly FLAT spiral with a slow climb")
print(f"\nloop structure (integers per loop grows ~linearly => cumulative ~k^2, the area law):")
print(f"{'loop k':>7}{'first integer n':>16}{'radius R':>12}{'height z':>10}")
prev = 0
for kk in range(1, int(k[-1])+1):
    nk = int(np.searchsorted(k, kk)) + 1
    print(f"{kk:>7}{nk:>16}{e6*kk:>12.1f}{U*kk:>10.4f}   (+{nk-prev} integers this loop)")
    prev = nk

print(f"\nfirst 14 primes as placed  (n, mod6, loop k, angle theta(rad), radius R, height z):")
for j in range(14):
    p = int(pv[j]); i = p-1
    print(f"   p={p:5d}  mod6={p%6}  k={k[i]:.4f}  theta={theta[i]:8.3f}  R={R[i]:9.2f}  z={z[i]:.4f}")

import collections
c = collections.Counter(m6.tolist())
print(f"\nprime residues mod 6 up to {N}: {dict(sorted(c.items()))}")
print(f"   (coprime-to-6 classes are 1 and 5: {c[1]} primes =1, {c[5]} primes =5;  2 and 3 appear once each)")

# save coordinates for the next step
np.savez('helix_coords.npz', n=n, k=k, theta=theta, R=R, z=z, x=x, y=y, isprime=isp, mod6=(n%6))
print("\nsaved coordinates -> helix_coords.npz  (n,k,theta,R,z,x,y,isprime,mod6)")

# visualization
try:
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    fig = plt.figure(figsize=(14,6))
    sub = slice(0, N, 7)
    ax1 = fig.add_subplot(121, projection='3d')
    ax1.plot(x[sub], y[sub], z[sub], lw=0.25, color='0.8')
    i1, i5 = pv[m6==1]-1, pv[m6==5]-1
    ax1.scatter(x[i1], y[i1], z[i1], s=4, c='tab:blue', label='prime ≡ 1 (mod 6)')
    ax1.scatter(x[i5], y[i5], z[i5], s=4, c='tab:red',  label='prime ≡ 5 (mod 6)')
    ax1.set_title('3D helix (out: +e^6/loop, up: +pi/3/loop)'); ax1.legend(loc='upper right', fontsize=8)
    ax2 = fig.add_subplot(122)
    ax2.plot(x[sub], y[sub], lw=0.25, color='0.8')
    ax2.scatter(x[i1], y[i1], s=4, c='tab:blue'); ax2.scatter(x[i5], y[i5], s=4, c='tab:red')
    ax2.set_aspect('equal'); ax2.set_title('seen down the axis (the collapse view): primes by mod 6')
    plt.tight_layout(); plt.savefig('helix3d.png', dpi=120)
    print("saved figure -> helix3d.png")
except Exception as ex:
    print("matplotlib unavailable, skipped figure:", ex)
