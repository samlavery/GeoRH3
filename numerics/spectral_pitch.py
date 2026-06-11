"""
spectral_pitch.py -- does the PITCH grow with each new harmonic/zero?
The standing wave Z(T)=cos(theta(T)-..) has instantaneous frequency f(T)=theta'(T)/2pi.
theta'(T) = (1/2) log(q T/2pi).  PITCH (frequency) = how fast the wave oscillates = how fast the
helix winds. We test: pitch grows with each harmonic; the GAP (spacing) is its reciprocal (shrinks).
"""
import numpy as np, mpmath as mp
mp.mp.dps = 22; q = 3
def L(s): return 3**(-s)*(mp.zeta(s, mp.mpf(1)/3) - mp.zeta(s, mp.mpf(2)/3))
def find_zeros(hi):
    ts = np.arange(0.6, hi, 0.05); f = lambda s: L(mp.mpf(1)/2+1j*s)
    mag = np.array([float(abs(f(mp.mpf(t)))) for t in ts]); zs=[]
    for i in range(1,len(ts)-1):
        if mag[i]<mag[i-1] and mag[i]<mag[i+1] and mag[i]<0.5:
            try:
                r=mp.findroot(f, mp.mpc(ts[i],0)); tm=float(mp.re(r))
                if abs(float(mp.im(r)))<1e-6 and abs(complex(f(mp.mpf(tm))))<1e-9 and tm>0.5 and all(abs(tm-z)>1e-3 for z in zs): zs.append(tm)
            except Exception: pass
    return np.array(sorted(zs))
G = find_zeros(130.0)
thetap = 0.5*np.log(q*G/(2*np.pi))          # PITCH = theta'(gamma) = instantaneous frequency*2pi
gap = np.diff(G)
print(f"computed {len(G)} consecutive chi3 zeros (T up to {G[-1]:.1f})\n")
print(f"  {'n':>3} {'gamma_n':>9} {'PITCH theta\\'(=(1/2)log(qT/2pi))':>32} {'gap to next':>12} {'pitch*gap/pi':>13}")
for n in [0,1,2,4,9,19,len(G)-2]:
    g = gap[n] if n < len(gap) else float('nan')
    pg = thetap[n]*g/np.pi if n < len(gap) else float('nan')
    print(f"  {n+1:3d} {G[n]:9.3f} {thetap[n]:32.4f} {g:12.4f} {pg:13.4f}")
print(f"\n  => PITCH (theta', the frequency) GROWS monotonically: {thetap[0]:.3f} -> {thetap[-1]:.3f}")
print(f"     (logarithmically, ~(1/2)log(qT/2pi)).  Each new harmonic oscillates a little faster.")
print(f"     The GAP shrinks as its reciprocal: pitch*gap/pi -> 1 (mean {np.mean(thetap[:-1]*gap/np.pi):.3f}),")
print(f"     i.e. gap = pi/pitch = exactly one HALF-WAVE per zero. Pitch up <=> gap down, same chirp.")
print(f"\n  GEOMETRY: a helix wound at angle theta(T) winds FASTER as you climb (pitch=freq grows);")
print(f"  equivalently its rungs (the zeros) get CLOSER (gap=half-wavelength shrinks). One node per pi.")
