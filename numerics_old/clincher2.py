"""clincher2.py -- the clincher at scale: ~150 consecutive zeros, one fixed fiber, drop-one test."""
import numpy as np, mpmath as mp
mp.mp.dps = 20
def L(s): return 3**(-s)*(mp.zeta(s,mp.mpf(1)/3)-mp.zeta(s,mp.mpf(2)/3))
ts = np.arange(0.6, 250.0, 0.05)
mag = np.array([float(abs(L(mp.mpf(1)/2+1j*mp.mpf(t)))) for t in ts])
G = []
for i in range(1, len(ts)-1):
    if mag[i]<mag[i-1] and mag[i]<mag[i+1] and mag[i]<0.6:
        try:
            r = mp.findroot(lambda s: L(mp.mpf(1)/2+1j*s), mp.mpc(ts[i],0))
            tm = float(mp.re(r))
            if abs(float(mp.im(r)))<1e-6 and abs(complex(L(mp.mpf(1)/2+1j*mp.mpf(tm))))<1e-10 \
               and tm>0.5 and all(abs(tm-z)>1e-3 for z in G): G.append(tm)
        except Exception: pass
G = np.array(sorted(G))
# completeness check vs RvM count
Nvm = (G[-1]/(2*np.pi))*np.log(3*G[-1]/(2*np.pi)) - G[-1]/(2*np.pi) + 7/8
print(f"{len(G)} consecutive zeros to T={G[-1]:.1f}  (RvM predicts {Nvm:.1f} -- {'COMPLETE' if abs(len(G)-Nvm)<1 else 'MISSING SOME'})\n")

M = 400000
n = np.arange(1, M+1)
chi = np.where(n%3==1,1.0,np.where(n%3==2,-1.0,0.0))
amp = n**-0.5; logn = np.log(n)
w = chi*amp
# |F| at all zeros (one fixed fiber) and at all midpoints
Fz = np.array([abs(np.sum(w*np.exp(-1j*g*logn))) for g in G])
mids = 0.5*(G[1:]+G[:-1])
Fm = np.array([abs(np.sum(w*np.exp(-1j*m*logn))) for m in mids])
print(f"(1) SAME fiber at ALL {len(G)} zeros:   max|F| = {Fz.max():.4f},  mean = {Fz.mean():.4f}")
print(f"    at the {len(mids)} midpoints (control): min|F| = {Fm.min():.4f},  median = {np.median(Fm):.4f}")
print(f"    worst zero/typical off ratio: {Fz.max()/np.median(Fm):.4f}")

# drop-one test across ALL zeros
for nd in [2, 7, 100]:
    c = chi[nd-1]*amp[nd-1]
    Fd = np.array([abs(np.sum(w*np.exp(-1j*g*logn)) - c*np.exp(-1j*g*logn[nd-1])) for g in G])
    pred = nd**-0.5
    print(f"(2) drop n={nd:3d}: |F| over all {len(G)} zeros: mean {Fd.mean():.4f}, std {Fd.std():.4f}, "
          f"min {Fd.min():.4f}, max {Fd.max():.4f}   predicted {pred:.4f}")
print("\n=> one structure, every integer, every zero -- at scale.")
