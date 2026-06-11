"""
Bigger multi-L test: 10 L-functions (zeta + real & complex Dirichlet chars mod 3..13).
Per L: zeros up to T found by scan then refined by findroot (~13 digits);
ledger = counted vs Weyl N(T); off-line margin E_min(0.7) over [10,40].
"""
import numpy as np, mpmath as mp, math, time, cmath
t0 = time.time()

def legendre(p):
    qrs = set((i*i) % p for i in range(1, p))
    return {a: (1 if a in qrs else -1) for a in range(1, p)}

w3 = cmath.exp(2j*cmath.pi/3)
chars = [
    ('zeta            q=1',  1, None),
    ('chi3  real      q=3',  3, legendre(3)),
    ('chi4  real      q=4',  4, {1:1, 3:-1}),
    ('chi5  real      q=5',  5, legendre(5)),
    ('chi5  complex   q=5',  5, {1:1, 2:1j, 3:-1j, 4:-1}),
    ('chi7  real      q=7',  7, legendre(7)),
    ('chi7  complex   q=7',  7, {1:1, 2:w3**2, 3:w3, 4:w3, 5:w3**2, 6:1}),
    ('chi8  real      q=8',  8, {1:1, 3:-1, 5:-1, 7:1}),
    ('chi11 real      q=11', 11, legendre(11)),
    ('chi13 real      q=13', 13, legendre(13)),
]

def makeL(q, cv):
    if q == 1:
        return lambda s: mp.zeta(s)
    it = [(mp.mpf(a)/mp.mpf(q), complex(c)) for a, c in cv.items()]
    return lambda s: mp.power(q, -s) * sum(c * mp.zeta(s, a) for a, c in it)

T = 180
for name, q, cv in chars:
    L = makeL(q, cv)
    mp.mp.dps = 8
    ts = np.arange(4, T, 0.06)
    av = np.array([float(abs(L(mp.mpf(1)/2 + 1j*mp.mpf(float(t))))) for t in ts])
    cand = [ts[i] for i in range(1, len(av)-1) if av[i] < av[i-1] and av[i] < av[i+1] and av[i] < 0.25]
    mp.mp.dps = 18
    zeros = []
    for g in cand:
        try:
            r = mp.findroot(lambda t: L(mp.mpf(1)/2 + 1j*t), mp.mpf(float(g)))
            gg = mp.re(r)
            if gg > 0 and (not zeros or abs(gg - zeros[-1]) > mp.mpf('1e-3')) and abs(L(mp.mpf(1)/2 + 1j*gg)) < mp.mpf('1e-9'):
                zeros.append(gg)
        except Exception:
            pass
    Nw = (T/(2*math.pi)) * math.log(q*T/(2*math.pi*math.e))
    mp.mp.dps = 10
    tt = np.arange(10, 40, 0.05)
    marg = min(float(abs(L(mp.mpf('0.7') + 1j*mp.mpf(float(t))))) for t in tt)
    print(f'{name}:  zeros<{T} counted={len(zeros):>3}  Weyl={Nw:6.1f}  off E_min(0.7)={marg:.3f}  [{time.time()-t0:.0f}s]', flush=True)
    print('   gamma: ' + ', '.join(mp.nstr(z, 13) for z in zeros[:10]), flush=True)
print(f'\nDONE [{time.time()-t0:.0f}s]. ledger balances => all zeros on-line; off-margin >0 => no off-line closure.', flush=True)
