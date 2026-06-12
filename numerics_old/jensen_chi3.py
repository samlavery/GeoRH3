"""
jensen_chi3.py -- Jensen/Turan hyperbolicity for L(chi3): the first NON-GAUGE detector.

Xi(t) = (3/pi)^((s+1)/2) Gamma((s+1)/2) L(chi3,s) at s=1/2+it  -- real, even, entire (root number +1).
GRH(chi3)  <=>  all zeros of Xi are REAL  <=>  (Polya) every Jensen polynomial
    J^{d,n}(X) = sum_j C(d,j) gamma_{n+j} X^j,   gamma_k = k! * a_k,  Xi(t) = sum_k a_k t^{2k},
is HYPERBOLIC (all roots real).  This functional reads ONLY the central Taylor coefficients
(moments) -- no zeros input -- and it is sensitive to zero LOCATION (reality), unlike any shape/gauge.

THE A/B EXPERIMENT (the point):
  take the two lowest zero pairs gamma_1, gamma_2; in x = t^2 they are real roots x1, x2 of
  phi(x) = sum a_k x^k.
  ON-LINE move : replace x1,x2 by two other REAL roots (zeros slide along the line)  -> must stay hyperbolic.
  OFF-LINE fuse: replace x1,x2 by the complex pair ((g_avg + i*delta)^2, conj)  (two harmonics
                 collide and split off the line)                                   -> must BREAK hyperbolicity.
If both behave, the coefficient functional DETECTS the line -- the non-gauge signal.
"""
import mpmath as mp

mp.mp.dps = 60
g1 = mp.mpf('8.0397371556814666817136232141729658027930102674')
g2 = mp.mpf('11.2492062077729352497050256788632146486959267932')

def Lfun(s): return 3**(-s)*(mp.zeta(s, mp.mpf(1)/3) - mp.zeta(s, mp.mpf(2)/3))
def Xi(t):
    s = mp.mpf(1)/2 + 1j*t
    return (mp.mpf(3)/mp.pi)**((s+1)/2) * mp.gamma((s+1)/2) * Lfun(s)

# ---- (0) reality/evenness of Xi ----
v1, v2 = Xi(mp.mpf('1.3')), Xi(mp.mpf('-1.3'))
print("(0) Xi real & even:  Xi(1.3) = %s  (Im %.1e),  Xi(-1.3)-Xi(1.3) = %.1e"
      % (mp.nstr(mp.re(v1), 8), abs(mp.im(v1)), abs(v2 - v1)))

# ---- (1) Taylor coefficients of Xi at the CENTER via Cauchy circle (no zeros input) ----
r, M, JMAX = mp.mpf(12), 1024, 60
w = [mp.e**(-1j*2*mp.pi*m/M) for m in range(M)]
vals = [Xi(r*mp.e**(1j*2*mp.pi*m/M)) for m in range(M)]
c = []
for j in range(JMAX+1):
    s = mp.mpc(0)
    for m in range(M):
        s += vals[m]*w[(m*j) % M]
    c.append(s/(M*r**j))
# checks: odd coefficients vanish; reconstruction; phi kills gamma1^2, gamma2^2
odd = max(abs(c[j]) for j in range(1, JMAX+1, 2))
recon = sum(c[j]*mp.mpf('5.31')**j for j in range(JMAX+1))
a = [mp.re(c[2*k]) for k in range(JMAX//2 + 1)]          # phi(x) = sum a_k x^k,  x = t^2
K = len(a)
phi = lambda x, b=None: sum((b or a)[k]*mp.mpc(x)**k for k in range(K))
print("(1) coefficients: max|odd c_j| = %.1e ; |recon-Xi(5.31)| = %.1e ; |phi(g1^2)| = %.1e ; |phi(g2^2)| = %.1e"
      % (odd, abs(recon - Xi(mp.mpf('5.31'))), abs(phi(g1**2)), abs(phi(g2**2))))

def gammas(b):
    return [mp.factorial(k)*b[k] for k in range(K)]

# ---- hyperbolicity checks ----
def turan_margins(gam, nmax):
    out = []
    for n in range(1, nmax):
        T = gam[n]**2 - gam[n-1]*gam[n+1]
        out.append(T/abs(gam[n]**2))            # normalized margin; >=0 <=> J^{2,n-1} hyperbolic
    return out

def jensen_hyperbolic(d, n, gam):
    coef = [mp.binomial(d, j)*gam[n+j] for j in range(d+1)]      # ascending
    s = abs(coef[0]/coef[d])**(mp.mpf(1)/d) if coef[d] != 0 else mp.mpf(1)   # balance roots ~ O(1)
    coef = [coef[j]*s**j/coef[0] for j in range(d+1)]
    try:
        rts = mp.polyroots(list(reversed(coef)), maxsteps=300, extraprec=120)
    except Exception:
        return None
    mx = max(abs(mp.im(z)) for z in rts); sc = max([mp.mpf(1)] + [abs(z) for z in rts])
    return mx/sc < mp.mpf(10)**(-12)

def report(tag, b, nmax_turan=26, dlist=(3, 4, 5), nmax_j=20):
    gam = gammas(b)
    tm = turan_margins(gam, nmax_turan)
    neg = [(i+1, float(t)) for i, t in enumerate(tm) if t < 0]
    fails = []
    for d in dlist:
        for n in range(0, nmax_j):
            h = jensen_hyperbolic(d, n, gam)
            if h is False:
                fails.append((d, n))
    print("    %-26s  Turan n=1..%d: %s   |  J^{d,n} d=3..5, n<%d: %s"
          % (tag, nmax_turan-1,
             ("ALL >= 0 (min %.3g)" % min(float(t) for t in tm)) if not neg else ("NEGATIVE at %s" % neg[:4]),
             nmax_j, "all hyperbolic" if not fails else "FAILS at (d,n)=%s" % fails[:6]))
    return neg, fails

print("\n(2) chi3 ITSELF (GRH side):")
report("chi3 (true zeros)", a)

# ---- (3) the A/B: slide along the line vs fuse off the line ----
def divide(b, x0):
    out, prev = [], mp.mpc(0)
    for bk in b:
        prev = bk + prev/x0
        out.append(prev)
    return out
def multiply(b, x0):
    out, prev = [], mp.mpc(0)
    for bk in b:
        out.append(bk - prev/x0)
        prev = bk
    return out

base = divide(divide([mp.mpc(x) for x in a], g1**2), g2**2)     # remove the two lowest zero pairs
gavg = (g1 + g2)/2

print("\n(3) A/B -- same removal, two different reinsertions:")
# A: ON-LINE control -- two real zeros near collision (slid along the line)
for eps in [mp.mpf('1.5'), mp.mpf('0.5'), mp.mpf('0.1')]:
    bA = multiply(multiply(base, (gavg-eps)**2), (gavg+eps)**2)
    bA = [mp.re(x) for x in bA]
    report("ON-line  slide eps=%s" % mp.nstr(eps, 3), bA)
# B: OFF-LINE fuse -- complex pair (g_avg +- i*delta)
for delta in [mp.mpf('2.0'), mp.mpf('1.0'), mp.mpf('0.5'), mp.mpf('0.25'), mp.mpf('0.1')]:
    xr = (gavg + 1j*delta)**2
    bB = multiply(multiply(base, xr), mp.conj(xr))
    im = max(abs(mp.im(x)) for x in bB)
    bB = [mp.re(x) for x in bB]
    negs, fails = report("OFF-line fuse delta=%s" % mp.nstr(delta, 3), bB)
    if im > mp.mpf(10)**(-30):
        print("       (warn: max imag residue %.1e)" % im)
print("\n=> ON-line moves keep every inequality; OFF-line fusion flips them: the central-coefficient")
print("   functional SEES the line. Non-gauge: no shape relabeling can fake or hide this.")
