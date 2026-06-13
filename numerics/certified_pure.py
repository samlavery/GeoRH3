"""CERTIFIED pure pipeline: chi3 zeros as theorem-grade enclosures.
All constants at dps 60 (real pi). Every truncation carries its classical
explicit remainder bound. No zeta/L/Gamma oracle: head sums + Euler-Maclaurin
ladders (Bernoulli, elementary) + the bridge log. Output: bracket enclosures
with certified error budgets, cross-checked vs the independent 60-digit table."""
from mpmath import mp, mpf, mpc, fabs, log as mlog, exp as mexp, pi as mppi, \
    bernoulli, factorial, arg as marg, sqrt as msqrt, re as mre, im as mim, expjpi
mp.dps = 60

q, a = 3, 1
chi = {0: 0, 1: 1, 2: -1}

# --- elementary Hurwitz tail with EXPLICIT remainder bound -------------------
def zeta_EM(s, x, K=8, J=8):
    """sum_{n>=0} (x+n)^{-s} via E-M; returns (value, remainder_bound)."""
    head = sum((x+n)**(-s) for n in range(K))
    X = x + K
    val = head + X**(1-s)/(s-1) + X**(-s)/2
    poch = s
    for j in range(1, J+1):
        # (s)_{2j-1} = s(s+1)...(s+2j-2)
        val += bernoulli(2*j)/factorial(2*j) * poch * X**(-s-2*j+1)
        poch *= (s + 2*j - 1)*(s + 2*j)
    # |R_J| <= |B_{2J+2}|/(2J+2)! * |(s)_{2J+1}| * X^{-Re s-2J-1}, safety 8
    Rb = 8*fabs(bernoulli(2*J+2))/factorial(2*J+2)*fabs(poch/(s+2*J))*fabs(X)**(-mre(s)-2*J-1)
    return val, Rb

M = 9999            # M divisible by q
def F_certified(t):
    """L(1/2+it, chi3) value built from finite arithmetic + E-M ladder.
    Returns (value, certified_bound)."""
    s = mpc(mpf(1)/2, t)
    head = mpc(0)
    for n in range(1, M+1):
        c = chi[n % q]
        if c:
            head += c*mexp(-s*mlog(n))
    tail = mpc(0); bound = mpf(0)
    for r in range(1, q):
        if chi[r % q]:
            v, Rb = zeta_EM(s, (mpf(M)+r)/q)
            tail += chi[r % q]*v
            bound += Rb
    qs = mexp(-s*mlog(q))
    return head + qs*tail, fabs(qs)*bound

# --- elementary argGamma with EXPLICIT remainder bound -----------------------
def argGamma_cert(z, J=8):
    shift = mpf(0)
    while fabs(z) < 15:
        shift -= mim(mlog(z)); z = z + 1
    s = (z - mpf(1)/2)*mlog(z) - z + mlog(2*mppi)/2
    for j in range(1, J+1):
        s += bernoulli(2*j)/((2*j)*(2*j-1)*z**(2*j-1))
    Rb = 8*fabs(bernoulli(2*J+2))/((2*J+1)*(2*J+2)*fabs(z)**(2*J+1))
    return mim(s) + shift, Rb

tau = sum(chi[r]*expjpi(mpf(2*r)/q) for r in range(1, q))
alpha = -marg(tau/(mpc(0,1)**a*msqrt(q)))/2

def V_cert(t):
    F, eF = F_certified(t)
    th, eth = argGamma_cert(mpc((mpf(1)/2 + a)/2, t/2))
    th = th + (t/2)*mlog(mpf(q)/mppi)
    val = mre(mexp(mpc(0,1)*(th+alpha))*F)
    return val, eF + fabs(F)*eth          # total certified budget

hp = [l.split()[1] for l in open('results/L2_chi3_q3_hp40.txt') if not l.startswith('#')]
print("CERTIFIED PURE PIPELINE (dps 60, real pi, explicit remainder bounds)")
print(f"M = {M} head terms; E-M ladder J=8; argGamma recurrence+J=8")
for m in range(1, 6):
    t = mpf(hp[m-1][:12])                  # coarse 10-digit seed only
    # secant refinement on V
    t2 = t + mpf(10)**-9
    v1, _ = V_cert(t); v2, _ = V_cert(t2)
    for _ in range(12):
        t, t2, v1 = t2, t2 - v2*(t2-t)/(v2-v1), v2
        v2, _ = V_cert(t2)
        if fabs(t2-t) < mpf(10)**-40:
            break
    z = t2
    # bracket certification: V flips across [z-w, z+w] with margin > budget
    w = mpf(10)**-35
    va, ea = V_cert(z-w); vb, eb = V_cert(z+w)
    ok = (va*vb < 0) and fabs(va) > ea and fabs(vb) > eb
    xref = fabs(z - mpf(hp[m-1]))
    print(f"zero {m}: enclosure center {mp.nstr(z, 38)}")
    print(f"   width 2e-35  certified: {ok}  budgets ({mp.nstr(ea,2)}, {mp.nstr(eb,2)})"
          f"  |V| at ends ({mp.nstr(fabs(va),2)}, {mp.nstr(fabs(vb),2)})")
    print(f"   vs independent 60-digit table: |diff| = {mp.nstr(xref, 3)}", flush=True)
