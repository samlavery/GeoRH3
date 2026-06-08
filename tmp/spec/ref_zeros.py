import mpmath as mp
import numpy as np
mp.mp.dps = 15

# --- zeta zeros (reference only) ---
zeta_zeros = [float(mp.im(mp.zetazero(n))) for n in range(1, 31)]

# --- Dirichlet L for real primitive odd chi via Hurwitz zeta ---
# chi mod 3: chi(1)=1, chi(2)=-1   (odd, real, primitive)
# chi mod 4: chi(1)=1, chi(3)=-1   (odd, real, primitive)
def Lchi(chi, q, s):
    # L(chi,s) = q^{-s} sum_{a=1}^{q} chi(a) zeta(s, a/q)
    s = mp.mpc(s)
    tot = mp.mpf(0)
    for a in range(1, q+1):
        c = chi.get(a%q if (a%q)!=0 else q, 0)
        if c == 0:
            continue
        tot += c * mp.zeta(s, mp.mpf(a)/q)
    return q**(-s) * tot

chi3 = {1:1, 2:-1}
chi4 = {1:1, 3:-1}

# For odd chi the completed L has gamma factor with a=1.
# Completed Lambda(chi,s) = (q/pi)^{(s+1)/2} Gamma((s+1)/2) L(chi,s).
# On s=1/2+it this is real (root number +1). Find zeros via sign change of real part of completed L.
def completed_real(chi, q, t):
    s = mp.mpc(0.5, t)
    L = Lchi(chi, q, s)
    gam = (mp.mpf(q)/mp.pi)**((s+1)/2) * mp.gamma((s+1)/2)
    val = gam * L
    return float(mp.re(val))

def find_zeros(chi, q, tmax=40.0, n_want=20):
    ts = np.arange(0.01, tmax, 0.01)
    vals = np.array([completed_real(chi, q, t) for t in ts])
    zeros = []
    for i in range(len(ts)-1):
        if vals[i]*vals[i+1] < 0:
            # bisect
            a,b = ts[i], ts[i+1]
            fa = vals[i]
            for _ in range(60):
                m = 0.5*(a+b)
                fm = completed_real(chi,q,m)
                if fa*fm <= 0:
                    b = m
                else:
                    a = m; fa = fm
            zeros.append(0.5*(a+b))
            if len(zeros) >= n_want:
                break
    return zeros

z3 = find_zeros(chi3, 3, tmax=45, n_want=20)
z4 = find_zeros(chi4, 4, tmax=45, n_want=20)

print("ZETA", [round(z,6) for z in zeta_zeros[:20]])
print("CHI3", [round(z,6) for z in z3])
print("CHI4", [round(z,6) for z in z4])

np.save('/Users/samuellavery/proof/three/tmp/spec/zeta_zeros.npy', np.array(zeta_zeros))
np.save('/Users/samuellavery/proof/three/tmp/spec/chi3_zeros.npy', np.array(z3))
np.save('/Users/samuellavery/proof/three/tmp/spec/chi4_zeros.npy', np.array(z4))
