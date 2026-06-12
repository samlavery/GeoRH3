"""
ROUTE 1 — Real-space twisted Chebyshev psi_chi(x) from the chi3 zeros.

Explicit formula (chi primitive, ODD, mod 3; NO pole, NO main term x):
    psi_chi(x) = - sum_rho x^rho / rho  - (log term) - trivial-zero sum

The dominant nontrivial part, pairing rho = 1/2 +- i gamma:
    psi_chi(x) ~ - sum_{gamma>0} ( x^rho/rho + x^conj(rho)/conj(rho) )
               = - 2 sqrt(x) * sum_{gamma>0} Re( x^{i gamma} / (1/2 + i gamma) ).

Target signature (Lambda_chi(n) = chi(n) Lambda(n), chi3(n)= +1 if n=1, -1 if n=2 mod 3, 0 if n=0 mod3):
    psi_chi JUMPS by chi3(p^k) log p at prime power n=p^k,
    and is FLAT across n=3,9,27 (since chi3(3)=0).

We can only resolve detail up to oscillation scale ~ 1/gamma_max. gamma_max ~ 3502,
so finest resolvable real-space scale in x is dx ~ x / gamma_max (the n^{i gamma} term
oscillates with local wavelength 2 pi x / gamma in x). To separate integers n and n+1
we need x/gamma_max < ~0.3, i.e. x < ~1000. So we test small n.

Naive sum blurs (Gibbs + slow conditional convergence). We BEAT it three ways:
  (a) DIFFERENCE over a window: D(n) = psi_chi(n+h) - psi_chi(n-h) should ~ jump if a
      prime power sits in (n-h, n+h), and ~0 otherwise.
  (b) GAUSSIAN damping of high gamma (Fejer/Gaussian) to kill Gibbs ringing:
      weight w(gamma) = exp( - (gamma * s)^2 / 2 ), s a smoothing scale; this convolves
      the jump with a Gaussian of width ~ s*x in log-x (equivalently smooths psi).
  (c) report psi at half-integers (midpoints) where the jump structure is cleanest.
"""
import math

# ---- load gammas (SECOND token!) ----
gammas = []
with open('lchi3_zeros_record.txt') as f:
    for line in f:
        line = line.strip()
        if not line or line.startswith('#'):
            continue
        toks = line.split()
        if len(toks) < 2:
            continue
        gammas.append(float(toks[1]))
gammas.sort()
GM = gammas[-1]
print('# zeros: %d, gamma_max=%.3f' % (len(gammas), GM))


def chi3(n):
    r = n % 3
    if r == 0:
        return 0
    return 1 if r == 1 else -1


def vonmangoldt(n):
    # Lambda(n)=log p if n=p^k else 0
    if n < 2:
        return 0.0, None, None
    m = n
    p = 2
    while p * p <= m:
        if m % p == 0:
            while m % p == 0:
                m //= p
            if m == 1:
                return math.log(p), p, None
            else:
                return 0.0, None, None
        p += 1
    # n is prime
    return math.log(n), n, None


def lambda_chi_table(N):
    out = {}
    for n in range(2, N + 1):
        lam, p, _ = vonmangoldt(n)
        if lam > 0:
            out[n] = chi3(p) ** 0 * lam * chi3(  # chi3(p^k)=chi3(p)^k; but chi multiplicative
                pow_prime_residue(n))
    return out


def pow_prime_residue(n):
    # return chi3(n) where n=p^k; chi3 is completely multiplicative so chi3(p^k)=chi3(p)^k=chi3(n)
    return chi3(n)


def psi_chi_reconstruct(x, smooth=0.0):
    """- 2 sqrt(x) sum_{gamma>0} Re( x^{i gamma}/(1/2 + i gamma) ) * w(gamma).
    smooth>0 applies Gaussian damping exp(-(gamma*smooth)^2/2)."""
    if x <= 0:
        return 0.0
    lx = math.log(x)
    sx = math.sqrt(x)
    acc = 0.0
    for g in gammas:
        if smooth > 0.0:
            w = math.exp(-0.5 * (g * smooth) ** 2)
            if w < 1e-12:
                break
        else:
            w = 1.0
        # x^{i gamma} = exp(i gamma log x); divide by (1/2 + i gamma)
        # Re( (cos + i sin) / (a + i g) ) with a=1/2
        c = math.cos(g * lx)
        s = math.sin(g * lx)
        denom = 0.25 + g * g
        # (c + i s)(a - i g)/denom ; Re = (c*a + s*g)/denom
        re = (c * 0.5 + s * g) / denom
        acc += re * w
    return -2.0 * sx * acc


def true_psi_chi(x):
    """exact partial-sum sum_{n<=x} chi3(n) Lambda(n)."""
    tot = 0.0
    n = 2
    while n <= x:
        lam, p, _ = vonmangoldt(n)
        if lam > 0:
            tot += chi3(n) * lam  # chi3(n)=chi3(p^k)=chi3(p)^k
        n += 1
    return tot


# ---------- (a) difference test at each integer ----------
print("\n=== TRUE Lambda_chi(n) for small n (reference jumps) ===")
ref = {}
for n in range(2, 30):
    lam, p, _ = vonmangoldt(n)
    if lam > 0:
        ref[n] = chi3(n) * lam
        print("n=%2d  prime power p=%2d  chi3(n)=%+d  jump=%+.4f" %
              (n, p, chi3(n), ref[n]))
    else:
        print("n=%2d  (not pp)            chi3(n)=%+d  jump= 0" % (n, chi3(n)))

# ---------- reconstruct difference D(n) = psi(n+0.5)-psi(n-0.5) at integers ----------
print("\n=== Reconstructed jump estimate D(n)=psi_chi(n+0.5)-psi_chi(n-0.5) ===")
print("(raw, no smoothing)")
for smooth in [0.0, 0.02, 0.05]:
    print("\n-- smoothing scale s=%.3f --" % smooth)
    print(" n  true_jump   recon_D    recon_psi(n)   note")
    for n in range(2, 28):
        D = psi_chi_reconstruct(n + 0.5, smooth) - psi_chi_reconstruct(n - 0.5, smooth)
        psi_n = psi_chi_reconstruct(n + 1e-6, smooth)
        tj = ref.get(n, 0.0)
        note = ""
        if n in (3, 9, 27):
            note = "<-- mult of 3 (should be FLAT, D~0)"
        elif n in ref:
            note = "<-- pp, expect %+.3f" % tj
        print("%2d  %+8.4f   %+8.4f   %+10.4f   %s" % (n, tj, D, psi_n, note))
