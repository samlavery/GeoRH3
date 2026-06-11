"""
helix_fibre_trivial.py  --  the trivial (principal) character, the one that needs special treatment.

The trivial character chi(n)=1 has ONE fibre and no +/- partner: sum_a chi(a) != 0, so its
running mean (DC component) does NOT vanish.  Consequently:

  (A) the RAW winding-phasor sum does NOT cancel on the line -- it DIVERGES ~ N^{1/2}, tracking
      the s=1 pole (= the surviving DC / smooth part);
  (B) subtracting the smooth part  N^{1-s}/(1-s) = int_1^N x^{-s} dx  (the leading Euler-Maclaurin
      term) leaves the fluctuation, which IS zeta, and which cancels at the Riemann zeros.

This is the same DC component that fibre cancellation (sum_a chi(a) = 0) removes for FREE for every
non-principal character -- so "the trivial character needs special treatment" = "it has no fibre to
cancel its mean."  The regularization is literally factoring out the smooth part; the residual
|R_N| ~ 1/2 * N^{-1/2} is exactly the next Euler-Maclaurin term.

Counterpart note: this is why HelixFibreCancellation.lean is stated for a non-principal character
(chi3); the principal case carries the s=1 pole and needs the smooth subtraction.
"""
import mpmath as mp
mp.mp.dps = 25

zeros = [mp.im(mp.zetazero(k)) for k in range(1, 11)]
print("first 10 Riemann zeros (gamma):", [round(float(g), 4) for g in zeros])
print("max |zeta(1/2+i*gamma)| over them:",
      f"{float(max(abs(mp.zeta(mp.mpf('0.5') + 1j * g)) for g in zeros)):.2e}")

g = zeros[0]; s = mp.mpf('0.5') + 1j * g
print("\n" + "=" * 70)
print(f"At the first Riemann zero gamma = {float(g):.6f}  (zeta = {complex(mp.zeta(s)):.1e})")

print("\n(A) RAW helix phasor sum S_N = sum_{n<=N} 1/sqrt(n) e^{-i*gamma*log n}")
print("    no fibre to cancel its mean -> DIVERGES, tracking the s=1 pole ~ N^1/2:")
for N in (10**3, 10**4, 10**5, 10**6):
    S = mp.fsum(mp.power(n, -s) for n in range(1, N + 1))
    print(f"    N={N:>8}: |S_N| = {float(abs(S)):.4e}")

print("\n(B) REGULARIZED R_N = S_N - N^{1-s}/(1-s)   (subtract the smooth part = the s=1 pole)")
print("    the Riemann zero reappears as a cancellation -> 0 at ~N^-1/2:")
for N in (10**3, 10**4, 10**5, 10**6):
    S = mp.fsum(mp.power(n, -s) for n in range(1, N + 1))
    print(f"    N={N:>8}: |R_N| = {float(abs(S - mp.power(N, 1 - s) / (1 - s))):.4e}")

print("\n(C) sanity: the same smooth subtraction reproduces zeta off the zeros")
for t0 in (mp.mpf('10.0'), mp.mpf('20.0')):
    ss = mp.mpf('0.5') + 1j * t0; N = 10**6
    S = mp.fsum(mp.power(n, -ss) for n in range(1, N + 1))
    print(f"    t={float(t0):.1f}:  |R_N - zeta(1/2+it)| = {float(abs(S - mp.power(N, 1 - ss) / (1 - ss) - mp.zeta(ss))):.3e}")

print("\n" + "=" * 70)
print("CONTRAST: non-principal chi (mod 3) at ITS first zero -- raw sum cancels, NO subtraction")
def chi3(n):
    r = n % 3; return 1 if r == 1 else (-1 if r == 2 else 0)
def L3(s): return mp.power(3, -s) * (mp.zeta(s, mp.mpf(1) / 3) - mp.zeta(s, mp.mpf(2) / 3))
g3 = mp.im(mp.findroot(L3, mp.mpf('0.5') + 1j * mp.mpf('8.0'))); s3 = mp.mpf('0.5') + 1j * g3
for N in (10**3, 10**4, 10**5, 10**6):
    S = mp.fsum(chi3(n) * mp.power(n, -s3) for n in range(1, N + 1))
    print(f"    N={N:>8}: |S_N (raw)| = {float(abs(S)):.4e}  (mean is 0 -> no pole to subtract)")
