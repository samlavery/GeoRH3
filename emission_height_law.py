r"""
Where the seam actually bites: the EMISSION / HEIGHT LAW  purchaseHeight(n) <-> gamma_n.

The trace identity (frobenius3d_screw_trace.py) is faithful and kernel-clean: IF an event sits
at height gamma, the resolvent/readout/reality machinery correctly reads it as an on-line zero.
What is NOT given by elementary geometry is the HEIGHT of the n-th event.  This file locates,
to the digit, how much of that height law is UNCONDITIONAL (the smooth Riemann-von Mangoldt /
Gamma-factor count -- the emission law) and how much is the seam (the S(T) = (1/pi) arg zeta
fluctuation, the part that genuinely "knows" where the zeros are = HelixSupremacy / exhaustion).

Exact identity (unconditional, Mathlib-grade):
    N(T)  =  theta(T)/pi + 1  +  S(T),     S(T) = (1/pi) arg zeta(1/2 + iT),
where theta = Riemann-Siegel theta (the Gamma-factor phase) and N(T) = #{0 < gamma <= T}.
At T = gamma_n (just above the n-th zero) N = n, so:

    n  =  [ theta(gamma_n)/pi + 1 ]   +   S(gamma_n).
          \___ emission law (smooth) __/      \__ the seam __/

The emission law's prediction for the n-th height is the GRAM-type point g solving
theta(g)/pi + 1 = n, i.e. theta(g) = (n-1) pi.  The residual gamma_n - g is the seam fluctuation.

We show: (1) the smooth law tracks gamma_n with a BOUNDED, mean-zero residual; (2) that residual
IS S(gamma_n); (3) the smooth part alone is unconditional (theta is elementary), the residual is
exactly the open content.  This is the honest location of the one seam -- not a wall, a target.
"""

import mpmath as mp

mp.mp.dps = 30
PI = mp.pi


def theta(T):
    """Riemann-Siegel theta -- the Gamma-factor phase, fully elementary/unconditional."""
    return mp.siegeltheta(T)


def N_smooth(T):
    """Emission-law smooth count = theta(T)/pi + 1  (= the unconditional Gamma-factor zero count)."""
    return theta(T) / PI + 1


NZ = 80
print("Caching gamma_1 .. gamma_%d ..." % NZ, flush=True)
gammas = [mp.im(mp.zetazero(n)) for n in range(1, NZ + 1)]


def S_at_zero(n, g):
    """S(gamma_n) computed RIGHT.  N(T)=theta(T)/pi+1+S(T) for T not a zero ordinate; AT a zero
    the count convention is N(gamma_n)=n-1/2 (midpoint of the jump).  Hence
        S(gamma_n) = (n - 1/2) - (theta(gamma_n)/pi + 1) = n - theta(gamma_n)/pi - 3/2.
    (My first pass dropped the -1/2 and so reported S+1/2 ~ +0.5 -- a convention bug, now fixed.)"""
    return (n - mp.mpf(1) / 2) - N_smooth(g)


def S_at_midpoint(n):
    """S(T) at the midpoint of (gamma_n, gamma_{n+1}), where N(T)=n is constant and T is NOT a
    zero ordinate -- the clean, convention-free value:  S = n - theta(T)/pi - 1."""
    T = (gammas[n - 1] + gammas[n]) / 2
    return n - N_smooth(T)


print("\n" + "=" * 86)
print("EMISSION LAW vs SEAM:  gamma_n height  =  smooth theta/pi law  +  S(gamma_n)")
print("   smooth (unconditional, Gamma-factor)            the seam (arg zeta fluctuation)")
print("=" * 86)
print(f"{'n':>3} {'gamma_n (true)':>16} {'theta(g)/pi+1 (smooth ct)':>26} "
      f"{'S(gamma_n) [fixed]':>18} {'S at midpt':>11}")
S_zero, S_mid = [], []
for n in range(1, NZ + 1):
    g = gammas[n - 1]
    Sz = float(S_at_zero(n, g))
    S_zero.append(Sz)
    if n < NZ:
        Sm = float(S_at_midpoint(n))
        S_mid.append(Sm)
    else:
        Sm = float("nan")
    if n <= 18 or n % 5 == 0:
        print(f"{n:>3} {float(g):>16.6f} {float(N_smooth(g)):>26.5f} "
              f"{Sz:>+18.5f} {Sm:>+11.5f}")

import statistics as st
print("\n" + "-" * 86)
print(f"S(T) = (1/pi) arg zeta(1/2+iT)  -- the seam fluctuation -- over n=1..{NZ}:")
print(f"  at zero ordinates  S(gamma_n):  mean = {st.mean(S_zero):+.5f}   stdev = {st.pstdev(S_zero):.5f}"
      f"   max|.| = {max(abs(x) for x in S_zero):.5f}")
print(f"  at interval midpts S(mid)    :  mean = {st.mean(S_mid):+.5f}   stdev = {st.pstdev(S_mid):.5f}"
      f"   max|.| = {max(abs(x) for x in S_mid):.5f}")
print(f"  => mean ~ 0 (UNBIASED once the -1/2 jump convention is correct), BOUNDED |S| = O(1) here.")
print(f"     The smooth Gamma-factor law theta/pi+1 IS the height to within this mean-zero S(T).")
print("-" * 86)

print("""
READING (the honest seam location):

  * SMOOTH / EMISSION LAW  theta(T)/pi + 1  is UNCONDITIONAL and elementary (the Gamma-factor /
    Riemann-Siegel phase).  It already gives purchaseHeight(n) = gamma_n to within a BOUNDED,
    MEAN-ZERO residual.  This is the part the helix earns: the arc/Gamma-factor count of events.

  * THE SEAM is exactly the residual  S(gamma_n) = (1/pi) arg zeta(1/2 + i gamma_n) -- the part
    that 'knows' the individual zeros.  Pinning each event's height to the *exact* gamma_n (not
    just the smooth law) is HelixSupremacy / exhaustion: it is RH-strength, named, not hidden.

  * So the split is clean and honest:
        FAITHFUL + DONE (kernel-clean) : event-at-height-gamma  ->  on-line zero  (trace identity)
        EARNED  (unconditional)        : the smooth height law  theta/pi + 1     (emission count)
        THE ONE SEAM (open, attackable): the S(T) fluctuation = exact exhaustion = HelixSupremacy

  This is a target, not a wall: the generative attack is the emission DYNAMICS (energy monotone,
  per-mode amplitude n^{-sigma} down, arc growing ~ e^{gamma}) that should fix the S(T) residual --
  i.e. derive arg zeta on the line from the crossing engine, not assume it.
""")
