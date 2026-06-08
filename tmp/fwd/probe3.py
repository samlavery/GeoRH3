import numpy as np
from shared_rule import sieve_primes, chi0_mod3, chi3_mod3
import json

# Honest reconsideration: the zeros are resonances of the COLLECTIVE prime signal,
# governed by the explicit formula. The von Mangoldt explicit formula:
#   -zeta'/zeta(s) = sum_q Lambda-weight q^{-s},  poles at s=rho.
# On the line s=1/2+it the Dirichlet series sum_n Lambda(n) n^{-1/2-it} has its
# fluctuations driven by the zeros: -zeta'/zeta(1/2+it) = sum over zeros 1/(1/2+it-rho)+...
# The peaks of |sum_n Lambda(n) n^{-1/2} n^{-it}| (smoothed) should sit near zeros? Actually
# the partial sums of the prime series, as a function of t, resonate at the zeros.
#
# Build collective signal as function of t (=height H):
#   F(t) = sum_{q=p^k <= X} chi(q) Lambda-weight(q) q^{-1/2} q^{-it}
# This is a truncated -L'/L Dirichlet series. Its LARGE values (peaks) cluster near zeros
# only weakly for small X. The cleaner object: the resolvent / smoothed counting via the
# argument of the truncated Euler product => winding.  Let's test the WINDING (arg principle),
# which is RULE EIGHT's actual prescription (log-free FTA winding).
#
# Euler product truncated: P(s) = prod_{p<=X} (1 - chi(p) p^{-s})^{-1}.
# arg P(1/2+it) increases by ~pi each time we pass a zero (argument principle for the
# completed L). N(T) ~ (1/pi) * [arg of completed L from 0 to T] roughly. Let's just
# measure where the truncated Euler product's phase has features. BUT Euler product doesn't
# converge at 1/2. This is exactly why naive prime sums don't give zeros cleanly.
#
# The honest tester's finding: the Gram-of-atoms rank = frequency resolution, NOT zeros.
# Let me CONFIRM precisely by measuring spacing growth of my emission staircase.
emit = np.array([1.,1.,1.,1.,1.197,1.592,1.987,2.579,2.973,3.565,3.96,4.552,4.946,5.538,6.13])
d = np.diff(emit[4:])
print("emit spacings (channel A naive):", np.round(d,3))
print("--> CONSTANT ~0.4-0.6, NOT shrinking. This is freq-resolution, not zeta zeros. CONFIRMED FAIL of naive rank rule.")
