"""
analytic_shadow.py — the analytic (Mellin/log) shadow test, kept OUT of the log-free lib.

This is the recreation of the 12/12 persistence result. It imports helixlib only for the
character table; everything log/Mellin (the truncated-L signal and the answer-key zeros) lives
here, not in the source library.

Signal:  S_N(gamma) = | sum_{n<=N} chi(n) n^{-1/2} e^{-i gamma log n} |   (truncated L; dips ~ zeros)
Event:   a dip that PERSISTS across increasing cutoff N (not a crossing).
Check:   persistent dips vs the actual L(chi) zeros (mpmath, answer key only).
"""
import sys
sys.path.insert(0, "/Users/samuellavery/proof/three")
import numpy as np
import mpmath
import helixlib as H

mpmath.mp.dps = 20
ch = H.chi3()                       # character only, from the log-free lib

# ---- answer key: first 12 zeros of L(chi3) via the completed Lambda (real on the line) ----
def Lam(t):
    s = mpmath.mpf(1) / 2 + 1j * mpmath.mpf(t)
    L = (ch.values[1] * mpmath.zeta(s, mpmath.mpf(1) / 3)
         + ch.values[2] * mpmath.zeta(s, mpmath.mpf(2) / 3)) * mpmath.power(3, -s)
    gam = mpmath.power(3 / mpmath.pi, (s + ch.parity) / 2) * mpmath.gamma((s + ch.parity) / 2)
    return mpmath.re(gam * L)

def ref_zeros(M, tmax=60.0):
    zs = []; t = mpmath.mpf("0.5"); prev = Lam(t); step = mpmath.mpf("0.1")
    while len(zs) < M and t < tmax:
        t2 = t + step; cur = Lam(t2)
        if (prev < 0) != (cur < 0):
            zs.append(float(mpmath.findroot(Lam, (t + t2) / 2)))
        prev = cur; t = t2
    return np.array(zs)

# ---- Mellin shadow signal + persistence ----
g = np.arange(1.0, 55, 0.01)
cutoffs = [300, 1000, 3000]

def shadow(N):
    n = np.arange(1, N + 1)
    amp = ch.chi(n).real / np.sqrt(n)
    return np.abs((amp[None, :] * np.exp(-1j * np.outer(g, np.log(n)))).sum(1))

def persistent(sigs, tol=0.3):
    def dip(m):
        return g[[i for i in range(1, len(m) - 1) if m[i] < m[i - 1] and m[i] < m[i + 1]]]
    sets = [dip(s) for s in sigs]
    base = sets[-1]
    return np.array([d for d in base if all(len(s) and np.min(np.abs(s - d)) < tol for s in sets)])

if __name__ == "__main__":
    zeros = ref_zeros(12); zeros = zeros[zeros <= 55]
    pm = persistent([shadow(N) for N in cutoffs])
    matched = [pm[np.argmin(np.abs(pm - z))] - z for z in zeros
               if len(pm) and abs(pm[np.argmin(np.abs(pm - z))] - z) < 0.5]
    rms = float(np.sqrt(np.mean(np.array(matched) ** 2))) if matched else float("nan")
    print("chi3 zeros      :", np.round(zeros, 3))
    print("persistent modes:", np.round(np.sort(pm), 3))
    print(f"matched {len(matched)}/{len(zeros)}   RMS={rms:.4f}   #persistent={len(pm)}")
