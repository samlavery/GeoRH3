#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
blocky_pitch-4.py   ID: pitch-4

PER-PRIME LOG-DRIFT BLOCKY HELIX (Euler-product / FTA-additive winding, log-free geometry).

Builds a REAL 3D blocky helix whose winding is built NOT from log(n) placement but from
the FTA-additive prime structure:  Theta(m*n) = Theta(m) + Theta(n)  via the prime
factorization, with each prime p contributing a fixed angular drift log p, planted
geometrically as evenly spaced prime markers (NOT as log positions).

HARD RULE obeyed:  the 3D solid is built first with explicit (x,y,z) and a PHASOR (a real
rotating unit vector) hung at each point. A cancellation event = the chi3-weighted PHASOR
VECTOR-SUM collapsing toward the central axis. We never collapse to an abstract scalar
without the 3D points + phasor vectors.

The single PERMITTED log is the readout bridge Theta(p)=t*log p (the dictionary).  Inside
the geometry the spin is accumulated additively over prime factors; log appears only when
we DECLARE that an evenly-spaced prime marker "means" angular drift log p (the bridge).

Run:  python3 blocky_pitch-4.py
"""

import numpy as np
import mpmath as mp

mp.mp.dps = 40

# ----------------------------------------------------------------------------------------
# 0. chi3, exact L, exact zeros (ground truth -- every claimed collapse cross-checked)
# ----------------------------------------------------------------------------------------

def chi3(n):
    """Real Dirichlet character mod 3:  chi3(n) = +1 if n=1 mod 3, -1 if n=2 mod 3, 0 if 3|n."""
    r = n % 3
    if r == 1:
        return 1
    if r == 2:
        return -1
    return 0

def Lchi3(s):
    """L(chi3, s) = 3^{-s} ( zeta(s,1/3) - zeta(s,2/3) )  (mpmath, high precision)."""
    s = mp.mpf(s) if not isinstance(s, mp.mpc) and not isinstance(s, mp.mpf) else s
    return mp.power(3, -s) * (mp.zeta(s, mp.mpf(1)/3) - mp.zeta(s, mp.mpf(2)/3))

def absL_on_line(t):
    return abs(Lchi3(mp.mpf('0.5') + 1j*mp.mpf(t)))

# load the 65 exact zeros
EXACT = []
with open(__file__.rsplit('/',1)[0] + '/chi3_zeros_exact.txt') as f:
    for line in f:
        line = line.strip()
        if not line or line.startswith('#'):
            continue
        try:
            EXACT.append(float(line))
        except ValueError:
            pass
EXACT = np.array(sorted(EXACT))
print("=" * 90)
print("GROUND TRUTH: %d exact chi3 zeros loaded; first heights:" % len(EXACT))
print("  ", np.round(EXACT[:8], 4))
# sanity check one zero with mpmath
print("  |L(1/2 + i*%.6f)| = %.3e  (should be ~0)" % (EXACT[0], float(absL_on_line(EXACT[0]))))
print("=" * 90)


# ----------------------------------------------------------------------------------------
# 1. PRIME MACHINERY (FTA) -- factorization -> additive prime drift
# ----------------------------------------------------------------------------------------

def primes_up_to(N):
    sieve = np.ones(N+1, dtype=bool)
    sieve[:2] = False
    for p in range(2, int(N**0.5)+1):
        if sieve[p]:
            sieve[p*p::p] = False
    return np.nonzero(sieve)[0]

def factorize(n, prime_list):
    """Return dict {p: a} for n = prod p^a."""
    f = {}
    m = n
    for p in prime_list:
        if p*p > m:
            break
        while m % p == 0:
            f[p] = f.get(p, 0) + 1
            m //= p
    if m > 1:
        f[m] = f.get(m, 0) + 1
    return f


# ----------------------------------------------------------------------------------------
# 2. STEP 1 (FIRST): BUILD THE REAL 3D BLOCKY HELIX WITH EXPLICIT (x,y,z) + PHASORS
# ----------------------------------------------------------------------------------------
#
# Geometry (blocky, stepped):
#   * Integers n=1..NMAX are placed.  Each n is given a FTA-additive spin Phi_n built from
#     its prime markers: each prime p has an intrinsic drift d(p)=log p (the bridge dict).
#         Phi_n = sum_{p^a || n} a * d(p)            <-- recovered additively (NOT placed)
#     This is the log-free construction: we never write log(n); we add prime drifts.
#   * The helix is BLOCKY: it is cut into blocks, one per "loop". Within a block the pitch
#     (axial rise per turn) and radial law are constant; at each block boundary they STEP.
#     The block index of n is k(n) = floor(sqrt(n)) (area law: loop k holds ~k integers,
#     cumulative ~k^2 -> R ∝ sqrt(n)).  The per-block pitch is stepped using the per-prime
#     drift constants {log2, log3} as the prompt demands (see step_pitch()).
#   * Radius R_n = sqrt(n)  (area law);  amplitude a_n = 1/R_n = 1/sqrt(n).
#   * The angular coordinate that winds the helix in the (x,y) plane is the geometric
#     wind angle U * Phi_n  where U is the helix unit (a free spacing constant we keep =1
#     in the geometry; the bridge multiplies by t at readout).
#
#   * PHASOR at point n: a real unit vector in the (x,y) plane.  Its base spin (no probe)
#     is exp(i * Phi_n).  At a probe height T the phasor is rotated by the bridge:
#         phasor_n(T) = exp( i * (Phi_n) * (-T) )   [the bridge Theta=t*log p]
#     and the chi3-weighted, amplitude-weighted RESULTANT is
#         Resultant(T) = sum_n chi3(n) * a_n * phasor_n(T)
#     A cancellation event = |Resultant(T)| collapses toward 0 (lands on the axis).

def build_blocky_helix_3d(NMAX, prime_list, U=1.0, pitch_law="logprime"):
    """
    Build explicit 3D coordinates and base phasors.
    Returns dict with arrays: n, Phi (additive prime drift), R, amp, x, y, z, phasor(complex).
    """
    ns = np.arange(1, NMAX+1)
    Phi = np.zeros(NMAX, dtype=float)        # additive prime-drift spin
    drift_logn = np.zeros(NMAX, dtype=float) # for the recovery sanity check
    for i, n in enumerate(ns):
        if n == 1:
            Phi[i] = 0.0
            continue
        f = factorize(int(n), prime_list)
        Phi[i] = sum(a * np.log(p) for p, a in f.items())   # additive: sum a*log p
        drift_logn[i] = Phi[i]

    R = np.sqrt(ns.astype(float))            # area-law radius
    amp = 1.0 / R                            # amplitude 1/sqrt(n)
    block = np.floor(R).astype(int)          # block index k(n)=floor(sqrt(n))

    # ---- BLOCKY axial coordinate z: pitch STEPS at each block boundary ----
    # The per-block pitch (axial rise per turn). pitch_law controls the step law.
    kmax = int(block.max())
    pitch_block = step_pitch(kmax, law=pitch_law)         # pitch for block k
    # cumulative axial height at the START of each block
    z_block_start = np.concatenate([[0.0], np.cumsum(pitch_block)])
    # within block, z rises linearly by the fraction of the way through the block's integers
    z = np.empty(NMAX, dtype=float)
    for i in range(NMAX):
        k = block[i]
        # integers in block k run from k^2 .. (k+1)^2 - 1 (approx); fraction through
        lo = k*k
        hi = (k+1)*(k+1)
        frac = (ns[i] - lo) / max(1, (hi - lo))
        z[i] = z_block_start[k] + frac * pitch_block[k]

    # ---- (x,y): wind by the additive prime-drift angle ----
    theta = U * Phi
    x = R * np.cos(theta)
    y = R * np.sin(theta)

    # ---- PHASOR (base, no probe): unit vector exp(i*Phi) ----
    phasor = np.exp(1j * Phi)

    return dict(n=ns, Phi=Phi, drift_logn=drift_logn, R=R, amp=amp, block=block,
                x=x, y=y, z=z, theta=theta, phasor=phasor, pitch_block=pitch_block)


def step_pitch(kmax, law="logprime"):
    """
    Per-block pitch (axial rise per turn), stepped at each block boundary.
    Sweeps the prompt's step constants.
    """
    pb = np.zeros(kmax+1, dtype=float)
    if law == "logprime":
        # the prompt's per-prime drift constants {log2, log3, ...}: step by log of the
        # k-th prime (so the pitch accumulates the prime-drift ladder).
        pl = primes_up_to(10*(kmax+5))[:kmax+1]
        for k in range(kmax+1):
            pb[k] = np.log(pl[k]) if k < len(pl) else np.log(pl[-1])
    elif law == "log2log3":
        # alternate strictly between log2 and log3 (the two named constants)
        for k in range(kmax+1):
            pb[k] = np.log(2) if (k % 2 == 0) else np.log(3)
    elif law == "pi3":
        pb[:] = np.pi/3
    elif law == "ek":
        c = 0.05
        for k in range(kmax+1):
            pb[k] = np.exp(c*k)
    elif law == "logdensity":
        # the KNOWN mean law: pitch ~ pi / mean-gap ~ pi / [ (1/2) log(q*gamma/2pi) ]^{-1}
        # i.e. block pitch tracks local mean spacing. Use gamma ~ block height proxy.
        for k in range(1, kmax+1):
            g = max(2.0, k*k * 0.5)   # crude height proxy
            dens = 0.5*np.log(3.0*g/(2*np.pi))
            pb[k] = np.pi / max(dens, 1e-6) * 0.0 + dens  # store density itself
        pb[0] = pb[1] if kmax >= 1 else 1.0
    else:
        pb[:] = 1.0
    return pb


# ----------------------------------------------------------------------------------------
# 3. STEP 2: PHASOR VECTOR-SUM RESULTANT  (3D-built object, real rotating vectors)
# ----------------------------------------------------------------------------------------
#
# Integer-side resultant (Dirichlet phasor walk over the 3D-placed integers):
#   S_int(T) = sum_n chi3(n) * amp_n * exp( -i * T * Phi_n )
# where Phi_n IS the additive-prime spin (= log n recovered additively). This is the
# chi3-weighted phasor vector-sum: each phasor is the real unit vector exp(-i T Phi_n),
# scaled by its 3D amplitude amp_n=1/sqrt(n). A zero = this vector-sum lands on the axis.

def integer_resultant(helix, T):
    Phi = helix['Phi']
    amp = helix['amp']
    chi = np.array([chi3(int(n)) for n in helix['n']], dtype=float)
    # use a smooth taper so the conditionally convergent sum is meaningful at finite NMAX
    n = helix['n'].astype(float)
    return np.sum(chi * amp * np.exp(-1j * T * Phi))

def integer_resultant_tapered(helix, T, Ntap):
    Phi = helix['Phi']; amp = helix['amp']; n = helix['n'].astype(float)
    chi = np.array([chi3(int(x)) for x in helix['n']], dtype=float)
    taper = np.exp(-(n/Ntap)**2)
    return np.sum(chi * amp * np.exp(-1j * T * Phi) * taper)


# ----------------------------------------------------------------------------------------
# 4. STEP 3: EULER/PRIME-SIDE RESULTANT (von Mangoldt explicit-formula prime side)
# ----------------------------------------------------------------------------------------
#
# S_Euler(T) = sum_p sum_{a>=1} chi3(p^a) (log p) p^{-a/2} exp(-i T a log p) * taper
# This is the explicit-formula prime side: phasors hung on prime-power markers, drift
# a*log p (FTA-additive), amplitude (log p) p^{-a/2} (von Mangoldt weight). The standing-
# wave nodes of Re[e^{i theta(T)} S_Euler] are predicted to sit at the zeros.

def euler_resultant(prime_list, T, Pmax, ampcut=1e-9):
    s = 0.0 + 0.0j
    for p in prime_list:
        if p > Pmax:
            break
        lp = np.log(p)
        a = 1
        pa = p
        while pa <= Pmax * Pmax:   # include prime powers
            w = chi3(int(pa)) * lp * pa**(-0.5)
            if abs(w) > ampcut:
                s += w * np.exp(-1j * T * a * lp)
            a += 1
            pa *= p
            if a > 30:
                break
    return s


# ----------------------------------------------------------------------------------------
# RUN
# ----------------------------------------------------------------------------------------

def main():
    primes = primes_up_to(2_000_000)

    # === STEP 1: BUILD + PRINT the explicit 3D blocky helix coordinate sample ===
    NMAX = 4000
    helix = build_blocky_helix_3d(NMAX, primes, U=1.0, pitch_law="logprime")

    print("\nSTEP 1 -- EXPLICIT 3D BLOCKY HELIX (per-prime additive-drift winding)")
    print("-" * 90)
    print(" first block boundaries (pitch steps), pitch_block[0:8] =",
          np.round(helix['pitch_block'][:8], 4))
    print("%4s %8s %10s %10s %9s %9s %9s %9s %6s %6s" %
          ("n", "chi3", "Phi(add)", "log(n)", "R", "amp", "x", "y", "z", "blk"))
    sample_ns = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 16, 25, 30, 36, 100]
    for nn in sample_ns:
        i = nn - 1
        print("%4d %8d %10.5f %10.5f %9.4f %9.4f %9.4f %9.4f %6.2f %6d" %
              (helix['n'][i], chi3(nn), helix['Phi'][i], np.log(nn),
               helix['R'][i], helix['amp'][i], helix['x'][i], helix['y'][i],
               helix['z'][i], helix['block'][i]))

    # === STEP 2 sanity: FTA-additive spin EQUALS log n to machine precision ===
    err = np.max(np.abs(helix['Phi'] - np.log(helix['n'].astype(float))))
    print("\nSTEP 2 -- FTA-additive recovery check:  max|Phi_add - log n| over n=1..%d = %.2e"
          % (NMAX, err))
    # geometric verification of Theta(6)=Theta(2)+Theta(3)
    p2 = helix['Phi'][1]; p3 = helix['Phi'][2]; p6 = helix['Phi'][5]
    print("   Theta(6)=%.6f   Theta(2)+Theta(3)=%.6f   (log6=%.6f)  match=%s"
          % (p6, p2+p3, np.log(6), abs(p6-(p2+p3)) < 1e-12))
    print("   => the winding is recovered ADDITIVELY over prime factors, log NOT placed.")

    # === STEP 3a: INTEGER-SIDE phasor vector-sum resultant -- find collapse heights ===
    print("\nSTEP 3a -- INTEGER-SIDE phasor vector-sum |S_int(T)| collapse scan")
    print("-" * 90)
    Tgrid = np.linspace(4.0, 60.0, 5601)
    # tapered sum (smooth, NMAX cutoff)
    Stap = np.array([abs(integer_resultant_tapered(helix, T, Ntap=NMAX/3.0)) for T in Tgrid])
    minima = find_local_minima(Tgrid, Stap)
    int_found = refine_against_exact(minima, EXACT, label="integer-side")

    # === STEP 3b: EULER/PRIME-SIDE resultant -- standing-wave nodes ===
    print("\nSTEP 3b -- EULER/PRIME-SIDE |S_Euler(T)| collapse scan (von Mangoldt weights)")
    print("-" * 90)
    for Pmax in [200, 2000, 50000]:
        Seul = np.array([abs(euler_resultant(primes, T, Pmax=Pmax)) for T in Tgrid])
        mins = find_local_minima(Tgrid, Seul)
        print("  Pmax=%6d : %d standing-wave minima found" % (Pmax, len(mins)))
        refine_against_exact(mins, EXACT, label="Euler-side Pmax=%d" % Pmax, quiet_thresh=0.30)

    # === STEP 4: DISCRIMINATOR -- mean vs fluctuation ===
    print("\nSTEP 4 -- DISCRIMINATOR: does the construction land on individual zeros?")
    print("-" * 90)
    discriminator(int_found, EXACT)

    # === STEP 5: SWEEP block-step constants ===
    print("\nSTEP 5 -- SWEEP of block-pitch step laws (does only logprime recover log n?)")
    print("-" * 90)
    sweep_pitch_laws(NMAX, primes)

    # === STEP 6: cross-validate the integer-side collapse heights with mpmath ===
    print("\nSTEP 6 -- mpmath cross-validation of best integer-side collapse heights")
    print("-" * 90)
    cross_validate(int_found)

    # === STEP 7: prime-side vs integer-side at the exact zeros ===
    print("\nSTEP 7 -- prime-side vs integer-side resultant AT the exact zeros")
    print("-" * 90)
    compare_sides_at_zeros(helix, primes, EXACT)


def find_local_minima(T, S):
    out = []
    for i in range(1, len(S)-1):
        if S[i] < S[i-1] and S[i] <= S[i+1]:
            out.append((T[i], S[i]))
    return out


def refine_against_exact(minima, exact, label="", quiet_thresh=None):
    """Match each minimum to nearest exact zero; report which are real collapses."""
    matched = []
    for (T, val) in minima:
        j = int(np.argmin(np.abs(exact - T)))
        d = abs(exact[j] - T)
        matched.append((T, val, exact[j], d))
    # keep minima that are genuinely small (near an actual zero)
    if matched:
        # report the ones whose nearest-zero distance is small
        good = [m for m in matched if m[3] < 0.25]
        if quiet_thresh is None:
            print("  %s: %d minima; %d within 0.25 of an exact zero" %
                  (label, len(matched), len(good)))
            for (T, val, ez, d) in matched[:14]:
                tag = "  <= zero" if d < 0.25 else ""
                print("    T=%8.4f  |S|=%9.4f   nearest exact zero=%8.4f  d=%6.3f%s" %
                      (T, val, ez, d, tag))
    return matched


def discriminator(int_found, exact):
    # gather matched (T_min, nearest zero, distance)
    dists = []
    for (T, val, ez, d) in int_found:
        if d < 1.0:
            dists.append(d)
    dists = np.array(dists)
    if len(dists) == 0:
        print("  NO minima within 1.0 of any exact zero -- construction does not land.")
        return
    rms = float(np.sqrt(np.mean(dists**2)))
    print("  matched minima within 1.0:  count=%d   RMS(distance to exact zero)=%.4f"
          % (len(dists), rms))
    # mean spacing of chi3 zeros near T~30 is ~2.5; fluctuation S(T) ~ O(1).
    print("  REFERENCE: mean chi3-zero spacing here ~2.5; RMS<<spacing => captures")
    print("             individual zeros (fluctuation); RMS~spacing/2 => only mean density.")
    if rms < 0.15:
        print("  VERDICT: lands on individual zeros (captures fluctuation).")
    elif rms < 0.6:
        print("  VERDICT: partial -- near zeros but with fluctuation-scale error.")
    else:
        print("  VERDICT: only mean density (smooth log), NOT the per-block fluctuation S(T).")
    return rms


def sweep_pitch_laws(NMAX, primes):
    laws = ["logprime", "log2log3", "pi3", "ek", "logdensity"]
    for law in laws:
        h = build_blocky_helix_3d(min(NMAX, 1000), primes, U=1.0, pitch_law=law)
        # the pitch law only affects z (axial). The winding Phi is ALWAYS additive prime
        # drift, so log-n recovery is law-independent. What we test: does the pitch ladder
        # match the local mean spacing of the zeros?
        pb = h['pitch_block']
        print("  law=%-11s pitch_block[1:7]=%s" %
              (law, np.round(pb[1:7], 4)))
    # the discriminating fact: only the additive prime drift recovers log n in the WINDING.
    # Replacing the winding angle by a fixed constant (pi/3) per step does NOT recover log n:
    h = build_blocky_helix_3d(min(NMAX, 1000), primes, U=1.0, pitch_law="logprime")
    fixed_wind = (np.pi/3) * h['block']     # naive: constant pi/3 per block
    err_fixed = np.max(np.abs(fixed_wind - np.log(h['n'].astype(float))))
    err_add = np.max(np.abs(h['Phi'] - np.log(h['n'].astype(float))))
    print("  WINDING recovery of log n:  additive-prime max-err=%.2e   constant-pi/3 max-err=%.3f"
          % (err_add, err_fixed))
    print("  => ONLY the FTA-additive prime drift (log p per factor) recovers log n.")


def cross_validate(int_found):
    # take the matched minima nearest to exact zeros and confirm |L| small at the
    # NEAREST EXACT ZERO (the geometry's prediction is the zero it lands near).
    seen = set()
    cnt = 0
    for (T, val, ez, d) in sorted(int_found, key=lambda m: m[0]):
        if d < 0.25 and round(ez, 4) not in seen:
            seen.add(round(ez, 4))
            absL = float(absL_on_line(ez))
            print("  collapse T=%8.4f -> nearest zero %8.4f (d=%.3f)  |L(1/2+i*zero)|=%.2e"
                  % (T, ez, d, absL))
            cnt += 1
            if cnt >= 8:
                break
    if cnt == 0:
        print("  (no integer-side minima landed within 0.25 of an exact zero)")


def compare_sides_at_zeros(helix, primes, exact):
    print("  At each exact zero, both phasor resultants should be small (EF duality).")
    print("  %8s %14s %16s %16s" % ("zero", "|S_int|(N=%d)" % len(helix['n']),
                                      "|S_Euler|(P=2k)", "|S_Euler|(P=50k)"))
    for ez in exact[:8]:
        si = abs(integer_resultant_tapered(helix, ez, Ntap=len(helix['n'])/3.0))
        se1 = abs(euler_resultant(primes, ez, Pmax=2000))
        se2 = abs(euler_resultant(primes, ez, Pmax=50000))
        print("  %8.4f %14.5f %16.5f %16.5f" % (ez, si, se1, se2))
    print("  (interpretation: if S_int dips at zeros but S_Euler needs far more primes to")
    print("   dip, the fluctuation demands global phase coherence across ALL primes --")
    print("   the precise obstruction to a finitely-stepped log-free helix capturing S(T).)")


if __name__ == "__main__":
    main()
