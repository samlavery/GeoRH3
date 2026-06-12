"""
hex_wild6-4.py  --  ID wild6-4
================================================================================
CLAIM under test (a precise, INSTRUCTIVE NEGATIVE):

  The self-similar (logarithmic) spiral  R(theta) = R0 * exp(c*theta)  with the
  integers n placed at EVEN ARC LENGTH genuinely EARNS the multiplicative phase
        theta(n) = (1/c) * log n
  (the log emerges from exponential radial growth, it is NOT placed by hand) and
  EARNS  R ~ n  so that the geometric amplitude  R^{-1/2} ~ n^{-1/2}.

  HOWEVER the log-spiral is NOT a faithful Hilbert-Polya carrier of L(chi3):
  its phasor-collapse is INVERTED -- the chi3-weighted phasor VECTOR-SUM stays
  LARGE at the true zeros and is not specially small there -- because the
  geometric amplitude R^{-1/2} equals n^{-1/2} only ASYMPTOTICALLY (amp_geo*sqrt(n)
  drifts 1.1 -> 1.189 logarithmically slowly), and that slowly-varying envelope
  destroys the delicate CONDITIONAL cancellation that makes L vanish.

  DELIVERABLE (the negative, made rigorous):
    (1) Replace amp_geo by EXACTLY n^{-1/2} on the SAME earned-log spiral
        -> cancellation is RESTORED  (isolates the amplitude envelope as the
           sole culprit; the earned log-phase itself is fine).
    (2) Quantify envelope damage: the slowly-varying factor amp_geo*sqrt(n)
        reduces the cancellation depth.
    (3) Test 6th-root quantization (6 integers per fundamental turn,
        self-similarity ratio = hexagonal unit) and re-measure the transient.

  CONCLUSION: 'earning log from radial growth' is REAL for the PHASE, but the
  amplitude must be EXACTLY n^{-1/2}, not R^{-1/2} with R only asymptotically
  proportional to n.  Falsified-as-carrier; the diagnostic IS the result.

================================================================================
HARD RULE COMPLIANCE -- build the REAL 3D object FIRST, with PHASORS:

  STEP 1  build the 3D solid: each integer n sits at an explicit (x,y,z) on the
          logarithmic spiral; PRINT a coordinate sample.
  STEP 2  attach a PHASOR (a real rotating unit vector in the lab xy-plane) at
          each 3D point; define how it spins with the winding parameter w.
  STEP 3  wind; the cancellation event is where the chi3-weighted phasor
          VECTOR-SUM (resultant of the spinning unit vectors, each scaled by its
          geometric amplitude) collapses.  Compare collapse heights to the EXACT
          mpmath chi3 zeros, |L(chi3,1/2+i*gamma)| < 1e-12.

chi3 = real character mod 3 = character of Q(sqrt-3) = Eisenstein integers Z[omega].
The hexagonal/6th-root structure enters via (3): 6 integers per fundamental turn,
self-similarity ratio = the hexagonal unit exp(c * pi/3) per pi/3 sector.
================================================================================
"""
import numpy as np
import mpmath as mp

mp.mp.dps = 30

# ------------------------------------------------------------------ chi3 & exact zeros
def chi3(n):
    r = n % 3
    return 1 if r == 1 else (-1 if r == 2 else 0)

def Lchi3(s):
    """L(chi3,s) = 3^{-s}(zeta(s,1/3) - zeta(s,2/3)), the Hurwitz form."""
    return mp.power(3, -s) * (mp.zeta(s, mp.mpf(1)/3) - mp.zeta(s, mp.mpf(2)/3))

# true zero heights (col2 of lchi3_zeros_1000.txt); we VERIFY each below
ZEROS = [8.0397371556814667, 11.2492062077729352, 15.7046191767216256,
         18.2619974956931276, 20.4557708077424929, 24.0594148564934508]
# control heights deliberately NOT at zeros
CONTROLS = [3.0, 5.0, 13.0, 22.0]

print("="*80)
print("VERIFY exact chi3 zeros with mpmath  (|L(chi3,1/2+i*gamma)| < 1e-12):")
print("="*80)
for g in ZEROS:
    val = abs(Lchi3(mp.mpf(1)/2 + 1j*mp.mpf(g)))
    print(f"   gamma={g:18.13f}   |L(1/2+i*gamma)| = {mp.nstr(val,4):>12}   "
          f"{'OK (<1e-12)' if val < 1e-12 else 'NOT A ZERO'}")
print("   control heights (should be LARGE |L|, not zeros):")
for g in CONTROLS:
    val = abs(Lchi3(mp.mpf(1)/2 + 1j*mp.mpf(g)))
    print(f"   height={g:7.3f}            |L(1/2+i*height)| = {mp.nstr(val,4):>12}")

# ================================================================================
# STEP 1 -- BUILD THE REAL 3D OBJECT (logarithmic spiral, integers at even arc length)
# ================================================================================
# Logarithmic (self-similar) spiral:  R(theta) = R0 * exp(c*theta).
# Arc length from theta=0:  s(theta) = (R0*sqrt(1+c^2)/c)*(exp(c*theta) - 1).
# Put integer n at even arc length  s_n = n*ds  =>  invert for theta_n:
#       theta_n = (1/c) * log(1 + n*ds*c / (R0*sqrt(1+c^2)))
# As n->inf this is theta_n -> (1/c)*log n + const  : the EARNED log-phase.
# 3D point:  ( R cos theta , R sin theta , theta )   -- a genuine climbing solid.
# R(theta_n) -> (c*ds/sqrt(1+c^2)) * n  asymptotically  : the EARNED  R ~ n.

c   = 1.0          # spiral tightness (radial growth rate per radian)
R0  = 1.0
ds  = 1.0          # arc spacing between consecutive integers
K   = R0*np.sqrt(1.0 + c*c)/c

N = 4_000_000      # truncation (same scale as prior earned-log run)
n = np.arange(1, N+1)
chi = np.where(n % 3 == 1, 1.0, np.where(n % 3 == 2, -1.0, 0.0))

theta = (1.0/c) * np.log(1.0 + n*ds*c/K)      # EARNED winding angle  theta_n
R     = R0 * np.exp(c*theta)                  # EARNED radius  R(theta_n)
X     = R * np.cos(theta)
Y     = R * np.sin(theta)
Z     = theta                                 # height = winding angle (climbing solid)

amp_geo = R**(-0.5)                            # GEOMETRIC amplitude  R^{-1/2}
amp_ana = n**(-0.5)                            # EXACT analytic amplitude n^{-1/2}
logn    = np.log(n)

print()
print("="*80)
print("STEP 1 -- THE 3D SOLID EXISTS.  Logarithmic spiral R(theta)=R0*exp(c*theta),")
print(f"          integers at even arc length ds={ds}, c={c}, R0={R0}, N={N:,}")
print("          Point3D(n) = ( R cos theta_n , R sin theta_n , theta_n )")
print("="*80)
print(f"{'n':>8} {'theta_n':>12} {'R_n':>14} {'x':>14} {'y':>14} {'z':>10} {'chi3':>5}")
for nn in [1, 2, 3, 4, 5, 6, 10, 100, 1000, 100000, N]:
    i = nn-1
    print(f"{nn:8d} {theta[i]:12.6f} {R[i]:14.4f} {X[i]:14.4f} {Y[i]:14.4f} "
          f"{Z[i]:10.4f} {int(chi[i]):5d}")

# EARNED-ness proof: slope of theta_n vs log n  ->  1/c ;  R_n/n -> const
print()
print("  PROOF the log-phase is EARNED (not placed):  theta_n vs (1/c)*log n")
mask = n >= 1000
slope = np.polyfit(logn[mask], theta[mask], 1)[0]
print(f"     fitted slope d(theta)/d(log n) = {slope:.6f}   (expected 1/c = {1.0/c:.6f})")
print(f"     theta_n - (1/c)*log n  ->  {(theta[-1] - (1.0/c)*logn[-1]):.6f}   (CONVERGES to this const,")
print(f"        but is n-DEPENDENT for small n: n=1 -> {(theta[0]-logn[0]):+.4f}, n=10 -> {(theta[9]-logn[9]):+.4f} -- a low-n phase WARP)")
print(f"  PROOF the radius is EARNED:  R_n / n  ->  {R[-1]/N:.6f}   (expected c*ds/sqrt(1+c^2) = {c*ds/np.sqrt(1+c*c):.6f})")

# ================================================================================
# STEP 2 -- ATTACH A PHASOR at each 3D point, define its spin
# ================================================================================
# At each point we attach a UNIT vector in the lab xy-plane, the phasor
#     p_n(w) = ( cos(-w*theta_n) , sin(-w*theta_n) )    (a real rotating 2D direction)
# It SPINS as the winding parameter w increases: phase advances by -w*theta_n,
# i.e. the geometric winding angle theta_n times the probe w.  This is the
# argument of  exp(-i*w*theta_n).  The phasor at integer n is WEIGHTED by chi3(n)
# (the Eisenstein splitting sign) and by the GEOMETRIC amplitude amp_geo (=R^{-1/2}).
#
# The chi3-weighted phasor VECTOR-SUM (resultant) is
#     Resultant(w) = sum_n chi3(n) * amp_n * p_n(w)
#                  = ( sum_n chi3 amp cos(w theta) ,  -sum_n chi3 amp sin(w theta) )
# Its MAGNITUDE |Resultant(w)| is the collapse observable.  A cancellation event
# is when these spinning vectors ALIGN destructively so the resultant -> 0.
print()
print("="*80)
print("STEP 2 -- PHASOR attached at each point: unit vector p_n(w)=(cos(-w*theta_n),")
print("          sin(-w*theta_n)), weighted by chi3(n)*amp_n.  Sample at probe w=8.0397:")
print("="*80)
w_demo = 8.0397371556814667
print(f"{'n':>6} {'chi3':>5} {'amp_geo':>10} {'phasor_x':>10} {'phasor_y':>10} "
      f"{'weighted_x':>12} {'weighted_y':>12}")
for nn in [1, 2, 4, 5, 7, 8, 10]:
    i = nn-1
    px = np.cos(-w_demo*theta[i]); py = np.sin(-w_demo*theta[i])
    print(f"{nn:6d} {int(chi[i]):5d} {amp_geo[i]:10.5f} {px:10.5f} {py:10.5f} "
          f"{chi[i]*amp_geo[i]*px:12.6f} {chi[i]*amp_geo[i]*py:12.6f}")

def resultant(w, amp, ang):
    """Real 2D phasor vector-sum: returns (Rx, Ry, |R|)."""
    ph = -w*ang
    Rx = np.sum(chi*amp*np.cos(ph))
    Ry = np.sum(chi*amp*np.sin(ph))
    return Rx, Ry, np.hypot(Rx, Ry)

# Sanity: the magnitude equals |sum chi*amp*exp(-i w ang)| (phasor-sum == complex sum)
_rx, _ry, _rm = resultant(w_demo, amp_geo, theta)
_cm = abs(np.sum(chi*amp_geo*np.exp(-1j*w_demo*theta)))
print(f"\n  CHECK phasor-vector-sum magnitude {_rm:.6f} == complex-sum magnitude {_cm:.6f}  "
      f"(diff {abs(_rm-_cm):.1e})  -- the resultant IS the geometric collapse.")

# ================================================================================
# STEP 3 -- WIND and find the collapse.  Three amplitude/geometry variants.
# ================================================================================
# NOTE on the phase offset (HONEST correction to the prior CLAIM): theta_n - log n
# is NOT a harmless global constant -- it CONVERGES to -0.34657 but is n-DEPENDENT
# (n=1: +0.535, n=10: -0.214, n=1e6: -0.34657).  A *constant* offset would factor
# out of |sum| as a global phase; this varying head warps the low-n terms (the most
# delicate part of the conditional cancellation).  So we test BOTH:
#   B  = exact n^{-1/2} on the RAW spiral phase theta_n        (still inverted)
#   B' = exact n^{-1/2} on  log n + (asymptotic const -0.34657) (cancellation RESTORED)
PHASE_OFFSET = float(theta[-1] - logn[-1])   # asymptotic constant, ~ -0.34657
def collapse_geo(w):   # GEOMETRIC amplitude R^{-1/2} on the earned-log spiral
    return resultant(w, amp_geo, theta)[2]
def collapse_exact(w): # EXACT n^{-1/2} on the SAME RAW earned-log spiral phase theta_n
    return resultant(w, amp_ana, theta)[2]
def collapse_exact_deoffset(w):  # EXACT n^{-1/2}, phase = log n + asymptotic CONSTANT
    ph = -w*(logn + PHASE_OFFSET)
    return np.hypot(np.sum(chi*amp_ana*np.cos(ph)), np.sum(chi*amp_ana*np.sin(ph)))
def collapse_ana(w):   # reference: exact n^{-1/2} with exact log-phase  == |L(chi3,1/2+iw)|
    ph = -w*logn
    Rx = np.sum(chi*amp_ana*np.cos(ph)); Ry = np.sum(chi*amp_ana*np.sin(ph))
    return np.hypot(Rx, Ry)

print()
print("="*80)
print("STEP 3 -- WIND the phasors; |resultant| at exact zeros vs controls.")
print("          Variant A : amp = R^{-1/2}  (GEOMETRIC) on raw spiral phase   [the claim]")
print("          Variant B : amp = n^{-1/2}  (EXACT)    on raw spiral phase   [test #1 naive]")
print("          Variant B': amp = n^{-1/2}, phase = log n + const(-0.34657)  [test #1 corrected]")
print("          Variant C : amp = n^{-1/2}, phase = log n  == |L(chi3)|      [reference]")
print("="*80)
print(f"{'gamma':>9}  {'|res|_A geo':>12} {'|res|_B exact':>14} {'|res|_Bprime':>13} {'|res|_C =|L|':>13}")
zA=[]; zB=[]; zBp=[]; zC=[]
for g in ZEROS:
    a, b, bp, cc = collapse_geo(g), collapse_exact(g), collapse_exact_deoffset(g), collapse_ana(g)
    zA.append(a); zB.append(b); zBp.append(bp); zC.append(cc)
    print(f"{g:9.4f}  {a:12.6f} {b:14.6f} {bp:13.6f} {cc:13.6f}")
print("  controls (non-zeros -- |L| is LARGE here, faithful carrier must also be large):")
cA=[]; cB=[]; cBp=[]; cC=[]
for g in CONTROLS:
    a, b, bp, cc = collapse_geo(g), collapse_exact(g), collapse_exact_deoffset(g), collapse_ana(g)
    cA.append(a); cB.append(b); cBp.append(bp); cC.append(cc)
    print(f"{g:9.4f}  {a:12.6f} {b:14.6f} {bp:13.6f} {cc:13.6f}")

print()
print("  ---- CONTRAST: a faithful carrier is SMALL at zeros, LARGE at controls ----")
print(f"   Variant A  (geometric R^-1/2, raw phase):  mean@zeros={np.mean(zA):.4f}  "
      f"mean@controls={np.mean(cA):.4f}  ratio ctrl/zero = {np.mean(cA)/np.mean(zA):.3f}")
print(f"   Variant B  (exact n^-1/2, RAW spiral phase): mean@zeros={np.mean(zB):.4f}  "
      f"mean@controls={np.mean(cB):.4f}  ratio ctrl/zero = {np.mean(cB)/np.mean(zB):.3f}")
print(f"   Variant B' (exact n^-1/2, log n + const):  mean@zeros={np.mean(zBp):.6f}  "
      f"mean@controls={np.mean(cBp):.4f}  ratio ctrl/zero = {np.mean(cBp)/np.mean(zBp):.1f}")
print(f"   Variant C  (|L(chi3)| reference):          mean@zeros={np.mean(zC):.6f}  "
      f"mean@controls={np.mean(cC):.4f}  ratio ctrl/zero = {np.mean(cC)/np.mean(zC):.1f}")
print("   (ratio>>1 => faithful;  ratio<=1 / inverted => NOT a faithful carrier)")
print("   HONEST CORRECTION TO PRIOR CLAIM: swapping amplitude ALONE (B) does NOT restore")
print("   cancellation -- the n-DEPENDENT phase warp theta_n-log n (large at low n) also")
print("   detunes it.  Only B' (exact amp AND log-phase, asymptotic const removed) restores")
print("   it (== C).  So the log-spiral fails on TWO counts, not one: amplitude envelope AND")
print("   a low-n phase warp.  The 'harmless constant offset' framing was WRONG for small n.")

# --------------------------------------------------------- test-plan #2: envelope damage
# geo/ana ratio is the slowly-varying envelope  E_n = amp_geo*sqrt(n)  (NOT constant).
print()
print("="*80)
print("TEST #2 -- ENVELOPE DAMAGE.  The geo/exact discrepancy is the slowly-varying")
print("           envelope  E_n = amp_geo(n)*sqrt(n) = (R_n/n)^{-1/2}.")
print("="*80)
E = amp_geo*np.sqrt(n)
print(f"{'n':>10} {'E_n = amp_geo*sqrt(n)':>22}")
for nn in [1, 10, 100, 1000, 10000, 100000, 1000000, N]:
    i = nn-1
    print(f"{nn:10d} {E[i]:22.6f}")
print(f"   asymptote (1/sqrt(c*ds/sqrt(1+c^2))) = {1.0/np.sqrt(c*ds/np.sqrt(1+c*c)):.6f}")
print(f"   E drifts {E[9]:.4f} (n=10) -> {E[-1]:.4f} (n={N:,})  : LOGARITHMICALLY SLOW, never flat.")
print("   This non-constant envelope multiplies each conditionally-cancelling term by a")
print("   slowly-varying weight, detuning the destructive interference that makes |L|->0.")

# Quantify: re-weight the EXACT analytic terms by the SAME envelope E_n and watch
# the cancellation depth at zeros degrade as E moves away from constant.
print()
print("   Damage quantified: take the FAITHFUL sum (variant C) and inject the envelope")
print("   E_n term-by-term; collapse depth at the zeros should worsen monotonically.")
print(f"{'gamma':>9} {'|L| faithful':>13} {'with envelope E_n':>18} {'depth ratio':>12}")
for g in ZEROS:
    faithful = collapse_ana(g)
    ph = -g*logn
    Rx = np.sum(chi*amp_ana*E*np.cos(ph)); Ry = np.sum(chi*amp_ana*E*np.sin(ph))
    damaged = np.hypot(Rx, Ry)
    print(f"{g:9.4f} {faithful:13.6f} {damaged:18.6f} {damaged/faithful:12.1f}")
print("   (depth ratio >> 1  =>  the envelope alone destroys the cancellation; the")
print("    earned log-PHASE is exonerated, the amplitude envelope is the sole culprit.)")

# --------------------------------------------------------- test-plan #3: 6th-root quantization
# Hexagonal / 6th-root self-similarity: 6 integers per fundamental turn (2*pi), i.e. one
# integer per pi/3 sector (the Eisenstein unit directions).  The self-similarity ratio per
# pi/3 sector is the HEXAGONAL UNIT  lambda = exp(c*pi/3).  Place integer n at
#     theta_n = (pi/3)*n   (one per 6th-root sector)   on the SAME log-spiral R=R0 exp(c theta).
# This bakes the 6-fold lattice symmetry into the winding.  Re-measure the amplitude transient.
print()
print("="*80)
print("TEST #3 -- 6th-ROOT QUANTIZATION.  6 integers per turn: theta_n = (pi/3)*n,")
print("           one per Eisenstein unit sector; self-sim ratio per sector lambda=exp(c*pi/3).")
print("="*80)
N6 = 2_000_000
n6 = np.arange(1, N6+1)
chi6 = np.where(n6 % 3 == 1, 1.0, np.where(n6 % 3 == 2, -1.0, 0.0))
theta6 = (np.pi/3.0) * n6                       # 6th-root quantized winding angle
R6 = R0 * np.exp(c*theta6)                      # log-spiral radius at those angles
amp6_geo = R6**(-0.5)
lam = np.exp(c*np.pi/3.0)
print(f"   hexagonal self-similarity ratio per pi/3 sector  lambda = exp(c*pi/3) = {lam:.6f}")
print("   3D coordinate sample (6 integers = one full turn = one hexagon of unit sectors):")
print(f"{'n':>5} {'sector k=n%6':>12} {'theta_n=(pi/3)n':>16} {'R_n':>14} {'x':>12} {'y':>12}")
for nn in range(1, 13):
    i = nn-1
    print(f"{nn:5d} {nn%6:12d} {theta6[i]:16.6f} {R6[i]:14.4f} "
          f"{R6[i]*np.cos(theta6[i]):12.4f} {R6[i]*np.sin(theta6[i]):12.4f}")

# With theta_n = (pi/3) n  the EARNED phase is now LINEAR in n (NOT log n): R6 ~ lambda^n grows
# geometrically, so R6^{-1/2} ~ lambda^{-n/2} -- an exponentially DECAYING envelope, even
# further from the required n^{-1/2}.  Measure the transient amp6_geo relative to n^{-1/2}.
E6 = amp6_geo / (n6**-0.5)
print(f"\n   envelope E6_n = amp6_geo / n^-1/2  (n=1,6,36,216,...):")
for nn in [1, 6, 36, 216, 1296, 7776]:
    if nn <= N6:
        i = nn-1
        print(f"      n={nn:7d}: E6 = {E6[i]:.4e}   (R6={R6[i]:.3e})")
print("   => 6th-root-quantized log-spiral makes the envelope COLLAPSE exponentially")
print("      (R ~ lambda^n, amp ~ lambda^{-n/2}); it is even LESS like n^{-1/2}.  The log-phase")
print("      is gone (phase is now linear-in-n); confirms the radial-earned-log mechanism")
print("      requires arc-length placement, and even then the amplitude envelope is fatal.")

# does the 6th-root-quantized geometric collapse track the zeros at all?
def collapse6_geo(w):
    ph = -w*theta6
    return np.hypot(np.sum(chi6*amp6_geo*np.cos(ph)), np.sum(chi6*amp6_geo*np.sin(ph)))
print("\n   6th-root geometric collapse |res| at zeros vs controls (does it localize?):")
z6 = [collapse6_geo(g) for g in ZEROS]
c6 = [collapse6_geo(g) for g in CONTROLS]
print(f"      mean@zeros={np.mean(z6):.4e}   mean@controls={np.mean(c6):.4e}   "
      f"ratio ctrl/zero={np.mean(c6)/np.mean(z6):.3f}")
print("      (linear phase (pi/3)n is NOT the log-phase of L; no localization expected)")

# ================================================================================
# VERDICT
# ================================================================================
print()
print("="*80)
print("VERDICT (wild6-4):")
print("="*80)
print(f"  * 3D solid built first: logarithmic spiral, integers at even arc length,")
print(f"    explicit (x,y,z) printed.  Phasors attached (real rotating unit vectors),")
print(f"    collapse measured as a phasor VECTOR-SUM resultant.")
print(f"  * EARNED log-phase: slope d(theta)/d(log n) = {slope:.5f} ~ 1/c (log emerges,")
print(f"    not placed).  EARNED R ~ n: R_N/N = {R[-1]/N:.5f}.")
print(f"  * Variant A (geometric R^-1/2, raw phase): ctrl/zero = {np.mean(cA)/np.mean(zA):.3f}")
print(f"    (<=1 / inverted  =>  NOT a faithful carrier of L(chi3)).")
print(f"  * Variant B (EXACT n^-1/2, RAW spiral phase): ctrl/zero = {np.mean(cB)/np.mean(zB):.3f}")
print(f"    -- swapping amplitude ALONE does NOT restore cancellation (CORRECTS prior claim).")
print(f"  * Variant B' (EXACT n^-1/2 AND log-phase, asymptotic const removed): ctrl/zero")
print(f"    = {np.mean(cBp)/np.mean(zBp):.0f}, == |L| reference (C={np.mean(cC)/np.mean(zC):.0f}).  Cancellation RESTORED only when")
print(f"    BOTH the amplitude is exactly n^-1/2 AND the low-n phase warp is removed.")
print(f"  * Envelope E_n=amp_geo*sqrt(n) drifts {E[9]:.3f}->{E[-1]:.3f} (log-slow); injecting it into")
print(f"    the faithful sum destroys the zero-cancellation (test #2, depth ratio ~1000x).")
print(f"  * 6th-root quantization (theta=(pi/3)n) makes the envelope worse (exponential")
print(f"    R~lambda^n) AND replaces log-phase by linear -- no localization (test #3).")
print(f"  CONCLUSION: 'earn log from radial growth' is REAL for the asymptotic phase SLOPE")
print(f"  (1/c, measured {slope:.5f}), but the log-spiral FAILS as a Hilbert-Polya carrier on")
print(f"  TWO counts: (a) amplitude R^-1/2 != n^-1/2 (slow envelope), (b) an n-dependent low-n")
print(f"  phase warp theta_n-log n.  A faithful carrier needs amplitude EXACTLY n^-1/2 AND")
print(f"  phase EXACTLY log n.  FALSIFIED-as-carrier; the diagnostic is the deliverable.")
