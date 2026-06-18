"""
Full-channel spectral-determinant test.

Channel (trivial character), as defined: every number n contributes a phasor to the
  positive channel  n^(-s)        (magnitude n^(-Re s), spin -Im s · log n)
  negative channel  n^(-(1-s))    (the s -> 1-s reflection)
summed over ALL n.  Vanishing = the entire phasor sum cancels = the two channel sums cancel.

Continued (the honest infinite object):
  posChannel(s) = Σ_n n^(-s)      = ζ(s)
  negChannel(s) = Σ_n n^(-(1-s))  = ζ(1-s)
  channel(s)    = ζ(s) + ζ(1-s)

The spectral-determinant test: find every zero (cancellation) of channel(s) in the
critical strip and read off Re s.  Forcing inherited  <=>  every zero has Re s = 1/2.
"""

import mpmath as mp

mp.mp.dps = 20


def channel(s):
    return mp.zeta(s) + mp.zeta(1 - s)


print("=" * 72)
print("FULL CHANNEL   F(s) = Σ_n (n^-s + n^-(1-s)) = ζ(s) + ζ(1-s)")
print("=" * 72)

# (1) on the line F is real (the two channels are conjugate there): F = 2·Re ζ(1/2+it)
print("\n(1) On Re=1/2, F is real (= 2·Re ζ): the channels have equal magnitude, opposite spin")
for t in [5, 10, 14.1347, 20, 25.0109]:
    s = mp.mpf(1) / 2 + 1j * mp.mpf(t)
    F = channel(s)
    print(f"   t={t:>9}:  F = {complex(F).real:+.6f} {complex(F).imag:+.2e}i   "
          f"|posCh|={float(abs(mp.zeta(s))):.4f}  |negCh|={float(abs(mp.zeta(1-s))):.4f}")

# (2) ON-LINE cancellations: real sign changes of F on Re=1/2
print("\n(2) ON-LINE cancellations of the channel (sign changes of F on Re=1/2):")
def Fline(t):
    return mp.re(channel(mp.mpf(1) / 2 + 1j * mp.mpf(t)))

onzeros = []
t = mp.mpf("0.4"); dt = mp.mpf("0.1"); prev = Fline(t)
while t < 40:
    t2 = t + dt; cur = Fline(t2)
    if prev * cur < 0:
        onzeros.append(mp.findroot(Fline, (t, t2), solver="bisect"))
    t, prev = t2, cur
print("   channel zeros on the line at t =", [round(float(z), 4) for z in onzeros[:18]])
gammas = [round(float(mp.im(mp.zetazero(n))), 4) for n in range(1, 9)]
print("   (actual ζ zeros γ_n, for contrast:  ", gammas, ")")

# (3) THE FORCING TEST: search the whole strip for ANY off-line zero
print("\n(3) FORCING TEST — grid-search the strip 0.05<Re<0.95, 0<Im<45 for ALL zeros:")
roots = []
for si in range(5, 96, 5):          # Re = 0.05 .. 0.95
    for ti in range(0, 90, 1):      # Im = 0 .. 45 (step 0.5)
        seed = mp.mpf(si) / 100 + 1j * (mp.mpf(ti) / 2)
        try:
            r = mp.findroot(channel, seed)
            if (mp.mpf("0.02") < mp.re(r) < mp.mpf("0.98")
                    and mp.mpf("0.2") < mp.im(r) < 46
                    and abs(channel(r)) < mp.mpf(10) ** (-9)):
                if all(abs(r - q) > mp.mpf("1e-5") for q in roots):
                    roots.append(r)
        except Exception:
            pass

roots.sort(key=lambda r: float(mp.im(r)))
on_ct = off_ct = 0
print(f"   {'Re s':>10} {'Im s':>12}   status")
for r in roots:
    off = abs(mp.re(r) - mp.mpf("0.5")) > mp.mpf("1e-5")
    on_ct += (not off); off_ct += off
    print(f"   {float(mp.re(r)):>10.5f} {float(mp.im(r)):>12.5f}   "
          f"{'<<<<< OFF LINE' if off else 'on line'}")

print(f"\n   zeros on Re=1/2: {on_ct}      OFF the line: {off_ct}")
print("   VERDICT: forcing inherited — channel cancels only on Re=1/2"
      if off_ct == 0 else
      "   VERDICT: channel has OFF-LINE zeros — the sum does NOT inherit single-pair forcing")

# (4) WHY — the functional equation factors the channel:  ζ(s) = Φ(s)·ζ(1-s),
#     Φ(s) = ζ(s)/ζ(1-s)  (the channel ratio).  Then
#        F(s) = ζ(s) + ζ(1-s) = ζ(1-s)·(Φ(s) + 1).
#     So the channel cancels two ways:
#       (a) Φ(s) = -1  : the two channels are antiphase AND equal magnitude (|Φ|=1),
#                        and |Φ|=1 happens ONLY on Re=1/2  -> on-line, UNCONDITIONALLY.
#       (b) ζ(1-s) = 0 : s = 1 - ρ for an actual zeta zero ρ (reflected).
def Phi(s):
    return mp.zeta(s) / mp.zeta(1 - s)

print("\n(4) WHY all-on-line:  F(s) = ζ(1-s)·(Φ(s)+1),  Φ(s)=ζ(s)/ζ(1-s)")
print("    |Φ(σ+20i)| = 1 only on Re=1/2 (the channel-balance forcing, unconditional):")
for sig in [0.30, 0.40, 0.50, 0.60, 0.70]:
    print(f"      Re={sig:.2f}:  |Φ| = {float(abs(Phi(mp.mpf(sig) + 20j))):.4f}")
print("    classify each on-line channel zero — antiphase (Φ=-1) vs an actual zeta zero:")
for z in onzeros[:12]:
    s = mp.mpf(1) / 2 + 1j * z
    zzero = abs(mp.zeta(s)) < mp.mpf(10) ** (-8)
    print(f"      t={float(z):>9.4f}:  "
          f"{'ζ zero (reflected)        ' if zzero else 'Φ(s)=-1  channel antiphase'}"
          f"   |Φ|={float(abs(Phi(s))):.4f}")
