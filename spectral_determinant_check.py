"""
Spectral / crossing-count check for the helix → ζ-zeros program.

Goal: see what the NUMBERS do before investing Lean time.

Ground truth (exact, from mpmath):
  - γ_n  : the imaginary parts of the nontrivial ζ zeros (14.1347, 21.0220, ...)
  - N(T) : the zero-counting function  #{0 < γ < T}  and its Riemann–von Mangoldt
           smooth form  (T/2π)(log(T/2π) − 1) + 7/8.

Helix geometry (from RequestProject/HelixArcLength.lean, zero-INDEPENDENT):
  - Archimedean spiral, radius R(t)=t, winding angle φ(t)=2π t (one turn per unit t).
  - planar arc length  arc0(k) = ∫₀ᵏ √(1+(2π t)²) dt
                              = [ 2πk·√(1+(2πk)²) + arcsinh(2πk) ] / (4π)   (≈ π k² large k).

Sam's calibration note (this run):
  "the arc length is NOT n·π itself; it is the COUNT of π-amplitude crossing events,
   measured in π/3-spaced units."

So below I compute the geometry's natural outputs and lay several candidate
"spectral value" recipes next to the true γ_n, so we can read off which one (if any)
tracks the zeros — and what sets the absolute scale (why γ_1 ≈ 14.13).
"""

import mpmath as mp

mp.mp.dps = 30
TWO_PI = 2 * mp.pi
PI3 = mp.pi / 3

# ---------------------------------------------------------------- ground truth
NZ = 30
gammas = [mp.im(mp.zetazero(n)) for n in range(1, NZ + 1)]


def N_smooth(T):
    T = mp.mpf(T)
    return (T / TWO_PI) * (mp.log(T / TWO_PI) - 1) + mp.mpf(7) / 8


def zero_spacing_mean(T):
    # mean gap between consecutive zeros near height T
    return TWO_PI / mp.log(T / TWO_PI)


# ---------------------------------------------------------------- helix geometry
def arc0(k):
    u = TWO_PI * k
    return (u * mp.sqrt(1 + u ** 2) + mp.asinh(u)) / (4 * mp.pi)


def height_at_arc(s):
    # invert arc0(t) = s  (the "purchaseHeight" at arc length s); seed with √(s/π)
    s = mp.mpf(s)
    return mp.findroot(lambda t: arc0(t) - s, mp.sqrt(s / mp.pi) + mp.mpf("1e-6"))


# ---------------------------------------------------------------- candidate recipes
# Each maps an index m=1,2,... to a predicted ordinate v_m that should ~ γ_m.

def recipe_A(m):
    # π/3-spaced angular crossings: φ=2πt spaced π/3  ⇒  t_m = m/6 ;  value = arc length there
    return arc0(mp.mpf(m) / 6)

def recipe_B(m):
    # arc length itself in π/3 units: value = m · (π/3)
    return m * PI3

def recipe_C(m):
    # code-literal purchaseHeight: height where arc0(t) = m·π
    return height_at_arc(m * mp.pi)

def recipe_D(m):
    # height (the "iy" coordinate) at the π/3-angular crossing t_m = m/6
    return mp.mpf(m) / 6


def fmt(x):
    return f"{float(x):>12.4f}"


print("=" * 78)
print("GROUND TRUTH — true nontrivial ζ-zero ordinates γ_n and the zero density")
print("=" * 78)
print(f"{'n':>3} {'γ_n (true)':>14} {'gap γ_n-γ_{n-1}':>16} {'mean gap 2π/log(γ/2π)':>24}")
prev = mp.mpf(0)
for n in range(1, 16):
    g = gammas[n - 1]
    gap = g - prev
    print(f"{n:>3} {float(g):>14.5f} {float(gap):>16.4f} {float(zero_spacing_mean(g)):>24.4f}")
    prev = g

print()
print("Counting function N(T) vs smooth (T/2π)(log(T/2π)−1)+7/8:")
for T in [20, 50, 100, 200]:
    actual = sum(1 for g in (mp.im(mp.zetazero(n)) for n in range(1, 200)) if g < T)
    print(f"  T={T:>4}:  N(T) actual = {actual:>3}   smooth = {float(N_smooth(T)):>8.3f}")

print()
print("=" * 78)
print("HELIX GEOMETRY — candidate spectral recipes vs the true γ_n")
print("=" * 78)
print(f"{'m':>3} {'γ_m (true)':>12} {'A: arc0(m/6)':>14} {'B: m·π/3':>12} "
      f"{'C: purchHt(mπ)':>16} {'D: m/6':>10}")
for m in range(1, 16):
    g = gammas[m - 1]
    print(f"{m:>3} {fmt(g)} {fmt(recipe_A(m))} {fmt(recipe_B(m))} "
          f"{fmt(recipe_C(m))} {fmt(recipe_D(m))}")

print()
print("Growth-rate fingerprints (does the recipe's spacing track the zeros'?):")
print("  zeros γ_n      : grow like 2πn/log n  (density increases ~ log T)")
print("  A arc0(m/6)    : grows like π(m/6)² = m²·π/36   (quadratic — density DEC.)")
print("  B m·π/3        : linear, constant spacing π/3 ≈ 1.047")
print("  C purchHt(mπ)  : grows like √m            (density increases, but as √)")
print("  D m/6          : linear, constant spacing 1/6")
print()
print("Decisive test — ratio v_m / γ_m should approach a CONSTANT if the law is right:")
print(f"{'m':>3} {'A/γ':>10} {'B/γ':>10} {'C/γ':>10} {'D/γ':>10}")
for m in [1, 5, 10, 15, 20, 25, 30]:
    g = gammas[m - 1]
    print(f"{m:>3} {float(recipe_A(m)/g):>10.4f} {float(recipe_B(m)/g):>10.4f} "
          f"{float(recipe_C(m)/g):>10.4f} {float(recipe_D(m)/g):>10.4f}")
