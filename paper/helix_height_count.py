import mpmath as mp
mp.mp.dps = 30
def ns(x,n=12): return mp.nstr(x,n)

g1 = mp.im(mp.zetazero(1))
print("first zeta zero (principal channel):  gamma_1 =", ns(g1))

print("\n[1] GEOMETRIC HEIGHT = the climb at which the standing wave vanishes")
print("    z = gamma_1 =", ns(g1), "  (the axial climb, = Im rho_1)")

print("\n[2] HOW MANY NUMBERS CONSUMED before it vanished")
# the convergent (finite) representation of zeta on the line is the Riemann-Siegel
# main sum: exactly  N = floor( sqrt(t / 2pi) )  integers contribute.
r = mp.sqrt(g1/(2*mp.pi))
N_rs = int(mp.floor(r))
print(f"    Riemann-Siegel main-sum length:  sqrt(gamma_1/2pi) = {ns(r,10)}")
print(f"    -> N = floor = {N_rs}   (a single integer, n=1 -- and note it sits a")
print(f"       hair under 1.5: the first zero lives right at the edge of the 1->2 step)")
print(f"    the 1->2 boundary is at t = 8*pi = {ns(8*mp.pi,8)} (gamma_2={ns(mp.im(mp.zetazero(2)),8)})")

# for contrast: if 'consumed' = all integers wound up to that climb by the area law
# n ~ R^2/C with C=(pi/3)^2 and (one natural identification) R = z:
C = (mp.pi/3)**2
N_area = g1**2 / C
print(f"\n    (area-law count up to the climb, C=(pi/3)^2, R=z:  n = z^2/C = {ns(N_area,7)}")
print(f"     ~ {int(mp.floor(N_area))} integers wound -- but the partial sum only")
print(f"     approaches 0 there; exact vanishing needs the RS-finite/limit form.)")
