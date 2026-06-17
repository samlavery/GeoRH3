import mpmath as mp
mp.mp.dps = 20
def ns(x,n=10): return mp.nstr(x,n)

print("OFF-LINE PAIR  rho = sigma+i*gamma ,  rho* = (1-sigma)+i*gamma  (FE reflection)")
print("represented at each level.  beta := sigma = Re(rho).\n")

C = (mp.pi/3)**2                     # repo gauge C = (pi/3)^2
gamma = mp.mpf('25.0')

print(f"{'sigma':>6} | {'2D: |w|=|1-1/rho|':>20} | {'3D: gauge radius C^-sigma':>26}")
print("-"*60)
for s in [mp.mpf('0.30'), mp.mpf('0.40'), mp.mpf('0.50'), mp.mpf('0.60'), mp.mpf('0.70')]:
    rho = s + 1j*gamma
    w = 1 - 1/rho
    R = C**(-s)
    tag = "  <-- on-line (baseline)" if s == mp.mpf('0.5') else ""
    print(f"{ns(s,4):>6} | {ns(abs(w),12):>20} | {ns(R,12):>26}{tag}")

print("\nPAIRING (sigma=0.7 with its reflection 0.3):")
w1 = 1 - 1/(mp.mpf('0.7')+1j*gamma)
w2 = 1 - 1/(mp.mpf('0.3')+1j*gamma)
print(f"  2D:  |w(rho)| * |w(rho*)| = {ns(abs(w1)*abs(w2),8)}"
      f"   ( = 1  => the two points are INVERSE across the unit circle )")
R1, R2, Rb = C**(-mp.mpf('0.7')), C**(-mp.mpf('0.3')), C**(-mp.mpf('0.5'))
print(f"  3D:  sqrt(R1*R2) = {ns(mp.sqrt(R1*R2),8)}   baseline C^(-1/2) = {ns(Rb,8)}"
      f"   ( geometric mean = baseline => the pair STRADDLES the cylinder )")
print("\n  on-line (sigma=1/2): |w|=1 (ON the circle) and radius=baseline (ON the")
print("  cylinder) -- the two pair-points MERGE. That merged config is the only")
print("  one the no-drift climb produces; the straddle (cone) is what it omits.")
