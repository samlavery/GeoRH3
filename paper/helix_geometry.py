import mpmath as mp
mp.mp.dps = 30
pi = mp.pi
def ns(x,n=10): return mp.nstr(x,n)

print("="*72)
print("THE GEOMETRIC HELIX: integers on a line -> wound, radial growth, pitch")
print("="*72)

# actual zeta zeros (targets)
zeros = [mp.im(mp.zetazero(k)) for k in range(1,6)]
print("\n[targets] first zeta zeros:", [ns(z,8) for z in zeros])

# ---------------------------------------------------------------------------
# THE CONSTRUCTION (as instructed):
#  * integers 1,2,3,... placed EVENLY on the unwound line, spacing U (=1, say)
#  * rewind onto an Archimedean spiral: LINEAR radial growth, CONSTANT pitch
#       equal arc-spacing  =>  arc length s_n = n*U
#       Archimedean r = b*theta, arc s ~ (b/2) theta^2  =>  theta_n ~ sqrt(n)
#       radius R_n ~ sqrt(n)           <-- the area law n ~ k^2, R ~ sqrt(n)
#  * readout at height t:  amplitude 1/R_n = n^{-1/2}   (GEOMETRIC, correct)
#                          phase     t*theta_n = t*c*sqrt(n)   <-- pure geometry
# So the geometric phasor is   g_n(t) = (-1)^{n-1} n^{-1/2} e^{-i t c sqrt(n)}
# ---------------------------------------------------------------------------

def summ(freq, t, M=4000):
    # Gaussian-regularized alternating sum  sum (-1)^{n-1} n^{-1/2} e^{-i t freq(n)}
    s = mp.mpc(0)
    for n in range(1, M+1):
        s += ((-1)**(n-1))*mp.mpf(n)**(mp.mpf(-1)/2)*mp.e**(-1j*t*freq(n))*mp.e**(-(mp.mpf(n)/M)**2)
    return s

log_freq  = lambda n: mp.log(n)          # ARITHMETIC phase (FTA / winding bridge)
sqrt_freq = lambda n: mp.sqrt(n)         # GEOMETRIC phase (Archimedean spiral)

print("\n[A] log-n phase (eta / FTA winding): zeros of the phasor sum")
for z in zeros[:4]:
    print(f"    t={ns(z,8):>10}:  |sum| = {ns(abs(summ(log_freq,z)),4)}   (target zero -> ~0)")

print("\n[B] sqrt-n phase (pure Archimedean geometry): does it cancel at the zeros?")
for c in [mp.mpf('1.0'), mp.mpf('2.0')]:
    f = lambda n: c*mp.sqrt(n)
    print(f"    c={ns(c)}:")
    for z in zeros[:4]:
        print(f"      t={ns(z,8):>10}:  |sum| = {ns(abs(summ(f,z,M=2000)),4)}   (target zero -> should be ~0 if it matched)")

print("\n[C] log n  vs  c*sqrt(n)  -- can geometry's frequencies equal arithmetic's?")
print("    n :   log n      sqrt(n)    ratio log/sqrt")
for n in [2,4,8,16,64,256,1024]:
    print(f"   {n:>4}: {ns(mp.log(n),6):>9}  {ns(mp.sqrt(n),6):>9}   {ns(mp.log(n)/mp.sqrt(n),5)}")
print("    -> log/sqrt is not constant: no single pitch c makes c*sqrt(n)=log n.")
print("       sqrt(n) grows polynomially, log n logarithmically. The geometry")
print("       supplies the n^{-1/2} AMPLITUDE; the log-n PHASE is arithmetic (FTA).")
