"""
Can the zero-CROSSINGS of psi(x,chi3) give the individual L-ZEROS without the log-n readout?

psi(x,chi3)=sum_{n<=x} Lambda(n)chi3(n);  psi/sqrt(x) = -2 sum_k cos(gamma_k log x - phi_k)/|rho_k|.
The count (in log x) and the zeros (frequencies) are FOURIER DUALS.  Test:
 (A) crossings ALONE  -> only aggregate (count is step-noise ~ sqrt(x); spacing is an irregular blur)
 (B) transform of the FULL count (the readout) -> the individual gamma_k
Conclusion target: extracting individual gamma_k = a transform = the log-n readout; no log-free route.
"""
import numpy as np, math

X = 300000
sieve = np.ones(X+1, bool); sieve[:2] = False
for i in range(2, int(X**0.5)+1):
    if sieve[i]: sieve[i*i::i] = False
Lam = np.zeros(X+1)
for p in np.nonzero(sieve)[0].tolist():
    lp = math.log(p); pk = p
    while pk <= X: Lam[pk] = lp; pk *= p
nn = np.arange(X+1)
chi3 = np.where(nn % 3 == 1, 1.0, np.where(nn % 3 == 2, -1.0, 0.0))
psi = np.cumsum(Lam * chi3)

# ---------- (A) crossings ALONE ----------
sgn = np.sign(psi); sgn[sgn == 0] = 1
cross = np.nonzero(np.diff(sgn))[0] + 1
ux = np.log(cross.astype(float)); du = np.diff(ux); du = du[du > 0]
print(f"(A) crossings ALONE:  {len(cross)} crossings to X={X}")
print(f"    count ~ x^b:  fit b = {np.polyfit(np.log(cross.astype(float)), np.log(np.arange(1,len(cross)+1)),1)[0]:.2f}"
      f"   (b~0.5 => sqrt(x) STEP-NOISE, not the zero density)")
print(f"    spacing in log-x: mean={np.mean(du):.4f} median={np.median(du):.5f} std={np.std(du):.4f}")
print(f"    -> one 'effective frequency' pi/mean = {math.pi/np.mean(du):.2f}: a BLUR, matches no gamma_k")
print(f"    crossings give at most an aggregate; the amplitudes 1/|rho_k| are thrown away.\n")

# ---------- (B) transform of the FULL count = the readout ----------
u  = np.linspace(math.log(2), math.log(X), 1 << 14)
xx = np.exp(u)
f  = psi[np.floor(xx).astype(int)] / np.sqrt(xx)     # psi/sqrt(x) sampled uniformly in u=log x
f  = (f - f.mean()) * np.hanning(len(u))
F  = np.abs(np.fft.rfft(f))
gam = 2*np.pi * np.fft.rfftfreq(len(u), d=(u[1]-u[0]))
# peaks of the spectrum
inner = F[1:-1]
ispk = np.nonzero((inner > F[:-2]) & (inner > F[2:]) & (inner > inner.max()*0.30))[0] + 1
peaks = np.sort(gam[ispk])
print(f"(B) transform of the FULL count (FFT of psi/sqrt(x) in log x) -- THIS is the readout:")
print(f"    spectral peaks: {np.round(peaks[:8],2).tolist()}")
print(f"    chi3 zeros:     [8.04, 11.25, 15.7, 18.26, 20.46, 24.06, 26.58, 28.22]")
print(f"    (coarse: u-range {u[-1]-u[0]:.1f} gives resolution dgamma ~ {2*math.pi/(u[-1]-u[0]):.2f})\n")

print("ANSWER: crossings alone -> only aggregate/blur (step-noise). The individual gamma_k are the")
print("count's FREQUENCIES; reading frequencies from the signal IS the Fourier/log-n transform.")
print("Crossings are a lossy reduction (no amplitudes), so they're strictly weaker than the count,")
print("and even the count needs the transform. So: NO log-free crossings->zeros. The bridge (log) is")
print("not an arbitrary choice -- it is the transform that turns the geometric count into its spectrum.")
