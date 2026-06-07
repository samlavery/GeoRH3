"""
Honest test: does the CHIRAL BLOCK A_N (the operator the trace identity is built for) have
eigenvalues = the zeros? A_N = [[0, Bᴴ],[B,0]], eig = ±singular_values(B_N).
B_N[j,n] = Λ(n)·n^(-(½+i u_j)).  Compare its singular values to the ζ zeros (14.13, 21.02, ...).
"""
import numpy as np, math
# von Mangoldt up to N
N = 4000
sieve = np.ones(N+1, bool); sieve[:2]=False
for i in range(2,int(N**0.5)+1):
    if sieve[i]: sieve[i*i::i]=False
Lam = np.zeros(N+1)
for p in np.nonzero(sieve)[0]:
    lp=math.log(p); pk=p
    while pk<=N: Lam[pk]=lp; pk*=p
n = np.arange(2, N+1); lam = Lam[2:N+1]
# sample points u_j (a grid over the zero range)
m = 80
u = np.linspace(0.5, 45, m)
# B_N[j,n] = Λ(n) n^(-(1/2 + i u_j))
B = lam[None,:] * np.exp(-(0.5 + 1j*u[:,None]) * np.log(n)[None,:])
sv = np.linalg.svd(B, compute_uv=False)   # singular values = |eigenvalues of A_N|
print("chiral block A_N: ± these singular values are its eigenvalues")
print("largest 12 singular values:", np.round(sv[:12], 3))
print("smallest 12 singular values:", np.round(sv[-12:], 4))
print("range of singular values: [%.4f, %.4f]" % (sv.min(), sv.max()))
print("\nζ zeros (what we WANT the spectrum to be): 14.13, 21.02, 25.01, 30.42, 32.94, ...")
print("\nscale check: Σ Λ(n)²/n =", round(float(np.sum(lam**2 / n)),3),
      " → singular values are O(√ that) ≈", round(math.sqrt(float(np.sum(lam**2/n))),3))
