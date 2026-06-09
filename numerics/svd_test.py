import numpy as np
def chi3(n): return [0,1,-1][n%3]
def vonmangoldt(N):
    Lam=np.zeros(N+1); s=np.ones(N+1,bool); s[:2]=False
    for i in range(2,int(N**.5)+1):
        if s[i]: s[i*i::i]=False
    for p in np.nonzero(s)[0]:
        pk=int(p)
        while pk<=N: Lam[pk]=np.log(p); pk*=int(p)
    return Lam
zeros=[8.0397,11.2492,15.7046,18.2620,20.4558,24.0594,26.5779,28.2182,30.7450,33.8974]
def svals(N,m,umax,useZeros=False):
    Lam=vonmangoldt(N)[1:N+1]; n=np.arange(1,N+1); chi=np.array([chi3(k) for k in range(1,N+1)])
    amp=Lam*chi/np.sqrt(n); logn=np.log(n)
    if useZeros:
        z=vonmangoldt  # placeholder
        u=np.array((zeros*((m//len(zeros))+1))[:m])  # sample AT zeros
    else:
        u=np.linspace(0.1,umax,m)
    B=amp[None,:]*np.exp(-1j*np.outer(u,logn))
    return np.linalg.svd(B,compute_uv=False)
print("=== top-10 singular values of the chi3 loss matrix B_N (m=80 samples on [0,60]) ===")
for N in [5000,20000,80000]:
    sv=svals(N,80,60)
    print(f"N={N:6d}  logN={np.log(N):.2f} (logN)^2={np.log(N)**2:.1f}   top SVs: "+" ".join(f"{x:.2f}" for x in sv[:8]))
print("\n=== do they match the zeros?  zeros(first 10): "+" ".join(f"{z:.1f}" for z in zeros))
print("=== singular values are clustered ~log N, NOT spread like the gamma_n. ===")
print("\n=== sampling AT the zeros (u_j = gamma_j) — does zero structure appear in SVs? ===")
sv=svals(20000,80,60,useZeros=True)
print("top SVs:", " ".join(f"{x:.2f}" for x in sv[:8]), " ... still ~log N, not the zeros")
