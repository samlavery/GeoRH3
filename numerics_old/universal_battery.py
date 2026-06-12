import mpmath
mpmath.mp.dps=18
# (q, char-table by residue, parity a)  — primitive characters spanning the cases
chars={'zeta':(1,{},0),                       # principal (pole at s=1, trivial zeros)
       'chi3':(3,{1:1,2:-1},1),               # real, ODD,  prime cond
       'chi4':(4,{1:1,3:-1},1),               # real, ODD,  cond 4 (Dirichlet beta)
       'chi5*':(5,{1:1,2:1j,3:-1j,4:-1},1),   # COMPLEX (order 4), odd
       'chi8':(8,{1:1,3:-1,5:-1,7:1},0)}      # real, EVEN, cond 8
def Lfun(name,s):
    q,chi,_=chars[name]
    if name=='zeta': return mpmath.zeta(s)
    return mpmath.power(q,-s)*sum(chi.get(a,0)*mpmath.zeta(s,mpmath.mpf(a)/q) for a in range(1,q+1))
def nLLp(name,s): return -complex(mpmath.diff(lambda x: mpmath.log(Lfun(name,x)), s))
print("=== (1) universal continuous density:  Re(−L'/L(1/2+it))  vs  (1/2)log(q·t/2π) ===")
print(f"{'L-fn':8s} {'q':>2s} {'par':>4s}   " + "   ".join(f"t={t}" for t in [14,18,22]))
for name in chars:
    q,_,a=chars[name]
    cells=[]
    for t in [14,18,22]:
        re=nLLp(name,complex(0.5,t)).real
        pred=float(mpmath.log(q*t/(2*mpmath.pi))/2)
        cells.append(f"{re:+.2f}|{pred:+.2f}")
    print(f"{name:8s} {q:2d} {'even' if a==0 else 'odd':>4s}   "+"   ".join(f"{c:>11s}" for c in cells))
print("  (measured | predicted-from-q;  close ⇒ density is the conductor-scaled Weyl term, universal)")
print("\n=== (2) absorption resonances (zeros) exist for each L: |−L'/L(0.6+it)| peaks ===")
for name in chars:
    raw=[]; t=4.0
    while t<20:
        if abs(nLLp(name,complex(0.6,t)))>3.0: raw.append(round(t,1))
        t+=0.2
    zz=[]
    for x in raw:
        if not zz or x-zz[-1]>0.6: zz.append(x)
    print(f"  {name:8s}: resonances near t = {zz[:7]}")
print("\n=== (3) complex case: chi5 zeros are NOT conjugate-symmetric (t vs -t differ) ===")
for t in [6.18,-6.18, 9.0,-9.0]:
    v=abs(complex(Lfun('chi5*',complex(0.5,t))))
    print(f"  |L(chi5,1/2+i·{t:+.2f})| = {v:.3f}")
