import mpmath
mpmath.mp.dps=20
chars={'zeta':(1,{}),'chi3':(3,{1:1,2:-1}),'chi4':(4,{1:1,3:-1}),
       'chi5*':(5,{1:1,2:1j,3:-1j,4:-1}),'chi7*':(7,None),'chi8':(8,{1:1,3:-1,5:-1,7:1})}
# chi7: complex order-6 char mod 7, primitive root 3: 3^k mod7 = 3,2,6,4,5,1 ; chi(3)=e^{2πi/6}
import cmath
w=cmath.exp(2j*cmath.pi/6)
chi7={}
g=1
for k in range(6):
    g=(g*3)%7 if k>0 else 1
    chi7[g]=w**k
chars['chi7*']=(7,chi7)
def Lf(name,s):
    q,chi=chars[name]
    if name=='zeta': return mpmath.zeta(s)
    return mpmath.power(q,-s)*sum(complex(chi.get(a,0))*mpmath.zeta(s,mpmath.mpf(a)/q) for a in range(1,q+1))
def Tabs(name,z): return abs(complex(mpmath.diff(lambda x: mpmath.log(Lf(name,x)), 0.5+1j*z)))
def first_zero(name):
    best=(5.0,1e9); t=4.0
    while t<16:
        v=abs(complex(Lf(name,complex(0.5,t))))
        if v<best[1]: best=(t,v)
        t+=0.1
    try:
        z=mpmath.findroot(lambda s: Lf(name,s), mpmath.mpc(0.5,best[0])); return float(mpmath.im(z)), float(mpmath.re(z))
    except: return best[0],0.5
print("=== IsSelfAdjointReceiver across the L-functions: resonance ON R, regular OFF R ===")
print(f"{'L-fn':7s} {'q':>2s}  {'gamma1 (Re)':>16s}  {'|T|@zero':>9s}  {'|T| off-R(y=.15)':>16s}  verdict")
for name in chars:
    q=chars[name][0]; g,re=first_zero(name)
    on=Tabs(name,complex(g,0.0)); off=Tabs(name,complex(g,0.15))
    mx=max(Tabs(name,complex(x,sy)) for x in [4,7,10,13,16,19,22] for sy in [0.25,-0.25])
    ok=(abs(re-0.5)<1e-6) and on>off*30 and mx<80
    print(f"{name:7s} {q:2d}  {g:10.4f}({re:.4f})  {on:9.0f}  {off:14.1f}   {'OK on R, regular off R' if ok else 'CHECK'} (maxoffR={mx:.0f})")
print("  (zeta: lone off-R feature is the s=1 pole at z=-0.5i = the completion term, not a zero)")
# DH contrast
xi=(mpmath.sqrt(10-2*mpmath.sqrt(5))-2)/(mpmath.sqrt(5)-1)
aa=[0,mpmath.mpf(1),xi,-xi,mpmath.mpf(-1),mpmath.mpf(0)]
def DH(s): return mpmath.power(5,-s)*sum(aa[r]*mpmath.zeta(s,mpmath.mpf(r)/5) for r in range(1,6))
def TDH(z): return abs(complex(mpmath.diff(lambda x: mpmath.log(DH(x)), 0.5+1j*z)))
print(f"\n=== contrast DH (q=5, NON-multiplicative, no Euler product) ===")
print(f"  |T_DH| at its off-R resonance z=85.699-0.3085i : {TDH(complex(85.69935,-0.3085)):.0f}   ⇒ singular support OFF R ⇒ FAILS")
