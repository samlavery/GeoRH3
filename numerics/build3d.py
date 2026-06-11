"""
build3d.py -- BUILD the 3D structure first, then measure. No imposed log n; the winding is whatever the
geometry gives. Rules: integers evenly on a line (arc spacing pi/3), wound up-and-out on a cone with
LINEAR radial growth per loop (e^6) and pitch pi/3 per loop. Get REAL coordinates, then ask what the
structure does: what is its winding law, where do the chi3 fibres balance, what volume sits between
those balance events.
"""
import numpy as np
A = np.exp(6.0)/(2*np.pi)            # radius R = A*theta  (linear growth e^6 per loop)
# arc length s(theta) = int sqrt(A^2(1+u^2)+1/36) du ; place integers at s_n = n*pi/3, solve theta_n
th = np.linspace(0, 6000, 6_000_00)
dsdth = np.sqrt(A**2*(1+th**2) + (1/6)**2)
s = np.concatenate([[0], np.cumsum(0.5*(dsdth[1:]+dsdth[:-1])*np.diff(th))])
M = 200000
n = np.arange(1, M+1)
s_n = n*(np.pi/3)
theta = np.interp(s_n, s, th)        # REAL winding angle of integer n
R = A*theta                          # REAL radius
z = theta/6                          # REAL height (pitch pi/3 per loop)
x, y = R*np.cos(theta), R*np.sin(theta)
sign = np.where(n%3==1,1.0,np.where(n%3==2,-1.0,0.0))

print("=== THE BUILT 3D STRUCTURE (real coordinates) ===")
print(f"A = e^6/2pi = {A:.3f}; integers at arc spacing pi/3 on the cone.")
print(f"{'n':>4} {'theta(wind)':>11} {'R(out)':>9} {'z(up)':>8}   (x, y, z)")
for nn in [1,2,3,5,10,100,1000,10000]:
    i=nn-1
    print(f"{nn:4d} {theta[i]:11.4f} {R[i]:9.3f} {z[i]:8.3f}   ({x[i]:8.2f},{y[i]:8.2f},{z[i]:7.3f})")

# what WINDING LAW did the geometry produce?  fit theta vs candidate laws on n in [1000, 200000]
m = (n>=1000)
def fitq(f): 
    c=np.polyfit(f[m], theta[m],1); res=np.std(theta[m]-(c[0]*f[m]+c[1]))/np.std(theta[m]); return c[0],res
print("\n=== WHAT WINDING LAW EMERGED?  theta(n) ~ ? ===")
for nm,f in [("sqrt(n)",np.sqrt(n)),("log n",np.log(n)),("n",n.astype(float)),("n^(1/3)",n**(1/3.))]:
    c,res=fitq(f); print(f"   theta ~ {c:.4g} * {nm:8s} :  residual {res:.4f}  {'<-- FITS' if res<0.02 else ''}")

# does the geometry's OWN winding cancel chi3?  use theta as the phase, 1/R as amplitude, NO imposed log.
gam=[]
with open("lchi3_zeros_1000.txt") as f:
    for ln in f:
        ln=ln.strip()
        if ln and not ln.startswith("#"): gam.append(float(ln.split()[1]))
gam=np.array(sorted(gam)); Z=gam[:8]
amp=1.0/R
def collapse_geo(w): return abs(np.sum(sign*amp*np.exp(1j*w*theta)))   # geometry's real winding
def collapse_log(w): return abs(np.sum(sign*(n**-0.5)*np.exp(-1j*w*np.log(n))))  # the L-function (control)
print("\n=== DOES THE BUILT STRUCTURE CANCEL AT THE chi3 ZEROS?  (geometry's own winding theta) ===")
print(f"   {'gamma':>8} {'|geo structure|':>16} {'|L (control)|':>14}")
for g in Z[:5]:
    print(f"   {g:8.3f} {collapse_geo(g):16.4f} {collapse_log(g):14.4f}")
print("   (geo uses the REAL winding theta(n); if it doesn't match L, the geometry's winding != log n)")

print("\n\n=== BUILD #2: radius and height carry DIFFERENT arithmetic (two real axes) ===")
# OUT: radius R2 = sqrt(n)  -> swept disk area = pi*R2^2 = pi*n ;  amplitude = 1/R2 = n^-1/2
# UP : height  z2 = log(area swept) = log(pi*n)            -> the FREQUENCY (rises by log-volume)
R2 = np.sqrt(n)
area = np.pi*R2**2                      # = pi n : the integer area/volume swept out to integer n
z2 = np.log(area)                       # height = log(swept area) -- the fiber rises by log-volume
amp2 = 1.0/R2
print(f"   integer n at: radius sqrt(n), height = log(pi*n).  e.g.")
for nn in [1,10,100,1000]:
    i=nn-1; print(f"     n={nn:4d}: R={R2[i]:7.2f}  area={area[i]:10.1f}  height=log(area)={z2[i]:6.3f}")
def collapse2(w): return abs(np.sum(sign*amp2*np.exp(1j*w*z2)))   # amplitude 1/R, frequency = height
print("\n   does THIS structure cancel at the chi3 zeros? (phase = winding * height, height=log area)")
print(f"   {'gamma':>8} {'|2-axis structure|':>18} {'|L control|':>12}")
for g in Z[:6]:
    print(f"   {g:8.3f} {collapse2(g):18.4f} {collapse2(g):12s if False else ''} {collapse_log(g):10.4f}")
