"""
blocky_mechanism.py -- is the angle signal GEOMETRIC or a re-derivation of analytic L?

The blocky helix replaces smooth amp n^{-1/2} by blocky 1/ceil(sqrt n). Write
  amp_blocky = n^{-1/2} + delta(n),  delta = blocky-smooth (a deterministic geometric sawtooth).
At a true zero g: smooth resultant ~ 0, so blocky resultant ~ sum chi(n) delta(n) e^{-i g log n}.
Its ANGLE is then arg of the delta-phasor-sum. Question: is that angle's S-correlation a
property of the GEOMETRIC sawtooth delta (the block structure), or would ANY perturbation do?
Test with several DIFFERENT perturbations; only block-structured ones should carry S.
"""
import numpy as np
from blocky_helix_core import chi3
np.random.seed(2)
F=np.load('/tmp/foundation.npz'); G,S=F['G'],F['S']
N=6000; n=np.arange(1,N+1); ch=chi3(n); logn=np.log(n)
sm=n**-0.5
def corr(a,b):
    v=np.isfinite(a)&np.isfinite(b); return np.corrcoef(a[v],b[v])[0,1] if v.sum()>5 else np.nan
def angle_sig(amp):
    out=[]
    for g in G[:64]:
        vx=np.sum(ch*amp*np.cos(g*logn)); vy=np.sum(ch*amp*np.sin(g*logn))
        out.append(np.arctan2(vy,vx))
    return np.sin(np.array(out))

# block-structured amplitudes (geometric)
k_ceil=np.ceil(np.sqrt(n)); k_floor=np.floor(np.sqrt(n)); k_floor[k_floor<1]=1
k_round=np.round(np.sqrt(n)); k_round[k_round<1]=1
variants={
 "smooth n^-1/2 (L)":          sm,
 "blocky 1/ceil(sqrt n)":      1/k_ceil,
 "blocky 1/floor(sqrt n)":     1/k_floor,
 "blocky 1/round(sqrt n)":     1/k_round,
 "delta only (ceil - smooth)": 1/k_ceil - sm,
 "smooth + RANDOM sawtooth":   sm + (np.random.rand(N)-0.5)*0.2*sm,   # null perturbation
 "smooth + n-periodic mod3":   sm*(1+0.2*np.cos(2*np.pi*n/3)),         # arithmetic but not block
}
print("=== which amplitude's misalignment-angle carries S(T)?  (geometric block vs nulls) ===")
for name,amp in variants.items():
    s=angle_sig(amp); print(f"  {name:30s} corr(sinA,S) = {corr(s,S[:64]):+.3f}")

print("\n=== what IS the angle analytically? compare to arg of (blocky resultant) directly ===")
# the delta-only signal should equal the blocky signal at zeros (since smooth ~0)
sb=angle_sig(1/k_ceil); sd=angle_sig(1/k_ceil - sm)
print(f"  corr(blocky-angle, delta-only-angle) = {corr(sb,sd):+.3f}  (=> angle is set by the GEOMETRIC delta)")

# Compare to a KNOWN analytic phase: arg L'/L or the secondary term. Use theta drift S directly:
# S(T) ~ (1/pi) Im log L(1/2+iT) fluctuation. Test corr(sinA, sin(pi*S)) and (cos):
print(f"  corr(sinA, sin(pi S)) = {corr(angle_sig(1/k_ceil), np.sin(np.pi*S[:64])):+.3f}")
print(f"  corr(sinA, S)         = {corr(angle_sig(1/k_ceil), S[:64]):+.3f}")
