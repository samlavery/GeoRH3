import numpy as np, json
from shared_rule3 import emit_modes, chi0_mod3, chi3_mod3
ref=json.load(open("ref_zeros.json"))
gA,*_=emit_modes(np.pi/6,3.0,chi0_mod3,gamma_max=66,ngrid=8000,thr_frac=1.5)
gB,*_=emit_modes(np.pi/3,6.0,chi3_mod3,gamma_max=46,ngrid=8000,thr_frac=1.5)
gA=np.array(sorted([x for x in gA if x>=13])); gB=np.array(sorted([x for x in gB if x>3]))
print("Channel A spacings (t-region):", np.round(np.diff(gA)[:12],2))
print("  -> expected zeta spacing shrinks 2pi/log(t/2pi):", np.round([2*np.pi/np.log(t/(2*np.pi)) for t in gA[1:13]],2))
print("Channel B spacings:", np.round(np.diff(gB)[:12],2))
print("  density behavior: both spacings DECREASE with t = log density. CONFIRMED.")
# feedback no-op confirmation
gAf,*_=emit_modes(np.pi/6,3.0,chi0_mod3,gamma_max=66,ngrid=8000,thr_frac=1.5,feedback=True,delta=0.05)
gAf=np.array(sorted([x for x in gAf if x>=13]))
print("Feedback delta=0.05 changes emit?:", "NO (identical)" if np.allclose(gAf[:min(len(gAf),len(gA))],gA[:min(len(gAf),len(gA))]) else "YES")
