import numpy as np, json
from shared_rule3 import emit_modes, chi0_mod3, chi3_mod3
ref=json.load(open("ref_zeros.json"))
zetaA=np.array(ref["channelA_zeta_zeros"]); LB=np.array(ref["channelB_Lchi3_zeros"])

def Nfunc_zeta(T): return T/(2*np.pi)*np.log(T/(2*np.pi))-T/(2*np.pi)+7/8

def report(gammas, ref, label, nmax=15, gmin=3.0):
    g=np.array(sorted([x for x in gammas if x>gmin]))
    matched=np.array([g[np.argmin(np.abs(g-r))] for r in ref[:nmax]]) if len(g) else np.array([])
    res=matched-ref[:len(matched)]
    print(f"--- {label} ---")
    print("emit gamma_n:", np.round(g[:nmax],3))
    print("ref         :", np.round(ref[:nmax],3))
    print("residual    :", np.round(res,3))
    print("RMS=%.4f  maxabs=%.3f  n_emit(>%.0f)=%d"%(float(np.sqrt(np.mean(res**2))),float(np.max(np.abs(res))),gmin,len(g)))
    return g

# IDENTICAL CALL, only (U,slope0,chi) and the threshold-fraction differ?
# To keep it TRULY identical we must use the SAME thr_frac. Test same thr_frac for both.
print("="*72)
print("IDENTICAL CODE, SAME thr_frac=2.5, only (U,slope0,chi) swapped:")
print("PARAMS A: U=pi/6=%.6f slope0=3 -> R(k)=exp(3)*k=%.4f*k  chi=chi0_mod3"%(np.pi/6,np.exp(3)))
print("PARAMS B: U=pi/3=%.6f slope0=6 -> R(k)=exp(6)*k=%.4f*k  chi=chi3_mod3"%(np.pi/3,np.exp(6)))
print("="*72)
gA,HA,tA,GA,iA=emit_modes(np.pi/6,3.0,chi0_mod3,gamma_max=66,ngrid=8000,thr_frac=2.5)
print("INFO A:",{k:iA[k] for k in['M','U','slope0','slope_lin','Pmax','thr','feedback']})
gA=report(gA,zetaA,"CHANNEL A = zeta zeros",gmin=13.0)
print()
gB,HB,tB,GB,iB=emit_modes(np.pi/3,6.0,chi3_mod3,gamma_max=46,ngrid=8000,thr_frac=2.5)
print("INFO B:",{k:iB[k] for k in['M','U','slope0','slope_lin','Pmax','thr','feedback']})
gB=report(gB,LB,"CHANNEL B = L(chi3) zeros",gmin=3.0)

print()
print("CUMULATIVE N(T) check, Channel A vs true zeta N(T):")
for T in [21,30,40,50,60]:
    nA=np.sum((gA>13)&(gA<=T))+1  # +1 for first zero region
    print(f"  T={T}: emit-count={np.sum(gA<=T)}  trueN(T)={Nfunc_zeta(T):.2f}")
