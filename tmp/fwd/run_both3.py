import numpy as np, json
from shared_rule3 import emit_modes, chi0_mod3, chi3_mod3
ref=json.load(open("ref_zeros.json"))
zetaA=np.array(ref["channelA_zeta_zeros"]); LB=np.array(ref["channelB_Lchi3_zeros"])

def report(gammas, ref, label, nmax=15):
    g=np.array(sorted([x for x in gammas if x>3.0]))  # drop sub-3 spurious (below first zero)
    print(f"--- {label} ---")
    print("emitted gamma_n (>3):", np.round(g[:nmax+5],3))
    matched=[]
    for r in ref[:nmax]:
        if len(g)==0: break
        j=np.argmin(np.abs(g-r)); matched.append(g[j])
    matched=np.array(matched)
    res=matched-ref[:len(matched)]
    print("ref         :", np.round(ref[:nmax],3))
    print("matched emit:", np.round(matched,3))
    print("residual    :", np.round(res,3))
    print("RMS:", round(float(np.sqrt(np.mean(res**2))),4), " maxabs:", round(float(np.max(np.abs(res))),3))
    return g

print("="*70)
print("PARAMS A: U=pi/6=%.6f  slope0=3 (R=exp(3)*k=%.4f*k)  chi=chi0 mod3"%(np.pi/6,np.exp(3)))
gA,HA,tA,GA,iA=emit_modes(np.pi/6, 3.0, chi0_mod3, gamma_max=66, ngrid=6000, thr_frac=1.5)
print("INFO A:",iA)
report(gA, zetaA, "CHANNEL A  (const pitch)")
print()
print("="*70)
print("PARAMS B: U=pi/3=%.6f  slope0=6 (R=exp(6)*k=%.4f*k)  chi=chi3 mod3"%(np.pi/3,np.exp(6)))
gB,HB,tB,GB,iB=emit_modes(np.pi/3, 6.0, chi3_mod3, gamma_max=46, ngrid=6000, thr_frac=1.5)
print("INFO B:",iB)
report(gB, LB, "CHANNEL B  (const pitch)")
