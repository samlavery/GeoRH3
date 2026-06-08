import numpy as np, json
from shared_rule2 import emit_modes, chi0_mod3, chi3_mod3

ref=json.load(open("ref_zeros.json"))
zetaA=np.array(ref["channelA_zeta_zeros"])
LB=np.array(ref["channelB_Lchi3_zeros"])

def compare(emit, ref, label, nmax=15):
    # match each ref zero to nearest emitted height above noise (drop spurious low ones)
    e=np.array(sorted(emit))
    matched=[]
    for r in ref[:nmax]:
        if len(e)==0: break
        j=np.argmin(np.abs(e-r))
        matched.append((r,e[j]))
    print(f"--- {label} ---")
    print("ref :", np.round(ref[:nmax],3))
    print("emit(matched):", np.round([m[1] for m in matched],3))
    res=np.array([m[1]-m[0] for m in matched])
    print("residuals:", np.round(res,3))
    print("RMS:", round(float(np.sqrt(np.mean(res**2))),4))
    print("all emit:", np.round(e[:25],2))
    return matched

# CHANNEL A: U=pi/6, slope=exp(3), chi0 mod3  -> zeta zeros
print("PARAMS A: U=pi/6=",np.pi/6," slope=exp(3)=",np.exp(3)," chi=chi0_mod3")
eA,HgA,GA,iA=emit_modes(np.pi/6, np.exp(3), chi0_mod3, Hmax=60, nH=1500, win=0.4, thr_frac=1.0)
print("info A:",iA)
compare(eA, zetaA, "CHANNEL A const-pitch")
print()
# CHANNEL B: U=pi/3, slope=exp(6), chi3 mod3 -> L(chi3) zeros
print("PARAMS B: U=pi/3=",np.pi/3," slope=exp(6)=",np.exp(6)," chi=chi3_mod3")
eB,HgB,GB,iB=emit_modes(np.pi/3, np.exp(6), chi3_mod3, Hmax=46, nH=1500, win=0.4, thr_frac=1.0)
print("info B:",iB)
compare(eB, LB, "CHANNEL B const-pitch")
