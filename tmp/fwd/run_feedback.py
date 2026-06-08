import numpy as np, json
from shared_rule3 import emit_modes, chi0_mod3, chi3_mod3
ref=json.load(open("ref_zeros.json"))
zetaA=np.array(ref["channelA_zeta_zeros"]); LB=np.array(ref["channelB_Lchi3_zeros"])

def density_check(gammas, label):
    g=np.array(sorted([x for x in gammas if x>3.0]))
    if len(g)<6: 
        print(label,"too few"); return
    sp=np.diff(g)
    # local density d N/dt ~ 1/spacing should grow like (1/2pi)log(t/2pi)
    mids=(g[:-1]+g[1:])/2
    print(f"{label}: emitted spacings (should SHRINK ~log density):")
    print("   t-mid:", np.round(mids[:12],1))
    print("   space:", np.round(sp[:12],2))
    # expected zeta spacing 2pi/log(t/2pi)
    exp_sp=2*np.pi/np.log(np.maximum(mids,7)/(2*np.pi))
    print("   exp  :", np.round(exp_sp[:12],2))

# CONSTANT pitch (baseline) vs FEEDBACK pitch+=delta
print("CONSTANT PITCH density:")
gA,*_=emit_modes(np.pi/6,3.0,chi0_mod3,gamma_max=66,ngrid=6000,thr_frac=1.5,feedback=False)
density_check(gA,"  A const")
gB,*_=emit_modes(np.pi/3,6.0,chi3_mod3,gamma_max=46,ngrid=6000,thr_frac=1.5,feedback=False)
density_check(gB,"  B const")
print()
print("FEEDBACK pitch+=delta (delta=0.01):")
for dl in [0.005,0.02,0.05]:
    gAf,*_=emit_modes(np.pi/6,3.0,chi0_mod3,gamma_max=66,ngrid=6000,thr_frac=1.5,feedback=True,delta=dl)
    gf=np.array(sorted([x for x in gAf if x>3]))
    matched=np.array([gf[np.argmin(np.abs(gf-r))] for r in zetaA[:13]]) if len(gf) else np.array([])
    rms=float(np.sqrt(np.mean((matched-zetaA[:len(matched)])**2))) if len(matched) else 9
    print(f"  A delta={dl}: nemit(>3)={len(gf)} RMS={rms:.3f}")
