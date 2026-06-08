import numpy as np
from shared_rule2 import build_atoms, chi0_mod3

# The resolvent: G(H) = |sum_q amp_q e^{i omega_q H}|, omega_q = log(q)/U.
# This peaks where the phases align. The classical explicit-formula object is
#   sum_q amp_q q^{-it} = sum_q amp_q e^{-i t log q}.  Comparing: e^{i omega_q H} = e^{i (log q /U) H}.
# To match q^{-it}=e^{-i t log q} we need  (log q /U) H  =  - t log q   =>  H/U = -t  => t = -H/U.
# So the height H maps to t = H/U (up to sign). For U=pi/6, t = H/(pi/6) = H*6/pi = 1.91*H.
# That means a zeta zero at t=14.13 should appear at H = 14.13 * U = 14.13*pi/6 = 7.4, NOT at H~13.2!
U=np.pi/6
print("If t=H/U, zeta zero t=14.13 -> H =", 14.13*U)
print("But emit gave H~13.2 for the first zero. So t = H/U is NOT what's happening.")
# Reconcile: in my code omega_q=log q/U and I sweep H directly comparing to t. The peak at H~13.2
# for t=14.13 means effectively t ≈ H (within ~7%), i.e. U is NOT rescaling t. Why?
# Because amp e^{i omega H}: the BEAT frequencies are differences (omega_a-omega_b)=log(q_a/q_b)/U.
# The collective peak structure... let me just MEASURE: vary U, see if peak heights move.
def Gprofile(U, Hgrid):
    qs,ws,chis,om=build_atoms(U,np.exp(3),chi0_mod3,Pmax=1000)
    amp=ws*chis
    return np.array([abs(np.sum(amp*np.exp(1j*om*H))) for H in Hgrid])
Hgrid=np.linspace(1,40,2000)
for Utest in [np.pi/12, np.pi/6, np.pi/3]:
    G=Gprofile(Utest,Hgrid)
    pk=[Hgrid[i] for i in range(1,len(Hgrid)-1) if G[i]>G[i-1] and G[i]>=G[i+1] and G[i]>np.median(G)*1.5]
    print(f"U={Utest:.4f}: first peaks H=", np.round(pk[:6],2))
