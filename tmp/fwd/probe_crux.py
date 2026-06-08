import numpy as np
from shared_rule2 import build_atoms, chi0_mod3, chi3_mod3

# The resolvent G(H)=|sum_q amp_q e^{i (log q/U) H}|. Substitute tau = H/U:
#   = |sum_q amp_q e^{i tau log q}| = |sum_q amp_q q^{i tau}|.
# This is the truncated Dirichlet series at s = -i*tau on the line Re=0... but our amp has
# q^{-1/2} built in (weight=log p * q^{-1/2}), so it's sum_q (logp) q^{-1/2} q^{i tau}
#   = sum over n of vonMangoldt-ish * n^{-1/2+i tau}  = -L'/L(1/2 - i tau) truncated.
# Poles of -L'/L are at zeros rho=1/2+i*gamma -> at tau=-gamma (or |tau|=gamma).
# So PEAKS occur at tau = gamma_zero. And tau = H/U => H_peak = gamma * U.
# Therefore reading the EMITTED HEIGHT as the zero requires emit_t = H/U, NOT H!
# Let me recheck: for U=pi/6, zero gamma=14.13 -> H=14.13*pi/6=7.40. But peak was at 13.21.
# 13.21/U = 13.21/(pi/6)=25.2. Hmm that's the 3rd zero region. Let me just compute tau=H/U for the peaks.
U=np.pi/6
qs,ws,chis,om=build_atoms(U,np.exp(3),chi0_mod3,Pmax=1000)
amp=ws*chis
Hgrid=np.linspace(1,60,4000)
G=np.array([abs(np.sum(amp*np.exp(1j*om*H))) for H in Hgrid])
pk=[Hgrid[i] for i in range(1,len(Hgrid)-1) if G[i]>G[i-1] and G[i]>=G[i+1] and G[i]>np.median(G)*1.5]
pk=np.array(pk)
print("U=pi/6 peaks in H:", np.round(pk[:12],2))
print("tau=H/U:          ", np.round(pk[:12]/U,2))
print("zeta zeros:        [14.13 21.02 25.01 30.42 32.94 37.59 ...]")
# Now check: which reading matches? H directly or tau=H/U?
