import numpy as np
from shared_rule2 import build_atoms, chi0_mod3, chi3_mod3

# Is U genuinely entering, or normalized away? omega(q)=log(q)/U. The resolvent peaks at H
# where omega*H resonates. If we rescale U, peaks move to H'=H*(U'/U). So the ABSOLUTE
# heights depend on U. Channel A uses U=pi/6, channel B U=pi/3 -> factor 2 difference in omega.
qsA,wsA,chisA,omA = build_atoms(np.pi/6, np.exp(3), chi0_mod3, Pmax=1000)
qsB,wsB,chisB,omB = build_atoms(np.pi/3, np.exp(6), chi3_mod3, Pmax=1000)
print("Channel A omega(q=2):", np.log(2)/(np.pi/6), " B omega(q=2):", np.log(2)/(np.pi/3))
print("ratio omega_A/omega_B for same q:", (np.log(2)/(np.pi/6))/(np.log(2)/(np.pi/3)))
print("So A's helix has 2x the angular frequency per atom -> DIFFERENT helix. Good.")
print("A num atoms:",len(omA)," B num atoms:",len(omB))
print("A chi values (first primes):", chisA[np.argsort(qsA)][:8], "qs:", np.sort(qsA)[:8])
# show chi differs: A has all +1 (trivial), B has +-1
qsB_s=np.argsort(qsB)
print("B chi values (by q):", chisB[qsB_s][:8], "qs:", qsB[qsB_s][:8])
