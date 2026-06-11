"""
Your mechanism, run forward: the LOSS = the data to reconstruct the 3D mode from the 2D atom.
A projection-loss atom at rho is forced onto the circle iff a VALID 3D reconstruction exists only there.
So: build the reconstruction (the radial completion of the 2D atom) and find its consistency condition.

2D atom at rho: the area-law readout, amplitude n^{-rho} at integer n (R^2=Cn => R^{-2rho}).
3D reconstruction / loss = the radial profile that lifts it back up the helix.
Two consistency tests a genuine 3D mode must pass:
  (A) finite norm  ||loss||^2 = sum_n |n^{-rho}|^2 = sum_n n^{-2sigma}   (the mode is reconstructible)
  (B) per-loop holonomy  ((k+1)/k)^{-2rho}  (the mode closes under one winding -> |holonomy|=1 = no drift)
Question: does either single out sigma = Re(rho) = 1/2 ?
"""
import numpy as np

print("(A) reconstruction norm  ||loss||^2 = sum_{n<=X} n^{-2 sigma}  (finite => mode reconstructible):")
print(f"    {'sigma':>7} {'X=1e3':>12} {'X=1e5':>12} {'X=1e7':>12}   verdict")
for sigma in [0.30, 0.50, 0.70]:
    vals = []
    for X in [10**3, 10**5, 10**7]:
        n = np.arange(1, X+1, dtype=float)
        vals.append(np.sum(n**(-2*sigma)))
    grow = "DIVERGES" if vals[2] > 3*vals[0] else "finite"
    print(f"    {sigma:>7.2f} {vals[0]:>12.3f} {vals[1]:>12.3f} {vals[2]:>12.3f}   {grow}")
print("    => finite (reconstructible) only for sigma > 1/2; ON the line sum n^{-1} DIVERGES.")
print("       reconstruction-normalizability picks the CONVERGENCE region sigma>1/2, NOT the line.\n")

print("(B) per-loop holonomy  |((k+1)/k)^{-2 rho}|  (mode closes under one winding => |.|=1, no drift):")
print(f"    {'sigma':>7} {'loop k=10':>12} {'k=100':>12} {'k=1000':>12}")
for sigma in [0.30, 0.50, 0.70]:
    row = [abs(((k+1)/k)**(-2*sigma)) for k in [10, 100, 1000]]
    print(f"    {sigma:>7.2f} {row[0]:>12.6f} {row[1]:>12.6f} {row[2]:>12.6f}")
print("    => holonomy -> 1 for EVERY sigma (linear radial growth => per-loop ratio ->1).")
print("       the bare helix has no per-loop drift to distinguish sigma. No forcing here either.\n")

print("FORWARD VERDICT:")
print(" - the loss/reconstruction is well-defined; both consistency tests are real.")
print(" - but neither pins sigma=1/2: (A) gives sigma>1/2 (abscissa of convergence), (B) gives 1 for all sigma.")
print(" - so the BARE helix reconstruction lands on the convergence region, not the critical line.")
print(" - the missing piece is a REGULARIZATION/boundary that makes the modes DISCRETE eigenstates pinned to")
print("   |w|=1 (the Hilbert-Polya/Berry-Keating step). That is the one input the geometry doesn't yet carry.")
print()
print("So tell me the extra constraint in YOUR loss-reconstruction that I'm not using -- the boundary/closure")
print("that makes off-circle reconstruction inconsistent -- and I'll encode it and we finish. Right now the")
print("reconstruction itself is consistent on a whole half-plane, not just the line.")
