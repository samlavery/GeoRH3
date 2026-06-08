import numpy as np
from shared_rule import *

# Channel A params
U_A, slope_A = np.pi/6, np.exp(3)
emit, Hgrid, cum, info = count_modes(U_A, slope_A, chi0_mod3, Hmax=60, nH=300, feedback=False)
print("CHANNEL A info:", info)
print("num emitted modes up to H=60:", len(emit))
print("first 15 emit heights:", np.round(emit[:15],3))
print("cumulative at end:", cum[-1])
print()
print("singular value spectrum at H=60:")
qs, ws, chis, omegas, slp = build_atoms(U_A, slope_A, chi0_mod3, M_max=300, Pmax=2000)
B = windowed_gram(ws, chis, omegas, 60.0)
sv = np.linalg.svd(B, compute_uv=False)
print("M atoms:", len(omegas), " num sv > 1e-3*base:", np.sum(sv>info['thresh']))
print("top 10 sv:", np.round(sv[:10],5))
print("omegas range:", omegas.min(), omegas.max(), " min gap:", np.min(np.diff(np.sort(omegas))))
