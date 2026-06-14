#!/usr/bin/env python3
"""
reproduce_all.py -- reproduce 500 zeros x 50 decimals for EVERY L-function with certified data,
purely geometrically (pi/3 helix: placement -> sqrt-n amplitude, running count-residual ledger,
log-projection to 1D, phasor cancellation, cone+discreteness continuation; constants from mp.pi;
NO gamma, NO functional equation).  zeta is handled by the closed-form ETA technique.

Writes one file per L-function to numerics/results/geometric_500x50/geometric_<label>.txt:
each line is  `index  geometric_ordinate(>=50dp)  |geometric - reference|`, with a summary footer,
for direct comparison against the independent zeros_500x50/ set and for reproduction.

Run:  python3 reproduce_all.py
"""
import time

import geometric_crossings as G

if __name__ == "__main__":
    t0 = time.time()
    G.reproduce_all()
    print(f"\ntotal wall: {time.time() - t0:.0f}s")
