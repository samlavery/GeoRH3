import numpy as np
# What is the target density? N(T) for zeta:
def N_zeta(T):
    return T/(2*np.pi)*np.log(T/(2*np.pi)) - T/(2*np.pi) + 7/8
for T in [14,21,25,30,40,50,60]:
    print(f"T={T:5.1f}  N(T)={N_zeta(T):7.3f}")
# So up to T=60 there should be ~ N(60) zeros. spacing ~ 2pi/log(T/2pi).
print("local spacing near T=30:", 2*np.pi/np.log(30/(2*np.pi)))
print("local spacing near T=50:", 2*np.pi/np.log(50/(2*np.pi)))
# The emission staircase I got was ~0.4 spacing CONSTANT -> wrong (that's freq resolution).
# Correct: spacing must SHRINK with T (log density). That is the test.
