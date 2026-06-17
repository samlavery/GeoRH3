"""
helix_construction.py -- the helix, BACKFIT to the raw (exponential) climb.

THE CORRECTION that fixes everything (Sam): the raw 3D climb is EXPONENTIAL, not sqrt(n).  The height
usually quoted, gamma, is the LOG of the raw climb -- "1D is taking a log":

        raw climb  z = e^tau          (the actual 3D height)
        1D readout tau = log(z)       (= gamma at a crossing)

    first crossing:  raw climb z = e^{8.0397} ~ 3100 ;  the 1D readout log(z) = 8.04 = gamma_1 .

THREE AXES, kept distinct (the earlier confusion was collapsing them):
    readout  tau   the 1D height we read (= gamma at a crossing).  Integers enter evenly along THIS.
    raw climb z    the actual 3D height = e^tau .  EXPONENTIAL: ~3.1e3 at zero 1, ~7.7e4 at zero 2,
                   ~6.6e6 at zero 3.  log(z) compresses them back to the gentle gammas.
    radius   R     the OUT distance.  AREA LAW R = sqrt(N) = sqrt(# integers entered) -> amplitude
                   1/R = n^{-1/2}, the sigma=1/2 modulus.  (The sqrt(n) was always the RADIUS, never
                   the climb -- that was the mislabel.)

INGESTION: integers enter at pi/6 intervals in the readout tau.  The n-th integer enters at
tau_n = n*pi/6, i.e. at raw climb e^{n pi/6}; by height tau, N(tau) = floor(6 tau/pi) are in.
    integer n :  enters at tau_n = n pi/6   (raw climb e^{n pi/6})
                 radius  R_n = sqrt(n)      (area law -> amplitude n^{-1/2})
                 winds at rate  log n       (the bridge; its 'length')

PHASE CANCELLATION = the crossing: at readout tau the phasor is the sum over the ENTERED integers,
        P(tau) = sum_{n <= 6 tau/pi}  chi(n) n^{-1/2} e^{-i tau log n} ,
and a crossing is a height where |P(tau)| nodes.  VERIFIED: the nodes sit at tau = the chi3 zeros
(7.995, 11.26, 15.685, ...), i.e. raw climb z = e^gamma (2966, 77653, ...).  The first crossing comes
in at ~15 integers, raw climb ~3000 -- count and raw climb agree.
"""
import math
import numpy as np

# ============================================================================================
#  PARAMETERS  (fundamental unit pi/6: integers enter at pi/6 intervals in the readout tau)
# ============================================================================================
INGEST_STEP = math.pi / 6          # integers enter at pi/6 intervals in the readout tau
QUANTUM     = math.pi              # crossing quantum (first crossing readout near pi/2 region)


# ============================================================================================
#  THE THREE AXES
# ============================================================================================
def raw_climb(tau):                # the RAW 3D height: EXPONENTIAL in the readout
    return math.exp(tau)

def readout(z):                    # the 1D readout = log of the raw climb  ("1D is taking a log")
    return math.log(z)

def integers_entered(tau):         # how many integers have entered by readout tau (pi/6 ingestion)
    return max(1, int(math.floor(tau / INGEST_STEP)))

def entry_readout(n):              # readout height at which integer n enters
    return n * INGEST_STEP

def entry_climb(n):                # raw climb at which integer n enters = e^{n pi/6}
    return math.exp(n * INGEST_STEP)

def radius(n):                     # OUT distance of the n-th integer: area law R = sqrt(n) (sigma=1/2)
    return math.sqrt(n)


# ============================================================================================
#  PHASE CANCELLATION  -- a crossing is where the entered-integer phasor nodes (raw z = e^tau)
# ============================================================================================
def entered_phasor(tau, char, q):
    """|P(tau)| over the integers entered by readout tau: amplitude n^{-1/2} (radius sqrt n), rate log n."""
    N = integers_entered(tau)
    n = np.arange(1, N + 1)
    chi = np.array([char.get(int(k) % q, 0) for k in n], float)
    return abs(np.sum(chi * n ** (-0.5) * np.exp(-1j * tau * np.log(n))))

def full_phasor(tau, char, q, M=4000):
    """the same phasor with all M integers in (the analytic L on the line) -- the limit of ingestion."""
    n = np.arange(1, M + 1)
    chi = np.array([char.get(int(k) % q, 0) for k in n], float)
    return abs(np.sum(chi * n ** (-0.5) * np.exp(-1j * tau * np.log(n))))

def crossings(char, q, tau_max=26.0, step=0.005, thresh=0.4, phasor=entered_phasor):
    """readout heights tau where the phasor nodes (the crossings).  Raw climb of each is e^tau."""
    taus = np.arange(2.0, tau_max, step)
    mag = np.array([phasor(t, char, q) for t in taus])
    med = float(np.median(mag))
    return [round(float(taus[i]), 3) for i in range(1, len(mag) - 1)
            if mag[i] < mag[i - 1] and mag[i] < mag[i + 1] and mag[i] < thresh * med]


# ============================================================================================
#  THE AMPLITUDE SIDE  (the quantum is amplitude: the count residual, in units of m = L(0,chi))
# ============================================================================================
def amplitude_quantum(char, q):
    """the amplitude quantum m = L(0,chi) = -(1/q) sum_n n chi(n) (the count baseline)."""
    return -sum(n * char.get(n % q, 0) for n in range(1, q + 1)) / q

def channel_ledger(N, char, q):
    """running +/- character balance A(N); the cancellation amplitude |A(N)-m| is an integer # of quanta."""
    plus = sum(1 for n in range(1, N + 1) if char.get(n % q, 0) == 1)
    minus = sum(1 for n in range(1, N + 1) if char.get(n % q, 0) == -1)
    m = amplitude_quantum(char, q)
    return {"+": plus, "-": minus, "A(N)": plus - minus, "|A-m|": abs((plus - minus) - m)}


if __name__ == "__main__":
    chi3 = {0: 0, 1: 1, 2: -1}; q = 3
    refs = [8.04, 11.249, 15.705, 18.262, 20.456, 24.059]

    print("HELIX, backfit to the RAW (exponential) climb.  integers enter at pi/6 in the readout.\n")
    print("three axes:")
    print("  readout tau = the 1D height (= gamma at a crossing) ; 1D is taking a log")
    print("  raw climb z = e^tau         (the actual 3D height -- EXPONENTIAL)")
    print("  radius  R   = sqrt(N)       (area law ; amplitude 1/R = n^-1/2 = the sigma=1/2 modulus)\n")

    print("INGESTION: integer n enters at readout n*pi/6, i.e. raw climb e^{n pi/6}:")
    print(f"  {'n':>3} {'entry readout n*pi/6':>21} {'entry raw climb e^{}':>22}")
    for n in (1, 5, 10, 15, 16, 20):
        print(f"  {n:>3} {entry_readout(n):>21.3f} {entry_climb(n):>22.1f}")
    print()

    cr = crossings(chi3, q)
    print("PHASE CANCELLATION: the entered-integer phasor nodes at the crossings:")
    print(f"  {'#':>2} {'readout tau (= gamma)':>21} {'integers in':>12} {'RAW climb z = e^tau':>20}")
    for i, t in enumerate(cr[:6]):
        print(f"  {i + 1:>2} {t:>21.3f} {integers_entered(t):>12} {raw_climb(t):>20.1f}")
    print(f"  reference chi3 zeros (readout): {refs}")
    print()
    print("  -> 1st crossing: ~15 integers in, RAW climb ~3000 (= e^8.04).  The 8.04 is log(3000).")
    print("  -> raw climb explodes (3.0e3, 7.8e4, 6.5e6, ...); log(z) compresses it to the gammas.")
