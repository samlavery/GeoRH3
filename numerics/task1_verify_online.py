"""
Task 1: Verify χ₃ zeros are genuinely on σ=½.
- Random sample of 25 γ values from the record.
- Compute |L(½+iγ, χ₃)| with mpmath (expect < 1e-8).
- Also check |L(σ+iγ)| for σ=0.4, 0.6 to confirm it's nonzero off the line.
"""
import mpmath
import random

mpmath.mp.dps = 50  # 50 decimal places

def L_chi3(s):
    """L(s,χ₃) = 3^{-s}(ζ(s,1/3) - ζ(s,2/3))"""
    return mpmath.power(3, -s) * (mpmath.zeta(s, mpmath.mpf('1')/3) - mpmath.zeta(s, mpmath.mpf('2')/3))

# Parse record file
gammas = []
with open('/Users/samuellavery/proof/three/numerics/lchi3_zeros_record.txt') as f:
    for line in f:
        line = line.strip()
        if not line or line.startswith('#'):
            continue
        parts = line.split()
        if len(parts) >= 2:
            try:
                gamma = mpmath.mpf(parts[1])
                gammas.append(gamma)
            except:
                pass

print(f"Total χ₃ zeros in record: {len(gammas)}")
print(f"Range: [{float(gammas[0]):.4f}, {float(gammas[-1]):.4f}]")

# Random sample of 25
random.seed(42)
sample_indices = sorted(random.sample(range(len(gammas)), 25))
sample_gammas = [gammas[i] for i in sample_indices]

print("\n--- Task 1: Verify zeros on σ=½ ---")
print(f"{'idx':>6}  {'γ':>12}  {'|L(½+iγ)|':>14}  {'|L(0.4+iγ)|':>14}  {'|L(0.6+iγ)|':>14}")
print("-" * 72)

max_on_line = mpmath.mpf(0)
on_line_values = []
off_line_04 = []
off_line_06 = []

for i, (idx, gamma) in enumerate(zip(sample_indices, sample_gammas)):
    s_half = mpmath.mpc('0.5', gamma)
    s_04   = mpmath.mpc('0.4', gamma)
    s_06   = mpmath.mpc('0.6', gamma)

    val_half = abs(L_chi3(s_half))
    val_04   = abs(L_chi3(s_04))
    val_06   = abs(L_chi3(s_06))

    on_line_values.append(val_half)
    off_line_04.append(val_04)
    off_line_06.append(val_06)

    if val_half > max_on_line:
        max_on_line = val_half

    print(f"{idx+1:>6}  {float(gamma):>12.4f}  {float(val_half):>14.3e}  {float(val_04):>14.6f}  {float(val_06):>14.6f}")

print("-" * 72)
print(f"\nMax |L(½+iγ)| over sample: {float(max_on_line):.3e}")
print(f"Min |L(0.4+iγ)| over sample: {float(min(off_line_04)):.6f}")
print(f"Min |L(0.6+iγ)| over sample: {float(min(off_line_06)):.6f}")

# Confirm: all on-line values tiny, off-line values clearly nonzero
n_tiny = sum(1 for v in on_line_values if v < mpmath.mpf('1e-8'))
n_big_04 = sum(1 for v in off_line_04 if v > mpmath.mpf('0.01'))
n_big_06 = sum(1 for v in off_line_06 if v > mpmath.mpf('0.01'))

print(f"\nVerdicts:")
print(f"  Samples with |L(½+iγ)| < 1e-8: {n_tiny}/25")
print(f"  Samples with |L(0.4+iγ)| > 0.01: {n_big_04}/25")
print(f"  Samples with |L(0.6+iγ)| > 0.01: {n_big_06}/25")

if n_tiny == 25:
    print("\n  ✓ All 25 sampled γ values are genuine zeros on σ=½.")
else:
    print(f"\n  WARNING: {25-n_tiny} samples did NOT satisfy |L(½+iγ)| < 1e-8!")
