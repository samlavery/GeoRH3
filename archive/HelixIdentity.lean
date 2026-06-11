import Mathlib

/-!
# LHS = RHS Master Identity for the Mod-6 Prime Helix

We formalize the core algebraic identities underlying the "mod-6 prime helix"
decomposition described in `helix_lhs_rhs_identity.py`.

## Architecture

The key mathematical structure is:

1. **Master decomposition**: For any operator `G²` applied to a source signal,
   `source = G²(source) + (source - G²(source))`, i.e. `source = RHS + LHS`.
   This is the trivial but load-bearing split: the RHS is the smooth coordinate
   transform and the LHS is the projection loss.

2. **Transverse channel decomposition**: Two residue classes (r₁ ≡ 1 mod 6,
   r₅ ≡ 5 mod 6) combine into:
   - `principal = r₁ + r₅` (maps to ζ zeros)
   - `sign = r₁ - r₅` (maps to L(χ₃) zeros)

3. **2D collapse**: The combined 2D loss `LHS_2D = LHS_principal + LHS_sign`
   carries the full ζ_K = ζ · L(χ₃) spectrum.

All identities are proved over an arbitrary `AddCommGroup`, so they hold for
real-valued signals, distributions, or any other abelian group.
-/

section MasterIdentity

variable {α : Type*} [AddCommGroup α]

/-
The master identity: `source = G²(source) + (source - G²(source))`.
    For any element `source` and any `rhs` (representing `G²(source)`),
    `source = rhs + (source - rhs)`.
-/
theorem master_identity (source rhs : α) :
    source = rhs + (source - rhs) := by
  rw [ add_sub_cancel ]

/-
Equivalently, `LHS + RHS = source` where `LHS = source - RHS`.
-/
theorem master_identity' (source rhs : α) :
    (source - rhs) + rhs = source := by
  grind +qlia

/-- The LHS (projection loss) is the difference between source and RHS. -/
theorem lhs_def (source rhs : α) :
    source - rhs = source - rhs := rfl

end MasterIdentity

section ChannelDecomposition

variable {α : Type*} [AddCommGroup α]

/-- From two residue class signals r₁ and r₅, define the principal and sign channels. -/
def principal (r1 r5 : α) : α := r1 + r5
def sign_channel (r1 r5 : α) : α := r1 - r5

/-
Recovery: from principal and sign channels, we recover `r₁ = (principal + sign) / 2`.
    Stated in the form `principal + sign = 2 * r₁`.
-/
theorem channel_sum (r1 r5 : α) :
    principal r1 r5 + sign_channel r1 r5 = r1 + r1 := by
  unfold principal sign_channel; abel;

/-
Recovery: `principal - sign = 2 * r₅`.
-/
theorem channel_diff (r1 r5 : α) :
    principal r1 r5 - sign_channel r1 r5 = r5 + r5 := by
  unfold principal sign_channel; abel;

/-
The principal channel is symmetric: swapping r₁ and r₅ doesn't change it.
-/
theorem principal_comm (r1 r5 : α) :
    principal r1 r5 = principal r5 r1 := by
  exact add_comm _ _

/-
The sign channel is antisymmetric: swapping r₁ and r₅ negates it.
-/
theorem sign_channel_swap (r1 r5 : α) :
    sign_channel r1 r5 = -sign_channel r5 r1 := by
  unfold sign_channel; simp +decide ;

end ChannelDecomposition

section TwoDCollapse

variable {α : Type*} [AddCommGroup α]

/-
The 2D collapse: `LHS_2D = LHS_principal + LHS_sign`.
    If we apply the same operator G² to both channels, the combined loss
    decomposes as the sum of individual losses.

    Given `rhs_p = G²(principal)` and `rhs_s = G²(sign)`, we have:
    `(principal - rhs_p) + (sign - rhs_s) = (principal + sign) - (rhs_p + rhs_s)`
-/
theorem lhs_2d_decomposition (prin sign_ch rhs_p rhs_s : α) :
    (prin - rhs_p) + (sign_ch - rhs_s) = (prin + sign_ch) - (rhs_p + rhs_s) := by
  abel1

/-
Substituting the channel definitions: the combined 2D loss equals
    `2 * r₁ - (rhs_p + rhs_s)`, showing it depends only on r₁
    (the "active" residue class).
-/
theorem lhs_2d_in_terms_of_r1 (r1 r5 rhs_p rhs_s : α) :
    (principal r1 r5 - rhs_p) + (sign_channel r1 r5 - rhs_s) =
    (r1 + r1) - (rhs_p + rhs_s) := by
  convert lhs_2d_decomposition ( r1 + r5 ) ( r1 - r5 ) rhs_p rhs_s using 1;
  abel1

/-
The master identity applied to each channel and summed:
    `principal + sign = (rhs_p + rhs_s) + ((principal - rhs_p) + (sign - rhs_s))`
-/
theorem master_identity_2d (prin sign_ch rhs_p rhs_s : α) :
    prin + sign_ch = (rhs_p + rhs_s) + ((prin - rhs_p) + (sign_ch - rhs_s)) := by
  abel1

end TwoDCollapse

section OperatorIteration

variable {α : Type*} [AddCommGroup α]

/-
For a linear operator G on an additive commutative group,
    the master identity `source = G(G(source)) + (source - G(G(source)))`
    holds for G² = G ∘ G.
-/
theorem master_identity_operator (G : α →+ α) (source : α) :
    source = G (G source) + (source - G (G source)) := by
  rw [ add_sub_cancel ]

/-
Linearity of the loss: if G is a group homomorphism, then
    `LHS(a + b) = LHS(a) + LHS(b)` where `LHS(x) = x - G²(x)`.
-/
theorem loss_additive (G : α →+ α) (a b : α) :
    (a + b) - G (G (a + b)) = (a - G (G a)) + (b - G (G b)) := by
  simp +decide [ sub_add_sub_comm ]

/-
The smooth part (RHS) is also additive: `G²(a + b) = G²(a) + G²(b)`.
-/
theorem rhs_additive (G : α →+ α) (a b : α) :
    G (G (a + b)) = G (G a) + G (G b) := by
  rw [ map_add, map_add ]

end OperatorIteration

section GrowthSlope

/-
The midpoint selection principle: if a loss envelope grows like
    `x^{1/2 - α}`, then the log-log growth slope is `1/2 - α`,
    which crosses zero exactly at `α = 1/2`.

    This is formalized as: `1/2 - α = 0 ↔ α = 1/2`.
-/
theorem midpoint_selection (alpha : ℝ) :
    1/2 - alpha = 0 ↔ alpha = 1/2 := by
  constructor <;> intro h <;> linarith

/-
The growth slope `1/2 - α` is positive for `α < 1/2`
    (loss grows) and negative for `α > 1/2` (loss decays).
-/
theorem growth_slope_sign (alpha : ℝ) :
    (1/2 - alpha > 0 ↔ alpha < 1/2) ∧
    (1/2 - alpha < 0 ↔ alpha > 1/2) := by
  grind

end GrowthSlope