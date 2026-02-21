import SyntheticGameTheory
import SyntheticGameTheory.Precision.Grid
import SyntheticGameTheory.Precision.PrecisionGame

namespace SyntheticGameTheory

-- ================================================================
-- Section 1: Sign type
-- ================================================================

/-- The sign of an affine difference function at a grid point.
    - `pos`: player i strictly prefers action a over a'
    - `zero`: player i is indifferent
    - `neg`: player i strictly prefers a' over a -/
inductive Sign where
  | pos : Sign
  | neg : Sign
  | zero : Sign
  deriving DecidableEq, Repr

instance Sign.instFintype : Fintype Sign :=
  ⟨{.pos, .neg, .zero}, by intro x; cases x <;> simp⟩

namespace Sign

/-- Negation of a sign: flips pos ↔ neg, zero stays. -/
def flip : Sign → Sign
  | pos => neg
  | neg => pos
  | zero => zero

@[simp] theorem flip_pos : flip pos = neg := rfl
@[simp] theorem flip_neg : flip neg = pos := rfl
@[simp] theorem flip_zero : flip zero = zero := rfl
@[simp] theorem flip_flip (s : Sign) : s.flip.flip = s := by cases s <;> rfl

/-- A sign is nonneg if it is pos or zero. -/
def isNonneg : Sign → Bool
  | pos => true
  | zero => true
  | neg => false

/-- A sign is nonpos if it is neg or zero. -/
def isNonpos : Sign → Bool
  | pos => false
  | zero => true
  | neg => true

/-- Convert a sign to an integer payoff difference.
    pos → 1, zero → 0, neg → -1. -/
def toInt : Sign → Int
  | .pos => 1
  | .zero => 0
  | .neg => -1

@[simp] theorem toInt_pos : Sign.pos.toInt = 1 := rfl
@[simp] theorem toInt_neg : Sign.neg.toInt = -1 := rfl
@[simp] theorem toInt_zero : Sign.zero.toInt = 0 := rfl

theorem isNonneg_iff_toInt (s : Sign) : s.isNonneg = true ↔ 0 ≤ s.toInt := by
  cases s <;> simp [isNonneg, toInt]

theorem toInt_nonneg_iff_isNonneg (s : Sign) : 0 ≤ s.toInt ↔ s.isNonneg = true := by
  cases s <;> simp [isNonneg, toInt]

end Sign

-- ================================================================
-- Section 2: Midpoint sign coherence (the affine constraint table)
-- ================================================================

/-- The midpoint sign constraint from the full affine coherence table (§2.3).
    Given signs at adjacent level-k points, constrains the midpoint sign at level k+1.

    Returns `none` if the midpoint is unconstrained (opposite nonzero signs),
    or `some s` if the midpoint must be `s`. -/
def forcedMidpointSign (sx sy : Sign) : Option Sign :=
  match sx, sy with
  | .pos, .pos => some .pos
  | .neg, .neg => some .neg
  | .zero, .zero => some .zero
  | .pos, .zero => some .pos
  | .zero, .pos => some .pos
  | .neg, .zero => some .neg
  | .zero, .neg => some .neg
  | .pos, .neg => none    -- unconstrained (sign change)
  | .neg, .pos => none    -- unconstrained (sign change)

end SyntheticGameTheory
