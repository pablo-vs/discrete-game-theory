/-
  Invariance.lean — Ordinal and cardinal invariance of sign games

  This file proves:
  1. SignGame extensionality (games are determined by their sign functions)
  2. Level-0 ordinal invariance: any strictly monotone transformation of
     payoffs preserves the sign game (and hence Nash equilibria)
  3. Affine invariance at higher levels: scaling both sides of a cmpSign
     by a positive constant preserves the sign
  4. A concrete counterexample showing that non-affine transformations
     can change signs at higher refinement levels

  The mathematical content: at level 0, Nash equilibria depend only on
  the ordinal ranking of payoffs (the "ordinal" theory). At higher
  refinement levels, the grid structure introduces cardinal content —
  the sign at grid point j depends on the exact indifference point,
  which is preserved by affine transformations but not by arbitrary
  strictly monotone ones. In the limit, this recovers the VNM uniqueness
  class (positive affine transformations).
-/

import SyntheticGameTheory.Refinement
import Mathlib.Order.Monotone.Basic

namespace Invariance

open Base (Sign SignGame Face PureProfile Profile cmpSign)
open Refinement (gridSize edgeCount)

-- ================================================================
-- Section 1: SignGame extensionality
-- ================================================================

variable {I : Type*} [DecidableEq I] {V : I → Type*} [∀ i, DecidableEq (V i)]

set_option linter.unusedSectionVars false in
/-- Two sign games are equal if and only if their sign functions agree. -/
theorem SignGame.ext' {G H : SignGame I V}
    (h : ∀ i p a b, G.sign i p a b = H.sign i p a b) : G = H := by
  have hsign : G.sign = H.sign :=
    funext fun i => funext fun p => funext fun a => funext fun b => h i p a b
  cases G; cases H; subst hsign; rfl

-- ================================================================
-- Section 2: Level-0 ordinal invariance
-- ================================================================

/-- Applying per-player strictly monotone transformations to payoffs
    does not change the sign game. This is the ordinal invariance theorem:
    Nash equilibria at level 0 depend only on the ordinal ranking
    of payoffs, not their cardinal values.

    Each player i can have a different transformation f i, as long as
    each one is strictly monotone. -/
theorem ofPayoffs_strictMono_invariant [Fintype I]
    (u : (i : I) → (∀ j, V j) → Int)
    (f : (i : I) → Int → Int) (hf : ∀ i, StrictMono (f i)) :
    SignGame.ofPayoffs (fun i q => f i (u i q)) = SignGame.ofPayoffs u := by
  apply SignGame.ext'
  intro i p a b
  simp only [SignGame.ofPayoffs]
  have hlt := (hf i).lt_iff_lt (a := u i (Function.update p i a))
    (b := u i (Function.update p i b))
  have heq := (hf i).injective.eq_iff (a := u i (Function.update p i a))
    (b := u i (Function.update p i b))
  split_ifs <;> simp_all <;> omega

-- ================================================================
-- Section 3: Nash invariance corollaries
-- ================================================================

/-- Nash equilibria are invariant under per-player strictly monotone
    payoff transformations. -/
theorem IsNash_invariant_strictMono [Fintype I]
    [∀ i, Fintype (V i)] [∀ i, Nonempty (V i)]
    (u : (i : I) → (∀ j, V j) → Int)
    (f : (i : I) → Int → Int) (hf : ∀ i, StrictMono (f i))
    (σ : Profile I V)
    (hN : (SignGame.ofPayoffs u).IsNash σ) :
    (SignGame.ofPayoffs (fun i q => f i (u i q))).IsNash σ := by
  rw [ofPayoffs_strictMono_invariant u f hf]; exact hN

/-- Pure Nash equilibria are invariant under per-player strictly monotone
    payoff transformations. -/
theorem IsPureNash_invariant_strictMono [Fintype I]
    (u : (i : I) → (∀ j, V j) → Int)
    (f : (i : I) → Int → Int) (hf : ∀ i, StrictMono (f i))
    (p : PureProfile I V)
    (hN : (SignGame.ofPayoffs u).IsPureNash p) :
    (SignGame.ofPayoffs (fun i q => f i (u i q))).IsPureNash p := by
  rw [ofPayoffs_strictMono_invariant u f hf]; exact hN

-- ================================================================
-- Section 4: Concrete example — two PD payoff matrices, same game
-- ================================================================

/-- Standard PD payoffs.
    Player 0: u₀(C,C)=3, u₀(C,D)=0, u₀(D,C)=5, u₀(D,D)=1.
    Player 1: u₁(C,C)=3, u₁(C,D)=5, u₁(D,C)=0, u₁(D,D)=1.
    (C = true, D = false) -/
private def pdPayoff (i : Fin 2) (q : ∀ _ : Fin 2, Bool) : Int :=
  if (i : ℕ) = 0 then
    if q 0 then (if q 1 then 3 else 0) else (if q 1 then 5 else 1)
  else
    if q 0 then (if q 1 then 3 else 5) else (if q 1 then 0 else 1)

/-- Transformed PD payoffs under f(x) = 2x + 1.
    Player 0: 7, 1, 11, 3.  Player 1: 7, 11, 1, 3. -/
private def pdPayoff' (i : Fin 2) (q : ∀ _ : Fin 2, Bool) : Int :=
  if (i : ℕ) = 0 then
    if q 0 then (if q 1 then 7 else 1) else (if q 1 then 11 else 3)
  else
    if q 0 then (if q 1 then 7 else 11) else (if q 1 then 1 else 3)

private theorem strictMono_2x_plus_1 : StrictMono (fun x : Int => 2 * x + 1) := by
  intro a b h; show 2 * a + 1 < 2 * b + 1; omega

private theorem pd_transform :
    (fun i q => (2 : Int) * pdPayoff i q + 1) = pdPayoff' := by
  funext i q
  simp only [pdPayoff, pdPayoff']
  fin_cases i <;> simp <;> (cases q 0 <;> cases q 1 <;> rfl)

/-- The two PD payoff matrices produce the same sign game,
    because f(x) = 2x + 1 is a strictly monotone transformation. -/
theorem pd_same_sign_game :
    SignGame.ofPayoffs pdPayoff' =
    SignGame.ofPayoffs pdPayoff (I := Fin 2) (V := fun _ : Fin 2 => Bool) := by
  rw [show pdPayoff' = (fun i q => 2 * pdPayoff i q + 1) from pd_transform.symm]
  exact ofPayoffs_strictMono_invariant pdPayoff (fun _ => fun x => 2 * x + 1)
    (fun _ => strictMono_2x_plus_1)

-- ================================================================
-- Section 5: cmpSign with positive scaling
-- ================================================================

/-- Scaling both arguments of cmpSign by a positive constant preserves the sign. -/
theorem cmpSign_pos_mul (c : ℕ) (hc : 0 < c) (a b : ℕ) :
    cmpSign (c * a) (c * b) = cmpSign a b := by
  simp only [cmpSign]
  split_ifs <;> simp_all

-- ================================================================
-- Section 6: Affine invariance of tower signs
-- ================================================================

/-- For bilinear towers with oppSign(k, j) = cmpSign(c·j, D·2^k),
    multiplying c and D by a positive slope doesn't change the signs.
    This is the affine invariance theorem for refinement levels:
    the tower structure is preserved by positive affine transformations. -/
theorem affine_preserves_oppSign (c D slope : ℕ) (hslope : 0 < slope) (k : ℕ)
    (j : Fin (gridSize k)) :
    cmpSign (slope * c * j.val) (slope * D * 2^k) = cmpSign (c * j.val) (D * 2^k) := by
  have h1 : slope * c * j.val = slope * (c * j.val) := Nat.mul_assoc _ _ _
  have h2 : slope * D * 2 ^ k = slope * (D * 2 ^ k) := Nat.mul_assoc _ _ _
  rw [h1, h2]
  exact cmpSign_pos_mul slope hslope _ _

-- ================================================================
-- Section 7: Counterexample — non-affine f breaks level-2 signs
-- ================================================================

/-- Original opponent-sign function for a game with indifference at p=2/5.
    Payoffs: u(A,H)=3, u(A,T)=0, u(B,H)=0, u(B,T)=2.
    Expected payoff difference = 3p - 2(1-p) = 5p - 2.
    Zero at p = 2/5. At grid point j/2^k: sign = cmpSign(5j, 2·2^k). -/
def exampleOppSign (k : ℕ) (j : Fin (gridSize k)) := cmpSign (5 * j.val) (2 * 2^k)

/-- Transformed opponent-sign under g(x) = x³.
    Payoffs become: u'(A,H)=27, u'(A,T)=0, u'(B,H)=0, u'(B,T)=8.
    Expected payoff difference = 27p - 8(1-p) = 35p - 8.
    Zero at p = 8/35. At grid point j/2^k: sign = cmpSign(35j, 8·2^k). -/
def transformedOppSign (k : ℕ) (j : Fin (gridSize k)) := cmpSign (35 * j.val) (8 * 2^k)

/-- At level 2, grid point j=1 (representing p=1/4):
    - Original: 5·1 = 5 ≤ 2·4 = 8, so sign is pos (action 0 better)
    - Transformed: 35·1 = 35 > 8·4 = 32, so sign is neg (action 1 better)
    The non-affine transformation g(x) = x³ shifted the indifference point
    from 2/5 to 8/35 ≈ 0.229, which crossed the grid point 1/4 = 0.25. -/
theorem counterexample_level2 :
    exampleOppSign 2 ⟨1, by grid_omega⟩ = .pos ∧
    transformedOppSign 2 ⟨1, by grid_omega⟩ = .neg := by
  constructor <;> decide

/-- The signs agree at level 0 (both pos at j=0, neg at j=1),
    showing that the non-affine transformation preserves level-0 behavior. -/
theorem signs_agree_level0 :
    exampleOppSign 0 ⟨0, by grid_omega⟩ = transformedOppSign 0 ⟨0, by grid_omega⟩ ∧
    exampleOppSign 0 ⟨1, by grid_omega⟩ = transformedOppSign 0 ⟨1, by grid_omega⟩ := by
  constructor <;> decide

-- ================================================================
-- Section 8: Summary
-- ================================================================

/--
## Summary: Ordinal vs Cardinal Invariance

**Level 0 (Theorem `ofPayoffs_strictMono_invariant`):**
Any per-player strictly monotone transformation of payoffs preserves
the sign game. Nash equilibria depend only on the ordinal ranking of
outcomes.

**Level k ≥ 1 (Theorem `affine_preserves_oppSign` + `counterexample_level2`):**
Only affine transformations (positive scaling) preserve the tower signs.
Non-affine monotone transformations can shift indifference points past
grid points, changing the sign data. The counterexample shows g(x) = x³
changes the sign at level 2, grid point j=1.

**In the limit:**
As k → ∞, the grid becomes dense in [0,1]. The transformations that
preserve signs at *every* level are exactly the positive affine maps
f(x) = αx + β with α > 0. This recovers the von Neumann–Morgenstern
uniqueness class for expected utility.
-/
theorem invariance_summary :
    -- Level 0: ordinal invariance (per-player strictly monotone transforms)
    (∀ {I : Type*} [DecidableEq I] [Fintype I]
      {V : I → Type*} [∀ i, DecidableEq (V i)]
      (u : (i : I) → (∀ j, V j) → Int)
      (f : (i : I) → Int → Int) (_ : ∀ i, StrictMono (f i)),
      SignGame.ofPayoffs (fun i q => f i (u i q)) = SignGame.ofPayoffs u) ∧
    -- Level 2: non-affine transformation changes signs
    (exampleOppSign 2 ⟨1, by grid_omega⟩ ≠ transformedOppSign 2 ⟨1, by grid_omega⟩) := by
  exact ⟨fun u f hf => ofPayoffs_strictMono_invariant u f hf, by decide⟩

end Invariance
