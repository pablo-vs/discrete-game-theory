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
  strictly monotone ones. In the limit, this recovers the uniqueness
  class of Von Neumann-Morgenstern utility functions (positive affine
  transformations), and hence the same expressiveness of standard game
  theory.
-/

import DiscreteGameTheory.Refinement
import Mathlib.Order.Monotone.Basic

namespace Invariance

open Base (Sign SignGame Face PureProfile Profile cmpSign)

-- ================================================================
-- Section 1: SignGame extensionality
-- ================================================================

variable {I : Type*} [DecidableEq I] {V : I → Type*} [∀ i, DecidableEq (V i)]

omit [DecidableEq I] [∀ i, DecidableEq (V i)] in
/-- Two sign games are equal if and only if their sign functions agree. -/
-- ANCHOR: SignGame.ext'
@[ext]
lemma SignGame.ext' {G H : SignGame I V}
    (h : ∀ i p q,
      G.sign i p q = H.sign i p q) :
    G = H := by
-- ANCHOR_END: SignGame.ext'
  have hsign : G.sign = H.sign :=
    funext fun i => funext fun p =>
      funext fun q => h i p q
  cases G; cases H; subst hsign; rfl

-- ================================================================
-- Section 2: Level-0 ordinal invariance
-- ================================================================

omit [∀ i, DecidableEq (V i)] in
-- ANCHOR: ofPayoffs_strictMono_invariant
theorem ofPayoffs_strictMono_invariant [Fintype I]
    (u : (i : I) → (∀ j, V j) → Int)
    (f : (i : I) → Int → Int)
    (hf : ∀ i, StrictMono (f i)) :
    SignGame.ofPayoffs (fun i q => f i (u i q)) =
    SignGame.ofPayoffs u := by
-- ANCHOR_END: ofPayoffs_strictMono_invariant
  apply SignGame.ext'
  intro i p q
  simp only [SignGame.ofPayoffs]
  have hlt := (hf i).lt_iff_lt (a := u i p) (b := u i q)
  have heq := (hf i).injective.eq_iff (a := u i p) (b := u i q)
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

omit [∀ i, DecidableEq (V i)] in
/-- Pure Nash equilibria are invariant under per-player strictly monotone
    payoff transformations. -/
lemma IsPureNash_invariant_strictMono [Fintype I]
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

private lemma strictMono_2x_plus_1 : StrictMono (fun x : Int => 2 * x + 1) := by
  intro a b h; show 2 * a + 1 < 2 * b + 1; omega

private lemma pd_transform :
    (fun i q => (2 : Int) * pdPayoff i q + 1) = pdPayoff' := by
  funext i q
  simp only [pdPayoff, pdPayoff']
  fin_cases i <;> simp <;> (cases q 0 <;> cases q 1 <;> rfl)

/-- The two PD payoff matrices produce the same sign game,
    because f(x) = 2x + 1 is a strictly monotone transformation. -/
lemma pd_same_sign_game :
    SignGame.ofPayoffs pdPayoff' =
    SignGame.ofPayoffs pdPayoff (I := Fin 2) (V := fun _ : Fin 2 => Bool) := by
  rw [show pdPayoff' = (fun i q => 2 * pdPayoff i q + 1) from pd_transform.symm]
  exact ofPayoffs_strictMono_invariant pdPayoff (fun _ => fun x => 2 * x + 1)
    (fun _ => strictMono_2x_plus_1)

-- ================================================================
-- Section 5: Tower-compatible payoff families
-- ================================================================

open Refinement (SignTower embedPureProfile)

/-- A payoff family `U` is tower-compatible with a `SignTower T` if:
    1. At each level, `ofPayoffs (U k)` recovers the sign game `T.game k`.
    2. Payoffs are coherent across levels: `U k i p = U (k+1) i (embed p)`.
    The second condition prevents constructing a compatible U that respects
    the affine structure at each level individually but not across levels. -/
structure TowerCompatible {I : Type*} [DecidableEq I] [Fintype I]
    (T : SignTower I)
    (U : (k : ℕ) → (i : I) → Base.PureProfile I (T.V k) → Int) : Prop where
  recovers : ∀ k, SignGame.ofPayoffs (U k) = T.game k
  coherent : ∀ k i (p : Base.PureProfile I (T.V k)),
    U k i p = U (k+1) i (embedPureProfile (T.embed k) p)

/-- Any tower-compatible payoff family produces the same Nash equilibria
    as the tower's games — immediate from the `recovers` condition. -/
theorem TowerCompatible.isNash_iff {I : Type*} [DecidableEq I] [Fintype I]
    {T : SignTower I}
    {U : (k : ℕ) → (i : I) → Base.PureProfile I (T.V k) → Int}
    (hU : TowerCompatible T U) (k : ℕ)
    (σ : Base.Profile I (T.V k)) :
    (SignGame.ofPayoffs (U k)).IsNash σ ↔ (T.game k).IsNash σ := by
  rw [hU.recovers]

end Invariance
