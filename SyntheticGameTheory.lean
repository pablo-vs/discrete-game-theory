/-
  Synthetic Game Theory: Nash Equilibria via Ordinal Utilities and Crossing Axioms

  This formalization develops game theory without numerical probabilities or cardinal utilities.
  Mixed strategies live in "synthetic simplices" with an abstract mixing operation, and
  utilities are purely ordinal (LinearOrder). The existence of Nash equilibria follows from
  a Crossing Axiom that asserts crossing points exist for betweenness-respecting functions.

  Inspired by cubical type theory's treatment of the interval.
-/

import Mathlib.Order.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.MinMax
import Mathlib.Order.Defs.PartialOrder

universe u v

/-! ## Part 1: The Synthetic Interval -/

/-- A synthetic interval abstracts [0,1] without numerical structure.
    It has endpoints and a mixing operation, with order only on the interval itself. -/
class SyntheticInterval (I : Type u) extends PartialOrder I where
  zero : I
  one : I
  mix : I → I → I
  le_total : ∀ x y : I, x ≤ y ∨ y ≤ x
  zero_le : ∀ x : I, zero ≤ x
  le_one : ∀ x : I, x ≤ one
  zero_ne_one : zero ≠ one
  mix_idem : ∀ x : I, mix x x = x
  mix_comm : ∀ x y : I, mix x y = mix y x
  mix_between_left : ∀ x y : I, x ≤ y → x ≤ mix x y
  mix_between_right : ∀ x y : I, x ≤ y → mix x y ≤ y

namespace SyntheticInterval

variable {I : Type u} [SyntheticInterval I]

/-- The mix of distinct points lies strictly between them -/
lemma mix_strict_between {x y : I} (hxy : x < y) :
    x < mix x y ∧ mix x y < y := by
  sorry

end SyntheticInterval


/-! ## Part 2: Ordinal Utilities

We use Mathlib's `LinearOrder` directly instead of a custom `OrdinalUtility` class.
Any type with `[LinearOrder R]` can serve as an ordinal utility codomain.
This gives us `≤`, `<`, `min`, `max`, decidable comparisons, and all Mathlib order lemmas. -/


/-! ## Part 3: Betweenness -/

/-- A function satisfies weak betweenness if images of mixtures lie between images of endpoints -/
def weakBetweenness {I : Type u} {R : Type v} [SyntheticInterval I] [LE R]
    (f : I → R) : Prop :=
  ∀ x y : I,
    (f x ≤ f y → f x ≤ f (SyntheticInterval.mix x y) ∧ f (SyntheticInterval.mix x y) ≤ f y) ∧
    (f y ≤ f x → f y ≤ f (SyntheticInterval.mix x y) ∧ f (SyntheticInterval.mix x y) ≤ f x)


/-! ## Part 4: The Crossing Axiom -/

/-- Two functions cross on the interval if they swap order between endpoints -/
def Crosses {I : Type u} {R : Type v} [SyntheticInterval I] [LE R]
    (f g : I → R) : Prop :=
  (f SyntheticInterval.zero ≤ g SyntheticInterval.zero ∧
   g SyntheticInterval.one ≤ f SyntheticInterval.one) ∨
  (g SyntheticInterval.zero ≤ f SyntheticInterval.zero ∧
   f SyntheticInterval.one ≤ g SyntheticInterval.one)

/-- The Crossing Axiom: if two betweenness-respecting functions cross,
    they have a common value somewhere on the interval -/
class CrossingAxiom (I : Type u) (R : Type v) [SyntheticInterval I] [LE R] where
  crossing_point : ∀ (f g : I → R),
    weakBetweenness f → weakBetweenness g → Crosses f g →
    ∃ p : I, f p = g p


/-! ## Part 5: Synthetic Simplices -/

/-- A synthetic simplex over a finite set of vertices.
    This is the abstract mixed strategy space. -/
structure SyntheticSimplex (V : Type u) [Fintype V] where
  carrier : Type u
  vertex : V → carrier
  mix : carrier → carrier → carrier
  vertex_injective : Function.Injective vertex
  mix_idem : ∀ x, mix x x = x
  mix_comm : ∀ x y, mix x y = mix y x

/-- The edge between two vertices forms a synthetic interval -/
structure Edge {V : Type u} [Fintype V] (Δ : SyntheticSimplex V) (v w : V) where
  points : Set Δ.carrier
  has_v : Δ.vertex v ∈ points
  has_w : Δ.vertex w ∈ points
  mix_closed : ∀ x y, x ∈ points → y ∈ points → Δ.mix x y ∈ points
  le : Δ.carrier → Δ.carrier → Prop
  le_total : ∀ x y, x ∈ points → y ∈ points → le x y ∨ le y x
  le_refl : ∀ x, x ∈ points → le x x
  le_antisymm : ∀ x y, x ∈ points → y ∈ points → le x y → le y x → x = y
  le_trans : ∀ x y z, x ∈ points → y ∈ points → z ∈ points →
    le x y → le y z → le x z
  v_le_w : le (Δ.vertex v) (Δ.vertex w)
  le_v : ∀ x, x ∈ points → le (Δ.vertex v) x
  le_w : ∀ x, x ∈ points → le x (Δ.vertex w)
  mix_between_left : ∀ x y, x ∈ points → y ∈ points →
    le x y → le x (Δ.mix x y)
  mix_between_right : ∀ x y, x ∈ points → y ∈ points →
    le x y → le (Δ.mix x y) y

/-- Embedding an edge point into the carrier -/
def Edge.embed {V : Type u} [Fintype V] {Δ : SyntheticSimplex V} {v w : V}
    (e : Edge Δ v w) (t : Subtype e.points) : Δ.carrier := t.val

/-- An edge can be viewed as a synthetic interval -/
def Edge.toSyntheticInterval {V : Type u} [Fintype V] {Δ : SyntheticSimplex V} {v w : V}
    (e : Edge Δ v w) (hne : v ≠ w) : SyntheticInterval (Subtype e.points) where
  le := fun x y => e.le x.val y.val
  lt := fun x y => e.le x.val y.val ∧ ¬e.le y.val x.val
  le_refl := fun x => e.le_refl x.val x.prop
  le_trans := fun {a b c} hab hbc => e.le_trans a.val b.val c.val a.prop b.prop c.prop hab hbc
  lt_iff_le_not_ge := fun _ _ => Iff.rfl
  le_antisymm := fun {a b} hab hba =>
    Subtype.ext (e.le_antisymm a.val b.val a.prop b.prop hab hba)
  zero := ⟨Δ.vertex v, e.has_v⟩
  one := ⟨Δ.vertex w, e.has_w⟩
  mix := fun x y => ⟨Δ.mix x.val y.val, e.mix_closed x.val y.val x.prop y.prop⟩
  le_total := fun x y => e.le_total x.val y.val x.prop y.prop
  zero_le := fun x => e.le_v x.val x.prop
  le_one := fun x => e.le_w x.val x.prop
  zero_ne_one := fun h => hne (Δ.vertex_injective (Subtype.mk.inj h))
  mix_idem := fun x => Subtype.ext (Δ.mix_idem x.val)
  mix_comm := fun x y => Subtype.ext (Δ.mix_comm x.val y.val)
  mix_between_left := fun x y hxy => e.mix_between_left x.val y.val x.prop y.prop hxy
  mix_between_right := fun x y hxy => e.mix_between_right x.val y.val x.prop y.prop hxy


/-! ## Part 6: Finite Games -/

/-- A finite game with ordinal utilities -/
structure FiniteGame where
  numPlayers : ℕ
  Action : Fin numPlayers → Type*
  actionFintype : ∀ i, Fintype (Action i)
  R : Type*
  instLinearOrder : LinearOrder R
  simplex : ∀ i, SyntheticSimplex (Action i)
  payoff : (∀ i, Action i) → Fin numPlayers → R

attribute [instance] FiniteGame.actionFintype FiniteGame.instLinearOrder

/-- A pure strategy profile -/
def FiniteGame.PureProfile (G : FiniteGame) := ∀ i, G.Action i

/-- A mixed strategy profile: a point in each player's simplex -/
def FiniteGame.MixedProfile (G : FiniteGame) := ∀ i, (G.simplex i).carrier

/-- Embed a pure strategy profile into a mixed strategy profile -/
def FiniteGame.pureToMixed (G : FiniteGame) (pure : G.PureProfile) : G.MixedProfile :=
  fun i => (G.simplex i).vertex (pure i)

/-- Substitute player i's strategy in a mixed profile -/
def FiniteGame.substStrategy (G : FiniteGame) (σ : G.MixedProfile)
    (i : Fin G.numPlayers) (τ : (G.simplex i).carrier) : G.MixedProfile :=
  fun j => if h : j = i then h ▸ τ else σ j


/-! ## Part 7: Extended Utilities and Best Response -/

/-- Utility extended to mixed strategies, satisfying betweenness.
    This is axiomatic: we assert the extension exists with the right properties. -/
class ExtendedUtility (G : FiniteGame) where
  payoff : G.MixedProfile → Fin G.numPlayers → G.R
  agrees_pure : ∀ (pure : G.PureProfile) (i : Fin G.numPlayers),
    payoff (G.pureToMixed pure) i = G.payoff pure i
  betweenness : ∀ (σ : G.MixedProfile) (i j : Fin G.numPlayers)
    {a b : G.Action i} (e : Edge (G.simplex i) a b) (hne : a ≠ b),
    @weakBetweenness _ G.R (e.toSyntheticInterval hne) _
      (fun t => payoff (G.substStrategy σ i (e.embed t)) j)

/-- Best response: player i's strategy is optimal given others' strategies -/
def FiniteGame.isBestResponse (G : FiniteGame) [ExtendedUtility G]
    (σ : G.MixedProfile) (i : Fin G.numPlayers) : Prop :=
  ∀ τ : (G.simplex i).carrier,
    ExtendedUtility.payoff (G.substStrategy σ i τ) i ≤
    ExtendedUtility.payoff σ i


/-! ## Part 8: Nash Equilibrium -/

/-- A Nash equilibrium: every player is best-responding -/
def FiniteGame.isNashEquilibrium (G : FiniteGame) [ExtendedUtility G]
    (σ : G.MixedProfile) : Prop :=
  ∀ i, G.isBestResponse σ i

/-- Key lemma: Best responses always include a pure strategy.
    By betweenness, the utility of any mixed strategy lies between the utilities
    of the pure strategies it mixes. Therefore the maximum utility among pure
    strategies is at least as large as any mixed strategy's utility. -/
lemma FiniteGame.bestResponseContainsPure (G : FiniteGame) [ExtendedUtility G]
    (σ : G.MixedProfile) (i : Fin G.numPlayers) :
    ∃ a : G.Action i, ∀ τ : (G.simplex i).carrier,
      ExtendedUtility.payoff (G.substStrategy σ i τ) i ≤
      ExtendedUtility.payoff (G.substStrategy σ i ((G.simplex i).vertex a)) i := by
  sorry


/-! ## Part 9: General Nash Existence via Synthetic Fixed-Point Axiom -/

/-- Synthetic Fixed-Point Axiom: any betweenness-respecting self-map of a product
    of simplices has a fixed point. This is the synthetic analog of Brouwer's
    fixed-point theorem.

    In the standard model (simplices over ℝ), betweenness-respecting maps are
    continuous, and the axiom follows from Brouwer. In finitely-presented models,
    the user provides the fixed-point witness. -/
class SyntheticFixedPoint (G : FiniteGame) where
  fixed_point :
    ∀ (F : G.MixedProfile → G.MixedProfile),
    (∀ (σ : G.MixedProfile) (i j : Fin G.numPlayers)
      {a b : G.Action i} (e : Edge (G.simplex i) a b) (hne : a ≠ b),
      @weakBetweenness _ (G.simplex j).carrier (e.toSyntheticInterval hne) ⟨fun _ _ => True⟩
        (fun t => (F (G.substStrategy σ i (e.embed t))) j)) →
    ∃ x : G.MixedProfile, F x = x

/-- General Nash existence theorem: every finite game with extended utilities
    and the synthetic fixed-point property has a Nash equilibrium. -/
theorem FiniteGame.nash_exists (G : FiniteGame) [ExtendedUtility G]
    [SyntheticFixedPoint G] :
    ∃ σ : G.MixedProfile, G.isNashEquilibrium σ := by
  sorry


/-! ## Part 10: The 2×2 Proof in Detail -/

section TwoByTwo

/-- A 2×2 game: two players, each with two actions -/
structure TwoByTwoGame where
  R : Type*
  instR : LinearOrder R
  u1_TL : R
  u1_TR : R
  u1_BL : R
  u1_BR : R
  u2_TL : R
  u2_TR : R
  u2_BL : R
  u2_BR : R

attribute [instance] TwoByTwoGame.instR

/-- Player 1's strategies -/
inductive P1Strategy | Top | Bottom
  deriving DecidableEq

instance : Fintype P1Strategy where
  elems := {P1Strategy.Top, P1Strategy.Bottom}
  complete := fun x => by cases x <;> simp

/-- Player 2's strategies -/
inductive P2Strategy | Left | Right
  deriving DecidableEq

instance : Fintype P2Strategy where
  elems := {P2Strategy.Left, P2Strategy.Right}
  complete := fun x => by cases x <;> simp

/-- A pure Nash exists if some cell is a mutual best response -/
def TwoByTwoGame.hasPureNash (G : TwoByTwoGame) : Prop :=
  (G.u1_BL ≤ G.u1_TL ∧ G.u2_TR ≤ G.u2_TL) ∨
  (G.u1_BR ≤ G.u1_TR ∧ G.u2_TL ≤ G.u2_TR) ∨
  (G.u1_TL ≤ G.u1_BL ∧ G.u2_BR ≤ G.u2_BL) ∨
  (G.u1_TR ≤ G.u1_BR ∧ G.u2_BL ≤ G.u2_BR)

/-- Best response cycling: no pure Nash, preferences cycle -/
def TwoByTwoGame.hasCycling (G : TwoByTwoGame) : Prop :=
  ¬G.hasPureNash ∧
  ((G.u2_TR < G.u2_TL ∧ G.u2_BL < G.u2_BR) ∨
   (G.u2_TL < G.u2_TR ∧ G.u2_BR < G.u2_BL))

/-- When cycling occurs, there exists an indifference point for player 2.
    The cycling condition implies the payoff functions cross, so the
    crossing axiom yields a common value. -/
lemma TwoByTwoGame.indifference_point_exists
    (G : TwoByTwoGame) (I : Type u) [SyntheticInterval I] [CrossingAxiom I G.R]
    (h_cycle : G.hasCycling)
    (f : I → G.R)
    (g : I → G.R)
    (hf : weakBetweenness f)
    (hg : weakBetweenness g)
    (hf0 : f SyntheticInterval.zero = G.u2_TL)
    (hf1 : f SyntheticInterval.one = G.u2_BL)
    (hg0 : g SyntheticInterval.zero = G.u2_TR)
    (hg1 : g SyntheticInterval.one = G.u2_BR) :
    ∃ p : I, f p = g p := by
  have h_cross : Crosses f g := by
    obtain ⟨_, hcyc⟩ := h_cycle
    cases hcyc with
    | inl h =>
      -- u2_TR < u2_TL and u2_BL < u2_BR
      -- So g(0)=u2_TR ≤ f(0)=u2_TL and f(1)=u2_BL ≤ g(1)=u2_BR
      right
      exact ⟨by rw [hf0, hg0]; exact le_of_lt h.1,
             by rw [hf1, hg1]; exact le_of_lt h.2⟩
    | inr h =>
      -- u2_TL < u2_TR and u2_BR < u2_BL
      -- So f(0)=u2_TL ≤ g(0)=u2_TR and g(1)=u2_BR ≤ f(1)=u2_BL
      left
      exact ⟨by rw [hf0, hg0]; exact le_of_lt h.1,
             by rw [hf1, hg1]; exact le_of_lt h.2⟩
  exact CrossingAxiom.crossing_point f g hf hg h_cross

/-- Main theorem for 2×2 games: either a pure Nash exists, or given
    betweenness-respecting payoff extensions along the mixing edge,
    indifference points exist for both players -/
theorem TwoByTwoGame.twoByTwo_nash_exists
    (G : TwoByTwoGame) (I : Type u) [SyntheticInterval I] [CrossingAxiom I G.R] :
    G.hasPureNash ∨ (∀ (f₁ g₁ f₂ g₂ : I → G.R),
      weakBetweenness f₁ → weakBetweenness g₁ →
      weakBetweenness f₂ → weakBetweenness g₂ →
      f₁ SyntheticInterval.zero = G.u1_TL →
      f₁ SyntheticInterval.one = G.u1_BL →
      g₁ SyntheticInterval.zero = G.u1_TR →
      g₁ SyntheticInterval.one = G.u1_BR →
      f₂ SyntheticInterval.zero = G.u2_TL →
      f₂ SyntheticInterval.one = G.u2_BL →
      g₂ SyntheticInterval.zero = G.u2_TR →
      g₂ SyntheticInterval.one = G.u2_BR →
      G.hasCycling →
      (∃ p : I, f₂ p = g₂ p) ∧ (∃ q : I, f₁ q = g₁ q)) := by
  by_cases h : G.hasPureNash
  · left; exact h
  · right
    intro f₁ g₁ f₂ g₂ hf₁ hg₁ hf₂ hg₂ hf₁0 hf₁1 hg₁0 hg₁1 hf₂0 hf₂1 hg₂0 hg₂1 hcyc
    constructor
    · exact G.indifference_point_exists I hcyc f₂ g₂ hf₂ hg₂ hf₂0 hf₂1 hg₂0 hg₂1
    · -- Player 1's indifference point: symmetric argument via crossing
      sorry

end TwoByTwo


/-! ## Part 11: Example Games -/

section Examples

/-- Matching Pennies: 2×2 game with no pure Nash equilibrium.
    Player 1 wins when both choose the same side, Player 2 wins on mismatch. -/
def matchingPennies : TwoByTwoGame where
  R := Fin 2
  instR := inferInstance
  u1_TL := 1; u1_TR := 0; u1_BL := 0; u1_BR := 1
  u2_TL := 0; u2_TR := 1; u2_BL := 1; u2_BR := 0

/-- Matching Pennies has no pure Nash equilibrium -/
theorem matchingPennies_no_pure_nash : ¬matchingPennies.hasPureNash := by
  simp only [matchingPennies, TwoByTwoGame.hasPureNash]
  rintro (⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩) <;> revert h <;> decide

/-- Matching Pennies exhibits cycling -/
theorem matchingPennies_has_cycling : matchingPennies.hasCycling := by
  refine ⟨matchingPennies_no_pure_nash, Or.inr ?_⟩
  simp only [matchingPennies]
  exact ⟨by decide, by decide⟩

/-- Prisoner's Dilemma: 2×2 game with a unique pure Nash equilibrium (Defect, Defect).
    Utilities: 0=sucker, 1=punish, 2=reward, 3=temptation -/
def prisonersDilemma : TwoByTwoGame where
  R := Fin 4
  instR := inferInstance
  u1_TL := 2; u1_TR := 0; u1_BL := 3; u1_BR := 1
  u2_TL := 2; u2_TR := 3; u2_BL := 0; u2_BR := 1

/-- Prisoner's Dilemma has a pure Nash equilibrium (Bottom-Right = Defect-Defect) -/
theorem prisonersDilemma_has_pure_nash : prisonersDilemma.hasPureNash := by
  unfold prisonersDilemma TwoByTwoGame.hasPureNash
  right; right; right
  exact ⟨by decide, by decide⟩

/-- Battle of the Sexes: 2×2 game with two pure Nash equilibria -/
def battleOfSexes : TwoByTwoGame where
  R := Fin 3
  instR := inferInstance
  u1_TL := 2; u1_TR := 0; u1_BL := 0; u1_BR := 1
  u2_TL := 1; u2_TR := 0; u2_BL := 0; u2_BR := 2

/-- Battle of the Sexes has a pure Nash equilibrium -/
theorem battleOfSexes_has_pure_nash : battleOfSexes.hasPureNash := by
  unfold battleOfSexes TwoByTwoGame.hasPureNash
  left
  exact ⟨by decide, by decide⟩

/-- A common action type for both players in a 2×2 game (2 pure strategies each) -/
inductive TwoAction | A | B
  deriving DecidableEq

instance : Fintype TwoAction where
  elems := {TwoAction.A, TwoAction.B}
  complete := fun x => by cases x <;> simp

/-- Convert a TwoByTwoGame into a FiniteGame using a common action type.
    Player 0: A=Top, B=Bottom. Player 1: A=Left, B=Right. -/
noncomputable def TwoByTwoGame.toFiniteGame (G : TwoByTwoGame)
    (Δ : ∀ (_ : Fin 2), SyntheticSimplex TwoAction) : FiniteGame where
  numPlayers := 2
  Action := fun _ => TwoAction
  actionFintype := fun _ => inferInstance
  R := G.R
  instLinearOrder := G.instR
  simplex := Δ
  payoff := fun profile player =>
    match profile ⟨0, by omega⟩, profile ⟨1, by omega⟩, player with
    | TwoAction.A, TwoAction.A, ⟨0, _⟩ => G.u1_TL
    | TwoAction.A, TwoAction.B, ⟨0, _⟩ => G.u1_TR
    | TwoAction.B, TwoAction.A, ⟨0, _⟩ => G.u1_BL
    | TwoAction.B, TwoAction.B, ⟨0, _⟩ => G.u1_BR
    | TwoAction.A, TwoAction.A, ⟨1, _⟩ => G.u2_TL
    | TwoAction.A, TwoAction.B, ⟨1, _⟩ => G.u2_TR
    | TwoAction.B, TwoAction.A, ⟨1, _⟩ => G.u2_BL
    | TwoAction.B, TwoAction.B, ⟨1, _⟩ => G.u2_BR
    | _, _, ⟨n + 2, h⟩ => absurd h (by omega)

end Examples
