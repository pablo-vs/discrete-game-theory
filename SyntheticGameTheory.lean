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
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Fintype.EquivFin

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
  mix_strict_left : ∀ x y : I, x < y → x < mix x y
  mix_strict_right : ∀ x y : I, x < y → mix x y < y

namespace SyntheticInterval

variable {I : Type u} [SyntheticInterval I]

/-- The mix of distinct points lies strictly between them -/
lemma mix_strict_between {x y : I} (hxy : x < y) :
    x < mix x y ∧ mix x y < y :=
  ⟨mix_strict_left x y hxy, mix_strict_right x y hxy⟩

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


/-- Betweenness for functions on a type with a binary mix operation.
    No domain order is needed — only the codomain order matters.
    The value at mix(x,y) lies between the values at x and y. -/
def mixBetweenness {S : Type*} {R : Type*} [LE R]
    (mix : S → S → S) (f : S → R) : Prop :=
  ∀ x y : S,
    (f x ≤ f y → f x ≤ f (mix x y) ∧ f (mix x y) ≤ f y) ∧
    (f y ≤ f x → f y ≤ f (mix x y) ∧ f (mix x y) ≤ f x)


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
  /-- The carrier is inductively generated from vertices and mix.
      This is the recursor for the free algebra over vertex and mix. -/
  induction : ∀ (P : carrier → Prop),
    (∀ v : V, P (vertex v)) →
    (∀ x y, P x → P y → P (mix x y)) →
    ∀ x, P x

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
  mix_ne_left : ∀ x y, x ∈ points → y ∈ points →
    le x y → ¬le y x → ¬le (Δ.mix x y) x
  mix_ne_right : ∀ x y, x ∈ points → y ∈ points →
    le x y → ¬le y x → ¬le y (Δ.mix x y)

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
  mix_strict_left := fun x y hxy =>
    ⟨e.mix_between_left x.val y.val x.prop y.prop hxy.1,
     e.mix_ne_left x.val y.val x.prop y.prop hxy.1 hxy.2⟩
  mix_strict_right := fun x y hxy =>
    ⟨e.mix_between_right x.val y.val x.prop y.prop hxy.1,
     e.mix_ne_right x.val y.val x.prop y.prop hxy.1 hxy.2⟩


/-! ## Part 6: Finite Games -/

/-- A finite game with ordinal utilities -/
structure FiniteGame where
  numPlayers : ℕ
  Action : Fin numPlayers → Type*
  actionFintype : ∀ i, Fintype (Action i)
  actionNonempty : ∀ i, Nonempty (Action i)
  R : Type*
  instLinearOrder : LinearOrder R
  simplex : ∀ i, SyntheticSimplex (Action i)
  payoff : (∀ i, Action i) → Fin numPlayers → R

attribute [instance] FiniteGame.actionFintype FiniteGame.instLinearOrder FiniteGame.actionNonempty

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

/-- `substStrategy` with `G` implicit, for use with notation. -/
def FiniteGame.MixedProfile.subst {G : FiniteGame} (σ : G.MixedProfile)
    (i : Fin G.numPlayers) (τ : (G.simplex i).carrier) : G.MixedProfile :=
  G.substStrategy σ i τ

scoped[FiniteGame] notation σ "[" i " ↦ " τ "]" => FiniteGame.MixedProfile.subst σ i τ

@[simp] lemma FiniteGame.substStrategy_same (G : FiniteGame) (σ : G.MixedProfile)
    (i : Fin G.numPlayers) (τ : (G.simplex i).carrier) :
    G.substStrategy σ i τ i = τ := by
  simp [FiniteGame.substStrategy]

@[simp] lemma FiniteGame.substStrategy_ne (G : FiniteGame) (σ : G.MixedProfile)
    (i : Fin G.numPlayers) (τ : (G.simplex i).carrier)
    (j : Fin G.numPlayers) (h : j ≠ i) :
    G.substStrategy σ i τ j = σ j := by
  simp [FiniteGame.substStrategy, h]

/-! ## Part 7: Extended Utilities and Best Response -/

/-- Utility extended to mixed strategies, satisfying betweenness.
    This is axiomatic: we assert the extension exists with the right properties. -/
class ExtendedUtility (G : FiniteGame) where
  payoff : G.MixedProfile → Fin G.numPlayers → G.R
  agrees_pure : ∀ (pure : G.PureProfile) (i : Fin G.numPlayers),
    payoff (G.pureToMixed pure) i = G.payoff pure i
  /-- Mixing any two strategies for player i produces an intermediate utility
      for every player j. This is the carrier-wide betweenness axiom — no
      domain order is needed. -/
  betweenness : ∀ (σ : G.MixedProfile) (i j : Fin G.numPlayers),
    mixBetweenness (G.simplex i).mix
      (fun τ => payoff (G.substStrategy σ i τ) j)

/-- Betweenness on the full carrier implies weakBetweenness when restricted
    to an edge, since the edge mix is just the simplex mix on edge points. -/
lemma ExtendedUtility.edge_betweenness (G : FiniteGame) [ExtendedUtility G]
    (σ : G.MixedProfile) (i j : Fin G.numPlayers)
    {a b : G.Action i} (e : Edge (G.simplex i) a b) (hne : a ≠ b) :
    @weakBetweenness _ G.R (e.toSyntheticInterval hne) _
      (fun t => ExtendedUtility.payoff (G.substStrategy σ i (e.embed t)) j) :=
  fun x y => ExtendedUtility.betweenness σ i j x.val y.val

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
  -- Abbreviate the utility function
  set f := fun τ => ExtendedUtility.payoff (G.substStrategy σ i τ) i with hf_def
  -- Find the best pure strategy (argmax over the finite nonempty action set)
  have hmax : ∃ a : G.Action i, ∀ b : G.Action i,
      f ((G.simplex i).vertex b) ≤ f ((G.simplex i).vertex a) := by
    haveI : Finite (G.Action i) := Finite.of_fintype (G.Action i)
    exact Finite.exists_max (fun a => f ((G.simplex i).vertex a))
  obtain ⟨a, ha⟩ := hmax
  exact ⟨a, (G.simplex i).induction
    (fun τ => f τ ≤ f ((G.simplex i).vertex a))
    (fun v => ha v)
    (fun x y hx hy => by
      -- By mixBetweenness, f(mix x y) is between f(x) and f(y)
      have hbet := ExtendedUtility.betweenness σ i i x y
      -- Both f(x) ≤ f(vertex a) and f(y) ≤ f(vertex a)
      -- Case split: which of f(x), f(y) is larger?
      rcases le_total (f x) (f y) with hxy | hyx
      · exact le_trans (hbet.1 hxy).2 hy
      · exact le_trans (hbet.2 hyx).2 hx)⟩


/-! ## Part 9: General Nash Existence via Synthetic Fixed-Point Axiom -/

/-- A Nash equilibrium witness: bundles a profile with its proof.
    Useful for finite models where the equilibrium is explicit data. -/
structure NashWitness (G : FiniteGame) [ExtendedUtility G] where
  profile : G.MixedProfile
  is_nash : G.isNashEquilibrium profile

/-- Synthetic Fixed-Point Axiom: any betweenness-respecting self-map of a product
    of simplices has a fixed point. This is the synthetic analog of Brouwer's
    fixed-point theorem.

    Betweenness is tested via utilities: for each input edge (player i varying
    between actions a and b) and each player j, the utility of j at F(σ)
    satisfies weakBetweenness along the edge.

    In the standard model (simplices over ℝ), betweenness-respecting maps are
    continuous, and the axiom follows from Brouwer. In finitely-presented models,
    the user provides the fixed-point witness. -/
class SyntheticFixedPoint (G : FiniteGame) [ExtendedUtility G] where
  fixed_point :
    ∀ (F : G.MixedProfile → G.MixedProfile),
    (∀ (σ : G.MixedProfile) (i : Fin G.numPlayers)
      {a b : G.Action i} (e : Edge (G.simplex i) a b) (hne : a ≠ b)
      (j : Fin G.numPlayers),
      @weakBetweenness _ G.R (e.toSyntheticInterval hne) _
        (fun t => ExtendedUtility.payoff
          (F (G.substStrategy σ i (e.embed t))) j)) →
    ∃ x : G.MixedProfile, F x = x

/-- A `NashMap` bundles a self-map on mixed profiles together with:
    (1) a betweenness proof matching the hypothesis of `SyntheticFixedPoint`, and
    (2) a proof that any fixed point of the map is a Nash equilibrium.

    This factoring (AD-8) separates the topological content (the fixed-point axiom
    gives a fixed point of any betweenness-respecting map) from the game-theoretic
    content (this particular map's fixed points are equilibria).

    The hard part — constructing such a map — is isolated into `NashMap.construct`. -/
structure NashMap (G : FiniteGame) [ExtendedUtility G] where
  /-- The self-map on mixed strategy profiles. -/
  toFun : G.MixedProfile → G.MixedProfile
  /-- The map respects betweenness: for each base profile σ, player i's edge
      between actions a ≠ b, and any player j, the utility of j at F(σ[i ↦ ·])
      satisfies weakBetweenness along the edge. This is exactly the hypothesis
      required by `SyntheticFixedPoint.fixed_point`. -/
  betweenness : ∀ (σ : G.MixedProfile) (i : Fin G.numPlayers)
    {a b : G.Action i} (e : Edge (G.simplex i) a b) (hne : a ≠ b)
    (j : Fin G.numPlayers),
    @weakBetweenness _ G.R (e.toSyntheticInterval hne) _
      (fun t => ExtendedUtility.payoff (toFun (G.substStrategy σ i (e.embed t))) j)
  /-- Every fixed point of the map is a Nash equilibrium. -/
  fixed_point_is_nash : ∀ σ, toFun σ = σ → G.isNashEquilibrium σ

/-- Given a `NashMap` and the synthetic fixed-point axiom, a Nash equilibrium exists.

    Proof: apply the fixed-point axiom to obtain a fixed point of the map,
    then invoke `fixed_point_is_nash`. -/
theorem FiniteGame.nash_of_nashMap (G : FiniteGame) [ExtendedUtility G]
    [SyntheticFixedPoint G] (nm : NashMap G) :
    ∃ σ, G.isNashEquilibrium σ := by
  obtain ⟨σ, hσ⟩ := SyntheticFixedPoint.fixed_point nm.toFun nm.betweenness
  exact ⟨σ, nm.fixed_point_is_nash σ hσ⟩

/-- Construct a `NashMap` for an arbitrary finite game.

    This is the hard part of general Nash existence. The map must:
    - be betweenness-respecting (so the fixed-point axiom applies), and
    - have the property that fixed points are Nash equilibria.

    The naive "mix toward best response" map fails because `argmax` over pure
    strategies can jump discontinuously as the profile varies along an edge,
    breaking the betweenness hypothesis (see OQ-1).

    The intended construction uses *indifference-seeking*: move profiles toward
    points where players are indifferent between actions (found via crossing data
    on each edge). This avoids the argmax discontinuity.

    For games where a direct `NashWitness` is available (e.g., 2×2 games via
    `twoByTwo_nash_exists`), `NashMap` is not needed — the witness suffices. -/
noncomputable def NashMap.construct (G : FiniteGame) [ExtendedUtility G] :
    NashMap G := by
  exact sorry

/-- General Nash existence theorem: every finite game with extended utilities
    and the synthetic fixed-point property has a Nash equilibrium.

    Strategy (per AD-8): factor through `NashMap`.
    1. `NashMap.construct` builds a betweenness-respecting self-map whose fixed
       points are Nash equilibria. (Currently sorry — see `NashMap.construct`.)
    2. `nash_of_nashMap` applies the fixed-point axiom and extracts the equilibrium.

    The sole remaining sorry is in `NashMap.construct`, which requires solving
    the discontinuity problem described in OQ-1. -/
theorem FiniteGame.nash_exists (G : FiniteGame) [ExtendedUtility G]
    [SyntheticFixedPoint G] :
    ∃ σ : G.MixedProfile, G.isNashEquilibrium σ :=
  G.nash_of_nashMap (NashMap.construct G)


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

/-- Best response cycling: no pure Nash, preferences cycle (player 2 only).
    Superseded by `fullCycling` but kept for compatibility. -/
@[deprecated "Use fullCycling instead." (since := "2026-01-31")]
def TwoByTwoGame.hasCycling (G : TwoByTwoGame) : Prop :=
  ¬G.hasPureNash ∧
  ((G.u2_TR < G.u2_TL ∧ G.u2_BL < G.u2_BR) ∨
   (G.u2_TL < G.u2_TR ∧ G.u2_BR < G.u2_BL))

/-- Full cycling: both players' preferences cross.
    Case 1: P1 prefers B@L, T@R; P2 prefers L@T, R@B
    Case 2: P1 prefers T@L, B@R; P2 prefers R@T, L@B -/
def TwoByTwoGame.fullCycling (G : TwoByTwoGame) : Prop :=
  (G.u1_TL < G.u1_BL ∧ G.u1_BR < G.u1_TR ∧
   G.u2_TR < G.u2_TL ∧ G.u2_BL < G.u2_BR) ∨
  (G.u1_BL < G.u1_TL ∧ G.u1_TR < G.u1_BR ∧
   G.u2_TL < G.u2_TR ∧ G.u2_BR < G.u2_BL)

/-- Full cycling implies (deprecated) player-2-only cycling. -/
lemma TwoByTwoGame.hasCycling_of_fullCycling (G : TwoByTwoGame) :
    G.fullCycling → G.hasCycling := by
  intro h
  rcases h with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · have hnp : ¬ G.hasPureNash := by
      intro hnp
      rcases hnp with h | h | h | h
      · exact (not_lt_of_ge h.1) h1
      · exact (not_lt_of_ge h.2) h3
      · exact (not_lt_of_ge h.2) h4
      · exact (not_lt_of_ge h.1) h2
    exact ⟨hnp, Or.inl ⟨h3, h4⟩⟩
  · have hnp : ¬ G.hasPureNash := by
      intro hnp
      rcases hnp with h | h | h | h
      · exact (not_lt_of_ge h.2) h3
      · exact (not_lt_of_ge h.1) h2
      · exact (not_lt_of_ge h.1) h1
      · exact (not_lt_of_ge h.2) h4
    exact ⟨hnp, Or.inr ⟨h3, h4⟩⟩

/-- In a 2×2 game with LinearOrder, absence of a pure Nash implies full cycling:
    both players' preferences must cross. -/
lemma TwoByTwoGame.no_pure_implies_full_cycling (G : TwoByTwoGame)
    (h : ¬G.hasPureNash) : G.fullCycling := by
  simp only [hasPureNash, not_or] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [not_and_or] at h1 h2 h3 h4
  simp only [not_le] at h1 h2 h3 h4
  -- h1 : u1_TL < u1_BL ∨ u2_TL < u2_TR
  -- h2 : u1_TR < u1_BR ∨ u2_TR < u2_TL
  -- h3 : u1_BL < u1_TL ∨ u2_BL < u2_BR
  -- h4 : u1_BR < u1_TR ∨ u2_BR < u2_BL
  unfold fullCycling
  rcases lt_trichotomy G.u2_TL G.u2_TR with htop | htop | htop
  · -- Case: u2_TL < u2_TR → second disjunct of fullCycling
    right
    have p2 : G.u1_TR < G.u1_BR := h2.resolve_right (not_lt.mpr (le_of_lt htop))
    have p4 : G.u2_BR < G.u2_BL := h4.resolve_left (not_lt.mpr (le_of_lt p2))
    have p3 : G.u1_BL < G.u1_TL := h3.resolve_right (not_lt.mpr (le_of_lt p4))
    exact ⟨p3, p2, htop, p4⟩
  · -- Case: u2_TL = u2_TR → contradiction
    have p1 : G.u1_TL < G.u1_BL := h1.resolve_right (htop ▸ lt_irrefl _)
    have p2 : G.u1_TR < G.u1_BR := h2.resolve_right (htop ▸ lt_irrefl _)
    have p4 : G.u2_BR < G.u2_BL := h4.resolve_left (not_lt.mpr (le_of_lt p2))
    have p3 : G.u1_BL < G.u1_TL := h3.resolve_right (not_lt.mpr (le_of_lt p4))
    exact absurd p3 (not_lt.mpr (le_of_lt p1))
  · -- Case: u2_TR < u2_TL → first disjunct of fullCycling
    left
    have p1 : G.u1_TL < G.u1_BL := h1.resolve_right (not_lt.mpr (le_of_lt htop))
    have p3 : G.u2_BL < G.u2_BR := h3.resolve_left (not_lt.mpr (le_of_lt p1))
    have p4 : G.u1_BR < G.u1_TR := h4.resolve_right (not_lt.mpr (le_of_lt p3))
    exact ⟨p1, p4, htop, p3⟩

/-- Generic crossing lemma: if f and g are betweenness-respecting and cross,
    there exists a common value. Wraps CrossingAxiom for direct use. -/
lemma crossing_gives_common_value {I : Type u} {R : Type*}
    [SyntheticInterval I] [LinearOrder R] [CrossingAxiom I R]
    {f g : I → R} (hf : weakBetweenness f) (hg : weakBetweenness g)
    (hf0_le_g0 : f SyntheticInterval.zero ≤ g SyntheticInterval.zero)
    (hg1_le_f1 : g SyntheticInterval.one ≤ f SyntheticInterval.one) :
    ∃ p : I, f p = g p :=
  CrossingAxiom.crossing_point f g hf hg (Or.inl ⟨hf0_le_g0, hg1_le_f1⟩)

/-- Symmetric version: g starts above f and f ends above g. -/
lemma crossing_gives_common_value' {I : Type u} {R : Type*}
    [SyntheticInterval I] [LinearOrder R] [CrossingAxiom I R]
    {f g : I → R} (hf : weakBetweenness f) (hg : weakBetweenness g)
    (hg0_le_f0 : g SyntheticInterval.zero ≤ f SyntheticInterval.zero)
    (hf1_le_g1 : f SyntheticInterval.one ≤ g SyntheticInterval.one) :
    ∃ p : I, f p = g p :=
  CrossingAxiom.crossing_point f g hf hg (Or.inr ⟨hg0_le_f0, hf1_le_g1⟩)

/-- Main theorem for 2×2 games: either a pure Nash exists, or given
    betweenness-respecting payoff extensions along the mixing edges,
    indifference points exist for both players.

    Boundary conventions:
    - f₁(0→1) = u1(Top, Left→Right): Player 1's Top payoff as P2 varies
    - g₁(0→1) = u1(Bottom, Left→Right): Player 1's Bottom payoff as P2 varies
    - f₂(0→1) = u2(Top→Bottom, Left): Player 2's Left payoff as P1 varies
    - g₂(0→1) = u2(Top→Bottom, Right): Player 2's Right payoff as P1 varies -/
theorem TwoByTwoGame.twoByTwo_nash_exists
    (G : TwoByTwoGame) (I : Type u) [SyntheticInterval I] [CrossingAxiom I G.R] :
    G.hasPureNash ∨ (∀ (f₁ g₁ f₂ g₂ : I → G.R),
      weakBetweenness f₁ → weakBetweenness g₁ →
      weakBetweenness f₂ → weakBetweenness g₂ →
      -- f₁ = P1's payoff from Top as P2 varies Left(0)→Right(1)
      f₁ SyntheticInterval.zero = G.u1_TL →
      f₁ SyntheticInterval.one = G.u1_TR →
      -- g₁ = P1's payoff from Bottom as P2 varies Left(0)→Right(1)
      g₁ SyntheticInterval.zero = G.u1_BL →
      g₁ SyntheticInterval.one = G.u1_BR →
      -- f₂ = P2's payoff from Left as P1 varies Top(0)→Bottom(1)
      f₂ SyntheticInterval.zero = G.u2_TL →
      f₂ SyntheticInterval.one = G.u2_BL →
      -- g₂ = P2's payoff from Right as P1 varies Top(0)→Bottom(1)
      g₂ SyntheticInterval.zero = G.u2_TR →
      g₂ SyntheticInterval.one = G.u2_BR →
      -- Both players have indifference points
      (∃ p : I, f₂ p = g₂ p) ∧ (∃ q : I, f₁ q = g₁ q)) := by
  by_cases h : G.hasPureNash
  · left; exact h
  · right
    intro f₁ g₁ f₂ g₂ hf₁ hg₁ hf₂ hg₂ hf₁0 hf₁1 hg₁0 hg₁1 hf₂0 hf₂1 hg₂0 hg₂1
    have hfc := G.no_pure_implies_full_cycling h
    constructor
    · -- Player 2's indifference point: f₂ and g₂ cross
      rcases hfc with ⟨_, _, h_p2_top, h_p2_bot⟩ | ⟨_, _, h_p2_top, h_p2_bot⟩
      · -- Case 1: u2_TR < u2_TL and u2_BL < u2_BR
        -- g₂(0)=u2_TR ≤ f₂(0)=u2_TL and f₂(1)=u2_BL ≤ g₂(1)=u2_BR
        exact crossing_gives_common_value' hf₂ hg₂
          (by rw [hg₂0, hf₂0]; exact le_of_lt h_p2_top)
          (by rw [hf₂1, hg₂1]; exact le_of_lt h_p2_bot)
      · -- Case 2: u2_TL < u2_TR and u2_BR < u2_BL
        -- f₂(0)=u2_TL ≤ g₂(0)=u2_TR and g₂(1)=u2_BR ≤ f₂(1)=u2_BL
        exact crossing_gives_common_value hf₂ hg₂
          (by rw [hf₂0, hg₂0]; exact le_of_lt h_p2_top)
          (by rw [hg₂1, hf₂1]; exact le_of_lt h_p2_bot)
    · -- Player 1's indifference point: f₁ and g₁ cross
      rcases hfc with ⟨h_p1_left, h_p1_right, _, _⟩ | ⟨h_p1_left, h_p1_right, _, _⟩
      · -- Case 1: u1_TL < u1_BL and u1_BR < u1_TR
        -- f₁(0)=u1_TL ≤ g₁(0)=u1_BL and g₁(1)=u1_BR ≤ f₁(1)=u1_TR
        exact crossing_gives_common_value hf₁ hg₁
          (by rw [hf₁0, hg₁0]; exact le_of_lt h_p1_left)
          (by rw [hg₁1, hf₁1]; exact le_of_lt h_p1_right)
      · -- Case 2: u1_BL < u1_TL and u1_TR < u1_BR
        -- g₁(0)=u1_BL ≤ f₁(0)=u1_TL and f₁(1)=u1_TR ≤ g₁(1)=u1_BR
        exact crossing_gives_common_value' hf₁ hg₁
          (by rw [hg₁0, hf₁0]; exact le_of_lt h_p1_left)
          (by rw [hf₁1, hg₁1]; exact le_of_lt h_p1_right)

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

/-- Matching Pennies exhibits full cycling -/
theorem matchingPennies_has_fullCycling : matchingPennies.fullCycling := by
  simp [matchingPennies, TwoByTwoGame.fullCycling]

/-- Matching Pennies exhibits cycling -/
@[deprecated "Use matchingPennies_has_fullCycling." (since := "2026-01-31")]
theorem matchingPennies_has_cycling : matchingPennies.hasCycling := by
  exact (TwoByTwoGame.hasCycling_of_fullCycling (G := matchingPennies)
    matchingPennies_has_fullCycling)

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
  actionNonempty := fun _ => ⟨TwoAction.A⟩
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
