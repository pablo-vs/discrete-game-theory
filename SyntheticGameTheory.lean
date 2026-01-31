/-
  Synthetic Game Theory: Nash Equilibria via Ordinal Utilities and Crossing Axioms

  This formalization develops game theory without numerical probabilities or cardinal utilities.
  Mixed strategies live in "synthetic simplices" with an abstract mixing operation, and
  utilities are purely ordinal (LinearOrder). The existence of Nash equilibria follows from
  a Crossing Axiom that asserts crossing points exist for betweenness-respecting functions.

  Inspired by cubical type theory's treatment of the interval.
-/

import Mathlib.Order.Basic
import Mathlib.Data.Fintype.Basic
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

/-- A synthetic simplex over a set of vertices.
    This is the abstract mixed strategy space. The `convex_max` axiom asserts
    that for any total betweenness-respecting preorder on the carrier, some
    vertex is maximal — the synthetic Bauer maximum principle. -/
structure SyntheticSimplex (V : Type u) where
  carrier : Type u
  vertex : V → carrier
  mix : carrier → carrier → carrier
  vertex_injective : Function.Injective vertex
  mix_idem : ∀ x, mix x x = x
  mix_comm : ∀ x y, mix x y = mix y x
  /-- Synthetic Bauer maximum principle: for any total preorder on the carrier
      that respects mix-betweenness, some vertex is maximal. Formulated at the
      Prop level (no external type parameter) to avoid universe issues.
      The function-into-R version is derived as `convex_max_fn`. -/
  convex_max : ∀ (r : carrier → carrier → Prop),
    (∀ x y, r x y ∨ r y x) →
    (∀ x y z, r x y → r y z → r x z) →
    (∀ x y, (r x y → r x (mix x y) ∧ r (mix x y) y) ∧
            (r y x → r y (mix x y) ∧ r (mix x y) x)) →
    ∃ a : V, ∀ x : carrier, r x (vertex a)

/-- Derived form of `convex_max`: every betweenness-respecting function into a
    linear order achieves its maximum at a vertex. -/
lemma SyntheticSimplex.convex_max_fn {V : Type u} (Δ : SyntheticSimplex V)
    {R : Type*} [LinearOrder R] (f : Δ.carrier → R)
    (hf : mixBetweenness Δ.mix f) : ∃ a : V, ∀ x : Δ.carrier, f x ≤ f (Δ.vertex a) :=
  Δ.convex_max (fun x y => f x ≤ f y)
    (fun x y => le_total (f x) (f y))
    (fun _ _ _ hab hbc => le_trans hab hbc)
    (fun x y => hf x y)

/-- The edge between two vertices forms a synthetic interval -/
structure Edge {V : Type u} (Δ : SyntheticSimplex V) (v w : V) where
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
def Edge.embed {V : Type u} {Δ : SyntheticSimplex V} {v w : V}
    (e : Edge Δ v w) (t : Subtype e.points) : Δ.carrier := t.val

/-- An edge can be viewed as a synthetic interval -/
def Edge.toSyntheticInterval {V : Type u} {Δ : SyntheticSimplex V} {v w : V}
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

@[simp] lemma FiniteGame.substStrategy_self (G : FiniteGame) (σ : G.MixedProfile)
    (i : Fin G.numPlayers) :
    G.substStrategy σ i (σ i) = σ := by
  funext j
  simp only [substStrategy]
  split
  · next h => subst h; rfl
  · rfl

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
  /-- Order preservation: if pure action a ≤ b for player i at profiles
      differing in player k's strategy (x and y), then a ≤ b at the mixed
      profile (k ↦ mix x y). Strictly weaker than linearity of expected
      utility — the minimal axiom needed for the best-response correspondence
      to have the closed-graph property (synthetic upper hemicontinuity). -/
  order_preservation : ∀ (σ : G.MixedProfile) (k : Fin G.numPlayers)
    (x y : (G.simplex k).carrier) (i : Fin G.numPlayers) (a b : G.Action i),
    payoff (G.substStrategy (G.substStrategy σ k x) i ((G.simplex i).vertex a)) i ≤
    payoff (G.substStrategy (G.substStrategy σ k x) i ((G.simplex i).vertex b)) i →
    payoff (G.substStrategy (G.substStrategy σ k y) i ((G.simplex i).vertex a)) i ≤
    payoff (G.substStrategy (G.substStrategy σ k y) i ((G.simplex i).vertex b)) i →
    payoff (G.substStrategy (G.substStrategy σ k ((G.simplex k).mix x y)) i
      ((G.simplex i).vertex a)) i ≤
    payoff (G.substStrategy (G.substStrategy σ k ((G.simplex k).mix x y)) i
      ((G.simplex i).vertex b)) i

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
    By `convex_max`, the utility function (which satisfies betweenness) achieves
    its maximum at some vertex = pure strategy. -/
lemma FiniteGame.bestResponseContainsPure (G : FiniteGame) [ExtendedUtility G]
    (σ : G.MixedProfile) (i : Fin G.numPlayers) :
    ∃ a : G.Action i, ∀ τ : (G.simplex i).carrier,
      ExtendedUtility.payoff (G.substStrategy σ i τ) i ≤
      ExtendedUtility.payoff (G.substStrategy σ i ((G.simplex i).vertex a)) i :=
  (G.simplex i).convex_max_fn
    (fun τ => ExtendedUtility.payoff (G.substStrategy σ i τ) i)
    (ExtendedUtility.betweenness σ i i)

/-- If a pure action is optimal among all pure actions, it is optimal among all
    strategies (pure and mixed). Follows from `convex_max`: the maximum over
    all strategies is at some vertex b, and a beats b by hypothesis. -/
lemma FiniteGame.pureOptimal_implies_allOptimal (G : FiniteGame) [ExtendedUtility G]
    (σ : G.MixedProfile) (i : Fin G.numPlayers) (a : G.Action i)
    (ha : ∀ b : G.Action i,
      ExtendedUtility.payoff (G.substStrategy σ i ((G.simplex i).vertex b)) i ≤
      ExtendedUtility.payoff (G.substStrategy σ i ((G.simplex i).vertex a)) i) :
    ∀ τ : (G.simplex i).carrier,
      ExtendedUtility.payoff (G.substStrategy σ i τ) i ≤
      ExtendedUtility.payoff (G.substStrategy σ i ((G.simplex i).vertex a)) i := by
  obtain ⟨b, hb⟩ := (G.simplex i).convex_max_fn
    (fun τ => ExtendedUtility.payoff (G.substStrategy σ i τ) i)
    (ExtendedUtility.betweenness σ i i)
  intro τ
  exact le_trans (hb τ) (ha b)


/-! ## Part 9: General Nash Existence via Synthetic Kakutani Axiom -/

/-- A Nash equilibrium witness: bundles a profile with its proof.
    Useful for finite models where the equilibrium is explicit data. -/
structure NashWitness (G : FiniteGame) [ExtendedUtility G] where
  profile : G.MixedProfile
  is_nash : G.isNashEquilibrium profile

/-- Synthetic Kakutani Axiom: a correspondence on the product of simplices with
    nonempty, mix-closed values and vertex preservation under coordinate mixing
    has a fixed point. This replaces `SyntheticFixedPoint` (Brouwer for functions).
    Working with correspondences directly avoids the need to select a continuous
    function from the best-response set-valued map (see AD-11).

    In the standard model, this follows from Kakutani's fixed-point theorem.
    In finitely-presented models, the user provides the fixed-point witness. -/
class SyntheticKakutani (G : FiniteGame) where
  fixed_point :
    ∀ (F : G.MixedProfile → ∀ i : Fin G.numPlayers, Set (G.simplex i).carrier),
    -- Nonempty values
    (∀ σ i, ∃ x, x ∈ F σ i) →
    -- Mix-closed values
    (∀ σ i x y, x ∈ F σ i → y ∈ F σ i → (G.simplex i).mix x y ∈ F σ i) →
    -- Vertex preservation: if vertex a ∈ F(σ[k ↦ x])(i) and ∈ F(σ[k ↦ y])(i),
    -- then vertex a ∈ F(σ[k ↦ mix x y])(i)
    (∀ σ (k : Fin G.numPlayers) (x y : (G.simplex k).carrier)
       (i : Fin G.numPlayers) (a : G.Action i),
       (G.simplex i).vertex a ∈ F (G.substStrategy σ k x) i →
       (G.simplex i).vertex a ∈ F (G.substStrategy σ k y) i →
       (G.simplex i).vertex a ∈ F (G.substStrategy σ k ((G.simplex k).mix x y)) i) →
    ∃ σ : G.MixedProfile, ∀ i, σ i ∈ F σ i

/-- The best response set: all strategies for player i that are weakly optimal
    given the other players' strategies in σ. -/
def FiniteGame.bestResponseSet (G : FiniteGame) [ExtendedUtility G]
    (σ : G.MixedProfile) (i : Fin G.numPlayers) : Set (G.simplex i).carrier :=
  {τ | ∀ τ' : (G.simplex i).carrier,
    ExtendedUtility.payoff (G.substStrategy σ i τ') i ≤
    ExtendedUtility.payoff (G.substStrategy σ i τ) i}

/-- The best response set is nonempty: by `bestResponseContainsPure`, there is
    always a pure strategy that is optimal. -/
lemma FiniteGame.bestResponseSet_nonempty (G : FiniteGame) [ExtendedUtility G]
    (σ : G.MixedProfile) (i : Fin G.numPlayers) :
    ∃ x, x ∈ G.bestResponseSet σ i := by
  obtain ⟨a, ha⟩ := G.bestResponseContainsPure σ i
  exact ⟨(G.simplex i).vertex a, ha⟩

/-- The best response set is mix-closed: if τ₁ and τ₂ are both best responses,
    their mix is also a best response (by betweenness, its utility lies between
    the two, both of which are maximal). -/
lemma FiniteGame.bestResponseSet_mix_closed (G : FiniteGame) [ExtendedUtility G]
    (σ : G.MixedProfile) (i : Fin G.numPlayers)
    (x y : (G.simplex i).carrier)
    (hx : x ∈ G.bestResponseSet σ i) (hy : y ∈ G.bestResponseSet σ i) :
    (G.simplex i).mix x y ∈ G.bestResponseSet σ i := by
  intro τ'
  have hbet := ExtendedUtility.betweenness σ i i x y
  rcases le_total
    (ExtendedUtility.payoff (G.substStrategy σ i x) i)
    (ExtendedUtility.payoff (G.substStrategy σ i y) i) with hxy | hyx
  · exact le_trans (hx τ') (hbet.1 hxy).1
  · exact le_trans (hy τ') (hbet.2 hyx).1

/-- The best response set has vertex preservation: if vertex a is a best response
    at σ[k ↦ x] and at σ[k ↦ y], then it is a best response at σ[k ↦ mix x y].
    Proof uses order preservation to show a beats every pure b at the mixed profile,
    then pureOptimal_implies_allOptimal to extend to all mixed strategies. -/
lemma FiniteGame.bestResponseSet_vertex_monotone (G : FiniteGame) [ExtendedUtility G]
    (σ : G.MixedProfile) (k : Fin G.numPlayers)
    (x y : (G.simplex k).carrier)
    (i : Fin G.numPlayers) (a : G.Action i)
    (hx : (G.simplex i).vertex a ∈ G.bestResponseSet (G.substStrategy σ k x) i)
    (hy : (G.simplex i).vertex a ∈ G.bestResponseSet (G.substStrategy σ k y) i) :
    (G.simplex i).vertex a ∈
      G.bestResponseSet (G.substStrategy σ k ((G.simplex k).mix x y)) i :=
  G.pureOptimal_implies_allOptimal
    (G.substStrategy σ k ((G.simplex k).mix x y)) i a
    (fun b => ExtendedUtility.order_preservation σ k x y i b a
      (hx ((G.simplex i).vertex b))
      (hy ((G.simplex i).vertex b)))

/-- General Nash existence: every finite game with extended utilities and the
    Synthetic Kakutani axiom has a Nash equilibrium.

    Proof: the best response correspondence is nonempty (bestResponseContainsPure),
    mix-closed (betweenness), and vertex-monotone (order preservation). The Kakutani
    axiom gives a fixed point σ where σ i ∈ bestResponseSet σ i for all i.
    Since σ[i ↦ σ i] = σ (substStrategy_self), this means every player is
    best-responding — a Nash equilibrium. -/
theorem FiniteGame.nash_exists (G : FiniteGame) [ExtendedUtility G]
    [SyntheticKakutani G] :
    ∃ σ : G.MixedProfile, G.isNashEquilibrium σ := by
  obtain ⟨σ, hσ⟩ := SyntheticKakutani.fixed_point
    (fun σ i => G.bestResponseSet σ i)
    (fun σ i => G.bestResponseSet_nonempty σ i)
    (fun σ i x y hx hy => G.bestResponseSet_mix_closed σ i x y hx hy)
    (fun σ k x y i a hx hy => G.bestResponseSet_vertex_monotone σ k x y i a hx hy)
  exact ⟨σ, fun i τ => by
    have h := hσ i τ
    rwa [G.substStrategy_self] at h⟩


