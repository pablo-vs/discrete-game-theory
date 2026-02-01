/-
  Synthetic Game Theory: Nash Equilibria via Ordinal Utilities and Synthetic Simplices

  This formalization develops game theory without numerical probabilities or cardinal utilities.
  Mixed strategies live in "synthetic simplices" with an abstract mixing operation, and
  utilities are purely ordinal (LinearOrder). The existence of Nash equilibria follows from
  a Synthetic Kakutani Axiom applied to the best-response correspondence, which is shown
  to be nonempty (convex_max), mix-closed (betweenness), and vertex-monotone
  (order preservation).
-/

import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder

universe u v

/-! ## Part 1: Ordinal Utilities

We use Mathlib's `LinearOrder` directly instead of a custom `OrdinalUtility` class.
Any type with `[LinearOrder R]` can serve as an ordinal utility codomain.
This gives us `≤`, `<`, `min`, `max`, decidable comparisons, and all Mathlib order lemmas. -/


/-! ## Part 2: Betweenness -/

/-- Betweenness for functions on a type with a binary mix operation.
    No domain order is needed — only the codomain order matters.
    The value at mix(x,y) lies between the values at x and y. -/
def mixBetweenness {S : Type*} {R : Type*} [LE R]
    (mix : S → S → S) (f : S → R) : Prop :=
  ∀ x y : S,
    (f x ≤ f y → f x ≤ f (mix x y) ∧ f (mix x y) ≤ f y) ∧
    (f y ≤ f x → f y ≤ f (mix x y) ∧ f (mix x y) ≤ f x)


/-! ## Part 3: Synthetic Simplices -/

/-- A set is mix-closed if it is closed under the mixing operation. -/
def mixClosed {S : Type*} (mix : S → S → S) (T : Set S) : Prop :=
  ∀ a b, a ∈ T → b ∈ T → mix a b ∈ T

/-- The segment between two points: the smallest mix-closed set containing both.
    Defined via a universal property for Kripke/presheaf compatibility. -/
def mixSegment {S : Type*} (mix : S → S → S) (x y : S) : Set S :=
  { z | ∀ T : Set S, mixClosed mix T → x ∈ T → y ∈ T → z ∈ T }

lemma mem_mixSegment_left {S : Type*} {mix : S → S → S} {x y : S} :
    x ∈ mixSegment mix x y :=
  fun _ _ hx _ => hx

lemma mem_mixSegment_right {S : Type*} {mix : S → S → S} {x y : S} :
    y ∈ mixSegment mix x y :=
  fun _ _ _ hy => hy

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
  /-- Segment linear order with strict betweenness: for any two distinct
      carrier points, the segment between them (smallest mix-closed set
      containing both) admits a linear order in which mix produces a point
      strictly between its inputs. This prevents degenerate models with
      cyclic mixing (e.g., mix a b = m, mix a m = b, mix b m = a) where
      SyntheticKakutani would be falsifiable. See also derived lemmas
      `mix_nondegen` and `mix_ne_right`. -/
  segment_order : ∀ x y, x ≠ y →
    ∃ r : carrier → carrier → Prop,
      (∀ a b, a ∈ mixSegment mix x y → b ∈ mixSegment mix x y →
        r a b ∨ r b a) ∧
      (∀ a b c, a ∈ mixSegment mix x y → b ∈ mixSegment mix x y →
        c ∈ mixSegment mix x y → r a b → r b c → r a c) ∧
      (∀ a b, a ∈ mixSegment mix x y → b ∈ mixSegment mix x y →
        r a b → r b a → a = b) ∧
      (∀ a b, a ∈ mixSegment mix x y → b ∈ mixSegment mix x y → a ≠ b →
        mix a b ≠ a ∧ mix a b ≠ b ∧
        (r a b → r a (mix a b) ∧ r (mix a b) b) ∧
        (r b a → r b (mix a b) ∧ r (mix a b) a))
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

/-- Non-degeneracy: mixing distinct points never returns the first point.
    Derived from `segment_order`. -/
lemma SyntheticSimplex.mix_nondegen {V : Type u} (Δ : SyntheticSimplex V)
    {x y : Δ.carrier} (h : x ≠ y) : Δ.mix x y ≠ x := by
  obtain ⟨_, _, _, _, hbet⟩ := Δ.segment_order x y h
  exact (hbet x y mem_mixSegment_left mem_mixSegment_right h).1

lemma SyntheticSimplex.mix_ne_right {V : Type u} (Δ : SyntheticSimplex V)
    {x y : Δ.carrier} (h : x ≠ y) : Δ.mix x y ≠ y := by
  rw [Δ.mix_comm]
  exact Δ.mix_nondegen (Ne.symm h)

/-- Derived form of `convex_max`: every betweenness-respecting function into a
    linear order achieves its maximum at a vertex. -/
lemma SyntheticSimplex.convex_max_fn {V : Type u} (Δ : SyntheticSimplex V)
    {R : Type*} [LinearOrder R] (f : Δ.carrier → R)
    (hf : mixBetweenness Δ.mix f) : ∃ a : V, ∀ x : Δ.carrier, f x ≤ f (Δ.vertex a) :=
  Δ.convex_max (fun x y => f x ≤ f y)
    (fun x y => le_total (f x) (f y))
    (fun _ _ _ hab hbc => le_trans hab hbc)
    (fun x y => hf x y)


/-! ## Part 4: Games -/

/-- A game with ordinal utilities and synthetic simplices.
    No finiteness assumption on action sets — `convex_max` handles optimization. -/
structure Game where
  numPlayers : ℕ
  Action : Fin numPlayers → Type*
  R : Type*
  instLinearOrder : LinearOrder R
  simplex : ∀ i, SyntheticSimplex (Action i)
  payoff : (∀ i, Action i) → Fin numPlayers → R

attribute [instance] Game.instLinearOrder

/-- A pure strategy profile -/
def Game.PureProfile (G : Game) := ∀ i, G.Action i

/-- A mixed strategy profile: a point in each player's simplex -/
def Game.MixedProfile (G : Game) := ∀ i, (G.simplex i).carrier

/-- Embed a pure strategy profile into a mixed strategy profile -/
def Game.pureToMixed (G : Game) (pure : G.PureProfile) : G.MixedProfile :=
  fun i => (G.simplex i).vertex (pure i)

/-- Substitute player i's strategy in a mixed profile -/
def Game.substStrategy (G : Game) (σ : G.MixedProfile)
    (i : Fin G.numPlayers) (τ : (G.simplex i).carrier) : G.MixedProfile :=
  fun j => if h : j = i then h ▸ τ else σ j

/-- `substStrategy` with `G` implicit, for use with notation. -/
def Game.MixedProfile.subst {G : Game} (σ : G.MixedProfile)
    (i : Fin G.numPlayers) (τ : (G.simplex i).carrier) : G.MixedProfile :=
  G.substStrategy σ i τ

namespace Game
scoped notation σ "[" i " ↦ " τ "]" => Game.MixedProfile.subst σ i τ
end Game

open scoped Game

@[simp] lemma Game.substStrategy_same (G : Game) (σ : G.MixedProfile)
    (i : Fin G.numPlayers) (τ : (G.simplex i).carrier) :
    G.substStrategy σ i τ i = τ := by
  simp [Game.substStrategy]

@[simp] lemma Game.substStrategy_ne (G : Game) (σ : G.MixedProfile)
    (i : Fin G.numPlayers) (τ : (G.simplex i).carrier)
    (j : Fin G.numPlayers) (h : j ≠ i) :
    G.substStrategy σ i τ j = σ j := by
  simp [Game.substStrategy, h]

@[simp] lemma Game.substStrategy_self (G : Game) (σ : G.MixedProfile)
    (i : Fin G.numPlayers) :
    G.substStrategy σ i (σ i) = σ := by
  funext j
  simp only [substStrategy]
  split
  · next h => subst h; rfl
  · rfl

/-! ## Part 5: Extended Utilities and Best Response -/

/-- Utility extended to mixed strategies, satisfying betweenness.
    This is axiomatic: we assert the extension exists with the right properties. -/
class ExtendedUtility (G : Game) where
  payoff : G.MixedProfile → Fin G.numPlayers → G.R
  agrees_pure : ∀ (pure : G.PureProfile) (i : Fin G.numPlayers),
    payoff (G.pureToMixed pure) i = G.payoff pure i
  /-- Mixing any two strategies for player i produces an intermediate utility
      for every player j. This is the carrier-wide betweenness axiom — no
      domain order is needed. -/
  betweenness : ∀ (σ : G.MixedProfile) (i j : Fin G.numPlayers),
    mixBetweenness (G.simplex i).mix (fun τ => payoff (σ[i ↦ τ]) j)
  /-- Order preservation: if pure action a ≤ b for player i at profiles
      differing in player k's strategy (x and y), then a ≤ b at the mixed
      profile (k ↦ mix x y). Strictly weaker than linearity of expected
      utility — the minimal axiom needed for the best-response correspondence
      to have the closed-graph property (synthetic upper hemicontinuity). -/
  order_preservation : ∀ (σ : G.MixedProfile) (k : Fin G.numPlayers)
    (x y : (G.simplex k).carrier) (i : Fin G.numPlayers) (a b : G.Action i),
    payoff ((σ[k ↦ x])[i ↦ (G.simplex i).vertex a]) i ≤
    payoff ((σ[k ↦ x])[i ↦ (G.simplex i).vertex b]) i →
    payoff ((σ[k ↦ y])[i ↦ (G.simplex i).vertex a]) i ≤
    payoff ((σ[k ↦ y])[i ↦ (G.simplex i).vertex b]) i →
    payoff ((σ[k ↦ (G.simplex k).mix x y])[i ↦ (G.simplex i).vertex a]) i ≤
    payoff ((σ[k ↦ (G.simplex k).mix x y])[i ↦ (G.simplex i).vertex b]) i

/-- Best response: player i's strategy is optimal given others' strategies -/
def Game.isBestResponse (G : Game) [ExtendedUtility G]
    (σ : G.MixedProfile) (i : Fin G.numPlayers) : Prop :=
  ∀ τ : (G.simplex i).carrier,
    ExtendedUtility.payoff (σ[i ↦ τ]) i ≤ ExtendedUtility.payoff σ i


/-! ## Part 6: Nash Equilibrium -/

/-- A Nash equilibrium: every player is best-responding -/
def Game.isNashEquilibrium (G : Game) [ExtendedUtility G]
    (σ : G.MixedProfile) : Prop :=
  ∀ i, G.isBestResponse σ i

/-- Key lemma: Best responses always include a pure strategy.
    By `convex_max`, the utility function (which satisfies betweenness) achieves
    its maximum at some vertex = pure strategy. -/
lemma Game.bestResponseContainsPure (G : Game) [ExtendedUtility G]
    (σ : G.MixedProfile) (i : Fin G.numPlayers) :
    ∃ a : G.Action i, ∀ τ : (G.simplex i).carrier,
      ExtendedUtility.payoff (σ[i ↦ τ]) i ≤
      ExtendedUtility.payoff (σ[i ↦ (G.simplex i).vertex a]) i :=
  (G.simplex i).convex_max_fn
    (fun τ => ExtendedUtility.payoff (σ[i ↦ τ]) i)
    (ExtendedUtility.betweenness σ i i)

/-- If a pure action is optimal among all pure actions, it is optimal among all
    strategies (pure and mixed). Follows from `convex_max`: the maximum over
    all strategies is at some vertex b, and a beats b by hypothesis. -/
lemma Game.pureOptimal_implies_allOptimal (G : Game) [ExtendedUtility G]
    (σ : G.MixedProfile) (i : Fin G.numPlayers) (a : G.Action i)
    (ha : ∀ b : G.Action i,
      ExtendedUtility.payoff (σ[i ↦ (G.simplex i).vertex b]) i ≤
      ExtendedUtility.payoff (σ[i ↦ (G.simplex i).vertex a]) i) :
    ∀ τ : (G.simplex i).carrier,
      ExtendedUtility.payoff (σ[i ↦ τ]) i ≤
      ExtendedUtility.payoff (σ[i ↦ (G.simplex i).vertex a]) i := by
  obtain ⟨b, hb⟩ := (G.simplex i).convex_max_fn
    (fun τ => ExtendedUtility.payoff (σ[i ↦ τ]) i)
    (ExtendedUtility.betweenness σ i i)
  intro τ
  exact le_trans (hb τ) (ha b)


/-! ## Part 7: General Nash Existence via Synthetic Kakutani Axiom -/

/-- A Nash equilibrium witness: bundles a profile with its proof.
    Useful for finite models where the equilibrium is explicit data. -/
structure NashWitness (G : Game) [ExtendedUtility G] where
  profile : G.MixedProfile
  is_nash : G.isNashEquilibrium profile

/-- Synthetic Kakutani Axiom: a correspondence on the product of simplices with
    nonempty, mix-closed values and vertex preservation under coordinate mixing
    has a fixed point. This replaces `SyntheticFixedPoint` (Brouwer for functions).
    Working with correspondences directly avoids the need to select a continuous
    function from the best-response set-valued map (see AD-11).

    In the standard model, this follows from Kakutani's fixed-point theorem.
    In finitely-presented models, the user provides the fixed-point witness. -/
class SyntheticKakutani (G : Game) where
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
       (G.simplex i).vertex a ∈ F (σ[k ↦ x]) i →
       (G.simplex i).vertex a ∈ F (σ[k ↦ y]) i →
       (G.simplex i).vertex a ∈ F (σ[k ↦ (G.simplex k).mix x y]) i) →
    ∃ σ : G.MixedProfile, ∀ i, σ i ∈ F σ i

/-- The best response set: all strategies for player i that are weakly optimal
    given the other players' strategies in σ. -/
def Game.bestResponseSet (G : Game) [ExtendedUtility G]
    (σ : G.MixedProfile) (i : Fin G.numPlayers) : Set (G.simplex i).carrier :=
  {τ | ∀ τ', ExtendedUtility.payoff (σ[i ↦ τ']) i ≤ ExtendedUtility.payoff (σ[i ↦ τ]) i}

/-- The best response set is nonempty: by `bestResponseContainsPure`, there is
    always a pure strategy that is optimal. -/
lemma Game.bestResponseSet_nonempty (G : Game) [ExtendedUtility G]
    (σ : G.MixedProfile) (i : Fin G.numPlayers) :
    ∃ x, x ∈ G.bestResponseSet σ i := by
  obtain ⟨a, ha⟩ := G.bestResponseContainsPure σ i
  exact ⟨(G.simplex i).vertex a, ha⟩

/-- The best response set is mix-closed: if τ₁ and τ₂ are both best responses,
    their mix is also a best response (by betweenness, its utility lies between
    the two, both of which are maximal). -/
lemma Game.bestResponseSet_mix_closed (G : Game) [ExtendedUtility G]
    (σ : G.MixedProfile) (i : Fin G.numPlayers)
    (x y : (G.simplex i).carrier)
    (hx : x ∈ G.bestResponseSet σ i) (hy : y ∈ G.bestResponseSet σ i) :
    (G.simplex i).mix x y ∈ G.bestResponseSet σ i := by
  intro τ'
  have hbet := ExtendedUtility.betweenness σ i i x y
  rcases le_total
    (ExtendedUtility.payoff (σ[i ↦ x]) i)
    (ExtendedUtility.payoff (σ[i ↦ y]) i) with hxy | hyx
  · exact le_trans (hx τ') (hbet.1 hxy).1
  · exact le_trans (hy τ') (hbet.2 hyx).1

/-- The best response set has vertex preservation: if vertex a is a best response
    at σ[k ↦ x] and at σ[k ↦ y], then it is a best response at σ[k ↦ mix x y].
    Proof uses order preservation to show a beats every pure b at the mixed profile,
    then pureOptimal_implies_allOptimal to extend to all mixed strategies. -/
lemma Game.bestResponseSet_vertex_monotone (G : Game) [ExtendedUtility G]
    (σ : G.MixedProfile) (k : Fin G.numPlayers)
    (x y : (G.simplex k).carrier)
    (i : Fin G.numPlayers) (a : G.Action i)
    (hx : (G.simplex i).vertex a ∈ G.bestResponseSet (σ[k ↦ x]) i)
    (hy : (G.simplex i).vertex a ∈ G.bestResponseSet (σ[k ↦ y]) i) :
    (G.simplex i).vertex a ∈
      G.bestResponseSet (σ[k ↦ (G.simplex k).mix x y]) i :=
  G.pureOptimal_implies_allOptimal (σ[k ↦ (G.simplex k).mix x y]) i a
    (fun b => ExtendedUtility.order_preservation σ k x y i b a
      (hx ((G.simplex i).vertex b))
      (hy ((G.simplex i).vertex b)))

/-- General Nash existence: every game with extended utilities and the
    Synthetic Kakutani axiom has a Nash equilibrium.

    Proof: the best response correspondence is nonempty (bestResponseContainsPure),
    mix-closed (betweenness), and vertex-monotone (order preservation). The Kakutani
    axiom gives a fixed point σ where σ i ∈ bestResponseSet σ i for all i.
    Since σ[i ↦ σ i] = σ (substStrategy_self), this means every player is
    best-responding — a Nash equilibrium. -/
theorem Game.nash_exists (G : Game) [ExtendedUtility G]
    [SyntheticKakutani G] :
    ∃ σ : G.MixedProfile, G.isNashEquilibrium σ := by
  obtain ⟨σ, hσ⟩ := SyntheticKakutani.fixed_point
    (fun σ i => G.bestResponseSet σ i)
    (fun σ i => G.bestResponseSet_nonempty σ i)
    (fun σ i x y hx hy => G.bestResponseSet_mix_closed σ i x y hx hy)
    (fun σ k x y i a hx hy => G.bestResponseSet_vertex_monotone σ k x y i a hx hy)
  exact ⟨σ, fun i τ => by
    have h := hσ i τ
    unfold Game.MixedProfile.subst at h
    rwa [G.substStrategy_self] at h⟩
