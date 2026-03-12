import VersoManual
import DiscreteGameTheory.Base
import DiscreteGameTheoryExamples.Examples

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

set_option pp.rawOnError true
set_option verso.exampleProject "."
set_option verso.exampleModule "DiscreteGameTheory.Base"

open Base

#doc (Manual) "Games and Nash Equilibria" =>

Game theory studies strategic interactions: a set of players, each choosing actions, each with
preferences over outcomes. The central concept is *Nash equilibrium* — a combination of
strategies where no player can improve by changing only their own choice.

Standard game theory builds on real-valued payoffs and probability distributions, proving Nash
existence via topological fixed-point theorems. We replace all of this with discrete, finite
structures.

# Sign Games

A game has a finite set of players. Each player has a finite set of actions. A _pure profile_ is
a choice of action for every player.

In standard game theory, each player has a payoff function. We replace this with something weaker:
for each player, each profile, and each pair of actions, we record a _sign_ — positive if the
first action is better, negative if the second is better, zero if equivalent.

```anchor Sign
inductive Sign where
  | pos : Sign
  | neg : Sign
  | zero : Sign
```

A sign game bundles these signs with the axioms of a preference relation: reflexivity (comparing
an action to itself gives zero), antisymmetry (swapping actions flips the sign), transitivity,
and irrelevance (player i's preference depends only on opponents' actions, not on i's
"current" action).

```anchor SignGame
structure SignGame where
  sign : (i : I) → PureProfile I V → V i → V i → Sign
  sign_refl : ∀ i p a, sign i p a a = .zero
  sign_antisym : ∀ i p a b, sign i p a b = (sign i p b a).flip
  sign_trans : ∀ i p a b c, (sign i p a b).nonneg → (sign i p b c).nonneg →
    (sign i p a c).nonneg
  sign_irrel : ∀ i p q a b, (∀ j, j ≠ i → p j = q j) → sign i p a b = sign i q a b
```

A sign game can be constructed from integer payoff functions. The resulting signs just compare
payoff values. Crucially, any strictly monotone transformation of the payoffs produces the
same sign game — the theory is ordinal, not cardinal.

# Faces as Mixed Strategies

In standard game theory, players randomize using probability distributions over actions. We use
a discrete analogue: a _face_ is a nonempty subset of actions.

```anchor Face
def Face (V : Type*) [DecidableEq V] := { S : Finset V // S.Nonempty }
```

The face \{a, b\} represents "some distribution supported on a and b," without specifying
which one. A vertex \{a\} is a pure strategy. The full face is the maximally mixed strategy.
Mixing is set union — commutative, associative, idempotent.

A _profile_ assigns a face to each player.

# Dominance

Face A dominates face B for player i when every action in A is at least as good as every
action in B, against every consistent opponent play.

```anchor Dominates
def Dominates (i : I) (σ : Profile I V) (A B : Face (V i)) : Prop :=
  ∀ a ∈ A.1, ∀ p : PureProfile I V,
    ConsistentAt σ i p → ∀ b ∈ B.1, (G.sign i p a b).nonneg
```

This conservative comparison produces a *partial order*. Two faces can be genuinely incomparable —
and this is the key insight. In Matching Pennies, when the opponent mixes fully, neither Heads nor
Tails dominates the other. The deviation cycle dissolves into incomparability.

A _strict deviation_ exists when A dominates the current face but not vice versa. A profile is
*Nash* when no player has a strict deviation:

```anchor StrictDom
def StrictDom (i : I) (σ : Profile I V) (A : Face (V i)) : Prop :=
  G.Dominates i σ A (σ i) ∧ ¬G.Dominates i σ (σ i) A

def IsNash (σ : Profile I V) : Prop :=
  ∀ (i : I) (A : Face (V i)), ¬G.StrictDom i σ A
```

# Nash Existence

Every finite game has a Nash equilibrium:

```lean
example : ∀ (G : SignGame (Fin 2) (fun _ : Fin 2 => Bool)), ∃ σ, G.IsNash σ :=
  fun G => G.nash_exists
```

The proof is a descent algorithm. It starts from the fully mixed profile (every player plays every
action) and iteratively eliminates dominated actions.

The algorithm maintains the *OutsideDom (OD)* invariant: for each player, every action outside
the current face is dominated by every action inside:

```anchor OutsideDom
def OutsideDom (i : I) (σ : Profile I V) : Prop :=
  ∀ v, v ∉ (σ i).1 → ∀ w, w ∈ (σ i).1 →
    G.Dominates i σ (Face.vertex w) (Face.vertex v)
```

The full profile is vacuously OD (no outside actions). At each step, if some player has a strict
deviation, we restrict their face to a strict subface. Profile size (sum of face cardinalities)
decreases, so the algorithm terminates.

OD is preserved because: for the restricting player, the new face dominates the old, so it
dominates the already-dominated outside actions. For other players, antitonicity applies —
shrinking an opponent's face only makes domination easier.

# Examples

The Prisoner's Dilemma has a unique pure Nash at mutual defection:

```lean
example : ∀ p : PureProfile (Fin 2) (fun _ : Fin 2 => Bool),
    pd.IsPureNash p ↔ p = (fun _ => false) :=
  pd_unique_pureNash
```

Matching Pennies has no pure Nash — whatever pure profile you pick, one player wants to switch:

```lean
example : ∀ p : PureProfile (Fin 2) (fun _ : Fin 2 => Bool),
    ¬mp.IsPureNash p :=
  mp_no_pureNash
```

But the fully mixed profile (both players play both actions) is Nash — incomparability breaks
the cycle:

```lean
example : mp.IsNash (fun _ : Fin 2 => Face.full (V := Bool)) :=
  mp_mixed_nash
```
