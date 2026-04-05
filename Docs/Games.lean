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
preferences over outcomes defined by a payoff table. The fundamental concept is *Nash equilibrium* — a combination of
strategies where no player can improve by changing only their own choice.

Standard game theory builds on real-valued payoffs and probability distributions, proving Nash
existence via topological fixed-point theorems. We replace all of this with discrete, finite
structures.

The main goal of this section is to prove that all games with finite players and
finite actions have at least one Nash equilibrium. Standard game theory uses a
non-constructive fixed point theorem to do this, but in our setup we can give a
constructive algorithm.

# Sign Games

A game has a finite set of players. Each player has a finite set of actions.
Given an index of players `I: Type` and a function `V: I → Type` of possible actions
for each player, a _pure profile_ is defined as a choice of action for every player.

```anchor PureProfile
/-- A pure profile is a choice of action for each player. -/
abbrev PureProfile := ∀ i : I, V i
```

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
a discrete analogue: a _face_ is a nonempty subset of actions.  Intuitively
a face represents an unknown probability distribution, this intuition will be formalized
in {ref "refinement-towers"}[the refinement chapter].

```anchor Face
def Face (V : Type*) [DecidableEq V] := { S : Finset V // S.Nonempty }
```

The face \{a, b\} represents "some distribution supported on a and b," without specifying
which one. The name comes from the simplex, which all the possible mixtures of a set of
vertices form a face. A vertex \{a\} is a pure strategy. The full face (the whole simplex)
is the maximally mixed strategy. Mixing is set union — commutative, associative, idempotent.

A _profile_ assigns a face to each player.

```anchor Profile
/-- A profile is a choice of face (mixed strategy) for each player. -/
abbrev Profile := ∀ i : I, Face (V i)
```

# Dominance

In standard game theory one uses expected utility to extend a value function of pure actions
to one of probabilistic actions. The analogous ordinal concept is a preference order on faces
derived from the order on pure actions. Face A dominates face B for player i when every action
in A is at least as good as every action in B, against every consistent opponent play.

```anchor Dominates
def Dominates (i : I) (σ : Profile I V) (A B : Face (V i)) : Prop :=
  ∀ a ∈ A.1, ∀ p : PureProfile I V,
    ConsistentAt σ i p → ∀ b ∈ B.1, (G.sign i p a b).nonneg
```

This conservative comparison produces a *partial order*. Two faces can be genuinely incomparable —
and this is the key insight that makes it possible to prove the existence of Nash equilibria,
as we'll see later.

A _strict deviation_ exists when A dominates the current face but not vice versa. A profile is
*Nash* when no player has a strict deviation:

```anchor StrictDom
def StrictDom (i : I) (σ : Profile I V) (A : Face (V i)) : Prop :=
  G.Dominates i σ A (σ i) ∧ ¬G.Dominates i σ (σ i) A

def IsNash (σ : Profile I V) : Prop :=
  ∀ (i : I) (A : Face (V i)), ¬G.StrictDom i σ A
```

# Examples

Consider two classic 2-player games where each player has two actions. We write C/D
(cooperate/defect) for the Prisoner's Dilemma and H/T (heads/tails) for Matching Pennies.

## Prisoner's Dilemma

For each player, defection is strictly preferred regardless of the opponent's action:

$$`\begin{array}{c|ccc} \textbf{Opp} & & \textbf{Player} & \\ \hline C & C & \prec & D \\ D & C & \prec & D \end{array}`

Since D is better against every opponent action, the face \{D\} dominates every other face.
The dominance order on faces (for either player, against a fully mixed opponent) is total:

$$`\begin{array}{c|ccccc} \textbf{Opp} & & & \textbf{Player} & & \\ \hline \{C\} & \{C\} & \prec & \{C,D\} & \prec & \{D\} \\ \{D\} & \{C\} & \prec & \{C,D\} & \prec & \{D\} \\ \{C,D\} & \{C\} & \prec & \{C,D\} & \prec & \{D\} \end{array}`

The unique Nash equilibrium is mutual defection — no player can deviate from \{D\}.

## Matching Pennies

Player 1 (matcher) wants to match; player 2 (mismatcher) wants to differ.
For the matcher:

$$`\begin{array}{c|ccc} \textbf{Opp} & & \textbf{Matcher} & \\ \hline H & H & \succ & T \\ T & H & \prec & T \end{array}`

The preferred action depends on the opponent — H is better against H, T is better against T.
When the opponent plays the full face \{H, T\}, neither action dominates the other.
The dominance order on faces (against the fully mixed opponent) is flat — everything is
incomparable:

$$`\begin{array}{c|ccccc} \textbf{Opp} & & & \textbf{Matcher} & & \\ \hline \{H,T\} & \{H\} & \parallel & \{T\} & \parallel & \{H,T\} \end{array}`

There is no pure Nash equilibrium. But the fully mixed profile (\{H,T\} for both players) _is_
Nash — no face strictly dominates \{H,T\}, because incomparability blocks every deviation.
This is the key mechanism: the deviation cycle HH $`\to` HT $`\to` TT $`\to` TH $`\to` HH dissolves into
incomparability when we move from pure to mixed strategies.


# Nash Existence
%%%
tag := "outside-dom"
%%%

Every finite game has a Nash equilibrium:

```anchor nash_exists
theorem nash_exists [Fintype I] [∀ i, Fintype (V i)] [∀ i, Nonempty (V i)] :
    ∃ σ, G.IsNash σ :=
```

The proof is a descent algorithm. It starts from the fully mixed profile (every player plays
a mix of every action) and iteratively eliminates dominated actions.

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
